//! Deterministic renaming of type and presence variables for display.
//!
//! `tidy` rewrites a type so the variables it contains have small,
//! consecutive IDs assigned in traversal order. After tidying, the
//! pretty-printer's output is a pure function of its input: two
//! callers that hand the same tidied `Type` to a fresh
//! [`PrettyContext`] get byte-identical strings, with no need to
//! coordinate state between them.
//!
//! This is the boundary primitive that lets the CLI's AST decorator
//! and the LSP's hover/inlay-hint paths share one renderer without
//! drifting. The `PrettyContext` mutable letter-assignment state
//! still exists, but it becomes a redundant inner pass over already-
//! canonical IDs — fresh-per-call is fine.
//!
//! Inspired by GHC's `tidyType` / `TidyEnv`.

use std::collections::HashMap;

use super::ty::{
    FieldEntry, ModuleType, PVarId, PVarName, Presence, QualType, RowTail, RowType, TVarId,
    TVarName, Type, TypePred, TypeScheme,
};

/// Renaming context for one tidy operation.
///
/// Tidying multiple values *within the same scope* (e.g. a function
/// scheme plus every binding inside that function) means threading
/// one `TidyEnv` through them so a tvar shared by two of them ends
/// up with the same canonical ID — and therefore the same letter
/// once printed. Tidying values in unrelated scopes uses a fresh
/// env each.
#[derive(Debug, Default)]
pub struct TidyEnv {
    // Key on the full `TVarName` so a Flex and a Skolem that happen
    // to share an integer ID (in principle — inty's counter is
    // unified today but the type system doesn't promise it) get
    // distinct canonical IDs.
    type_vars: HashMap<TVarName, TVarId>,
    next_type: TVarId,
    presence_vars: HashMap<PVarName, PVarId>,
    next_presence: PVarId,
}

impl TidyEnv {
    pub fn new() -> Self {
        Self::default()
    }

    fn rename_tvar(&mut self, name: &TVarName) -> TVarName {
        let new_id = match self.type_vars.get(name) {
            Some(&v) => v,
            None => {
                let v = self.next_type;
                self.next_type += 1;
                self.type_vars.insert(name.clone(), v);
                v
            }
        };
        match name {
            TVarName::Flex(_) => TVarName::Flex(new_id),
            TVarName::Skolem(_) => TVarName::Skolem(new_id),
        }
    }

    fn rename_pvar(&mut self, name: &PVarName) -> PVarName {
        let new_id = match self.presence_vars.get(name) {
            Some(&v) => v,
            None => {
                let v = self.next_presence;
                self.next_presence += 1;
                self.presence_vars.insert(name.clone(), v);
                v
            }
        };
        match name {
            PVarName::Flex(_) => PVarName::Flex(new_id),
            PVarName::Skolem(_) => PVarName::Skolem(new_id),
        }
    }

    fn rename_presence(&mut self, p: &Presence) -> Presence {
        match p {
            Presence::Pre => Presence::Pre,
            Presence::Abs => Presence::Abs,
            Presence::Var(v) => Presence::Var(self.rename_pvar(v)),
        }
    }

    /// Rewrite `ty` so every type/presence variable inside it has a
    /// canonical ID. Walk order matches the pretty-printer's, so the
    /// printer's "encounter order" letter assignment lines up with
    /// the IDs tidy produces.
    pub fn tidy_type(&mut self, ty: &Type) -> Type {
        match ty {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::Literal(_)
            | Type::Error => ty.clone(),

            Type::Var(name) => Type::Var(self.rename_tvar(name)),

            Type::Func {
                this_type,
                params,
                ret,
            } => {
                // The printer hides `this_type` when it's `None`,
                // `Some(Undefined)`, or `Some(Var(_))`, and walks
                // the rest as `(params) => ret`. Tidy mirrors that
                // walk order so the canonical IDs match the order
                // letters get assigned downstream: visible
                // `this_type` first (it prints before the parens),
                // then params left-to-right, then ret. A hidden
                // `Some(Var(_))` is renamed last so it doesn't
                // claim the small IDs that should go to visible
                // vars.
                let this_hidden = matches!(
                    this_type.as_deref(),
                    None | Some(Type::Undefined) | Some(Type::Var(_))
                );
                let tidied_this_visible = if !this_hidden {
                    this_type
                        .as_ref()
                        .map(|t| Box::new(self.tidy_type(t)))
                } else {
                    None
                };
                let params = params.iter().map(|p| self.tidy_type(p)).collect();
                let ret = Box::new(self.tidy_type(ret));
                let this_final = match (this_hidden, this_type) {
                    (true, Some(t)) => Some(Box::new(self.tidy_type(t))),
                    (true, None) => None,
                    (false, _) => tidied_this_visible,
                };
                Type::Func {
                    this_type: this_final,
                    params,
                    ret,
                }
            }

            Type::Row(row) => Type::Row(self.tidy_row(row)),
            Type::Array(elem) => Type::Array(Box::new(self.tidy_type(elem))),
            Type::Promise(inner) => Type::Promise(Box::new(self.tidy_type(inner))),
            Type::Map(value) => Type::Map(Box::new(self.tidy_type(value))),
            Type::Named(id, args) => {
                Type::Named(*id, args.iter().map(|a| self.tidy_type(a)).collect())
            }
            Type::Union(members) => {
                Type::Union(members.iter().map(|m| self.tidy_type(m)).collect())
            }
            Type::Module(m) => Type::Module(ModuleType {
                source: m.source.clone(),
                exports: m
                    .exports
                    .iter()
                    .map(|(k, s)| (k.clone(), self.tidy_scheme(s)))
                    .collect(),
            }),
        }
    }

    fn tidy_row(&mut self, row: &RowType) -> RowType {
        // Walk props in BTreeMap (alphabetical) order — the printer
        // also iterates props that way, so tidy's traversal matches.
        let props = row
            .props
            .iter()
            .map(|(k, e)| {
                (
                    k.clone(),
                    FieldEntry {
                        presence: self.rename_presence(&e.presence),
                        ty: self.tidy_type(&e.ty),
                    },
                )
            })
            .collect();
        let tail = match &row.tail {
            RowTail::Closed => RowTail::Closed,
            RowTail::Open(v) => RowTail::Open(self.rename_tvar(v)),
            RowTail::Recursive(id, args) => {
                RowTail::Recursive(*id, args.iter().map(|a| self.tidy_type(a)).collect())
            }
        };
        RowType { props, tail }
    }

    pub fn tidy_pred(&mut self, pred: &TypePred) -> TypePred {
        TypePred {
            class: pred.class,
            types: pred.types.iter().map(|t| self.tidy_type(t)).collect(),
        }
    }

    /// Tidy a scheme. The body and predicates are walked in the
    /// same order the printer writes them (preds → body) so the
    /// canonical IDs match the order letters get assigned. The
    /// scheme's quantifier list is then renumbered too and sorted
    /// by canonical ID so `<a, b, c, d>` reads in the same order
    /// the letters first appear downstream.
    pub fn tidy_scheme(&mut self, scheme: &TypeScheme) -> TypeScheme {
        let preds: Vec<TypePred> = scheme
            .body
            .preds
            .iter()
            .map(|p| self.tidy_pred(p))
            .collect();
        let ty = self.tidy_type(&scheme.body.ty);

        // Rename quantifiers using the IDs the body walk already
        // assigned. A quantified var that didn't appear in the
        // body (e.g. a hidden `this`) gets a fresh ID at the tail,
        // which `write_scheme` filters away anyway.
        let mut vars: Vec<TVarName> = scheme
            .vars
            .iter()
            .map(|v| self.rename_tvar(v))
            .collect();
        vars.sort_by_key(|v| v.id());

        let mut pvars: Vec<PVarName> = scheme
            .pvars
            .iter()
            .map(|p| self.rename_pvar(p))
            .collect();
        pvars.sort_by_key(|p| p.id());

        TypeScheme {
            vars,
            pvars,
            body: QualType::with_preds(preds, ty),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::ty::ClassName;

    /// Tidying twice (with fresh envs) yields the same result —
    /// the canonical form is stable.
    #[test]
    fn tidy_is_idempotent() {
        // (Var(7), Var(12)) => Var(7)
        let ty = Type::Func {
            this_type: None,
            params: vec![
                Type::Var(TVarName::Flex(7)),
                Type::Var(TVarName::Flex(12)),
            ],
            ret: Box::new(Type::Var(TVarName::Flex(7))),
        };
        let a = TidyEnv::new().tidy_type(&ty);
        let b = TidyEnv::new().tidy_type(&ty);
        assert_eq!(a, b);
        // First var encountered → 0, second → 1; the repeated 7
        // reuses 0.
        let expected = Type::Func {
            this_type: None,
            params: vec![
                Type::Var(TVarName::Flex(0)),
                Type::Var(TVarName::Flex(1)),
            ],
            ret: Box::new(Type::Var(TVarName::Flex(0))),
        };
        assert_eq!(a, expected);
    }

    /// Two unrelated types tidied with a *shared* env keep the
    /// distinction between their variables — the second one's
    /// fresh vars come after the first one's.
    #[test]
    fn shared_env_preserves_distinctness() {
        let mut env = TidyEnv::new();
        let t1 = env.tidy_type(&Type::Var(TVarName::Flex(5)));
        let t2 = env.tidy_type(&Type::Var(TVarName::Flex(99)));
        assert_eq!(t1, Type::Var(TVarName::Flex(0)));
        assert_eq!(t2, Type::Var(TVarName::Flex(1)));
    }

    /// A scheme's quantifier list comes out sorted by traversal
    /// order — so the printer's `<a, b, …>` matches the order the
    /// letters appear in the body.
    #[test]
    fn scheme_quantifier_order_follows_body() {
        let scheme = TypeScheme {
            // Vars happen to be listed `[5, 1, 9]` from generalize's
            // sort, but in the body they appear in the order 9, 5, 1.
            vars: vec![
                TVarName::Flex(5),
                TVarName::Flex(1),
                TVarName::Flex(9),
            ],
            pvars: vec![],
            body: QualType::with_preds(
                vec![TypePred {
                    class: ClassName::Plus,
                    types: vec![Type::Var(TVarName::Flex(9))],
                }],
                Type::Func {
                    this_type: None,
                    params: vec![
                        Type::Var(TVarName::Flex(5)),
                        Type::Var(TVarName::Flex(1)),
                    ],
                    ret: Box::new(Type::Var(TVarName::Flex(9))),
                },
            ),
        };
        let tidied = TidyEnv::new().tidy_scheme(&scheme);
        // Body traversal: pred uses 9 first → 0; then params 5 → 1,
        // 1 → 2; return uses 9 → 0 again.
        assert_eq!(
            tidied.vars,
            vec![
                TVarName::Flex(0),
                TVarName::Flex(1),
                TVarName::Flex(2),
            ],
        );
        match &tidied.body.ty {
            Type::Func { params, ret, .. } => {
                assert_eq!(params[0], Type::Var(TVarName::Flex(1)));
                assert_eq!(params[1], Type::Var(TVarName::Flex(2)));
                assert_eq!(**ret, Type::Var(TVarName::Flex(0)));
            }
            _ => panic!("expected Func"),
        }
        assert_eq!(
            tidied.body.preds[0].types[0],
            Type::Var(TVarName::Flex(0))
        );
    }
}
