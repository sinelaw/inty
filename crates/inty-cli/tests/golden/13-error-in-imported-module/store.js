export const state = { volume: 1, name: "a" };

export function describe() {
  return state.name + state.volume * "2";
}
