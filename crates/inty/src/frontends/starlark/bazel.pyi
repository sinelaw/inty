# The globals Bazel gives a `.bzl` file, bound opaquely: calls of them
# type-check without constraining anything, so a `.bzl` file can be checked
# before inty has precise declarations of Bazel's API. Replacing these
# with real signatures is future work.
native: object
rule: object
attr: object
provider: object
depset: object
select: object
aspect: object
repository_rule: object
module_extension: object
tag_class: object
Label: object
DefaultInfo: object
OutputGroupInfo: object
RunEnvironmentInfo: object
InstrumentedFilesInfo: object
CcInfo: object
config_common: object
platform_common: object
cc_common: object
java_common: object
json: object
proto: object
testing: object
coverage_common: object
transition: object
analysis_test_transition: object
configuration_field: object
exec_group: object
visibility: object
