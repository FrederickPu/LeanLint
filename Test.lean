-- Root of the `Test` library: every module is a self-checking `#guard_msgs` suite,
-- so `lake build Test` runs the whole test suite (a mismatch fails the build).
import Test.Basic
import Test.Nested
import Test.Structuring
