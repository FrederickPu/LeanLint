-- Root of the `Test` library: importing these modules runs the self-checking linter tests,
-- so `lake build Test` runs the whole test suite (a mismatch fails the build).
import Test.Basic
import Test.Check
import Test.Let
import Test.Nested
import Test.Style
import Test.Structuring
import Test.TermMode
