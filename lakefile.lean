import Lake
open Lake DSL

package assertbytes240 where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib AssertBytes240 where
  globs := #[.submodules `AssertBytes240]

-- Pinned to the exact revision the proof was checked against.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
