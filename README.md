# assertbytes-240

A Lean 4 proof that the zkGolf AssertBytes record score of 240 is optimal, for
every R1CS circuit whose constraint system is sound over the algebraic closure
of the field. Every standard circuit satisfies this condition.

## The theorem

An R1CS circuit checks that 16 field elements are bytes. Its score is the
number of witness allocations plus the number of constraints. If the constraint
system stays sound over the algebraic closure, the score is at least 240.

```lean
theorem sixteen_bytes_score_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) (hX : ChecksBytes 16 X) :
    240 ≤ X.score
```

`ChecksBytes 16 X` means `X` has 16 public inputs and its accepted set projects
onto at least 2^128 scalars.

The bound is tight in each coordinate. It gives at least 112 allocations and at
least 128 constraints. The record circuit uses exactly 112 and 128.

`RecordInstance.lean` builds one byte of the record circuit as a checker: 7 low
bits, 7 booleanity rows, 1 product row. It proves `ChecksBytes 1` when the
casts of `0..255` are distinct in the field. The score is 15 by definition and
at least 15 by the theorem.

The proof has no `sorry` and uses only the three standard Lean axioms.
`AxiomAudit.lean` checks this with `#guard_msgs` on `#print axioms`, so the
build fails if an axiom is added.

## Proof sketch

Model the circuit as `C` quadratic equations in `n` variables over an
algebraically closed field. The accepted inputs are the solutions. A linear map
`L` packs the 16 bytes into one scalar. The circuit distinguishes as many inputs
as `L` takes values on the solution set.

1. **Affine Bézout bound.** The solution set of `C` equations of degree at most
   `d` has at most `min(d^C, d^n)` irreducible components. This is most of the
   repository. Replace the equations by a weakly regular sequence of linear
   combinations to get a complete intersection, then bound the Hilbert function
   along the sequence. Each generator of degree at most `d` multiplies the
   bound by at most `d`. The positive-dimensional case uses Lazard's
   divided-degree recurrence. With `d = 2` the bound is `2^min(C,n)`.

2. **Finite projections are constant on components.** If `L` has finite image
   on the solution set, `L` is constant on each irreducible component. The
   image of an irreducible set is irreducible, and a finite irreducible set is
   a point.

3. So `L` takes at most `2^min(C,n)` values.

4. 16 bytes give `256^16 = 2^128` inputs, so `min(C,n) ≥ 128`. This gives
   `C ≥ 128` and `n ≥ 128`. 16 variables are public, so at least 112 are
   witnesses.

```text
C ≥ 8B    A ≥ 7B    A + C ≥ 15B    B = 16  ⟹  score ≥ 240
```

The argument does not look at the structure of the circuit. It only counts
components.

## Limits

- **Degree 2 is required.** The bound is `2^min(C,n)` because R1CS rows are
  quadratic. Custom gates of higher degree give a weaker bound.

- **Soundness over the closure is required.** The field is algebraically
  closed and the finiteness hypothesis is on the geometric variety. A circuit
  can be sound over `F_p` and fail this. Example: take `c` a quadratic
  non-residue and per byte assert `bᵢ(bᵢ−1) = 0` for 8 bits, `y² = s`, and
  `(x − Σ2ⁱbᵢ)² = c·s`. Each row is rank 1. Over `F_p`, `y ≠ 0` would make `c`
  a square, so `y = 0` and `x` is the bit recomposition. Over the closure,
  `x = Σ2ⁱbᵢ + √c·t` is a solution for every `t`, so the accepted set is
  infinite. This circuit costs more than 240 and does not beat the bound. It
  shows the hypothesis cannot be dropped.

- **The link to Clean is not formalised.**
  [Clean](https://github.com/Verified-zkEVM/clean) formalises circuits,
  semantics, soundness, completeness, cost, and the R1CS check. Nothing here
  translates a Clean circuit into a `ConcreteScalarChecker`. A general
  translation cannot exist, by the example above. It must assume soundness over
  the closure. Whether an `F_p`-specific circuit scores below 240 is open.

## Build

Install [elan](https://github.com/leanprover/elan). It reads `lean-toolchain`.

```bash
lake exe cache get   # mathlib objects, about 7 GB
lake build
```

There is no `sorry` in the tree. `AxiomAudit.lean` is in the default target, so
the build fails if a theorem uses an extra axiom.

To print the axioms:

```bash
printf 'import AssertBytes240.Optimality\n#print axioms ZkGolfOptimality.AssertBytes.sixteen_bytes_score_lower_bound\n' > Axioms.lean
lake env lean Axioms.lean
```

```text
'ZkGolfOptimality.AssertBytes.sixteen_bytes_score_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

Mathlib is pinned in `lakefile.lean` to the revision the proof was checked
against.

## Layout

| Path | What |
|---|---|
| `AssertBytes240/Optimality.lean` | the public statements, including the 240 bound |
| `AssertBytes240/RecordInstance.lean` | one byte of the record circuit as a checker |
| `AssertBytes240/Components.lean` | finite projections are constant on components (step 2) |
| `AssertBytes240/Algebra/` | the affine Bézout bound (step 1) |
| `AssertBytes240/AxiomAudit.lean` | axiom check, run by the build |

Mathlib has no component-count bound of this kind. It has Bézout domains and
Bézout's identity for gcd.
