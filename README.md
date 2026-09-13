# assertbytes-240

The zkGolf AssertBytes challenge has a record score of 240. This is a Lean 4
proof that no circuit of the usual kind can beat it, and a precise account of
what "the usual kind" means.

## The theorem

Any R1CS circuit that proves sixteen field elements are each a byte, **and
whose constraint system stays sound over the algebraic closure of the field**,
costs at least **240**, counting one unit per witness allocation and one per
constraint.

That second condition is a real hypothesis, not boilerplate. See Limits.

```lean
theorem sixteen_bytes_score_lower_bound
    {K : Type*} [Field K] [IsAlgClosed K]
    (X : ConcreteScalarChecker K) (hX : ChecksBytes 16 X) :
    240 ≤ X.score
```

`ChecksBytes 16 X` says the circuit has sixteen public inputs and its accepted
set projects onto at least 2^128 scalars.

The bound is tight in each coordinate, not only in the total: it gives at least
112 allocations and at least 128 constraints, and a verified 240 circuit
achieves exactly 112 and 128.

The hypotheses are satisfiable, and the record's per-byte gadget is a proven
instance. `RecordInstance.lean` builds it as a checker in the model, seven
witnessed low bits with seven booleanity rows and one product row, and proves
`ChecksBytes 1` for it whenever the casts of `0..255` are distinct in the field.
Its score is 15 by definition and at least 15 by the theorem, so the bound is
attained, in Lean, with no paper step.

No `sorry`, and no axioms beyond the three Lean itself uses. The check is part
of the build: `AxiomAudit.lean` wraps `#print axioms` in `#guard_msgs`, so a
green build is the axiom audit.

## Proof sketch

Model the circuit as a system of C quadratic equations in n variables over an
algebraically closed field. Its accepted inputs are the solutions of that
system, and a linear map L packs the sixteen bytes into a single scalar, so the
answers the circuit can distinguish are the values L takes on the solution set.

**1. A quadratic system has few pieces.** The solution set of C equations of
degree at most d breaks into at most min(d^C, d^n) irreducible components. This
is the affine Bézout bound, and it is what the bulk of this repository proves.
The route: replace the original equations by a weakly regular sequence of
combinations of them, reducing to a complete intersection, then walk up that
sequence tracking the Hilbert function. Each generator of degree at most d
multiplies the component bound by at most d. The positive-dimensional case
needs Lazard's divided-degree recurrence, which is the longest single file
here. With d = 2 the bound is 2^min(C,n).

**2. A finite projection cannot separate points inside one piece.** If L takes
only finitely many values on the solution set, it is constant on each
irreducible component, because the image of an irreducible set is irreducible
and a finite irreducible set is a point. So the components cover the accepted
scalars, one value each at most.

**3. Combine.** The number of distinct accepted answers is at most the number
of components, so at most 2^min(C,n).

**4. Count.** Sixteen bytes means 256^16 = 2^128 inputs the circuit must tell
apart, so 2^128 ≤ 2^min(C,n) and therefore min(C,n) ≥ 128. That forces at least
128 constraints *and* at least 128 variables at once. Sixteen of the variables
are the public inputs, so at least 112 are allocated witnesses:

```text
C ≥ 8B        A ≥ 7B        A + C ≥ 15B        B = 16  ⟹  score ≥ 240
```

The argument never inspects how the circuit is built. It only counts, which is
why no bit-packing trick escapes it.

## Limits

- **Degree two is load-bearing.** The bound is 2^min(C,n) because R1CS rows are
  quadratic. A system with higher-degree custom gates gets a weaker bound.
- **Extension soundness is load-bearing.** The field here is algebraically
  closed and the finiteness hypothesis is a condition on the *geometric*
  variety. A circuit can be sound over the prime field and fail it. Take `c` a
  quadratic non-residue and, per byte, assert `bᵢ(bᵢ−1) = 0` for eight bits,
  `y² = s`, and `(x − Σ2ⁱbᵢ)² = c·s`. Every row is rank one, so it is R1CS.
  Over the prime field it is sound, because `y ≠ 0` would make `c` a square, so
  `y = 0` and `x` is the bit recomposition. Over the closure `√c` exists and
  `x = Σ2ⁱbᵢ + √c·t` solves it for every `t`, so the accepted set is infinite
  and the hypothesis fails. That circuit costs more than 240, so it does not
  beat the bound. It does show that no bridge can drop the hypothesis.
- **So the bridge to a concrete circuit is not merely unfinished.** The circuit
  side exists: [Clean](https://github.com/Verified-zkEVM/clean) formalises
  circuits, semantics, soundness, completeness, cost counting and R1CS-ness.
  But a general "valid contest circuit implies the hypotheses here" adapter
  cannot exist. An honest one must carry extension soundness as an added
  assumption. Ruling out a prime-field-specific circuit below 240 would need a
  different proof, over the prime field, and nothing here attempts it.

## Verify

You need [elan](https://github.com/leanprover/elan). It reads `lean-toolchain`
and fetches the pinned Lean itself.

```bash
lake exe cache get   # mathlib's prebuilt objects, about 7 GB on disk
lake build           # compiles the proofs in this repo
```

**A green build is the verification**, for two reasons:

- Lean will not compile an incomplete proof, and there is no `sorry` in the
  tree. Check for yourself: `grep -r sorry AssertBytes240` returns nothing.
- `AxiomAudit.lean` is part of the default target and wraps `#print axioms` in
  `#guard_msgs`. If any public theorem gained an axiom, the build would fail
  rather than warn.

To read the axioms rather than trust the guard:

```bash
printf 'import AssertBytes240.Optimality\n#print axioms ZkGolfOptimality.AssertBytes.sixteen_bytes_score_lower_bound\n' > Axioms.lean
lake env lean Axioms.lean
```

```text
'ZkGolfOptimality.AssertBytes.sixteen_bytes_score_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

Those three are Lean's own. Nothing else is assumed.

Mathlib is pinned in `lakefile.lean` to the revision the proof was checked
against.

## Layout

| Path | What |
|---|---|
| `AssertBytes240/Optimality.lean` | the four public statements, including the 240 bound |
| `AssertBytes240/RecordInstance.lean` | the record's per-byte gadget as a checker; the bound is attained |
| `AssertBytes240/Components.lean` | components to distinguishable scalars (step 2) |
| `AssertBytes240/Algebra/` | the affine Bézout bound (step 1) |
| `AssertBytes240/AxiomAudit.lean` | build-enforced axiom check |

The component bound is general, and no equivalent exists in mathlib today,
which has Bézout domains and Bézout's identity for gcd and nothing of this kind.
