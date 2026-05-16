/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, the LieLean team
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Ring
import Mathlib.Util.AtomM
import Mathlib.Algebra.Lie.Basic

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List

def V (M : Type*) := Sum M (M × M)

namespace AtomD

structure State where
  atoms : Array (V Expr) := #[]

abbrev AtomD := StateRefT AtomD.State MetaM

def run {α : Type} (m : AtomD α) :
    MetaM α :=
  m.run' {}

def addAtomSimple (e : Expr) : AtomD (Nat × Bool × Expr) := do
  let c ← get
  match e with
  | e₁ =>
    for h : i in [:c.atoms.size] do
      match c.atoms[i] with
      | Sum.inl j =>
        if ← withTransparency .instances <| isDefEq e₁ j then
          return (i, true, j)
      | _ => continue
    modifyGet fun c ↦ ((c.atoms.size, true, e₁), { c with atoms := c.atoms.push (Sum.inl e₁) })
def addAtomDouble (e₁ e₂ : Expr) : AtomD (Nat × Bool × (Expr × Expr)) := do
  let c ← get
  let e : Expr × Expr := ⟨ e₁, e₂ ⟩
  match e with
  | ⟨ e₁, e₂ ⟩ =>
    for h : i in [:c.atoms.size] do
      match c.atoms[i] with
      | Sum.inr ⟨j₁, j₂⟩ =>
        if ← withTransparency .instances (isDefEq e₁ j₁) then
          if ← withTransparency .instances (isDefEq e₂ j₂) then
            return (i, true, ⟨j₁, j₂⟩)
        if ← withTransparency .instances (isDefEq e₂ j₁) then
          if ← withTransparency .instances (isDefEq e₁ j₂) then
            return (i, false, ⟨j₁, j₂⟩)
      | _ => continue
    modifyGet fun c ↦ ((c.atoms.size, true, ⟨e₁,e₂⟩), { c with atoms := c.atoms.push (Sum.inr e) })

open Qq in

def addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomD (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, _, e') ← AtomD.addAtomSimple e
  return (n, ⟨e', ⟨⟩⟩)

def addAtomDoubleQ {u : Level} {α : Q(Type u)} (e₁ e₂ : Q($α)) :
    AtomD (Nat × Sum {e' : Q($α) × Q($α) // $e₁ =Q $(e'.2) ∧ $e₂ =Q $(e'.1)} {e' : Q($α) × Q($α) // $e₁ =Q $(e'.1) ∧ $e₂ =Q $(e'.2)}) := do
  let (n, b, e₁', e₂') ← AtomD.addAtomDouble e₁ e₂
  match b with
  | false =>
    return (n, Sum.inl ⟨⟨e₁',e₂'⟩, ⟨⟨⟩, ⟨⟩⟩⟩)
  | true =>
    return (n, Sum.inr ⟨⟨e₁',e₂'⟩, ⟨⟨⟩, ⟨⟩⟩⟩)
end AtomD

namespace Mathlib.Tactic.LieSolver

def v {M : Type*} [LieRing M] (x : V M) :=
  Sum.elim (fun m ↦ m) (fun ⟨ m₁ , m₂ ⟩ ↦ ⁅ m₁ , m₂ ⁆) x

def NF (R : Type*) (M : Type*) := List (R × V M)

namespace NF
variable {S : Type*} {R : Type*} {M : Type*}

@[match_pattern]
def cons (p : R × V M) (l : NF R M) : NF R M := p :: l

infixl:100 " ::ᵣ " => cons

def eval [Add M] [Zero M] [SMul R M] [LieRing M] (l : NF R M) : M :=
  (l.map (fun (⟨r, x⟩ : R × V M) ↦ r • v x)).sum

@[simp] theorem eval_cons [AddMonoid M] [SMul R M] [LieRing M] (p : R × V M) (l : NF R M) :
    (p ::ᵣ l).eval = p.1 • v p.2 + l.eval := by
  unfold eval cons
  rw [List.map_cons]
  rw [List.sum_cons]

theorem atom_eq_eval [AddMonoid M] [LieRing M] (x : M) : x = NF.eval [(1, Sum.inl x)] := by simp [eval, v]
theorem atom_eq_evalD [AddMonoid M] [LieRing M] (x y : M) : ⁅x,y⁆ = NF.eval ((1, Sum.inr ⟨x,y⟩) ::ᵣ []) := by
  simp [eval, v]
  dsimp!
  simp only [one_nsmul, add_zero]
  simp only [left_eq_add]
theorem atom_eq_evalD_skew [LieRing M] (x y : M) : ⁅x,y⁆ = NF.eval ((-1, Sum.inr ⟨y,x⟩) ::ᵣ []) := by
  simp [eval, v]
  dsimp!
  simp only [Int.reduceNeg, neg_smul, one_smul, add_zero]
  rw [lie_skew]

variable (M) in
theorem zero_eq_eval [LieRing M] : (0:M) = NF.eval (R := ℕ) (M := M) [] := rfl

theorem add_eq_eval₁ [SMul R M] [LieRing M] (a₁ : R × V M) {a₂ : R × V M} {l₁ l₂ l : NF R M}
    (h : l₁.eval + (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval + (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, add_assoc]

theorem add_eq_eval₂ [Semiring R] [LieRing M] [Module R M] (r₁ r₂ : R) (x : V M)
    {l₁ l₂ l : NF R M} (h : l₁.eval + l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval + ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, add_smul, add_assoc]
  congr! 1
  simp only [← add_assoc]
  congr! 1
  rw [add_comm]

theorem add_eq_eval₃ [Semiring R] [LieRing M] [Module R M] {a₁ : R × V M} (a₂ : R × V M)
    {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁).eval + l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval + (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  nth_rw 4 [add_comm]
  simp only [add_assoc]
  congr! 2
  rw [add_comm]

theorem add_eq_eval {R₁ R₂ : Type*} [AddCommMonoid M] [LieRing M] [Semiring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] {l₁ l₂ l : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval + l₂.eval = l.eval) :
    x₁ + x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

theorem sub_eq_eval₁ [SMul R M] [LieRing M]  (a₁ : R × V M) {a₂ : R × V M} {l₁ l₂ l : NF R M}
    (h : l₁.eval - (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval - (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, sub_eq_add_neg, add_assoc]

theorem sub_eq_eval₂ [Ring R] [LieRing M] [Module R M] (r₁ r₂ : R) (x : V M) {l₁ l₂ l : NF R M}
    (h : l₁.eval - l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval - ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, sub_smul, sub_eq_add_neg, neg_add, add_smul, neg_smul, add_assoc]
  congr! 1
  simp only [← add_assoc]
  congr! 1
  rw [add_comm]

theorem sub_eq_eval₃ [Ring R] [LieRing M] [Module R M] {a₁ : R × V M} (a₂ : R × V M)
    {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁).eval - l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval - (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, neg_smul, neg_add, sub_eq_add_neg, ← h, ← add_assoc]
  congr! 1
  rw [add_comm, add_assoc]

theorem sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} [LieRing M] [Ring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] [Semiring S₁] [Module S₁ M] [Semiring S₂]
    [Module S₂ M] {l₁ l₂ l : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M} {l₁'' : NF S₁ M}
    {l₂'' : NF S₂ M} {x₁ x₂ : M} (hx₁ : x₁ = l₁''.eval) (hx₂ : x₂ = l₂''.eval)
    (h₁' : l₁'.eval = l₁''.eval) (h₂' : l₂'.eval = l₂''.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval - l₂.eval = l.eval) :
    x₁ - x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁', ← h₂', ← h₁, ← h₂, h]

instance [Neg R] : Neg (NF R M) where
  neg l := l.map fun (a, x) ↦ (-a, x)

private lemma sum_map_neg_eq_neg_sum {M : Type*} [AddCommGroup M] (l : List M) :
    (l.map (fun x ↦ -x)).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [ih, add_comm]

theorem eval_neg [Ring R] [LieRing M] [Module R M] (l : NF R M) : (-l).eval = - l.eval := by
  show NF.eval (l.map (fun (a, x) ↦ (-a, x))) = -l.eval
  unfold NF.eval
  rw [List.map_map]
  have heq : (fun (x : R × V M) ↦ x.1 • v x.2) ∘ (fun x : R × V M ↦ (-x.1, x.2)) =
      fun x ↦ -(x.1 • v x.2) := by funext x; simp [neg_smul]
  rw [heq, show (fun x ↦ -((x : R × V M).1 • v x.2)) =
        (fun (z : M) ↦ -z) ∘ (fun (x : R × V M) ↦ x.1 • v x.2) from rfl,
      ← List.map_map]
  rw [sum_map_neg_eq_neg_sum]

theorem zero_sub_eq_eval [Ring R] [LieRing M] [Module R M] (l : NF R M) :
    0 - l.eval = (-l).eval := by
  simp [eval_neg]

theorem neg_eq_eval [LieRing M] [Semiring S] [Module S M] [Ring R] [Module R M] {l : NF R M}
    {l₀ : NF S M} (hl : l.eval = l₀.eval) {x : M} (h : x = l₀.eval) :
    - x = (-l).eval := by
  rw [h, ← hl, eval_neg]

instance [Mul R] : SMul R (NF R M) where
  smul r l := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem smul_apply [Mul R] (r : R) (l : NF R M) : r • l = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

theorem eval_smul [LieRing M] [Semiring R] [Module R M] {l : NF R M} {x : M} (h : x = l.eval)
    (r : R) : (r • l).eval = r • x := by
  unfold NF.eval at h ⊢
  simp only [h, smul_sum, map_map, NF.smul_apply]
  congr
  ext p
  simp [mul_smul]

theorem smul_eq_eval {R₀ : Type*} [LieRing M] [Semiring R] [Module R M] [Semiring R₀]
    [Module R₀ M] [Semiring S] [Module S M]  {l : NF R M} {l₀ : NF R₀ M} {s : S} {r : R}
    {x : M} (hx : x = l₀.eval) (hl : l.eval = l₀.eval) (hs : r • x = s • x) :
    s • x = (r • l).eval := by
  rw [← hs, hx, ← hl, eval_smul]
  rfl

theorem eq_cons_cons [LieRing M] [SMul R M] {r₁ r₂ : R} (m : V M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂)
    (h2 : l₁.eval = l₂.eval) :
    ((r₁, m) ::ᵣ l₁).eval = ((r₂, m) ::ᵣ l₂).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_cons_const [LieRing M] [Semiring R] [Module R M] {r : R} (m : V M) {n : V M}
    {l : NF R M} (h1 : r = 0) (h2 : l.eval = v n) :
    ((r, m) ::ᵣ l).eval = v n := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_const_cons [LieRing M] [Semiring R] [Module R M] {r : R} (m : V M) {n : V M}
    {l : NF R M} (h1 : 0 = r) (h2 : v n = l.eval) :
    v n = ((r, m) ::ᵣ l).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [← h1, h2]

theorem eq_of_eval_eq_eval {R₁ R₂ : Type*} [LieRing M] [Semiring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M]  {l₁ l₂ : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval = l₂.eval) :
    x₁ = x₂ := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

variable (R)

def algebraMap [CommSemiring S] [Semiring R] [Algebra S R] (l : NF S M) : NF R M :=
  l.map (fun ⟨s, x⟩ ↦ (_root_.algebraMap S R s, x))

theorem eval_algebraMap [CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid M] [LieRing M] [SMul S M]
    [MulAction R M] [IsScalarTower S R M] (l : NF S M) :
    (l.algebraMap R).eval = l.eval := by
  simp only [NF.eval, algebraMap, map_map]
  congr
  ext
  simp [IsScalarTower.algebraMap_smul]

end NF

variable {u v : Level}

abbrev qNF (R : Q(Type u)) (M : Q(Type v)) := List ((Q($R) × Q(V $M)) × ℕ)

namespace qNF

variable {M : Q(Type v)} {R : Q(Type u)}

def toNF (l : qNF R M) : Q(NF $R $M) :=
  let l' : List Q($R × V $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q($R × V $M) → Q(List ($R × V $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

def onScalar {u₁ u₂ : Level} {R₁ : Q(Type u₁)} {R₂ : Q(Type u₂)} (l : qNF R₁ M) (f : Q($R₁ → $R₂)) :
    qNF R₂ M :=
  l.map fun ((a, x), k) ↦ ((q($f $a), x), k)

def add (iR : Q(Semiring $R)) : qNF R M → qNF R M → qNF R M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: add iR t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((q($a₁ + $a₂), x₁), k₁) :: add iR t₁ t₂
    else
      ((a₂, x₂), k₂) :: add iR (((a₁, x₁), k₁) :: t₁) t₂

def mkAddProof {iR : Q(Semiring $R)} {iMM : Q(LieRing $M)} (iRM : Q(Module $R $M))
    (l₁ l₂ : qNF R M) :
    Q(NF.eval $(l₁.toNF) + NF.eval $(l₂.toNF) = NF.eval $((qNF.add iR l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(zero_add (NF.eval $(l.toNF))):)
  | l, [] => (q(add_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      let pf := mkAddProof iRM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.add_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkAddProof iRM t₁ t₂
      (q(NF.add_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkAddProof iRM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.add_eq_eval₃ ($a₂, $x₂) $pf):)

def sub (iR : Q(Ring $R)) : qNF R M → qNF R M → qNF R M
  | [], l => l.onScalar q(Neg.neg)
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: sub iR t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((q($a₁ - $a₂), x₁), k₁) :: sub iR t₁ t₂
    else
      ((q(-$a₂), x₂), k₂) :: sub iR (((a₁, x₁), k₁) :: t₁) t₂

def mkSubProof (iR : Q(Ring $R)) (iMM : Q(LieRing $M)) (iRM : Q(Module $R $M))
    (l₁ l₂ : qNF R M) :
    Q(NF.eval $(l₁.toNF) - NF.eval $(l₂.toNF) = NF.eval $((qNF.sub iR l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.zero_sub_eq_eval $(l.toNF)):)
  | l, [] => (q(sub_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      let pf := mkSubProof iR iMM iRM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.sub_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkSubProof iR iMM iRM t₁ t₂
      (q(NF.sub_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkSubProof iR iMM iRM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.sub_eq_eval₃ ($a₂, $x₂) $pf):)

variable {iMM : Q(LieRing $M)}
  {u₁ : Level} {R₁ : Q(Type u₁)} {iR₁ : Q(Semiring $R₁)} (iRM₁ : Q(@Module $R₁ $M $iR₁ _))
  {u₂ : Level} {R₂ : Q(Type u₂)} (iR₂ : Q(Semiring $R₂)) (iRM₂ : Q(@Module $R₂ $M $iR₂ _))

def matchRings (l₁ : qNF R₁ M) (l₂ : qNF R₂ M) (r : Q($R₂)) (x : Q($M)) :
    MetaM <| Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR _),
      (Σ l₁' : qNF R M, Q(NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)))
      × (Σ l₂' : qNF R M, Q(NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)))
      × (Σ r' : Q($R), Q($r' • $x = $r • $x)) := do
  if ← withReducible <| isDefEq R₁ R₂ then
    pure ⟨u₁, R₁, iR₁, iRM₁, ⟨l₁, q(rfl)⟩, ⟨l₂, (q(@rfl _ (NF.eval $(l₂.toNF))):)⟩,
      r, (q(@rfl _ ($r • $x)):)⟩
  else try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : qNF R₂ M := l₁.onScalar q(algebraMap $R₁ $R₂)
    pure ⟨u₂, R₂, iR₂, iRM₂, ⟨l₁', (q(NF.eval_algebraMap $R₂ $(l₁.toNF)):)⟩, ⟨l₂, q(rfl)⟩,
      r, q(rfl)⟩
  catch _ => try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let l₂' : qNF R₁ M := l₂.onScalar q(algebraMap $R₂ $R₁)
    let r' : Q($R₁) := q(algebraMap $R₂ $R₁ $r)
    pure ⟨u₁, R₁, iR₁, iRM₁, ⟨l₁, q(rfl)⟩, ⟨l₂', (q(NF.eval_algebraMap $R₁ $(l₂.toNF)):)⟩,
      r', (q(IsScalarTower.algebraMap_smul $R₁ $r $x):)⟩
  catch _ =>
    throwError "match_scalars_lie failed: {R₁} is not an {R₂}-algebra and {R₂} is not an {R₁}-algebra"

end qNF

variable {M : Q(Type v)}

def parseFuel : Nat := 4096

def parseAux (fuel : Nat) (iMM : Q(LieRing $M)) (x : Q($M)) :
    AtomD.AtomD (Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR _),
      Σ l : qNF R M, Q($x = NF.eval $(l.toNF))) := do
  match fuel with
  | 0 => throwError "match_scalars_lie: ran out of fuel while parsing {x}"
  | fuel + 1 =>
    match x with
    | ~q($x₁ + $x₂) =>
      let ⟨_, _, _, iRM₁, l₁', pf₁'⟩ ← parseAux fuel iMM x₁
      let ⟨_, _, _, iRM₂, l₂', pf₂'⟩ ← parseAux fuel iMM x₂
      assumeInstancesCommute
      let ⟨u, R, iR, iRM, ⟨l₁, pf₁⟩, ⟨l₂, pf₂⟩, _⟩ ← qNF.matchRings iRM₁ _ iRM₂ l₁' l₂' q(0) q(0)
      let pf := qNF.mkAddProof iRM l₁ l₂
      pure ⟨u, R, iR, iRM, qNF.add iR l₁ l₂, (q(NF.add_eq_eval $pf₁' $pf₂' $pf₁ $pf₂ $pf):)⟩
    | ~q(@HSub.hSub _ _ _ (@instHSub _ $iM') $x₁ $x₂) =>
      let ⟨_, _, _, iRM₁, l₁'', pf₁''⟩ ← parseAux fuel iMM x₁
      let ⟨_, _, _, iRM₂, l₂'', pf₂''⟩ ← parseAux fuel iMM x₂
      let iZ := q(Int.instSemiring)
      let iMZ ← synthInstanceQ q(Module ℤ $M)
      let ⟨_, _, _, iRM₁', ⟨l₁', pf₁'⟩, _, _⟩ ← qNF.matchRings iRM₁ iZ iMZ l₁'' [] q(0) q(0)
      let ⟨_, _, _, iRM₂', ⟨l₂', pf₂'⟩, _, _⟩ ← qNF.matchRings iRM₂ iZ iMZ l₂'' [] q(0) q(0)
      let ⟨u, R, iR, iRM, ⟨l₁, pf₁⟩, ⟨l₂, pf₂⟩, _⟩ ← qNF.matchRings iRM₁' _ iRM₂' l₁' l₂' q(0) q(0)
      let iR' ← synthInstanceQ q(Ring $R)
      let iMM' ← synthInstanceQ q(LieRing $M)
      assumeInstancesCommute
      let pf := qNF.mkSubProof iR' iMM' iRM l₁ l₂
      pure ⟨u, R, iR, iRM, qNF.sub iR' l₁ l₂,
        q(NF.sub_eq_eval $pf₁'' $pf₂'' $pf₁' $pf₂' $pf₁ $pf₂ $pf)⟩
    | ~q(@Neg.neg _ $iM' $y) =>
      let ⟨u₀, _, _, iRM₀, l₀, pf₀⟩ ← parseAux fuel iMM y
      let _i ← synthInstanceQ q(AddCommGroup $M)
      let iZ := q(Int.instSemiring)
      let iMZ ← synthInstanceQ q(Module ℤ $M)
      let ⟨u, R, iR, iRM, ⟨l, pf⟩, _, _⟩ ← qNF.matchRings iRM₀ iZ iMZ l₀ [] q(0) q(0)
      let _i' ← synthInstanceQ q(Ring $R)
      assumeInstancesCommute
      pure ⟨u, R, iR, iRM, l.onScalar q(Neg.neg), (q(NF.neg_eq_eval $pf $pf₀):)⟩
    | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s₀ $y) =>
      let ⟨_, _, _, iRM₀, l₀, pf₀⟩ ← parseAux fuel iMM y
      let i₁ ← synthInstanceQ q(Semiring $S)
      let i₂ ← synthInstanceQ q(Module $S $M)
      assumeInstancesCommute
      let ⟨u, R, iR, iRM, ⟨l, pf_l⟩, _, ⟨s, pf_r⟩⟩ ← qNF.matchRings iRM₀ i₁ i₂ l₀ [] s₀ y
      pure ⟨u, R, iR, iRM, l.onScalar q(HMul.hMul $s), (q(NF.smul_eq_eval $pf₀ $pf_l $pf_r):)⟩
    | ~q(0) =>
      pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [], q(NF.zero_eq_eval $M)⟩
    | ~q(@Bracket.bracket _ _ «$iMM».toBracket $x₁ $x₂) =>
      let (k, vmmm) ← AtomD.addAtomDoubleQ (q($x₁):Q($M)) (q($x₂):Q($M))
      match vmmm with
      | Sum.inl ⟨⟨x₁',x₂'⟩, ⟨_,_⟩⟩ =>
        let iMZ ← synthInstanceQ q(Module ℤ $M)
        assumeInstancesCommute
        pure ⟨0, q(Int), q(Int.instSemiring), q($iMZ), [((q(-1), q(Sum.inr ⟨$x₁', $x₂'⟩)), k)],
          q(NF.atom_eq_evalD_skew $x₁ $x₂)⟩
      | Sum.inr ⟨⟨x₁',x₂'⟩, ⟨_,_⟩⟩ =>
        assumeInstancesCommute
        pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [((q(1), q(Sum.inr ⟨$x₁', $x₂'⟩)), k)],
          q(NF.atom_eq_evalD $x₁ $x₂)⟩
    | _ =>
      let (k, ⟨x', _⟩) ← AtomD.addAtomQ x
      assumeInstancesCommute
      pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [((q(1), q(Sum.inl $x')), k)],
        q(NF.atom_eq_eval $x')⟩

def parse (iMM : Q(LieRing $M)) (x : Q($M)) :
    AtomD.AtomD (Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR _),
      Σ l : qNF R M, Q($x = NF.eval $(l.toNF))) :=
  parseAux parseFuel iMM x

def reduceCoefficientwiseAux (fuel : Nat) {R : Q(Type u)} {_ : Q(LieRing $M)} {_ : Q(Semiring $R)}
    (iRM : Q(Module $R $M)) (l₁ l₂ : qNF R M) :
    MetaM (List MVarId × Q(v (Sum.inl (NF.eval $(l₁.toNF))) =
      v (Sum.inl (NF.eval $(l₂.toNF))))) := do
  match fuel with
  | 0 => throwError "match_scalars_lie: ran out of fuel in reduceCoefficientwise"
  | fuel + 1 =>
    match l₁, l₂ with
    | [], [] =>
      let pf : Q(NF.eval $(l₁.toNF) = NF.eval $(l₁.toNF)) := q(rfl)
      pure ([], pf)
    | [], ((a, x), _) :: L =>
      let mvar : Q((0:$R) = $a) ← mkFreshExprMVar q((0:$R) = $a)
      let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM [] L
      pure (mvar.mvarId! :: mvars, (q(NF.eq_const_cons $x $mvar $pf):))
    | ((a, x), _) :: L, [] =>
      let mvar : Q($a = (0:$R)) ← mkFreshExprMVar q($a = (0:$R))
      let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM L []
      pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_const $x $mvar $pf):))
    | ((a₁, x₁), k₁) :: L₁, ((a₂, x₂), k₂) :: L₂ =>
      if k₁ < k₂ then
        let mvar : Q($a₁ = (0:$R)) ← mkFreshExprMVar q($a₁ = (0:$R))
        let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM L₁ (((a₂, x₂), k₂) :: L₂)
        pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_const $x₁ $mvar $pf):))
      else if k₁ = k₂ then
        let mvar : Q($a₁ = $a₂) ← mkFreshExprMVar q($a₁ = $a₂)
        let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM L₁ L₂
        pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_cons $x₁ $mvar $pf):))
      else
        let mvar : Q((0:$R) = $a₂) ← mkFreshExprMVar q((0:$R) = $a₂)
        let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM (((a₁, x₁), k₁) :: L₁) L₂
        pure (mvar.mvarId! :: mvars, (q(NF.eq_const_cons $x₂ $mvar $pf):))

def reduceCoefficientwise {R : Q(Type u)} {_ : Q(LieRing $M)} {_ : Q(Semiring $R)}
    (iRM : Q(Module $R $M)) (l₁ l₂ : qNF R M) :
    MetaM (List MVarId × Q(v (Sum.inl (NF.eval $(l₁.toNF))) =
      v (Sum.inl (NF.eval $(l₂.toNF))))) :=
  reduceCoefficientwiseAux parseFuel iRM l₁ l₂

def matchScalarsAux (g : MVarId) : AtomD.AtomD (List MVarId) := do
  let eqData ← do
    match (← g.getType').eq? with
    | some e => pure e
    | none => throwError "goal {← g.getType} is not an equality"
  let .sort v₀ ← whnf (← inferType eqData.1) | unreachable!
  let some v := v₀.dec | unreachable!
  let ((M : Q(Type v)), (lhs : Q($M)), (rhs :Q($M))) := eqData
  let iMM ← synthInstanceQ q(LieRing $M)
  let e₁ ← parse iMM lhs
  have u₁ : Level := e₁.fst
  have R₁ : Q(Type u₁) := e₁.snd.fst
  have _iR₁ : Q(Semiring.{u₁} $R₁) := e₁.snd.snd.fst
  let iRM₁ ← synthInstanceQ q(Module $R₁ $M)
  assumeInstancesCommute
  have l₁ : qNF R₁ M := e₁.snd.snd.snd.snd.fst
  let pf₁ : Q($lhs = NF.eval $(l₁.toNF)) := e₁.snd.snd.snd.snd.snd
  let e₂ ← parse iMM rhs
  have u₂ : Level := e₂.fst
  have R₂ : Q(Type u₂) := e₂.snd.fst
  have _iR₂ : Q(Semiring.{u₂} $R₂) := e₂.snd.snd.fst
  let iRM₂ ← synthInstanceQ q(Module $R₂ $M)
  have l₂ : qNF R₂ M := e₂.snd.snd.snd.snd.fst
  let pf₂ : Q($rhs = NF.eval $(l₂.toNF)) := e₂.snd.snd.snd.snd.snd
  let ⟨_, _, _, iRM, ⟨l₁', pf₁'⟩, ⟨l₂', pf₂'⟩, _⟩ ← qNF.matchRings iRM₁ _ iRM₂ l₁ l₂ q(0) q(0)
  let (mvars, pf) ← reduceCoefficientwise iRM l₁' l₂'
  g.assign q(NF.eq_of_eval_eq_eval $pf₁ $pf₂ $pf₁' $pf₂' $pf)
  return mvars

def algebraMapThms : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]

def postprocess (mvarId : MVarId) : MetaM MVarId := do
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  for thm in algebraMapThms do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in match_scalars_lie tactic: postprocessing should not close goals"
  return r

def matchScalars (g : MVarId) : MetaM (List MVarId) := do
  let mvars ← AtomD.run (matchScalarsAux g)
  mvars.mapM postprocess

elab "match_scalars_lie" : tactic => Tactic.liftMetaTactic matchScalars

elab "module_lie" : tactic => Tactic.liftMetaFinishingTactic fun g ↦ do
  let l ← matchScalars g
  discard <| l.mapM fun mvar ↦ AtomM.run .instances (Ring.proveEq mvar)

end Mathlib.Tactic.LieSolver

macro "simplify_lie" : tactic => `(tactic| {
  try simp only [lie_add, add_lie, lie_smul, smul_lie, lie_neg, neg_lie, sub_lie, lie_sub]
  match_scalars_lie <;> try ring})

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

theorem lie_solver3_example (v₁ v₂ v₃ : L) :
    4 • ⁅ v₁ , v₂ ⁆ + v₂ + ⁅ v₁ , v₃ ⁆ + ⁅ v₂ , v₁ ⁆ - ⁅ -2 • v₁ , v₂ ⁆
  = ⁅ v₁ , (7 : K) • v₂ ⁆ + 2 • v₂ + ⁅ v₂ + v₂ , v₁ ⁆ - v₂ + ⁅ (-1 : K) • v₃ , v₁ ⁆ := by
  simplify_lie

theorem lie_solver3_example' (v₁ v₂ : L) :
    4 • ⁅ v₁ , v₂ ⁆ + 4 • ⁅ v₂ , v₁ ⁆
  = 0 := by
  simplify_lie
