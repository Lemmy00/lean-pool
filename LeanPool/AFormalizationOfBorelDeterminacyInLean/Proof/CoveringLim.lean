/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Covering

namespace GaleStewartGame
open CategoryTheory
open Descriptive Tree
namespace Covering

noncomputable section «Section1»
variable {p : Player} {F : ℕᵒᵖ ⥤ PTrees} {K k m n m' n' : ℕ}
  (hF : ∀ k, Fixing (K + k) (F.map (homOfLE k.le_succ).op))

include hF in lemma transition_fixing_full {m n} (h : m ≤ n) :
  Fixing (K + m) (F.map (homOfLE h).op) := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp h
  rw [← recComp.functor]; apply recComp_induction _ (fun _ ↦ fixing_id _ _)
    (fun _ _ ↦ fixing_comp _ _ _) _ _ _ (fun n ↦ fixing_mon _ (hF (m + n)) (by omega))
include hF in lemma transition_fixing {m n} (h : m ≤ n) :
  Fixing m (F.map (homOfLE h).op) := by
  apply fixing_mon
  · apply transition_fixing_full hF h
  · omega
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev limConePt : PTrees := ⟨(limCone (F ⋙ PTreeForget)).pt, by
  constructor
  · apply lim_isPruned
    · intro n
      exact (hF n).1.mon (by omega)
    · intro n
      exact pTrees_isPruned _
  · apply lim_ne
    · intro n
      exact (hF n).1.mon (by omega)
    · intro n
      exact pTrees_ne _⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev limCone_π_map n : (limConePt hF).1 ⟶ (F.obj (Opposite.op n)).1 :=
  (limCone (F ⋙ PTreeForget)).π.app ⟨n⟩
lemma limCone_π_map_nat {n m : ℕ} (h : n ≤ m) :
  limCone_π_map hF m ≫ (F.map (homOfLE h).op).toHom = limCone_π_map hF n :=
  ((limCone (F ⋙ PTreeForget)).π.naturality (homOfLE h).op).symm
instance limCone_π_fixing_full k : Tree.Fixing (K + k) (limCone_π_map hF k) :=
  proj_fixing (F ⋙ PTreeForget) K (fun n ↦ (hF n).1) k

open ResStrategy
lemma fromMap_comp' k {S T U : Trees} (f : S ⟶ T) (g : T ⟶ U)
  (hf : Tree.Fixing k f) (hg : Tree.Fixing k g)
  (S' : ResStrategy S p k) :
  (fromMap (f ≫ g)) S' = (fromMap g hg) ((fromMap f hf) S') := by
  ext1 x _ hl; apply ExtensionsAt.ext_valT'
  simp_rw [fromMap, ExtensionsAt.map_valT', CategoryTheory.comp_apply, ← pInv_comp']
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def limCone_str n : PTreesS.mk (limConePt hF) ⟶ PTreesS.mk (F.obj (Opposite.op n)) where
  toFun := fun p m S ↦
    (F.map (homOfLE (by simp)).op).str.toFun p m
      (S.fromMap (limCone_π_map hF (m ⊔ n)))
  con := by
    intro p k m h S
    have ineq : m ⊔ n ≤ k ⊔ n := sup_le_sup_right h n
    have hsp : homOfLE (by simp : n ≤ k ⊔ n) = homOfLE (by simp) ≫ homOfLE ineq := by
      apply Subsingleton.elim
    simp_rw [LvlStratHom.con, hsp, op_comp, Functor.map_comp, comp_covering_str_apply,
      ResStrategy.res_fromMap, ← limCone_π_map_nat hF ineq]
    rw [fromMap_comp', fixing_snd_mon (by simp : m ≤ m ⊔ n) _ (transition_fixing hF ineq)]
lemma limCone_str_nat {n m : ℕ} (h : n ≤ m) :
  limCone_str hF m ≫ (F.map (homOfLE h).op).str = limCone_str hF n := by
  ext p k S x hx hl
  simp only [homOfLE_leOfHom, LvlStratHom.comp_toFun, Function.comp_apply]
  have ineq : k ⊔ n ≤ k ⊔ m := sup_le_sup_left h k
  have hFm : F.map (homOfLE (by simp)).op ≫ F.map (homOfLE h).op
    = F.map (homOfLE ineq).op ≫ F.map (homOfLE (by simp)).op := by
    simp_rw [← F.map_comp]; congr! 1
  simp_rw [limCone_str, ← comp_covering_str_apply]
  rw [hFm, comp_covering_str_apply, fixing_snd_mon
    (by simp) _ (transition_fixing hF ineq), ← ResStrategy.fromMap_comp']
  simp_rw [limCone_π_map_nat]

lemma cast_limCone_str {m m' : ℕ} (h : m' = m)
  (hi : Tree.Fixing k (limCone_π_map hF m) := by as_aux_lemma => synth_fixing) {S} :
  ((F.map (homOfLE h.le).op).str.toFun p k) ((ResStrategy.fromMap (limCone_π_map hF m)) S)
    = ResStrategy.fromMap (f := limCone_π_map hF m') (h := by subst h; exact hi) S
    := by subst h; simp

lemma limCone_str_large S n x hx hl (h : k ≤ n) :
  (((limCone_str hF n).toFun p k S) (limCone_π_map hF n x)
    (by as_aux_lemma => synth_isPosition) (by simpa only [LenHom.h_length_simp])).valT'
  --no as_aux_lemma => causes problems after proof, so misunderstood def
  = limCone_π_map hF n (S x hx hl).valT' := by
  rw [limCone_str, cast_limCone_str hF (by simp [h]), ResStrategy.fromMap_valT']

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def covering_lift_bodySystem {T U : PTrees} (f : T ⟶ U) (y : bodySystem.obj U.1)
  (S : StrategySystem T.1 p) (yc : consistent y (((LvlStratHom.system p).map f.str S))) :=
  ((bodyLiftExists_iff_system _ _).mp f.h_body _ yc).choose
lemma covering_lift_bodySystem_spec1 {T U : PTrees} (f : T ⟶ U) (y : bodySystem.obj U.1)
  (S : StrategySystem T.1 p) (yc : consistent y (((LvlStratHom.system p).map f.str S))) :
  consistent (covering_lift_bodySystem f y S yc) S :=
  ((bodyLiftExists_iff_system _ _).mp f.h_body _ yc).choose_spec.1
lemma covering_lift_bodySystem_spec2 {T U : PTrees} (f : T ⟶ U) (y : bodySystem.obj U.1)
  (S : StrategySystem T.1 p) (yc : consistent y (((LvlStratHom.system p).map f.str S))) :
  bodySystem.map f.toHom (covering_lift_bodySystem f y S yc) = y :=
  ((bodyLiftExists_iff_system _ _).mp f.h_body _ yc).choose_spec.2

lemma ineq_rec n k : n ⊔ k ≤ n ⊔ (k + 1) := by apply sup_le_sup_left; simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def map_ineq_rec n k := F.map (homOfLE (ineq_rec n k)).op
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def limCone_body_lifts (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) :
    ∀ k, Σ' (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ k))).1),
    consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ k)) S)
  | 0 => ⟨y, yc⟩
  | k + 1 =>
    let ih := limCone_body_lifts S y yc k
    let S' := (LvlStratHom.system p).map (limCone_str hF (n ⊔ (k + 1))) S
    have yc' := by simpa only [← limCone_str_nat hF (ineq_rec n k)] using ih.2
    ⟨covering_lift_bodySystem (map_ineq_rec n k) ih.1 S' yc',
    covering_lift_bodySystem_spec1 (map_ineq_rec n k) ih.1 S' yc'⟩
lemma limCone_body_is_lift (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) k m :
  (resEq m).map (map_ineq_rec n k).toHom ((limCone_body_lifts hF S y yc (k + 1)).1.res m)
  = (limCone_body_lifts hF S y yc k).1.res m := by
  let ih := limCone_body_lifts hF S y yc k
  let S' := (LvlStratHom.system p).map (limCone_str hF (n ⊔ (k + 1))) S
  have yc' := by simpa only [← limCone_str_nat hF (ineq_rec n k)] using ih.2
  have hs := covering_lift_bodySystem_spec2 (map_ineq_rec n k) ih.1 S' yc'
  simp_rw [limCone_body_lifts]
  rw [← (congr_arg BodySystemObj.res hs)]; rfl

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def limCone_body_system (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) :
  bodySystem.obj (limConePt hF).1 where
    res := fun k ↦
      have : Tree.Fixing k (limCone_π_map hF (n ⊔ k)) := by synth_fixing
      inv ((resEq k).map (limCone_π_map hF (n ⊔ k)))
      ((limCone_body_lifts hF S _ yc k).1.res k)
    con := by
      intro k; simp only [Set.mem_setOf_eq]; rw [← limCone_body_is_lift]
      have hnat := congr_arg (resEq k).map <| limCone_π_map_nat hF (ineq_rec n k)
      simp_rw [Functor.map_comp] at hnat
      have htr : Tree.Fixing (k + 1) (limCone_π_map hF (n ⊔ (k + 1))) := by synth_fixing
      have : Tree.Fixing k (limCone_π_map hF (n ⊔ (k + 1))) := by synth_fixing
      have : Tree.Fixing k (limCone_π_map hF (n ⊔ k)) := by synth_fixing
      rw [map_ineq_rec, iso_cancel_comp _ _ _ _ hnat]
      simp_rw [List.prefix_iff_eq_take, resEq_len]
      -- Regression: the second rewrite needs the explicit fixing proof.
      simp_rw [inv_val_eq_pInv_val', inv_val_eq_pInv_val' _ _ htr]
      simp_rw [← take_apply_pInv_val]
      congr; simp_rw [bodySystem_take]
      simp only [le_add_iff_nonneg_right, zero_le, inf_of_le_right]

lemma consistent_cast {S T : Trees} (h : S = T)
  {S' : StrategySystem S p} {S'' : StrategySystem T p} (h' : HEq S' S'')
  (y : bodySystem.obj S) (hc : consistent y S') :
  consistent (cast (by rw [h]) y : bodySystem.obj T) S'' := by
  subst h h'; exact hc
lemma cancel_resEq_inv_cast {m n} (h : n = m) (h' : k ≤ m) (x : (resEq k).obj _) :
  have : FixingEq k (limCone_π_map hF n) := by
    subst h; exact fixingEq_of_fixing (h := by synth_fixing)
  ((resEq k).map (limCone_π_map hF m)) (inv ((resEq k).map (limCone_π_map hF n)) x)
  = cast (by simp [h]) x := by
    subst h
    have : FixingEq k (limCone_π_map hF n) := fixingEq_of_fixing (h := by synth_fixing)
    apply cancel_inv_right_types
lemma cancel_pInv_cast {m n} (h : m = n) x [Tree.Fixing x.val.length (limCone_π_map hF n)] :
  (limCone_π_map hF m (pInv (limCone_π_map hF n) x)) = cast (by rw [h]) x :=
  by subst h; simp
lemma cast_lifts' {m n} (h : m = n) {S : (LvlStratHom.system p).obj ⟨limConePt hF⟩} {y} hy :
  (⟨((limCone_body_lifts hF S y hy n).1.res m).val, by apply resEq_mem⟩ :
    (F.obj (Opposite.op (k ⊔ n))).1)
  = ⟨((limCone_body_lifts hF S y hy n).1.res n).val, by apply resEq_mem⟩ :=
  by subst h; rfl

lemma take_apply_val_resEq {S T} (f : S ⟶ T) (k n : ℕ) (x : (resEq k).obj S) :
  (f ⟨x.val.take n, take_mem (resEq.val' x)⟩).val = (f (resEq.val' x)).val.take n :=
  by apply take_apply_val (x := resEq.val' x)

lemma limCone_body_is_lift' (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) k m :
  ((map_ineq_rec n k).toHom
    (resEq.val' ((limCone_body_lifts hF S y yc (k + 1)).1.res m)))
  = resEq.val' ((limCone_body_lifts hF S y yc k).1.res m) := by
  ext1
  apply congr_arg Subtype.val (limCone_body_is_lift hF S y yc k m)

lemma limCone_body_system_map_contains (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S))
  (x : (limConePt hF).1)
  (hc : (BodySystemObj.ofObj (limCone_body_system hF S y yc)).containsTree x) :
  (BodySystemObj.ofObj (limCone_body_lifts hF S y yc (x.val.length + 1)).1).containsTree
    ((limCone_π_map hF (n ⊔ (x.val.length + 1))) x) := by
  unfold BodySystemObj.containsTree at hc ⊢
  simp only [LenHom.h_length_simp]
  have hfix : Tree.Fixing x.val.length (map_ineq_rec (F := F) n x.val.length).toHom := by
    exact (transition_fixing hF (ineq_rec n x.val.length)).1.mon (by simp)
  apply Tree.Fixing.inj (map_ineq_rec (F := F) n x.val.length).toHom
    (ht := by simpa only [LenHom.h_length_simp] using hfix)
  rw [← CategoryTheory.comp_apply]
  change
    (ConcreteCategory.hom
      (limCone_π_map hF (n ⊔ (x.val.length + 1)) ≫
        (F.map (homOfLE (ineq_rec n x.val.length)).op).toHom)) x =
    (map_ineq_rec (F := F) n x.val.length).toHom
      (resEq.val' ((limCone_body_lifts hF S y yc (x.val.length + 1)).1.res x.val.length))
  rw [limCone_π_map_nat hF (ineq_rec n x.val.length)]
  rw [limCone_body_is_lift' hF S y yc x.val.length x.val.length]
  change (limCone_π_map hF (n ⊔ x.val.length)) x =
    resEq.val' ((limCone_body_lifts hF S y yc x.val.length).1.res x.val.length)
  conv_lhs =>
    arg 2
    rw [hc]
  change
    resEq.val'
      (((resEq x.val.length).map (limCone_π_map hF (n ⊔ x.val.length)))
        ((limCone_body_system hF S y yc).res x.val.length)) =
    resEq.val' ((limCone_body_lifts hF S y yc x.val.length).1.res x.val.length)
  simp [limCone_body_system]

lemma limCone_body_system_project (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) k :
  (limCone_π_map hF (n ⊔ k)) (resEq.val' ((limCone_body_system hF S y yc).res k)) =
    resEq.val' ((limCone_body_lifts hF S y yc k).1.res k) := by
  change
    resEq.val'
      (((resEq k).map (limCone_π_map hF (n ⊔ k)))
        ((limCone_body_system hF S y yc).res k)) =
    resEq.val' ((limCone_body_lifts hF S y yc k).1.res k)
  simp [limCone_body_system]

lemma limCone_body_consistent (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
    (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
    (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) :
    consistent (limCone_body_system hF S y yc) S := by
  intro x hp hc; rw [BodySystemObj.bodySystem_contains_iff']
  apply Tree.Fixing.inj (limCone_π_map hF (n ⊔ (x.val.length + 1))) _
  unfold resEq.val'
  rw [← limCone_str_large (h := by simp_rw [le_sup_iff, le_add_iff_nonneg_right, zero_le, or_true])]
  simp only [limCone_body_system, ExtensionsAt.valT'_coe, ExtensionsAt.val'_length]
  have :
      Tree.Fixing (x.val.length + 1) (limCone_π_map hF (n ⊔ (x.val.length + 1))) := by
    synth_fixing
  change _ = (limCone_π_map hF (n ⊔ (x.val.length + 1)))
    (resEq.val' ((limCone_body_system hF S y yc).res (x.val.length + 1)))
  rw [limCone_body_system_project hF S y yc (x.val.length + 1)]
  have h :=
    ((limCone_body_lifts hF S _ yc) (x.val.length + 1)).2
      ((limCone_π_map hF (n ⊔ (x.val.length + 1))) x)
      (by simpa only [IsPosition.iff_lenHom] using hp)
      (by
        rw [BodySystemObj.bodySystem_contains_iff] at hc ⊢
        exact limCone_body_system_map_contains hF S y yc x hc)
  rw [BodySystemObj.bodySystem_contains_iff'] at h
  simp_rw [BodySystemObj.containsTree] at h
  unfold resEq.val' at h ⊢
  simp_rw [ExtensionsAt.valT'_coe, ExtensionsAt.val'_length, LenHom.h_length_simp] at h
  exact h

lemma cast_apply_F (h : n ≤ m) (hn : n = n') (x : (resEq k).obj (F.obj (Opposite.op m)).1)
  hpr2 (hpr1 : (x : (resEq k).obj (F.obj (Opposite.op m)).1).val ∈ (F.obj (Opposite.op m)).1.2) :
  ((F.map (homOfLE h).op).toHom
    ⟨(x : (resEq k).obj (F.obj (Opposite.op m)).1).val, hpr1⟩ :
      (F.obj (Opposite.op n)).1).val
    = cast (by subst hn; rfl)
      ((F.map (homOfLE (by subst hn; exact h)).op).toHom ⟨x.val, hpr2⟩ :
        (F.obj (Opposite.op n')).1).val := by
  subst hn; rfl
lemma lifts_cast_lifts (hm : m = m') (hn : n = n') (y : bodySystem.obj (F.obj (Opposite.op m)).1) :
  cast (by rw [hm]) ((cast (by rw [hm]) y : bodySystem.obj (F.obj (Opposite.op m')).1).res n).val
  = (y.res n').val := by subst hm hn; rfl

lemma limCone_body_is_lift_fin (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
  (yc : consistent y ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) k m :
  ((F.map (homOfLE (by simp)).op).toHom
    (resEq.val' ((limCone_body_lifts hF S y yc k).1.res m))).val
  = (y.res m).val := by
  change _ = (resEq.val' (y.res m)).val
  congr 1
  induction k with
  | zero => simp [limCone_body_lifts]
  | succ k ih =>
    have h : F.map (homOfLE (by simp)).op
      = map_ineq_rec n k ≫ F.map (homOfLE (by simp : n ⊔ 0 ≤ n ⊔ k)).op := by
      rw [map_ineq_rec, ← Functor.map_comp]; congr
    rwa [h, comp_covering_toHom, CategoryTheory.comp_apply, limCone_body_is_lift']

lemma limCone_body_system_lift (S : (LvlStratHom.system p).obj ⟨limConePt hF⟩)
  (y : bodySystem.obj (F.obj (Opposite.op n)).1)
  (yc : consistent (cast (by simp) y) ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S)) :
  bodySystem.map (limCone_π_map hF n) (limCone_body_system hF S _ yc) = y := by
  apply BodySystemObj.obj_ext
  apply BodySystemObj.ext
  funext k
  apply resEq_ext
  rw [← bodySystem_take' (BodySystemObj.ofObj y) (by simp : k ≤ n ⊔ k),
    limCone_body_system, bodySystem_take_val,
    inf_of_le_right (by apply le_sup_right), ← limCone_π_map_nat hF (by simp : n ≤ n ⊔ k)]
  have hfix : Tree.Fixing k (limCone_π_map hF (n ⊔ k)) := by synth_fixing
  dsimp [BodySystemObj.ofObj, bodySystem, resEq_map]
  change
    ((limCone_π_map hF (n ⊔ k) ≫
        (F.map (homOfLE (by simp : n ≤ n ⊔ k)).op).toHom)
      (resEq.val'
        (inv ((resEq k).map (limCone_π_map hF (n ⊔ k)))
          ((limCone_body_lifts hF S (cast (by simp) y) yc k).1.res k)))).val =
      (y.res k).val
  rw [CategoryTheory.comp_apply]
  have hcancel :
      (limCone_π_map hF (n ⊔ k))
        (resEq.val' (inv ((resEq k).map (limCone_π_map hF (n ⊔ k)))
          ((limCone_body_lifts hF S (cast (by simp) y) yc k).1.res k))) =
        resEq.val' ((limCone_body_lifts hF S (cast (by simp) y) yc k).1.res k) := by
    exact congrArg (resEq.val' (S := (F.obj (Opposite.op (n ⊔ k))).1))
      (cancel_inv_right_types ((resEq k).map (limCone_π_map hF (n ⊔ k)))
        ((limCone_body_lifts hF S (cast (by simp) y) yc k).1.res k))
  rw [hcancel]
  erw [cast_apply_F (n := n) (n' := n ⊔ 0)]
  · change cast (by simp)
        (((F.map (homOfLE (by simp : n ⊔ 0 ≤ n ⊔ k)).op).toHom
          (resEq.val' ((limCone_body_lifts hF S (cast (by simp) y) yc k).1.res k))).val) =
        (y.res k).val
    rw [limCone_body_is_lift_fin hF S (cast (by simp) y) yc k k]
    simpa using
      (lifts_cast_lifts (F := F) (hm := (by simp : n = n ⊔ 0)) (hn := rfl) y)
  · simp

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def limCone_π n : limConePt hF ⟶ F.obj (Opposite.op n) where
  toHom := limCone_π_map hF n
  str := limCone_str hF n
  h_body := by
    have : ∀ k, FixingEq k (limCone_π_map hF (n ⊔ k)) :=
      fun k ↦ (fixing_iff_fixingEq (n ⊔ k) _).mp (by synth_fixing) k (by simp)
    rw [bodyLiftExists_iff_system]
    intro p S y yc
    have yc' : consistent (cast (by simp) y : bodySystem.obj (F.obj (Opposite.op (n ⊔ 0))).1)
      ((LvlStratHom.system p).map (limCone_str hF (n ⊔ 0)) S) :=
      consistent_cast (by simp) (by
        have hn : n ⊔ 0 = n := by simp
        rw [hn]
        simp [LvlStratHom.systemToObj, LvlStratHom.systemOfObj]
        rfl) y yc
    use limCone_body_system hF S _ yc'
    exact ⟨limCone_body_consistent hF S _ yc', limCone_body_system_lift hF S _ yc'⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def limCone : Limits.Cone F where
  pt := limConePt hF
  π := {
    app := fun ⟨n⟩ ↦ limCone_π hF n
    naturality := fun ⦃_ _⦄ f ↦
      Covering.ext ((Tree.limCone _).π.naturality f) ((limCone_str_nat hF _).symm)
  }
lemma limCone_fixing n : Fixing (K + n) ((limCone hF).π.app (Opposite.op n)) := by
  use limCone_π_fixing_full hF n; intro p; ext S
  simp_rw [limCone, limCone_π, limCone_str,
    (transition_fixing_full hF (by simp : n ≤ (K + n) ⊔ n)).2 p,
    ← ResStrategy.fromMap_comp', limCone_π_map_nat]
  rfl

end «Section1»
end GaleStewartGame.Covering
