import PEqualNP.Gct.Helpers.MincExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.CardEmbedding

/-!
# A dimension bound for cyclically invariant permanent-level spaces

Let L be a complex subspace of five by five matrices on which the permanent
of the all-ones matrix plus any member of L equals 120. If L is invariant under
cyclic shifts of the rows, its dimension is at most eight.

The degree-five part forces a common zero column in each nonconstant Fourier
mode. The polarized degree-two part pairs opposite modes orthogonally on the
remaining four coordinates. The constant mode vanishes, giving the bound 4 + 4.
-/

namespace PEqualNP.Gct.CyclicFive

namespace FivePair

open Finset
abbrev V := Fin 5 → ℂ
abbrev W := Fin 4 → ℂ

private noncomputable def deleteCoord (j : Fin 5) : V →ₗ[ℂ] W :=
  LinearMap.funLeft ℂ ℂ j.succAbove

private noncomputable def cross (j : Fin 5) : V →ₗ[ℂ] W :=
  LinearMap.pi fun k => (∑ i : Fin 5, LinearMap.proj i) - LinearMap.proj (j.succAbove k)

private lemma cross_formula (j : Fin 5) (x : V) (k : Fin 4) :
    cross j x k = (∑ i, x i) - x (j.succAbove k) := by simp [cross, LinearMap.sum_apply]

private lemma cross_trivial {i j : Fin 5} {x : V} (hi : x i = 0) (hz : cross j x = 0) :
    x = 0 := by
  let a := ∑ k, x k
  have he (k : Fin 4) : x (j.succAbove k) = a := by
    have hk := congrFun hz k
    change cross j x k = 0 at hk
    rw [cross_formula] at hk
    exact (sub_eq_zero.mp hk).symm
  have hj : a = x j + 4 * a := calc
    a = x j + ∑ k, x (j.succAbove k) := Fin.sum_univ_succAbove x j
    _ = _ := by simp [he]
  have ha : a = 0 := by
    by_cases hij : i = j
    · subst i; rw [hi] at hj; linear_combination -hj / 3
    · obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hij
      rw [← hk, he] at hi
      exact hi
  rw [ha] at hj
  funext k
  cases k using Fin.succAboveCases j with
  | x => simpa using hj.symm
  | p t => simpa [ha] using he t

/-- Opposite coordinate hyperplanes retain a nondegenerate restricted pairing. -/
theorem rank_pair {U Z : Submodule ℂ V} {i j : Fin 5}
    (hu : ∀ x ∈ U, x i = 0) (hz : ∀ y ∈ Z, y j = 0)
    (ho : ∀ x ∈ U, ∀ y ∈ Z, (∑ k, ((∑ l, x l) - x k) * y k) = 0) :
    Module.finrank ℂ U + Module.finrank ℂ Z ≤ 4 := by
  let A := (cross j).comp U.subtype
  let B := (deleteCoord j).comp Z.subtype
  have hA : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    exact fun x h => Subtype.ext (cross_trivial (hu x x.property) h)
  have hB : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply Subtype.ext
    funext k
    cases k using Fin.succAboveCases j with
    | x => exact hz y y.property
    | p t => exact congrFun (show B y = 0 from hy) t
  have H : (LinearMap.range A).map (dotProductEquiv ℂ (Fin 4)).toLinearMap ≤
      (LinearMap.range B).dualAnnihilator := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    simp only [Submodule.mem_dualAnnihilator]
    rintro _ ⟨y, rfl⟩
    change (∑ k, (cross j x k) * y.val (j.succAbove k)) = 0
    have he := ho x x.property y y.property
    rw [Fin.sum_univ_succAbove _ j] at he
    simpa only [hz y y.property, mul_zero, zero_add, cross_formula] using he
  have h₁ := Submodule.finrank_mono H
  rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hA] at h₁
  have h₂ := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range B)
  rw [LinearMap.finrank_range_of_inj hB, Module.finrank_fin_fun] at h₂
  exact (Nat.add_le_add_right h₁ _).trans_eq ((Nat.add_comm _ _).trans h₂)

end FivePair

namespace FiveFourier

open Finset
abbrev V := Fin 5 → ℂ
abbrev M := Fin 5 × Fin 5 → ℂ

private def char (z : ℂ) (i : Fin 5) := z ^ i.val

private lemma char_add {z : ℂ} (h : IsPrimitiveRoot z 5) (i j : Fin 5) :
    char z (i + j) = char z i * char z j := by
  unfold char
  rw [Fin.val_add, ← pow_add]
  simpa only [← h.eq_orderOf] using (pow_mod_orderOf z (i.val + j.val))

def phase (z : ℂ) (k i : Fin 5) := char z (k * i)

lemma phase_ne {z : ℂ} (h : IsPrimitiveRoot z 5) (k i : Fin 5) : phase z k i ≠ 0 :=
  pow_ne_zero _ (h.ne_zero (by decide))

private lemma sum_phase {z : ℂ} (h : IsPrimitiveRoot z 5) (k : Fin 5) :
    (∑ i, phase z k i) = if k = 0 then 5 else 0 := by
  classical
  split_ifs with hk
  · subst k; simp [phase, char]
  · have bij : ∀ a : Fin 5, a ≠ 0 → Function.Bijective (a * ·) := by decide
    change (∑ i : Fin 5, char z (k * i)) = 0
    calc
      _ = ∑ i : Fin 5, char z i := Equiv.sum_comp (Equiv.ofBijective _ (bij k hk)) (char z)
      _ = 0 := by simpa [char, Fin.sum_univ_five, Finset.sum_range_succ, add_assoc] using h.geom_sum_eq_zero (by decide)

private lemma phase_mix {z : ℂ} (h : IsPrimitiveRoot z 5) (k i s : Fin 5) :
    phase z k i * phase z (-k) s = phase z (i - s) k := by
  unfold phase
  rw [← char_add h]
  exact congrArg (char z) ((by decide : ∀ k i s : Fin 5, k * i + -k * s = (i - s) * k) k i s)

lemma opposite {z : ℂ} (h : IsPrimitiveRoot z 5) {k : Fin 5} (hk : k ≠ 0) :
    (∑ j, ((∑ i, phase z k i) - phase z k j) * phase z (-k) j) = -5 := by
  simp only [sum_phase h, ite_eq_right hk, zero_sub, neg_mul]
  simp_rw [phase_mix h, sub_self]
  simp [phase, char]

noncomputable def sample (z : ℂ) (k : Fin 5) : M →ₗ[ℂ] V where
  toFun t j := ∑ s, phase z (-k) s * t (s, j)
  map_add' a b := by ext j; simp [mul_add, sum_add_distrib]
  map_smul' c a := by
    ext j
    change (∑ s, phase z (-k) s * (c * a (s, j))) = c * ∑ s, phase z (-k) s * a (s, j)
    simp only [mul_sum, mul_left_comm]

def shifted (s : Fin 5) (t : M) : M := fun p => t (p.1 + s, p.2)

/-- Translation averaging projects a matrix onto one row character, up to scale. -/
lemma project {z : ℂ} (h : IsPrimitiveRoot z 5) (k : Fin 5) (t : M) :
    (fun p : Fin 5 × Fin 5 => phase z k p.1 * sample z k t p.2) =
    ∑ r, phase z (-k) r • shifted r t := by
  classical
  funext ⟨i,j⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, shifted]
  change phase z k i * (∑ s, phase z (-k) s * t (s,j)) = _
  rw [mul_sum]
  calc
    _ = ∑ r, phase z k i * (phase z (-k) (i + r) * t (i+r,j)) :=
      (Equiv.sum_comp (Equiv.addLeft i) (fun s => phase z k i * (phase z (-k) s * t (s,j)))).symm
    _ = _ := by
      apply sum_congr rfl
      intro r _
      rw [← mul_assoc]
      unfold phase
      rw [← char_add h]
      rw [show k * i + -k * (i + r) = -k * r from
        (by decide : ∀ a b c : Fin 5, a*b + -a*(b+c) = -a*c) k i r]

lemma reconstruct {z : ℂ} (h : IsPrimitiveRoot z 5) (t : M) (i j : Fin 5) :
    (∑ k, phase z k i * sample z k t j) = 5 * t (i,j) := by
  change (∑ k, phase z k i * ∑ s, phase z (-k) s * t (s,j)) = _
  simp_rw [mul_sum, ← mul_assoc, phase_mix h]
  rw [sum_comm]
  simp_rw [← sum_mul, sum_phase h]
  simp [sub_eq_zero, ite_mul]

end FiveFourier

namespace FiveRows

open Finset Polynomial

abbrev V := Fin 5 → ℂ
abbrev M := Fin 5 × Fin 5 → ℂ

def Level (L : Submodule ℂ M) : Prop :=
  ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120

private noncomputable def linePoly (t : M) : Polynomial ℂ :=
  ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + C (t (i,f i)) * X)

private lemma line_constant {L : Submodule ℂ M} (hl : Level L) {t : M} (ht : t ∈ L) :
    linePoly t = C 120 := by
  apply Polynomial.funext
  intro z
  rw [linePoly, Polynomial.eval_finsetSum, Polynomial.eval_C]
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [← hl (z • t) (L.smul_mem z ht)]
  exact Finset.sum_congr rfl fun f _ => Finset.prod_congr rfl fun i _ =>
    congrArg (1 + ·) (mul_comm _ z)

private lemma top_coeff (t : M) :
    (linePoly t).coeff 5 = ∑ f : Fin 5 ↪ Fin 5, ∏ i, t (i,f i) := by
  classical
  rw [linePoly, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro f _
  have h := Polynomial.coeff_prod_of_natDegree_le (s := (univ : Finset (Fin 5)))
    (fun i : Fin 5 => (1 + C (t (i,f i)) * X : Polynomial ℂ)) 1 (by
      intro i _
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_mul_le.trans (by simp)))
  simpa [Polynomial.coeff_one] using h

lemma top_vanishes {L : Submodule ℂ M} (hl : Level L) {t : M} (ht : t ∈ L) :
    (∑ f : Fin 5 ↪ Fin 5, ∏ i, t (i, f i)) = 0 := by
  rw [← top_coeff, line_constant hl ht]
  simp

private def tensor (a b : V) : M := fun p => a p.1 * b p.2

private lemma top_tensor (a b : V) :
    (∑ f : Fin 5 ↪ Fin 5, ∏ i, tensor a b (i, f i)) = 120 * (∏ i, a i) * ∏ j, b j := by
  classical
  have h (f : Fin 5 ↪ Fin 5) : (∏ i, tensor a b (i, f i)) = (∏ i, a i) * ∏ j, b j := by
    rw [show (∏ i, tensor a b (i, f i)) = (∏ i, a i) * (∏ i, b (f i)) from
      Finset.prod_mul_distrib]
    let e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective)
    exact congrArg ((∏ i, a i) * ·) (e.prod_comp b)
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  have hc : Fintype.card (Fin 5 ↪ Fin 5) = 120 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    decide
  rw [hc]
  push_cast
  ring

/-- All column profiles for a fixed nowhere-zero row profile vanish at one common index. -/
lemma common_zero {L : Submodule ℂ M} (hl : Level L) {a : V} (ha : ∀ i, a i ≠ 0)
    (U : Submodule ℂ V) (hu : ∀ b ∈ U, tensor a b ∈ L) :
    ∃ j : Fin 5, ∀ b ∈ U, b j = 0 := by
  classical
  have exists_zero (b : U) : ∃ j, (b : V) j = 0 := by
    have h := top_vanishes hl (hu b b.property)
    rw [top_tensor] at h
    have hp : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
    have hprod := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hp)
    simpa [Finset.prod_eq_zero_iff] using hprod
  let coordinate (j : Fin 5) : U →ₗ[ℂ] ℂ := (LinearMap.proj j).comp U.subtype
  have cover : (⋃ j, ((LinearMap.ker (coordinate j) : Submodule ℂ U) : Set U)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    obtain ⟨j, hj⟩ := exists_zero b
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ cover
  refine ⟨j, fun b hb => ?_⟩
  have : (⟨b,hb⟩ : U) ∈ LinearMap.ker (coordinate j) := by rw [hj]; trivial
  exact this


private noncomputable def injections (a b : V) : ℂ :=
  ∑ f : Fin 2 ↪ Fin 5, a (f 0) * b (f 1)

private def pairsEquiv : (Fin 2 ↪ Fin 5) ≃ (Σ j : Fin 5, {i : Fin 5 // i ≠ j}) where
  toFun f := ⟨f 1, f 0, fun h => (by decide : (0 : Fin 2) ≠ 1) (f.injective h)⟩
  invFun p := ⟨![p.2.val, p.1], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [p.2.property, Ne.symm p.2.property]⟩
  left_inv f := by ext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨j,i,h⟩; rfl

private lemma injections_sum (a b : V) :
    injections a b = ∑ j, ((∑ i, a i) - a j) * b j := by
  classical
  unfold injections
  rw [← pairsEquiv.symm.sum_comp (fun f : Fin 2 ↪ Fin 5 => a (f 0) * b (f 1)), Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  change (∑ i : {i : Fin 5 // i ≠ j}, a i.val * b j) = _
  rw [← sum_mul]
  congr 1
  have sub : (∑ i : {i : Fin 5 // i ≠ j}, a i.val) = ∑ i ∈ univ.erase j, a i :=
    (sum_subtype _ (by simp) a).symm
  rw [sub, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  ring

private lemma nextCoeff (p : Polynomial ℂ) (a : ℂ) (k : ℕ) :
    (p * (1 + C a * X)).coeff (k + 1) = p.coeff (k + 1) + p.coeff k * a := by
  rw [mul_add, mul_one, ← mul_assoc, coeff_add, coeff_mul_X, coeff_mul_C]

private lemma constCoeff (p : Polynomial ℂ) (a : ℂ) :
    (p * (1 + C a * X)).coeff 0 = p.coeff 0 := by
  rw [mul_add, mul_one, ← mul_assoc, coeff_add, coeff_mul_X_zero, add_zero]

private lemma polar_atom (a b : V) :
    (∏ i, (1 + C (a i + b i) * X)).coeff 2 -
      (∏ i, (1 + C (a i) * X)).coeff 2 - (∏ i, (1 + C (b i) * X)).coeff 2 = injections a b := by
  rw [injections_sum]
  simp only [Fin.prod_univ_five, Fin.sum_univ_five, nextCoeff, constCoeff]
  simp [Polynomial.coeff_one, Polynomial.coeff_X]
  ring

/-- The mixed degree-two coefficient vanishes on every pair of members of L. -/
private lemma mixed_zero {L : Submodule ℂ M} (hl : Level L) {a b : M}
    (ha : a ∈ L) (hb : b ∈ L) :
    (∑ f : Fin 5 ↪ Fin 5, injections (fun i => a (i,f i)) (fun i => b (i,f i))) = 0 := by
  simp_rw [← polar_atom]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h (t : M) (ht : t ∈ L) : (∑ f : Fin 5 ↪ Fin 5, (∏ i, (1 + C (t (i,f i)) * X)).coeff 2) = 0 := by
    rw [← finsetSum_coeff]
    change (linePoly t).coeff 2 = _
    rw [line_constant hl ht]
    simp
  have hab := h (a + b) (L.add_mem ha hb)
  simp only [Pi.add_apply] at hab
  rw [hab, h a ha, h b hb]
  simp

private noncomputable def permEmb : Equiv.Perm (Fin 5) ≃ (Fin 5 ↪ Fin 5) where
  toFun e := e.toEmbedding
  invFun f := Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective)
  left_inv e := by ext; rfl
  right_inv f := by ext; rfl

private lemma pair_avg (h : Fin 2 ↪ Fin 5) (u v : V) :
    (∑ f : Fin 5 ↪ Fin 5, u (f (h 0)) * v (f (h 1))) = 6 * injections u v := by
  rw [← permEmb.sum_comp (fun f : Fin 5 ↪ Fin 5 => u (f (h 0)) * v (f (h 1)))]
  exact PEqualNP.Gct.Helpers.Minc.sum_perm_res h (fun k => u (k 0) * v (k 1))

private lemma orthogonal {L : Submodule ℂ M} (hl : Level L)
    (a b u v : V) (ha : tensor a u ∈ L) (hb : tensor b v ∈ L)
    (hab : injections a b ≠ 0) : injections u v = 0 := by
  have h := mixed_zero hl ha hb
  unfold injections at h
  rw [Finset.sum_comm] at h
  have term (h : Fin 2 ↪ Fin 5) :
      (∑ f : Fin 5 ↪ Fin 5, tensor a u (h 0, f (h 0)) * tensor b v (h 1, f (h 1))) =
      (a (h 0) * b (h 1)) * (6 * injections u v) := by
    rw [← pair_avg h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    unfold tensor
    ring
  simp_rw [term] at h
  rw [← Finset.sum_mul] at h
  change injections a b * (6 * injections u v) = 0 at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hab)).resolve_left (by norm_num)


private noncomputable def tensorMap (a : V) : V →ₗ[ℂ] M where
  toFun := tensor a
  map_add' u v := by ext p; exact mul_add _ _ _
  map_smul' c u := by ext p; exact mul_left_comm _ _ _

private noncomputable def columns (L : Submodule ℂ M) (a : V) : Submodule ℂ V :=
  L.comap (tensorMap a)

private lemma pair_bound {L : Submodule ℂ M} (hl : Level L) (a b : V)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hab : injections a b ≠ 0) :
    Module.finrank ℂ (columns L a) + Module.finrank ℂ (columns L b) ≤ 4 := by
  obtain ⟨i, hi⟩ := common_zero hl ha (columns L a) (fun _ hu => hu)
  obtain ⟨j, hj⟩ := common_zero hl hb (columns L b) (fun _ hu => hu)
  refine FivePair.rank_pair hi hj (fun u hu v hv => ?_)
  rw [← injections_sum]
  exact orthogonal hl a b u v hu hv hab

private lemma constant_rows {L : Submodule ℂ M} (hl : Level L) (u : V)
    (hu : tensor (fun _ => 1) u ∈ L) : u = 0 := by
  funext j
  by_contra h
  change u j ≠ 0 at h
  let c := -(u j)⁻¹
  have eq := hl _ (L.smul_mem c hu)
  have line (f : Fin 5 ↪ Fin 5) :
      (∏ i, (1 + (c • tensor (fun _ => 1) u) (i, f i))) = 0 := by
    obtain ⟨i, hi⟩ := (Finite.injective_iff_bijective.mp f.injective).surjective j
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change 1 + c * (1 * u (f i)) = 0
    rw [hi]
    dsimp [c]
    simp [h]
  simp only [line, sum_const_zero] at eq
  norm_num at eq

open FiveFourier

/-- The four nonconstant row characters form two opposite pairs. -/
theorem cyclic_bound (L : Submodule ℂ M) (hl : Level L)
    (hs : ∀ t ∈ L, ∀ s : Fin 5, shifted s t ∈ L) : Module.finrank ℂ L ≤ 8 := by
  obtain ⟨z, h⟩ : ∃ z : ℂ, IsPrimitiveRoot z 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by decide)⟩
  let U (k : Fin 5) := columns L (phase z k)
  have in_U (k : Fin 5) (t : L) : sample z k t.val ∈ U k := by
    change (fun p : Fin 5 × Fin 5 => phase z k p.1 * sample z k t.val p.2) ∈ L
    rw [project h k t.val]
    exact L.sum_mem fun r _ => L.smul_mem _ (hs t.val t.property r)
  let coeff (k : Fin 5) : L →ₗ[ℂ] U k :=
    ((sample z k).comp L.subtype).codRestrict (U k) (in_U k)
  have noZero (t : L) : sample z 0 t.val = 0 := by
    apply constant_rows hl
    have h0 := in_U 0 t
    change tensor (phase z 0) (sample z 0 t.val) ∈ L at h0
    exact (show phase z 0 = fun _ => 1 by funext i; simp [phase, FiveFourier.char]) ▸ h0
  let pack := ((coeff 1).prod (coeff 4)).prod ((coeff 2).prod (coeff 3))
  have inj : Function.Injective pack := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro t ht
    change pack t = 0 at ht
    have h1 : sample z 1 t.val = 0 := congrArg (fun p => ((p.1.1 : U 1) : V)) ht
    have h4 : sample z 4 t.val = 0 := congrArg (fun p => ((p.1.2 : U 4) : V)) ht
    have h2 : sample z 2 t.val = 0 := congrArg (fun p => ((p.2.1 : U 2) : V)) ht
    have h3 : sample z 3 t.val = 0 := congrArg (fun p => ((p.2.2 : U 3) : V)) ht
    apply Subtype.ext
    funext ⟨i,j⟩
    have inv := reconstruct h t.val i j
    simp only [Fin.sum_univ_five, noZero, h1, h2, h3, h4, Pi.zero_apply, mul_zero,
      add_zero] at inv
    exact (mul_eq_zero.mp inv.symm).resolve_left (by norm_num)
  have bound (k : Fin 5) (hk : k ≠ 0) : Module.finrank ℂ (U k) + Module.finrank ℂ (U (-k)) ≤ 4 := by
    apply pair_bound hl _ _ (phase_ne h k) (phase_ne h (-k))
    rw [injections_sum, opposite h hk]
    norm_num
  have h14 : Module.finrank ℂ (U 1) + Module.finrank ℂ (U 4) ≤ 4 := bound 1 (by decide)
  have h23 : Module.finrank ℂ (U 2) + Module.finrank ℂ (U 3) ≤ 4 := bound 2 (by decide)
  have hn := LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod] at hn
  exact hn.trans (Nat.add_le_add h14 h23)

end FiveRows


/-- The constant-permanent bound for complex matrix spaces stable under cyclic row shifts. -/
theorem finrank_le_eight (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (hlevel : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (hshift : ∀ t ∈ L, ∀ s : Fin 5, (fun p : Fin 5 × Fin 5 => t (p.1 + s, p.2)) ∈ L) :
    Module.finrank ℂ L ≤ 8 :=
  FiveRows.cyclic_bound L hlevel hshift

end PEqualNP.Gct.CyclicFive
