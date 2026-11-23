import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_clb_034

private lemma stable (n : ℕ) (C : Circuit) (hsize : C.size ≤ 1)
    (harity : ∀ g ∈ C.gates, g.inputs.length ≤ 1) :
    ∃ k : ℕ, ∀ l r : List Bool, l.length = n → r.length = n →
      l.getD k false = r.getD k false → C.eval l = C.eval r := by
  rcases C with ⟨gates, o⟩
  cases gates with
  | nil =>
    exact ⟨o, fun _ _ _ _ he => he⟩
  | cons g rest =>
    have hr : rest = [] := by
      simpa [Circuit.size] using hsize
    subst rest
    have hg : g.inputs.length ≤ 1 := harity _ (by simp)
    by_cases ho : o < n
    · refine ⟨o, fun l r hl hr he => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
        List.getD_eq_getElem?_getD, List.getElem?_append, hl, hr, ite_eq_left ho] at he ⊢
      exact he
    · refine ⟨g.inputs.headD 0, fun l r hl hr he => ?_⟩
      have hw : (g.inputs.map fun i => l.getD i false) =
          (g.inputs.map fun i => r.getD i false) := by
        cases hi : g.inputs with
        | nil => rfl
        | cons a t =>
          have ht : t = [] := by simpa [hi] using hg
          subst t
          simpa [hi] using he
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
        List.getD_eq_getElem?_getD, List.getElem?_append, hl, hr, ite_eq_right ho] at hw ⊢
      rw [hw]

end PEqualNP.Outside.L_clb_034

theorem PEqualNP.Outside.L_clb_034 : ∀ (n d : ℕ), 2 ≤ n → ({x : List Bool | x.all id = true} : Language Bool) ∉ PEqualNP.CircuitLowerBounds.SizeDepth {PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} (fun m : ℕ => if m = n then 1 else m + 2) d := by
  intro n d hn hfamily
  obtain ⟨C, hgate, hsize, _, hdec⟩ := hfamily n
  have hs : C.size ≤ 1 := by simpa using hsize
  obtain ⟨k, hk⟩ := PEqualNP.Outside.L_clb_034.stable n C hs (fun g hg => by
    simpa using (hgate g hg).2)
  let yes : List Bool := List.ofFn (fun _ : Fin n => true)
  let no : List Bool := List.ofFn (fun i : Fin n => decide (i.val = k))
  have hy : yes.length = n := by simp [yes]
  have hn' : no.length = n := by simp [no]
  have hread : yes.getD k false = no.getD k false := by
    by_cases h : k < n <;> simp [yes, no, List.getD_eq_getElem?_getD, h]
  have hyes : C.eval yes = true := (hdec yes hy).2 (by
    change yes.all id = true
    simp [yes])
  have hall := (hdec no hn').1 ((hk yes no hy hn' hread).symm.trans hyes)
  change no.all id = true at hall
  have hbit : ∀ i : Fin n, i.val = k := by
    intro i
    have hi : decide (i.val = k) ∈ no := List.mem_ofFn.mpr ⟨i, rfl⟩
    simpa using (List.all_eq_true.mp hall) _ hi
  have hz : 0 = k := hbit ⟨0, by omega⟩
  have ho : 1 = k := hbit ⟨1, by omega⟩
  omega
