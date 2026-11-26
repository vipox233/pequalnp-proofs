import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20616
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev run (gs : List Gate) (x : List Bool) : List Bool := (Circuit.mk gs 0).wires x

private def emit (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

private theorem run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [emit g x]) := rfl

private def expose (n : Nat) (g : Gate) (s : Finset Nat) : Finset Nat :=
  if n ∈ s then s.erase n ∪ g.inputs.toFinset else s

def frontier (n : Nat) (gs : List Gate) (s : Finset Nat) : Finset Nat :=
  match gs with
  | [] => s
  | g :: gs => expose n g (frontier (n + 1) gs s)

private theorem expose_card (n : Nat) (g : Gate) (s : Finset Nat) (hg : g.inputs.length ≤ 2) :
    (expose n g s).card ≤ s.card + 1 := by
  unfold expose
  split
  next hn =>
    have h := Finset.card_union_le (s.erase n) g.inputs.toFinset
    have h₁ := Finset.card_erase_of_mem hn
    have h₂ := List.toFinset_card_le g.inputs
    have h₃ := Finset.card_pos.mpr ⟨n, hn⟩
    omega
  next => omega

theorem frontier_card (n : Nat) (gs : List Gate) (s : Finset Nat)
    (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (frontier n gs s).card ≤ s.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [frontier]
  | cons g gs ih =>
    have hh := ih (n + 1) (fun g' h => hgs g' (List.mem_cons_of_mem _ h))
    have he := expose_card n g (frontier (n + 1) gs s) (hgs g (List.mem_cons_self))
    simp only [frontier, List.length_cons]
    omega

private theorem getD_snoc_of_ne (x : List Bool) (v : Bool) {i : Nat} (hi : i ≠ x.length) :
    (x ++ [v]).getD i false = x.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  next => rfl
  next hh =>
    have hlarge : x.length < i := by omega
    have hs : 1 ≤ i - x.length := by omega
    rw [List.getElem?_eq_none (by simpa using hs), List.getElem?_eq_none (by omega)]

open PEqualNP.Represents

private theorem emit_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or) (x y : List Bool)
    (h : ∀ j ∈ g.inputs, x.getD j false = true → y.getD j false = true) :
    emit g x = true → emit g y = true := by
  rcases hg with ho | ho <;>
    simp only [emit, ho, GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map, id_eq]
  · intro hx t ht
    obtain ⟨i,hi,rfl⟩ := ht
    exact h i hi (hx _ ⟨i,hi,rfl⟩)
  · rintro ⟨t,⟨i,hi,rfl⟩,ht⟩
    exact ⟨_,⟨i,hi,rfl⟩,h i hi ht⟩

private theorem expose_mono (n : Nat) (g : Gate) (s : Finset Nat) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n) (hg : g.op = .and ∨ g.op = .or)
    (h : ∀ i ∈ expose n g s, x.getD i false = true → y.getD i false = true) :
    ∀ i ∈ s, (x ++ [emit g x]).getD i false = true → (y ++ [emit g y]).getD i false = true := by
  intro i hi
  by_cases hin : i = n
  · subst i
    rw [show (x ++ [emit g x]).getD n false = emit g x by simp [← hx],
      show (y ++ [emit g y]).getD n false = emit g y by simp [← hy]]
    exact emit_mono g hg x y (fun j hj => h j (by simp [expose, hi, hj]))
  · rw [getD_snoc_of_ne x _ (by omega), getD_snoc_of_ne y _ (by omega)]
    apply h
    by_cases hn : n ∈ s <;> simp [expose, hn, hi, hin]

private theorem frontier_mono (n : Nat) (gs : List Gate) (s : Finset Nat) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h : ∀ i ∈ frontier n gs s, x.getD i false = true → y.getD i false = true) :
    ∀ i ∈ s, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing n x y with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih (n+1) (x ++ [emit g x]) (y ++ [emit g y]) (by simp [hx]) (by simp [hy])
      (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    exact expose_mono n g (frontier (n+1) gs s) x y hx hy (hm _ (List.mem_cons_self)) h

private def graph (u v : Fin 5) : Bool := (15153184 : Nat).testBit (5 * u.val + v.val)

private def examples (q : Fin 8) : Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
  ([(1,0,0,0),(2,1,0,1),(3,1,0,1),(4,1,0,1),
    (1,0,1,4),(2,1,2,4),(2,2,2,4),(2,3,2,4)] :
    List (Fin 5 × Fin 5 × Fin 5 × Fin 5)).getD q.val (0,0,0,0)

private theorem sample_ok : ∀ q : Fin 8,
    let (u,v,u',v') := examples q
    graph u v = true ∧ graph u' v' = false ∧
    ∀ i : Fin 10, (oneEach u v).getD i.val false = true →
      (oneEach u' v').getD i.val false = true ∨ i.val = q.val + 1 := by
  decide +kernel

private theorem lower (C : Circuit) (mono : Monotone2 C) (rep : Represents graph C) :
    7 ≤ C.size := by
  let s := frontier 10 C.gates {C.output}
  have member (q : Fin 8) : q.val + 1 ∈ s := by
    obtain ⟨u,v,u',v',hh⟩ : ∃ u v u' v', examples q = (u,v,u',v') := by
      rcases h : examples q with ⟨u,v,u',v'⟩
      exact ⟨u,v,u',v',rfl⟩
    have cert := sample_ok q
    rw [hh] at cert
    obtain ⟨pos,neg,tests⟩ := cert
    by_contra hnot
    have hx : (oneEach u v).length = 10 := by simp [oneEach]
    have hy : (oneEach u' v').length = 10 := by simp [oneEach]
    have ht : ∀ i ∈ s, (oneEach u v).getD i false = true →
        (oneEach u' v').getD i false = true := by
      intro i hi yes
      by_cases hlt : i < 10
      · rcases tests ⟨i,hlt⟩ yes with good | bad
        · exact good
        · exact False.elim (hnot (bad ▸ hi))
      · rw [List.getD_eq_default _ _ (by omega)] at yes
        contradiction
    have hv : C.eval (oneEach u v) = true := (rep u v).trans pos
    have hn : C.eval (oneEach u' v') = false := (rep u' v').trans neg
    have hout := frontier_mono 10 C.gates {C.output} _ _ hx hy
      (fun g hg => by simpa using (mono g hg).1) ht C.output (by simp) hv
    change C.eval (oneEach u' v') = true at hout
    rw [hn] at hout
    contradiction
  have hc : (Finset.univ : Finset (Fin 8)).card ≤ s.card :=
    Finset.card_le_card_of_injOn (fun q => q.val+1) (fun q _ => member q)
      (fun q _ r _ e => Fin.ext (Nat.add_right_cancel e))
  have hs := frontier_card 10 C.gates {C.output} (fun g hg => (mono g hg).2)
  change s.card ≤ ({C.output} : Finset Nat).card + C.size at hs
  simp at hc hs
  omega

end PEqualNP.Outside.L_meta_20616

theorem PEqualNP.Outside.L_meta_20616 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15153184 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15153184 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  constructor
  · refine ⟨⟨[⟨.and,[1,5]⟩,⟨.or,[2,3]⟩,⟨.or,[11,4]⟩,⟨.or,[6,7]⟩,
        ⟨.or,[13,8]⟩,⟨.and,[12,14]⟩,⟨.or,[10,15]⟩],16⟩,
      ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · decide +kernel
  · rintro ⟨C,mono,size,rep⟩
    have h := PEqualNP.Outside.L_meta_20616.lower C mono rep
    omega
