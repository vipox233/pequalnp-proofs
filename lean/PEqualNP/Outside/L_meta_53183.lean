import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.FiniteGateBank

namespace PEqualNP.Outside.L_meta_53183_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.CoverCircuit
  (run wires_eq run_append run_nil run_singleton run_prefix run_length getD_run
   getD_snoc_length eval_and2 eval_or2)

open Classical

private def invF {m : Nat} (f : Fin m → Bool) : Fin m → Bool := fun t => !(f t)

private def pairF {m : Nat} (f : Fin m → Bool) : Finset (Fin m → Bool) := {f, invF f}

private lemma invF_invF {m : Nat} (f : Fin m → Bool) : invF (invF f) = f := by
  funext t; simp [invF]

private lemma pairF_invF {m : Nat} (f : Fin m → Bool) : pairF (invF f) = pairF f := by
  ext x
  simp only [pairF, invF_invF, Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma pairF_eq_iff {m : Nat} {f g : Fin m → Bool} :
    pairF f = pairF g ↔ g = f ∨ g = invF f := by
  constructor
  · intro h
    have hg : g ∈ pairF f := by rw [h]; simp [pairF]
    simpa [pairF] using hg
  · rintro (rfl | rfl)
    · rfl
    · exact (pairF_invF f).symm

private lemma run_gate_eval {n : Nat} (C : Circuit) (hR : ReadsBack n C)
    (w0 : List Bool) (hw : w0.length = n) (i : Fin C.size) :
    (C.wires w0).getD (n + i.val) false =
      (C.gates.get i).op.eval
        ((C.gates.get i).inputs.map fun k => (C.wires w0).getD k false) := by
  have hi : i.val < C.gates.length := i.isLt
  let g := C.gates.get i
  have hsplit : C.gates = C.gates.take i.val ++ [g] ++ C.gates.drop (i.val + 1) := by
    have h1 := List.take_append_drop i.val C.gates
    have h2 : C.gates.drop i.val = g :: C.gates.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; rfl
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  have hlen1 : (run (C.gates.take i.val) w0).length = n + i.val := by
    rw [run_length, hw, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hlen2 : (run (C.gates.take i.val ++ [g]) w0).length = n + i.val + 1 := by
    rw [run_append, run_singleton, List.length_append, hlen1]; rfl
  have hget : (C.wires w0).getD (n + i.val) false =
      g.op.eval (g.inputs.map fun k => (run (C.gates.take i.val) w0).getD k false) := by
    change (run C.gates w0).getD (n + i.val) false = _
    conv_lhs => rw [hsplit, run_append]
    rw [getD_run _ _ _ (by rw [hlen2]; omega)]
    rw [run_append, run_singleton, ← hlen1, getD_snoc_length]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hkl : k < n + i.val := by
    have hr := hR i.val hi k
    have hga : gateAt C i.val = g := by
      simp [gateAt, g, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    rw [hga] at hr
    exact hr hk
  change (run (C.gates.take i.val) w0).getD k false = (run C.gates w0).getD k false
  conv_rhs => rw [hsplit, List.append_assoc, run_append]
  exact (getD_run _ _ _ (by rw [hlen1]; exact hkl)).symm

private lemma notCount_eq_card (C : Circuit) :
    PEqualNP.NotBracket.notCount C =
      (Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op = GateOp.not)).card := by
  unfold PEqualNP.NotBracket.notCount Circuit.size
  generalize C.gates = gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.filter_cons]
    have hsplit : (Finset.univ.filter (fun i : Fin (g :: gs).length => ((g :: gs).get i).op = GateOp.not)).card =
        (if g.op = GateOp.not then 1 else 0) +
        (Finset.univ.filter (fun i : Fin gs.length => (gs.get i).op = GateOp.not)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact Fin.sum_univ_succ (fun i : Fin (g :: gs).length => if ((g :: gs).get i).op = GateOp.not then 1 else 0)
    rw [hsplit, ← ih]
    by_cases h : g.op = GateOp.not
    · simp [h, Nat.add_comm]
    · simp [h]

private lemma feeSum_snoc {m d : Nat} (inputs : Fin m → List Bool)
    (hwidth : ∀ t, (inputs t).length = d + 2)
    (fee : Finset (Fin m → Bool) → Nat) (gs : List Gate) (g : Gate) :
    (Finset.univ : Finset (Fin (gs ++ [g]).length)).sum (fun i =>
      if ((gs ++ [g]).get i).op = .not then
        fee (pairF (fun t => (run (gs ++ [g]) (inputs t)).getD (d + 2 + i.val) false))
      else 0) =
    (Finset.univ : Finset (Fin gs.length)).sum (fun i =>
      if (gs.get i).op = .not then
        fee (pairF (fun t => (run gs (inputs t)).getD (d + 2 + i.val) false))
      else 0) +
    if g.op = .not then
      fee (pairF (fun t => (run (gs ++ [g]) (inputs t)).getD (d + 2 + gs.length) false))
    else 0 := by
  let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length :=
    finCongr (by simp)
  rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < gs.length := i.isLt
    have hgate : (gs ++ [g]).get (e i.castSucc) = gs.get i := by
      simp [e, List.get_eq_getElem, List.getElem_append_left hi]
    have hwire : (fun t => (run (gs ++ [g]) (inputs t)).getD (d + 2 + (e i.castSucc).val) false) =
        (fun t => (run gs (inputs t)).getD (d + 2 + i.val) false) := by
      funext t
      have hv : (e i.castSucc).val = i.val := rfl
      rw [hv, run_append]
      exact getD_run _ _ _ (by rw [run_length, hwidth]; omega)
    rw [hgate, hwire]
  · have hgate : (gs ++ [g]).get (e (Fin.last gs.length)) = g := by
      simp [e, List.get_eq_getElem]
    have hv : (e (Fin.last gs.length)).val = gs.length := rfl
    rw [hgate, hv]

private lemma mem_A_false {m d : Nat} (X : Fin m → Fin d → Bool) :
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (fun _ : Fin m => false) ∈ A := by
  intro inputs A
  refine Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr (by omega), ?_⟩
  funext t
  simp [inputs, List.getD_eq_getElem?_getD]

private lemma mem_A_true {m d : Nat} (X : Fin m → Fin d → Bool) :
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (fun _ : Fin m => true) ∈ A := by
  intro inputs A
  refine Finset.mem_image.mpr ⟨d + 1, Finset.mem_range.mpr (by omega), ?_⟩
  funext t
  simp [inputs, List.getD_eq_getElem?_getD]

private theorem fwd (m d a p b g W : Nat) (X : Fin m → Fin d → Bool) (T : Fin a → Fin m → Bool)
    (fee : Finset (Fin m → Bool) → Nat) :
    let F := Fin m → Bool
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (∃ (C : Circuit) (tap : Fin a → Nat),
      let wire := fun (j : Nat) t => (C.wires (inputs t)).getD j false
      let neg := PEqualNP.NotBracket.notCount C
      FanInTwo C ∧ ReadsBack (d + 2) C ∧
      C.output < d + 2 + C.size ∧ (∀ j, tap j < d + 2 + C.size ∧ wire (tap j) = T j) ∧
      C.size - neg ≤ p ∧ neg ≤ b ∧ C.size ≤ g ∧
      (Finset.univ : Finset (Fin C.size)).sum (fun i =>
        if (C.gates.get i).op = .not then fee (pairF (wire (d + 2 + i.val))) else 0) ≤ W) →
    ∃ (D : Finset F) (H : Finset (Finset F)),
      let N := (D \ A).card
      let eligible := (D.filter (fun f => invF f ∈ D ∧ invF f ≠ f ∧ ¬ (f ∈ A ∧ invF f ∈ A))).image pairF
      A ⊆ D ∧ (∀ j, T j ∈ D) ∧ H ⊆ eligible ∧
      N - H.card ≤ p ∧ H.card ≤ b ∧ N ≤ g ∧ H.sum fee ≤ W ∧
      ∀ U : Finset F, A ⊆ U → U ⊂ D →
        (∀ x ∈ U, ∀ y ∈ U,
          ((fun t => x t && y t) ∈ D → (fun t => x t && y t) ∈ U) ∧
          ((fun t => x t || y t) ∈ D → (fun t => x t || y t) ∈ U)) →
        ∃ f ∈ U, invF f ∉ U ∧ pairF f ∈ H := by
  intro F inputs A
  rintro ⟨C, tap, hFan, hRB, _hOut, hTap, hP, hB, hG, hW⟩
  let wire : Nat → F := fun j t => (C.wires (inputs t)).getD j false
  have hwidth : ∀ t, (inputs t).length = d + 2 := fun t => by simp [inputs]
  have hwireBase : ∀ j < d + 2, wire j = fun t => (inputs t).getD j false := by
    intro j hj
    funext t
    exact getD_run _ _ _ (by rw [hwidth]; exact hj)
  let D : Finset F := (Finset.range (d + 2 + C.size)).image wire
  have hAD : A ⊆ D := by
    intro f hf
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hf
    have hj' : j < d + 2 := Finset.mem_range.mp hj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), hwireBase j hj'⟩
  have hTD : ∀ j, T j ∈ D := fun j =>
    Finset.mem_image.mpr ⟨tap j, Finset.mem_range.mpr (hTap j).1, (hTap j).2⟩
  let K : Finset (Fin C.size) :=
    Finset.univ.filter (fun i => ∀ k < d + 2 + i.val, wire k ≠ wire (d + 2 + i.val))
  let K_not : Finset (Fin C.size) := K.filter (fun i => (C.gates.get i).op = .not)
  let K_bin : Finset (Fin C.size) := K.filter (fun i => (C.gates.get i).op ≠ .not)
  let H : Finset (Finset F) := K_not.image (fun i => pairF (wire (d + 2 + i.val)))
  have hK_notA : ∀ i ∈ K, wire (d + 2 + i.val) ∉ A := by
    intro i hi hmem
    obtain ⟨k, hk, hkf⟩ := Finset.mem_image.mp hmem
    have hk' : k < d + 2 := Finset.mem_range.mp hk
    exact (Finset.mem_filter.mp hi).2 k (by omega) ((hwireBase k hk').trans hkf)
  have hK_card : K.card = (D \ A).card := by
    refine Finset.card_bij (fun i _ => wire (d + 2 + i.val)) ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨d + 2 + i.val, Finset.mem_range.mpr (by omega), rfl⟩,
         hK_notA i hi⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact (Finset.mem_filter.mp hi₂).2 (d + 2 + i₁.val) (by omega) heq
      · exact (Finset.mem_filter.mp hi₁).2 (d + 2 + i₂.val) (by omega) heq.symm
    · intro f hf
      obtain ⟨hfD, hfA⟩ := Finset.mem_sdiff.mp hf
      have hex : ∃ j, j < d + 2 + C.size ∧ wire j = f := by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hfD
        exact ⟨j, Finset.mem_range.mp hj, rfl⟩
      let j0 := Nat.find hex
      have hj0 : j0 < d + 2 + C.size ∧ wire j0 = f := Nat.find_spec hex
      have hj0_ge : d + 2 ≤ j0 := by
        by_contra hlt
        push Not at hlt
        apply hfA
        refine Finset.mem_image.mpr ⟨j0, Finset.mem_range.mpr hlt, ?_⟩
        rw [← hwireBase j0 hlt, hj0.2]
      let i0 : Fin C.size := ⟨j0 - (d + 2), by omega⟩
      have hi0_eq : d + 2 + i0.val = j0 := by dsimp [i0]; omega
      refine ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro k hk heq
        rw [hi0_eq, hj0.2] at heq
        have := Nat.find_min hex (show k < j0 by omega)
        exact this ⟨by omega, heq⟩
      · rw [hi0_eq, hj0.2]
  have hnot_mate : ∀ i ∈ K_not, ∃ k < d + 2 + i.val, wire k = invF (wire (d + 2 + i.val)) := by
    intro i hi
    have hiK : i ∈ K := (Finset.mem_filter.mp hi).1
    have hiOp : (C.gates.get i).op = .not := (Finset.mem_filter.mp hi).2
    have hev : ∀ t, wire (d + 2 + i.val) t =
        !(((C.gates.get i).inputs.map fun k => wire k t).headD false) := by
      intro t
      have h1 := run_gate_eval C hRB (inputs t) (hwidth t) i
      simpa [wire, hiOp, GateOp.eval] using h1
    cases hinp : (C.gates.get i).inputs with
    | nil =>
      have htrue : wire (d + 2 + i.val) = fun _ => true := by
        funext t; simpa [hinp] using hev t
      exact False.elim (hK_notA i hiK (htrue ▸ mem_A_true X))
    | cons k ks =>
      have hkl : k < d + 2 + i.val := by
        have hr := hRB i.val i.isLt k
        have hga : gateAt C i.val = C.gates.get i := by
          simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]; rfl
        rw [hga, hinp] at hr
        exact hr (by simp)
      refine ⟨k, hkl, ?_⟩
      funext t
      have h1 := hev t
      simp [hinp] at h1
      simp [invF, h1]
  have hH_inj : Set.InjOn (fun i : Fin C.size => pairF (wire (d + 2 + i.val))) (K_not : Set (Fin C.size)) := by
    intro i₁ hi₁ i₂ hi₂ heq
    by_contra hne
    have hi₁K : i₁ ∈ K := (Finset.mem_filter.mp hi₁).1
    have hi₂K : i₂ ∈ K := (Finset.mem_filter.mp hi₂).1
    have hneq : wire (d + 2 + i₁.val) ≠ wire (d + 2 + i₂.val) := by
      intro hsame
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact (Finset.mem_filter.mp hi₂K).2 (d + 2 + i₁.val) (by omega) hsame
      · exact (Finset.mem_filter.mp hi₁K).2 (d + 2 + i₂.val) (by omega) hsame.symm
    have hinv : wire (d + 2 + i₂.val) = invF (wire (d + 2 + i₁.val)) :=
      (pairF_eq_iff.mp heq).resolve_left hneq.symm
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · obtain ⟨k, hk, hkw⟩ := hnot_mate i₁ hi₁
      exact (Finset.mem_filter.mp hi₂K).2 k (by omega) (hkw.trans hinv.symm)
    · obtain ⟨k, hk, hkw⟩ := hnot_mate i₂ hi₂
      have hinv2 : wire (d + 2 + i₁.val) = invF (wire (d + 2 + i₂.val)) := by
        rw [hinv, invF_invF]
      exact (Finset.mem_filter.mp hi₁K).2 k (by omega) (hkw.trans hinv2.symm)
  have hH_card : H.card = K_not.card := Finset.card_image_of_injOn hH_inj
  have hH_elig : H ⊆ (D.filter (fun f => invF f ∈ D ∧ invF f ≠ f ∧ ¬ (f ∈ A ∧ invF f ∈ A))).image pairF := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    have hiK : i ∈ K := (Finset.mem_filter.mp hi).1
    obtain ⟨k, hk, hkw⟩ := hnot_mate i hi
    refine Finset.mem_image.mpr ⟨wire (d + 2 + i.val), Finset.mem_filter.mpr ?_, rfl⟩
    refine ⟨Finset.mem_image.mpr ⟨d + 2 + i.val, Finset.mem_range.mpr (by omega), rfl⟩, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hkw⟩
    · intro heq
      exact (Finset.mem_filter.mp hiK).2 k hk (hkw.trans heq)
    · rintro ⟨hfA, _⟩
      exact hK_notA i hiK hfA
  have hneg_eq := notCount_eq_card C
  have hKnot_le : K_not.card ≤ PEqualNP.NotBracket.notCount C := by
    rw [hneg_eq]
    exact Finset.card_le_card (fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  have hKbin_le : K_bin.card ≤ C.size - PEqualNP.NotBracket.notCount C := by
    have htot : (Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op ≠ .not)).card +
        (Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op = .not)).card = C.size := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin C.size))) (p := fun i => (C.gates.get i).op = .not)
      simpa [Nat.add_comm] using this
    have hsub : K_bin.card ≤ (Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op ≠ .not)).card :=
      Finset.card_le_card (fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
    omega
  have hK_split : K_not.card + K_bin.card = K.card :=
    Finset.card_filter_add_card_filter_not (s := K) (p := fun i => (C.gates.get i).op = .not)
  have hN_le_g : (D \ A).card ≤ g := by
    rw [← hK_card]
    have h1 : K.card ≤ (Finset.univ : Finset (Fin C.size)).card := Finset.card_le_card (Finset.subset_univ _)
    simp at h1
    omega
  have hH_sum : H.sum fee ≤ W := by
    rw [Finset.sum_image hH_inj]
    refine le_trans ?_ hW
    calc K_not.sum (fun i => fee (pairF (wire (d + 2 + i.val))))
        = K_not.sum (fun i => if (C.gates.get i).op = .not then fee (pairF (wire (d + 2 + i.val))) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ite_eq_left (Finset.mem_filter.mp hi).2]
      _ ≤ Finset.univ.sum (fun i => if (C.gates.get i).op = .not then fee (pairF (wire (d + 2 + i.val))) else 0) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  refine ⟨D, H, hAD, hTD, hH_elig, by omega, by omega, hN_le_g, hH_sum, ?_⟩
  intro U hAU hUD hUcl
  obtain ⟨f_miss, hf_missD, hf_missU⟩ := Finset.exists_of_ssubset hUD
  have hex : ∃ j, j < d + 2 + C.size ∧ wire j ∉ U := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hf_missD
    exact ⟨j, Finset.mem_range.mp hj, hf_missU⟩
  let j0 := Nat.find hex
  have hj0 : j0 < d + 2 + C.size ∧ wire j0 ∉ U := Nat.find_spec hex
  have hbefore : ∀ k < j0, wire k ∈ U := by
    intro k hk
    by_contra hnot
    exact Nat.find_min hex hk ⟨by omega, hnot⟩
  have hj0_ge : d + 2 ≤ j0 := by
    by_contra hlt
    push Not at hlt
    apply hj0.2
    exact hAU (Finset.mem_image.mpr ⟨j0, Finset.mem_range.mpr hlt, (hwireBase j0 hlt).symm⟩)
  let i0 : Fin C.size := ⟨j0 - (d + 2), by omega⟩
  have hi0_eq : d + 2 + i0.val = j0 := by dsimp [i0]; omega
  have hi0K : i0 ∈ K := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk heq => ?_⟩
    rw [hi0_eq] at hk heq
    exact hj0.2 (heq ▸ hbefore k hk)
  have hgate_mem : C.gates.get i0 ∈ C.gates := List.get_mem C.gates i0
  obtain ⟨hop, hlen⟩ := hFan (C.gates.get i0) hgate_mem
  have hread : ∀ k ∈ (C.gates.get i0).inputs, k < j0 := by
    intro k hk
    have hr := hRB i0.val i0.isLt k
    have hga : gateAt C i0.val = C.gates.get i0 := by
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i0.isLt]; rfl
    rw [hga] at hr
    have := hr hk
    omega
  have hev : ∀ t, wire j0 t =
      (C.gates.get i0).op.eval ((C.gates.get i0).inputs.map fun k => wire k t) := by
    intro t
    have h1 := run_gate_eval C hRB (inputs t) (hwidth t) i0
    simpa [wire, hi0_eq] using h1
  have hj0D : wire j0 ∈ D := Finset.mem_image.mpr ⟨j0, Finset.mem_range.mpr hj0.1, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hand | hor | hnot
  · cases hinp : (C.gates.get i0).inputs with
    | nil =>
      have : wire j0 = fun _ => true := by funext t; simpa [hand, hinp, GateOp.eval] using hev t
      exact False.elim (hj0.2 (this ▸ hAU (mem_A_true X)))
    | cons k1 rest =>
      cases rest with
      | nil =>
        have hk1 : wire k1 ∈ U := hbefore k1 (hread k1 (by simp [hinp]))
        have : wire j0 = wire k1 := by funext t; simpa [hand, hinp, GateOp.eval] using hev t
        exact False.elim (hj0.2 (this ▸ hk1))
      | cons k2 rest2 =>
        cases rest2 with
        | nil =>
          have hk1 : wire k1 ∈ U := hbefore k1 (hread k1 (by simp [hinp]))
          have hk2 : wire k2 ∈ U := hbefore k2 (hread k2 (by simp [hinp]))
          have hwf : wire j0 = fun t => wire k1 t && wire k2 t := by
            funext t; simpa [hand, hinp, GateOp.eval] using hev t
          exact False.elim (hj0.2 (hwf ▸ (hUcl _ hk1 _ hk2).1 (hwf ▸ hj0D)))
        | cons _ _ =>
          rw [hinp] at hlen; simp at hlen
  · cases hinp : (C.gates.get i0).inputs with
    | nil =>
      have : wire j0 = fun _ => false := by funext t; simpa [hor, hinp, GateOp.eval] using hev t
      exact False.elim (hj0.2 (this ▸ hAU (mem_A_false X)))
    | cons k1 rest =>
      cases rest with
      | nil =>
        have hk1 : wire k1 ∈ U := hbefore k1 (hread k1 (by simp [hinp]))
        have : wire j0 = wire k1 := by funext t; simpa [hor, hinp, GateOp.eval] using hev t
        exact False.elim (hj0.2 (this ▸ hk1))
      | cons k2 rest2 =>
        cases rest2 with
        | nil =>
          have hk1 : wire k1 ∈ U := hbefore k1 (hread k1 (by simp [hinp]))
          have hk2 : wire k2 ∈ U := hbefore k2 (hread k2 (by simp [hinp]))
          have hwf : wire j0 = fun t => wire k1 t || wire k2 t := by
            funext t; simpa [hor, hinp, GateOp.eval] using hev t
          exact False.elim (hj0.2 (hwf ▸ (hUcl _ hk1 _ hk2).2 (hwf ▸ hj0D)))
        | cons _ _ =>
          rw [hinp] at hlen; simp at hlen
  · have hi0Knot : i0 ∈ K_not := Finset.mem_filter.mpr ⟨hi0K, hnot⟩
    obtain ⟨k, hk, hkw⟩ := hnot_mate i0 hi0Knot
    rw [hi0_eq] at hk hkw
    refine ⟨wire k, hbefore k hk, ?_, ?_⟩
    · rw [hkw, invF_invF]; exact hj0.2
    · rw [hkw, pairF_invF, ← hi0_eq]
      exact Finset.mem_image.mpr ⟨i0, hi0Knot, rfl⟩

private theorem bwd (m d a p b g W : Nat) (X : Fin m → Fin d → Bool) (T : Fin a → Fin m → Bool)
    (fee : Finset (Fin m → Bool) → Nat) :
    let F := Fin m → Bool
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (∃ (D : Finset F) (H : Finset (Finset F)),
      let N := (D \ A).card
      let eligible := (D.filter (fun f => invF f ∈ D ∧ invF f ≠ f ∧ ¬ (f ∈ A ∧ invF f ∈ A))).image pairF
      A ⊆ D ∧ (∀ j, T j ∈ D) ∧ H ⊆ eligible ∧
      N - H.card ≤ p ∧ H.card ≤ b ∧ N ≤ g ∧ H.sum fee ≤ W ∧
      ∀ U : Finset F, A ⊆ U → U ⊂ D →
        (∀ x ∈ U, ∀ y ∈ U,
          ((fun t => x t && y t) ∈ D → (fun t => x t && y t) ∈ U) ∧
          ((fun t => x t || y t) ∈ D → (fun t => x t || y t) ∈ U)) →
        ∃ f ∈ U, invF f ∉ U ∧ pairF f ∈ H) →
    ∃ (C : Circuit) (tap : Fin a → Nat),
      let wire := fun (j : Nat) t => (C.wires (inputs t)).getD j false
      let neg := PEqualNP.NotBracket.notCount C
      FanInTwo C ∧ ReadsBack (d + 2) C ∧
      C.output < d + 2 + C.size ∧ (∀ j, tap j < d + 2 + C.size ∧ wire (tap j) = T j) ∧
      C.size - neg ≤ p ∧ neg ≤ b ∧ C.size ≤ g ∧
      (Finset.univ : Finset (Fin C.size)).sum (fun i =>
        if (C.gates.get i).op = .not then fee (pairF (wire (d + 2 + i.val))) else 0) ≤ W := by
  intro F inputs A
  rintro ⟨D, H, hAD, hTD, hHelig, hP, hB, hG, hW, hCut⟩
  have hwidth : ∀ t, (inputs t).length = d + 2 := fun t => by simp [inputs]
  have hHelig_spec : ∀ P ∈ H, ∃ f ∈ D, invF f ∈ D ∧ invF f ≠ f ∧ ¬ (f ∈ A ∧ invF f ∈ A) ∧ pairF f = P := by
    intro P hP
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (hHelig hP)
    obtain ⟨hfD, hinvD, hne, hnotA⟩ := Finset.mem_filter.mp hf
    exact ⟨f, hfD, hinvD, hne, hnotA, rfl⟩
  let Hdone : Finset F → Finset (Finset F) := fun U => H.filter (fun P => P ⊆ U)
  have hHdone_A : Hdone A = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro P hP hsub
    obtain ⟨f, _, _, _, hnotA, rfl⟩ := hHelig_spec P hP
    exact hnotA ⟨hsub (by simp [pairF]), hsub (by simp [pairF])⟩
  have hHdone_D : Hdone D = H := by
    rw [Finset.filter_eq_self]
    intro P hP
    obtain ⟨f, hfD, hinvD, _, _, rfl⟩ := hHelig_spec P hP
    intro x hx
    simp only [pairF, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hstep : ∀ (r : Nat) (U : Finset F) (gs : List Gate),
      A ⊆ U → U ⊆ D → (D \ U).card = r →
      gs.length = (U \ A).card →
      FanInTwo ⟨gs, 0⟩ → ReadsBack (d + 2) ⟨gs, 0⟩ →
      (∀ f ∈ U, ∃ idx < d + 2 + gs.length, ∀ t, (run gs (inputs t)).getD idx false = f t) →
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = (Hdone U).card →
      (Finset.univ : Finset (Fin gs.length)).sum (fun i =>
        if (gs.get i).op = .not then
          fee (pairF (fun t => (run gs (inputs t)).getD (d + 2 + i.val) false))
        else 0) = (Hdone U).sum fee →
      ∃ gs' : List Gate,
        gs'.length = (D \ A).card ∧
        FanInTwo ⟨gs', 0⟩ ∧ ReadsBack (d + 2) ⟨gs', 0⟩ ∧
        (∀ f ∈ D, ∃ idx < d + 2 + gs'.length, ∀ t, (run gs' (inputs t)).getD idx false = f t) ∧
        PEqualNP.NotBracket.notCount ⟨gs', 0⟩ = H.card ∧
        (Finset.univ : Finset (Fin gs'.length)).sum (fun i =>
          if (gs'.get i).op = .not then
            fee (pairF (fun t => (run gs' (inputs t)).getD (d + 2 + i.val) false))
          else 0) = H.sum fee := by
    intro r
    induction r with
    | zero =>
      intro U gs hAU hUD hrem hlen hFan hRB hhas hneg hfee
      have hDU : D \ U = ∅ := Finset.card_eq_zero.mp hrem
      have hEq : U = D := Finset.Subset.antisymm hUD (Finset.sdiff_eq_empty_iff_subset.mp hDU)
      subst hEq
      exact ⟨gs, hlen, hFan, hRB, hhas, hneg.trans (congrArg Finset.card hHdone_D),
        hfee.trans (congrArg (fun S => S.sum fee) hHdone_D)⟩
    | succ r ih =>
      intro U gs hAU hUD hrem hlen hFan hRB hhas hneg hfee
      have hUD_strict : U ⊂ D := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hUD, fun heq => ?_⟩
        rw [heq, Finset.sdiff_self, Finset.card_empty] at hrem
        omega

      have h_advance : ∀ (z : F) (hzD : z ∈ D) (hzU : z ∉ U) (gNew : Gate),
          gNew.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
          gNew.inputs.length ≤ 2 →
          (∀ k ∈ gNew.inputs, k < d + 2 + gs.length) →
          (∀ t, gNew.op.eval (gNew.inputs.map fun k => (run gs (inputs t)).getD k false) = z t) →
          (gNew.op = .not ↔ (pairF z ∈ H ∧ invF z ∈ U)) →
          ∃ gs' : List Gate,
            gs'.length = (D \ A).card ∧
            FanInTwo ⟨gs', 0⟩ ∧ ReadsBack (d + 2) ⟨gs', 0⟩ ∧
            (∀ f ∈ D, ∃ idx < d + 2 + gs'.length, ∀ t, (run gs' (inputs t)).getD idx false = f t) ∧
            PEqualNP.NotBracket.notCount ⟨gs', 0⟩ = H.card ∧
            (Finset.univ : Finset (Fin gs'.length)).sum (fun i =>
              if (gs'.get i).op = .not then
                fee (pairF (fun t => (run gs' (inputs t)).getD (d + 2 + i.val) false))
              else 0) = H.sum fee := by
        intro z hzD hzU gNew hop hgl hgk hgeval hnot_iff
        let U' := insert z U
        let gs1 := gs ++ [gNew]
        have hzA : z ∉ A := fun h => hzU (hAU h)
        have hAU' : A ⊆ U' := hAU.trans (Finset.subset_insert _ _)
        have hUD' : U' ⊆ D := Finset.insert_subset hzD hUD
        have hrem' : (D \ U').card = r := by
          have h1 : D \ U' = (D \ U).erase z := by
            ext x; simp [U', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
          rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hzD, hzU⟩), hrem]
          omega
        have hlen' : gs1.length = (U' \ A).card := by
          have h1 : U' \ A = insert z (U \ A) := by
            ext x
            simp only [U', Finset.mem_sdiff, Finset.mem_insert]
            by_cases hxz : x = z
            · subst hxz; simp [hzA]
            · simp [hxz]
          rw [h1, Finset.card_insert_of_notMem (by simp [hzU]), ← hlen]
          simp [gs1]
        have hFan' : FanInTwo ⟨gs1, 0⟩ := by
          intro v hv
          rcases List.mem_append.mp hv with old | last
          · exact hFan v old
          · rw [List.mem_singleton.mp last]; exact ⟨hop, hgl⟩
        have hRB' : ReadsBack (d + 2) ⟨gs1, 0⟩ := by
          intro j hj k hk
          have hga : gateAt ⟨gs1, 0⟩ j = gs1[j] := by
            simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          rw [hga] at hk
          by_cases hjlt : j < gs.length
          · have h1 : gs1[j] = gs[j] := List.getElem_append_left hjlt
            rw [h1] at hk
            have hr := hRB j hjlt k
            have hga0 : gateAt ⟨gs, 0⟩ j = gs[j] := by
              simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
            rw [hga0] at hr
            exact hr hk
          · have hjeq : j = gs.length := by simp [gs1] at hj; omega
            subst hjeq
            have h1 : gs1[gs.length] = gNew := by simp [gs1]
            rw [h1] at hk
            exact hgk k hk
        have hlast_wire : ∀ t, (run gs1 (inputs t)).getD (d + 2 + gs.length) false = z t := by
          intro t
          have hlen_run : (run gs (inputs t)).length = d + 2 + gs.length := by
            rw [run_length, hwidth]
          rw [show gs1 = gs ++ [gNew] from rfl, run_append, run_singleton, ← hlen_run,
            getD_snoc_length]
          exact hgeval t
        have hhas' : ∀ f ∈ U', ∃ idx < d + 2 + gs1.length,
            ∀ t, (run gs1 (inputs t)).getD idx false = f t := by
          intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hfU
          · exact ⟨d + 2 + gs.length, by simp [gs1], hlast_wire⟩
          · obtain ⟨idx, hidx, hread⟩ := hhas f hfU
            refine ⟨idx, by simp [gs1]; omega, fun t => ?_⟩
            rw [show gs1 = gs ++ [gNew] from rfl, run_append,
              getD_run _ _ _ (by rw [run_length, hwidth]; exact hidx)]
            exact hread t
        have hHdone_step : Hdone U' =
            if pairF z ∈ H ∧ invF z ∈ U then insert (pairF z) (Hdone U) else Hdone U := by
          by_cases hcond : pairF z ∈ H ∧ invF z ∈ U
          · rw [ite_eq_left hcond]
            ext P
            simp only [Hdone, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hPH, hPU'⟩
              by_cases hzP : z ∈ P
              · left
                obtain ⟨f, _, _, _, _, rfl⟩ := hHelig_spec P hPH
                have : z = f ∨ z = invF f := by simpa [pairF] using hzP
                exact pairF_eq_iff.mpr this
              · right
                refine ⟨hPH, fun x hx => ?_⟩
                have hx' := hPU' hx
                rcases Finset.mem_insert.mp hx' with hxz | hxU
                · rw [hxz] at hx; exact False.elim (hzP hx)
                · exact hxU
            · rintro (rfl | ⟨hPH, hPU⟩)
              · refine ⟨hcond.1, fun x hx => ?_⟩
                simp only [pairF, Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem hcond.2
              · exact ⟨hPH, hPU.trans (Finset.subset_insert _ _)⟩
          · rw [ite_eq_right hcond]
            ext P
            simp only [Hdone, Finset.mem_filter]
            constructor
            · rintro ⟨hPH, hPU'⟩
              refine ⟨hPH, fun x hx => ?_⟩
              have hx' := hPU' hx
              rcases Finset.mem_insert.mp hx' with hxz | hxU
              · exfalso
                apply hcond
                rw [hxz] at hx
                obtain ⟨f, _, _, hne, _, rfl⟩ := hHelig_spec P hPH
                have hzf : z = f ∨ z = invF f := by simpa [pairF] using hx
                have hpz : pairF z = pairF f := (pairF_eq_iff.mpr hzf).symm
                have hinvz_mem : invF z ∈ pairF f := by rw [← hpz]; simp [pairF]
                have hinvz_ne : invF z ≠ z := by
                  rcases hzf with h1 | h1
                  · rw [h1]; exact hne
                  · rw [h1, invF_invF]; exact hne.symm
                have hinvz_U' := hPU' hinvz_mem
                rcases Finset.mem_insert.mp hinvz_U' with heq | hmem
                · exact False.elim (hinvz_ne heq)
                · exact ⟨hpz ▸ hPH, hmem⟩
              · exact hxU
            · rintro ⟨hPH, hPU⟩
              exact ⟨hPH, hPU.trans (Finset.subset_insert _ _)⟩
        have hnot_mem : pairF z ∉ Hdone U := by
          intro hmem
          have hsub := (Finset.mem_filter.mp hmem).2
          exact hzU (hsub (by simp [pairF]))
        have hneg' : PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ = (Hdone U').card := by
          have hnc : PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ =
              PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + if gNew.op = .not then 1 else 0 := by
            unfold PEqualNP.NotBracket.notCount
            simp only [gs1, List.filter_append, List.length_append]
            by_cases h : gNew.op = .not <;> simp [h]
          rw [hnc, hneg, hHdone_step]
          by_cases hcond : pairF z ∈ H ∧ invF z ∈ U
          · have hgnot : gNew.op = .not := hnot_iff.mpr hcond
            rw [ite_eq_left hgnot, ite_eq_left hcond, Finset.card_insert_of_notMem hnot_mem]
          · have hgnot : gNew.op ≠ .not := fun h => hcond (hnot_iff.mp h)
            rw [ite_eq_right hgnot, ite_eq_right hcond, Nat.add_zero]
        have hfee' : (Finset.univ : Finset (Fin gs1.length)).sum (fun i =>
            if (gs1.get i).op = .not then
              fee (pairF (fun t => (run gs1 (inputs t)).getD (d + 2 + i.val) false))
            else 0) = (Hdone U').sum fee := by
          rw [feeSum_snoc inputs hwidth fee gs gNew, hfee, hHdone_step]
          have hzw : (fun t => (run (gs ++ [gNew]) (inputs t)).getD (d + 2 + gs.length) false) = z := by
            funext t; exact hlast_wire t
          rw [hzw]
          by_cases hcond : pairF z ∈ H ∧ invF z ∈ U
          · have hgnot : gNew.op = .not := hnot_iff.mpr hcond
            rw [ite_eq_left hgnot, ite_eq_left hcond, Finset.sum_insert hnot_mem, Nat.add_comm]
          · have hgnot : gNew.op ≠ .not := fun h => hcond (hnot_iff.mp h)
            rw [ite_eq_right hgnot, ite_eq_right hcond, Nat.add_zero]
        exact ih U' gs1 hAU' hUD' hrem' hlen' hFan' hRB' hhas' hneg' hfee'

      by_cases hbin : ∃ x ∈ U, ∃ y ∈ U,
          ((fun t => x t && y t) ∈ D ∧ (fun t => x t && y t) ∉ U) ∨
          ((fun t => x t || y t) ∈ D ∧ (fun t => x t || y t) ∉ U)
      · obtain ⟨x, hxU, y, hyU, hxy⟩ := hbin
        rcases hxy with ⟨hzD, hzU⟩ | ⟨hzD, hzU⟩
        · let z : F := fun t => x t && y t
          by_cases hcond : pairF z ∈ H ∧ invF z ∈ U
          · obtain ⟨idx, hidx, hread⟩ := hhas (invF z) hcond.2
            refine h_advance z hzD hzU ⟨.not, [idx]⟩ (by simp) (by simp) (by simp [hidx]) ?_ (by simp [hcond])
            intro t
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hread t, invF, Bool.not_not]
          · obtain ⟨ix, hix, hrx⟩ := hhas x hxU
            obtain ⟨iy, hiy, hry⟩ := hhas y hyU
            refine h_advance z hzD hzU ⟨.and, [ix, iy]⟩ (by simp) (by simp) (by simp [hix, hiy]) ?_ (by simp [hcond])
            intro t
            simp only [List.map_cons, List.map_nil, eval_and2, hrx t, hry t, z]
        · let z : F := fun t => x t || y t
          by_cases hcond : pairF z ∈ H ∧ invF z ∈ U
          · obtain ⟨idx, hidx, hread⟩ := hhas (invF z) hcond.2
            refine h_advance z hzD hzU ⟨.not, [idx]⟩ (by simp) (by simp) (by simp [hidx]) ?_ (by simp [hcond])
            intro t
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hread t, invF, Bool.not_not]
          · obtain ⟨ix, hix, hrx⟩ := hhas x hxU
            obtain ⟨iy, hiy, hry⟩ := hhas y hyU
            refine h_advance z hzD hzU ⟨.or, [ix, iy]⟩ (by simp) (by simp) (by simp [hix, hiy]) ?_ (by simp [hcond])
            intro t
            simp only [List.map_cons, List.map_nil, eval_or2, hrx t, hry t, z]
      · have hcl : ∀ x ∈ U, ∀ y ∈ U,
            ((fun t => x t && y t) ∈ D → (fun t => x t && y t) ∈ U) ∧
            ((fun t => x t || y t) ∈ D → (fun t => x t || y t) ∈ U) := by
          intro x hxU y hyU
          constructor <;> intro hmem <;> by_contra hnot
          · exact hbin ⟨x, hxU, y, hyU, Or.inl ⟨hmem, hnot⟩⟩
          · exact hbin ⟨x, hxU, y, hyU, Or.inr ⟨hmem, hnot⟩⟩
        obtain ⟨f, hfU, hinvU, hpairH⟩ := hCut U hAU hUD_strict hcl
        let z : F := invF f
        have hzD : z ∈ D := by
          obtain ⟨h, hhD, hinvD, _, _, hpeq⟩ := hHelig_spec (pairF f) hpairH
          rcases pairF_eq_iff.mp hpeq.symm with rfl | rfl
          · exact hinvD
          · simp [z, hhD]
        have hcond : pairF z ∈ H ∧ invF z ∈ U := by
          simp [z, pairF_invF, invF_invF, hpairH, hfU]
        obtain ⟨idx, hidx, hread⟩ := hhas f hfU
        refine h_advance z hzD hinvU ⟨.not, [idx]⟩ (by simp) (by simp) (by simp [hidx]) ?_ (by simp [hcond])
        intro t
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hread t, z, invF]
  have hhasA : ∀ f ∈ A, ∃ idx < d + 2 + ([] : List Gate).length,
      ∀ t, (run [] (inputs t)).getD idx false = f t := by
    intro f hf
    obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨idx, by simpa using Finset.mem_range.mp hidx, fun _ => rfl⟩
  obtain ⟨gs, hlen, hFan, hRB, hhasD, hneg, hfee⟩ :=
    hstep (D \ A).card A [] (Finset.Subset.refl _) hAD rfl (by simp)
      (by intro v hv; simp at hv) (by intro j hj; simp at hj) hhasA
      (by simp [PEqualNP.NotBracket.notCount, hHdone_A])
      (by simp [hHdone_A])
  let C : Circuit := ⟨gs, 0⟩
  have htap_ex : ∀ j : Fin a, ∃ idx < d + 2 + C.size,
      (fun t => (C.wires (inputs t)).getD idx false) = T j := by
    intro j
    obtain ⟨idx, hidx, hread⟩ := hhasD (T j) (hTD j)
    exact ⟨idx, hidx, funext hread⟩
  let tap : Fin a → Nat := fun j => Classical.choose (htap_ex j)
  refine ⟨C, tap, hFan, hRB, by simp [C], ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Classical.choose_spec (htap_ex j)
  · change gs.length - PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ p
    rw [hlen, hneg]; exact hP
  · change PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b
    rw [hneg]; exact hB
  · change gs.length ≤ g
    rw [hlen]; exact hG
  · change (Finset.univ : Finset (Fin gs.length)).sum (fun i =>
      if (gs.get i).op = .not then
        fee (pairF (fun t => (run gs (inputs t)).getD (d + 2 + i.val) false))
      else 0) ≤ W
    rw [hfee]; exact hW

theorem main (m d a p b g W : Nat) (X : Fin m → Fin d → Bool) (T : Fin a → Fin m → Bool)
    (fee : Finset (Fin m → Bool) → Nat) :
    letI : ∀ q : Prop, Decidable q := Classical.propDecidable
    let F := Fin m → Bool
    let inv := fun (f : F) (t : Fin m) => !(f t)
    let pair := fun f => ({f, inv f} : Finset F)
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
      let wire := fun (j : Nat) t => (C.wires (inputs t)).getD j false
      let neg := PEqualNP.NotBracket.notCount C
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C ∧
      C.output < d + 2 + C.size ∧ (∀ j, tap j < d + 2 + C.size ∧ wire (tap j) = T j) ∧
      C.size - neg ≤ p ∧ neg ≤ b ∧ C.size ≤ g ∧
      (Finset.univ : Finset (Fin C.size)).sum (fun i =>
        if (C.gates.get i).op = .not then fee (pair (wire (d + 2 + i.val))) else 0) ≤ W) ↔
    ∃ (D : Finset F) (H : Finset (Finset F)),
      let N := (D \ A).card
      let eligible := (D.filter (fun f => inv f ∈ D ∧ inv f ≠ f ∧ ¬ (f ∈ A ∧ inv f ∈ A))).image pair
      A ⊆ D ∧ (∀ j, T j ∈ D) ∧ H ⊆ eligible ∧
      N - H.card ≤ p ∧ H.card ≤ b ∧ N ≤ g ∧ H.sum fee ≤ W ∧
      ∀ U : Finset F, A ⊆ U → U ⊂ D →
        (∀ x ∈ U, ∀ y ∈ U,
          ((fun t => x t && y t) ∈ D → (fun t => x t && y t) ∈ U) ∧
          ((fun t => x t || y t) ∈ D → (fun t => x t || y t) ∈ U)) →
        ∃ f ∈ U, inv f ∉ U ∧ pair f ∈ H := by
  have hiff := Iff.intro (fwd m d a p b g W X T fee) (bwd m d a p b g W X T fee)
  have hpair_eq : ∀ (d1 d2 : DecidableEq (Fin m → Bool)) (f : Fin m → Bool),
      @insert _ _ (@Finset.instInsert _ d1) f {fun t => !f t} =
      @insert _ _ (@Finset.instInsert _ d2) f {invF f} := fun _ _ f => by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; rfl
  have hSDiff_card : ∀ (d1 d2 : DecidableEq (Fin m → Bool)) (D : Finset (Fin m → Bool)),
      (@SDiff.sdiff _ (@Finset.instSDiff _ d1) D
        (@Finset.image Nat (Fin m → Bool) d1 (fun j t => (List.ofFn (X t) ++ [false, true]).getD j false) (Finset.range (d + 2)))).card =
      (@SDiff.sdiff _ (@Finset.instSDiff _ d2) D
        (@Finset.image Nat (Fin m → Bool) d2 (fun j t => (List.ofFn (X t) ++ [false, true]).getD j false) (Finset.range (d + 2)))).card :=
    fun _ _ D => congrArg Finset.card (by ext x; simp)
  constructor
  · rintro ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩
    have h8' : (Finset.univ : Finset (Fin C.size)).sum (fun i =>
        if (C.gates.get i).op = .not then
          fee (pairF (fun t => (C.wires (List.ofFn (X t) ++ [false, true])).getD (d + 2 + i.val) false))
        else 0) ≤ W := by
      refine le_trans (le_of_eq ?_) h8
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : (C.gates.get i).op = .not
      · simp only [ite_eq_left h]
        exact congrArg fee (hpair_eq _ _ _).symm
      · simp only [ite_eq_right h]
    obtain ⟨D, H, hAD, hTD, hHelig, hP, hB, hG, hW, hCut⟩ :=
      hiff.mp ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8'⟩
    refine ⟨D, H, ?_, hTD, ?_, ?_, hB, ?_, hW, ?_⟩
    · intro x hx; exact hAD (by simpa using hx)
    · intro P hP
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (hHelig hP)
      obtain ⟨hfD, hinvD, hne, hnotA⟩ := Finset.mem_filter.mp hf
      rw [@Finset.mem_image]
      refine ⟨f, ?_, (hpair_eq _ _ f).symm⟩
      rw [@Finset.mem_filter]
      refine ⟨hfD, hinvD, hne, ?_⟩
      rintro ⟨h1, h2⟩
      have h2' : invF f ∈ @Finset.image Nat (Fin m → Bool) (fun a b => Classical.propDecidable (a = b))
          (fun j t => (List.ofFn (X t) ++ [false, true]).getD j false) (Finset.range (d + 2)) := h2
      exact hnotA ⟨by simpa using h1, by simpa using h2'⟩
    · rw [hSDiff_card _ (inferInstance : DecidableEq (Fin m → Bool)) D]; exact hP
    · rw [hSDiff_card _ (inferInstance : DecidableEq (Fin m → Bool)) D]; exact hG
    · intro U hAU hUD hcl
      obtain ⟨f, hfU, hinvU, hpairH⟩ := hCut U (fun x hx => hAU (by simpa using hx)) hUD hcl
      refine ⟨f, hfU, hinvU, ?_⟩
      dsimp only
      rwa [hpair_eq _ _ f]
  · rintro ⟨D, H, hAD, hTD, hHelig, hP, hB, hG, hW, hCut⟩
    have hHelig' : H ⊆ (D.filter (fun f => invF f ∈ D ∧ invF f ≠ f ∧
        ¬ (f ∈ (Finset.range (d + 2)).image (fun j t => (List.ofFn (X t) ++ [false, true]).getD j false) ∧
          invF f ∈ (Finset.range (d + 2)).image (fun j t => (List.ofFn (X t) ++ [false, true]).getD j false)))).image pairF := by
      intro P hP
      have h1 := hHelig hP
      rw [@Finset.mem_image] at h1
      obtain ⟨f, hf, rfl⟩ := h1
      rw [@Finset.mem_filter] at hf
      obtain ⟨hfD, hinvD, hne, hnotA⟩ := hf
      refine Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hfD, hinvD, hne, ?_⟩, hpair_eq _ _ f⟩
      rintro ⟨h1, h2⟩
      have h2' : (fun t => !f t) ∈ (Finset.range (d + 2)).image (fun j t => (List.ofFn (X t) ++ [false, true]).getD j false) := h2
      exact hnotA ⟨by simpa using h1, by simpa using h2'⟩
    obtain ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      hiff.mpr ⟨D, H, fun x hx => hAD (by simpa using hx), hTD, hHelig',
        by rw [← hSDiff_card _ (inferInstance : DecidableEq (Fin m → Bool)) D]; exact hP,
        hB, by rw [← hSDiff_card _ (inferInstance : DecidableEq (Fin m → Bool)) D]; exact hG, hW,
        fun U hAU hUD hcl => by
          obtain ⟨f, hfU, hinvU, hpairH⟩ := hCut U (fun x hx => hAU (by simpa using hx)) hUD hcl
          refine ⟨f, hfU, hinvU, ?_⟩
          dsimp only at hpairH
          unfold pairF
          rwa [← hpair_eq _ _ f]⟩
    refine ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, ?_⟩
    refine le_trans (le_of_eq ?_) h8
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (C.gates.get i).op = .not
    · simp only [ite_eq_left h]
      exact congrArg fee (hpair_eq _ _ _)
    · simp only [ite_eq_right h]

end PEqualNP.Outside.L_meta_53183_aux

theorem PEqualNP.Outside.L_meta_53183 : (∀ (m d a p b g W : Nat) (X : Fin m → Fin d → Bool) (T : Fin a → Fin m → Bool)
  (fee : Finset (Fin m → Bool) → Nat),
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := Fin m → Bool
  let inv := fun (f : F) (t : Fin m) => !(f t)
  let pair := fun f => ({f, inv f} : Finset F)
  let inputs := fun t => List.ofFn (X t) ++ [false,true]
  let A := (Finset.range (d+2)).image (fun j t => (inputs t).getD j false)
  (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    let wire := fun (j : Nat) t => (C.wires (inputs t)).getD j false
    let neg := PEqualNP.NotBracket.notCount C
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
    C.output < d+2+C.size ∧ (∀ j, tap j < d+2+C.size ∧ wire (tap j) = T j) ∧
    C.size-neg ≤ p ∧ neg ≤ b ∧ C.size ≤ g ∧
    (Finset.univ : Finset (Fin C.size)).sum (fun i =>
      if (C.gates.get i).op = .not then fee (pair (wire (d+2+i.val))) else 0) ≤ W) ↔
  ∃ (D : Finset F) (H : Finset (Finset F)),
    let N := (D \ A).card
    let eligible := (D.filter (fun f => inv f ∈ D ∧ inv f ≠ f ∧ ¬ (f ∈ A ∧ inv f ∈ A))).image pair
    A ⊆ D ∧ (∀ j, T j ∈ D) ∧ H ⊆ eligible ∧
    N-H.card ≤ p ∧ H.card ≤ b ∧ N ≤ g ∧ H.sum fee ≤ W ∧
    ∀ U : Finset F, A ⊆ U → U ⊂ D →
      (∀ x ∈ U, ∀ y ∈ U,
        ((fun t => x t && y t) ∈ D → (fun t => x t && y t) ∈ U) ∧
        ((fun t => x t || y t) ∈ D → (fun t => x t || y t) ∈ U)) →
      ∃ f ∈ U, inv f ∉ U ∧ pair f ∈ H) :=
  PEqualNP.Outside.L_meta_53183_aux.main
