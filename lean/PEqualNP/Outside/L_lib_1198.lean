import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1198_aux

private lemma main_aux :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (T A : Finset (Fin m)),
      (∀ p, p ∉ nb p) → (∀ p q, q ∈ nb p ↔ p ∈ nb q) → (∀ i, (i,true) ∈ nb (i,false)) →
      (∀ c i j, (j,c) ∈ nb (i,c) → i ∈ T ∨ j ∈ T) →
      let U := A \ T
      let B := A ∩ T
      let path := Relation.ReflTransGen (fun (i j : Fin m) => i ∈ U ∧ j ∈ U ∧ (j,false) ∈ nb (i,true))
      let covers := (Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        ∀ i, xor (x (i,false)) (x (i,true)) = decide (i ∈ A))
      let branch := fun (f : ↥B → Bool) =>
        let hit := fun (i : Fin m) (c : Bool) => ∃ j : ↥B, (i,c) ∈ nb (j.val,f j)
        let up := U.filter (fun i => ∃ j ∈ U, hit j false ∧ path j i)
        let down := U.filter (fun i => ∃ j ∈ U, hit j true ∧ path i j)
        let free := (U \ up) \ down
        let reps := free.filter (fun i => ∀ j ∈ free, path i j → path j i → i ≤ j)
        let anti := reps.powerset.filter (fun S => ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ path i j)
        if (∃ i j : ↥B, (j.val,f j) ∈ nb (i.val,f i)) ∨ ¬ Disjoint up down
        then 0 else anti.card
      covers.card = ∑ f : ↥B → Bool, branch f := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro m nb T A hirr hsym hpair hshore U B path covers branch
  have hUB_disj : ∀ i : Fin m, i ∈ B → i ∉ U := by
    intro i hiB hiU
    have hT : i ∈ T := (Finset.mem_inter.mp hiB).2
    have hnT : i ∉ T := (Finset.mem_sdiff.mp hiU).2
    exact hnT hT
  have hB_sub_A : ∀ i : Fin m, i ∈ B → i ∈ A := fun i hi => (Finset.mem_inter.mp hi).1
  have hU_sub_A : ∀ i : Fin m, i ∈ U → i ∈ A := fun i hi => (Finset.mem_sdiff.mp hi).1
  have hA_cases : ∀ i : Fin m, i ∈ A → i ∈ B ∨ i ∈ U := by
    intro i hiA
    by_cases hiT : i ∈ T
    · exact Or.inl (Finset.mem_inter.mpr ⟨hiA, hiT⟩)
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hiA, hiT⟩)
  have hpart : covers.card = ∑ f ∈ (Finset.univ : Finset (↥B → Bool)),
      (covers.filter (fun x => (fun j : ↥B => x (j.val, false)) = f)).card := by
    exact Finset.card_eq_sum_card_fiberwise (f := fun (x : (Fin m × Bool) → Bool) (j : ↥B) => x (j.val, false))
      (t := (Finset.univ : Finset (↥B → Bool))) (fun _ _ => Finset.mem_univ _)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro f _
  dsimp only [branch]
  set hit : Fin m → Bool → Prop := fun i c => ∃ j : ↥B, (i, c) ∈ nb (j.val, f j)
  set up : Finset (Fin m) := U.filter (fun i => ∃ j ∈ U, hit j false ∧ path j i)
  set down : Finset (Fin m) := U.filter (fun i => ∃ j ∈ U, hit j true ∧ path i j)
  set free : Finset (Fin m) := (U \ up) \ down
  set reps : Finset (Fin m) := free.filter (fun i => ∀ j ∈ free, path i j → path j i → i ≤ j)
  set anti : Finset (Finset (Fin m)) :=
    reps.powerset.filter (fun S => ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ path i j)
  set fiber : Finset ((Fin m × Bool) → Bool) :=
    covers.filter (fun x => (fun j : ↥B => x (j.val, false)) = f)
  have hfree_sub_U : ∀ i ∈ free, i ∈ U := by
    intro i hi
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).1
  have hfree_not_up : ∀ i ∈ free, i ∉ up := by
    intro i hi
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).2
  have hfree_not_down : ∀ i ∈ free, i ∉ down := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2
  have hreps_sub_free : ∀ i ∈ reps, i ∈ free := fun i hi => (Finset.mem_filter.mp hi).1
  have hreps_antisymm : ∀ i ∈ reps, ∀ j ∈ reps, path i j → path j i → i = j := by
    intro i hi j hj hij hji
    have h1 : i ≤ j := (Finset.mem_filter.mp hi).2 j (hreps_sub_free j hj) hij hji
    have h2 : j ≤ i := (Finset.mem_filter.mp hj).2 i (hreps_sub_free i hi) hji hij
    exact le_antisymm h1 h2
  have hx_notA : ∀ x ∈ covers, ∀ i, i ∉ A → ∀ c, x (i, c) = true := by
    intro x hx i hiA c
    have hmem := (Finset.mem_filter.mp hx).2
    have hcov := hmem.1 (i, false) (i, true) (hpair i)
    have hxor := hmem.2 i
    rw [decide_eq_false hiA] at hxor
    cases h0 : x (i, false) <;> cases h1 : x (i, true)
    · rw [h0, h1] at hcov; rcases hcov with h | h <;> cases h
    · rw [h0, h1] at hxor; cases hxor
    · rw [h0, h1] at hxor; cases hxor
    · cases c <;> assumption
  have hx_inA_true : ∀ x ∈ covers, ∀ i, i ∈ A → x (i, true) = !(x (i, false)) := by
    intro x hx i hiA
    have hxor := (Finset.mem_filter.mp hx).2.2 i
    rw [decide_eq_true hiA] at hxor
    cases h0 : x (i, false) <;> cases h1 : x (i, true)
    · rw [h0, h1] at hxor; cases hxor
    · rfl
    · rfl
    · rw [h0, h1] at hxor; cases hxor
  have hx_inA_zero : ∀ x ∈ covers, ∀ i, i ∈ A → x (i, x (i, false)) = false := by
    intro x hx i hiA
    have ht := hx_inA_true x hx i hiA
    cases h0 : x (i, false) <;> simp [h0, ht]
  have hx_U_path : ∀ x ∈ covers, ∀ i j, path i j → x (i, false) = true → x (j, false) = true := by
    intro x hx i j hp
    induction hp with
    | refl => exact id
    | @tail b c _ hbc ih =>
      intro hxi
      have hxb : x (b, false) = true := ih hxi
      have hxbt : x (b, true) = false := by
        rw [hx_inA_true x hx b (hU_sub_A b hbc.1), hxb]
        rfl
      have hcov := (Finset.mem_filter.mp hx).2.1 (b, true) (c, false) hbc.2.2
      rw [hxbt] at hcov
      rcases hcov with h | h
      · cases h
      · exact h
  have hx_up : ∀ x ∈ fiber, ∀ i ∈ up, x (i, false) = true := by
    intro x hxf i hiup
    have hx : x ∈ covers := (Finset.mem_filter.mp hxf).1
    have hfeq : (fun j : ↥B => x (j.val, false)) = f := (Finset.mem_filter.mp hxf).2
    rcases (Finset.mem_filter.mp hiup).2 with ⟨j, _, ⟨b, hjb⟩, hji⟩
    have hxb : x (b.val, f b) = false := by
      have hbf : x (b.val, false) = f b := congrFun hfeq b
      rw [← hbf]
      exact hx_inA_zero x hx b.val (hB_sub_A b.val b.property)
    have hcov := (Finset.mem_filter.mp hx).2.1 (b.val, f b) (j, false) hjb
    rw [hxb] at hcov
    have hxj : x (j, false) = true := by
      rcases hcov with h | h
      · cases h
      · exact h
    exact hx_U_path x hx j i hji hxj
  have hx_down : ∀ x ∈ fiber, ∀ i ∈ down, x (i, false) = false := by
    intro x hxf i hidn
    have hx : x ∈ covers := (Finset.mem_filter.mp hxf).1
    have hfeq : (fun j : ↥B => x (j.val, false)) = f := (Finset.mem_filter.mp hxf).2
    rcases (Finset.mem_filter.mp hidn).2 with ⟨j, hjU, ⟨b, hjb⟩, hij⟩
    have hxb : x (b.val, f b) = false := by
      have hbf : x (b.val, false) = f b := congrFun hfeq b
      rw [← hbf]
      exact hx_inA_zero x hx b.val (hB_sub_A b.val b.property)
    have hcov := (Finset.mem_filter.mp hx).2.1 (b.val, f b) (j, true) hjb
    rw [hxb] at hcov
    have hxjt : x (j, true) = true := by
      rcases hcov with h | h
      · cases h
      · exact h
    have hxjf : x (j, false) = false := by
      have ht := hx_inA_true x hx j (hU_sub_A j hjU)
      rw [hxjt] at ht
      cases h0 : x (j, false)
      · rfl
      · rw [h0] at ht; cases ht
    cases h0 : x (i, false)
    · rfl
    · have h1 := hx_U_path x hx i j hij h0
      rw [hxjf] at h1
      cases h1
  split_ifs with hbad
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hxf
    have hx : x ∈ covers := (Finset.mem_filter.mp hxf).1
    have hfeq : (fun j : ↥B => x (j.val, false)) = f := (Finset.mem_filter.mp hxf).2
    rcases hbad with ⟨i, j, hij⟩ | hndisj
    · have hxi : x (i.val, f i) = false := by
        rw [← congrFun hfeq i]
        exact hx_inA_zero x hx i.val (hB_sub_A i.val i.property)
      have hxj : x (j.val, f j) = false := by
        rw [← congrFun hfeq j]
        exact hx_inA_zero x hx j.val (hB_sub_A j.val j.property)
      have hcov := (Finset.mem_filter.mp hx).2.1 (i.val, f i) (j.val, f j) hij
      rw [hxi, hxj] at hcov
      rcases hcov with h | h <;> cases h
    · rw [Finset.not_disjoint_iff] at hndisj
      rcases hndisj with ⟨i, hiup, hidn⟩
      have h1 := hx_up x hxf i hiup
      have h2 := hx_down x hxf i hidn
      rw [h1] at h2
      cases h2
  · push Not at hbad
    rcases hbad with ⟨hgood_B, hdisj⟩
    let toAnti : ((Fin m × Bool) → Bool) → Finset (Fin m) := fun x =>
      (reps.filter (fun r => x (r, false) = true)).filter
        (fun r => ∀ r' ∈ reps, x (r', false) = true → path r' r → r' = r)
    let fromAnti : Finset (Fin m) → (Fin m × Bool) → Bool := fun S p =>
      if hB : p.1 ∈ B then xor p.2 (f ⟨p.1, hB⟩)
      else if p.1 ∈ U then xor p.2 (decide (p.1 ∈ up ∨ ∃ r ∈ S, path r p.1))
      else true
    refine Finset.card_bij' (fun x _ => toAnti x) (fun S _ => fromAnti S) ?_ ?_ ?_ ?_
    · intro x _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro r hr
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      · intro r1 hr1 r2 hr2 hne h12
        have hr1' := Finset.mem_filter.mp (Finset.mem_filter.mp hr1).1
        have hr2min := (Finset.mem_filter.mp hr2).2
        exact hne (hr2min r1 hr1'.1 hr1'.2 h12)
    · intro S hS
      have hS_sub_reps : S ⊆ reps := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro p q hpq
          rcases p with ⟨i, c⟩
          rcases q with ⟨j, d⟩
          by_contra hboth
          push Not at hboth
          have hfp : fromAnti S (i, c) = false := by
            cases h : fromAnti S (i, c)
            · rfl
            · exact absurd h hboth.1
          have hfq : fromAnti S (j, d) = false := by
            cases h : fromAnti S (j, d)
            · rfl
            · exact absurd h hboth.2
          have haux_UB : ∀ u ∈ U, ∀ cu : Bool, ∀ v : ↥B, ∀ cv : Bool,
              (u, cu) ∈ nb (v.val, cv) →
              fromAnti S (u, cu) = false → fromAnti S (v.val, cv) = false → False := by
            intro u huU cu v cv huv hfu hfv
            have hcv : cv = f v := by
              simp only [fromAnti, v.property, ↓reduceDIte] at hfv
              cases cv <;> cases hfv_eq : f v
              · rfl
              · rw [hfv_eq] at hfv; cases hfv
              · rw [hfv_eq] at hfv; cases hfv
              · rfl
            rw [hcv] at huv
            have hhit : hit u cu := ⟨v, huv⟩
            have hu_notB : u ∉ B := fun hB => hUB_disj u hB huU
            simp only [fromAnti, hu_notB, ↓reduceDIte, huU, ↓reduceIte] at hfu
            cases cu
            · have hnot : ¬ (u ∈ up ∨ ∃ r ∈ S, path r u) := by
                cases hdec : decide (u ∈ up ∨ ∃ r ∈ S, path r u)
                · exact of_decide_eq_false hdec
                · rw [hdec] at hfu; cases hfu
              apply hnot
              left
              exact Finset.mem_filter.mpr ⟨huU, u, huU, hhit, Relation.ReflTransGen.refl⟩
            · have hyes : u ∈ up ∨ ∃ r ∈ S, path r u := by
                cases hdec : decide (u ∈ up ∨ ∃ r ∈ S, path r u)
                · rw [hdec] at hfu; cases hfu
                · exact of_decide_eq_true hdec
              have hudown : u ∈ down :=
                Finset.mem_filter.mpr ⟨huU, u, huU, hhit, Relation.ReflTransGen.refl⟩
              rcases hyes with huup | ⟨r, hrS, hru⟩
              · exact Finset.disjoint_left.mp hdisj huup hudown
              · have hrfree : r ∈ free := hreps_sub_free r (hS_sub_reps hrS)
                have hrdown : r ∈ down :=
                  Finset.mem_filter.mpr ⟨hfree_sub_U r hrfree, u, huU, hhit, hru⟩
                exact hfree_not_down r hrfree hrdown
          by_cases hiB : i ∈ B
          · by_cases hjB : j ∈ B
            · have hc : c = f ⟨i, hiB⟩ := by
                simp only [fromAnti, hiB, ↓reduceDIte] at hfp
                cases c <;> cases hf1 : f ⟨i, hiB⟩
                · rfl
                · rw [hf1] at hfp; cases hfp
                · rw [hf1] at hfp; cases hfp
                · rfl
              have hd : d = f ⟨j, hjB⟩ := by
                simp only [fromAnti, hjB, ↓reduceDIte] at hfq
                cases d <;> cases hf2 : f ⟨j, hjB⟩
                · rfl
                · rw [hf2] at hfq; cases hfq
                · rw [hf2] at hfq; cases hfq
                · rfl
              rw [hc, hd] at hpq
              exact hgood_B ⟨i, hiB⟩ ⟨j, hjB⟩ hpq
            · by_cases hjU : j ∈ U
              · exact haux_UB j hjU d ⟨i, hiB⟩ c hpq hfq hfp
              · simp only [fromAnti, hjB, ↓reduceDIte, hjU, ↓reduceIte] at hfq
                cases hfq
          · by_cases hiU : i ∈ U
            · by_cases hjB : j ∈ B
              · exact haux_UB i hiU c ⟨j, hjB⟩ d ((hsym _ _).mp hpq) hfp hfq
              · by_cases hjU : j ∈ U
                · have hstep_contra : ∀ u ∈ U, ∀ v ∈ U, (v, false) ∈ nb (u, true) →
                      fromAnti S (u, true) = false → fromAnti S (v, false) = false → False := by
                    intro u huU v hvU huv hfu hfv
                    have hu_notB : u ∉ B := fun hB => hUB_disj u hB huU
                    have hv_notB : v ∉ B := fun hB => hUB_disj v hB hvU
                    simp only [fromAnti, hu_notB, ↓reduceDIte, huU, ↓reduceIte] at hfu
                    simp only [fromAnti, hv_notB, ↓reduceDIte, hvU, ↓reduceIte] at hfv
                    have huyes : u ∈ up ∨ ∃ r ∈ S, path r u := by
                      cases hdec : decide (u ∈ up ∨ ∃ r ∈ S, path r u)
                      · rw [hdec] at hfu; cases hfu
                      · exact of_decide_eq_true hdec
                    have hvno : ¬ (v ∈ up ∨ ∃ r ∈ S, path r v) := by
                      cases hdec : decide (v ∈ up ∨ ∃ r ∈ S, path r v)
                      · exact of_decide_eq_false hdec
                      · rw [hdec] at hfv; cases hfv
                    have hpuv : path u v := Relation.ReflTransGen.single ⟨huU, hvU, huv⟩
                    apply hvno
                    rcases huyes with huup | ⟨r, hrS, hru⟩
                    · left
                      rcases (Finset.mem_filter.mp huup).2 with ⟨k, hkU, hkhit, hku⟩
                      exact Finset.mem_filter.mpr ⟨hvU, k, hkU, hkhit, hku.trans hpuv⟩
                    · right
                      exact ⟨r, hrS, hru.trans hpuv⟩
                  cases c <;> cases d
                  · rcases hshore false i j hpq with hiT | hjT
                    · exact (Finset.mem_sdiff.mp hiU).2 hiT
                    · exact (Finset.mem_sdiff.mp hjU).2 hjT
                  · exact hstep_contra j hjU i hiU ((hsym _ _).mp hpq) hfq hfp
                  · exact hstep_contra i hiU j hjU hpq hfp hfq
                  · rcases hshore true i j hpq with hiT | hjT
                    · exact (Finset.mem_sdiff.mp hiU).2 hiT
                    · exact (Finset.mem_sdiff.mp hjU).2 hjT
                · simp only [fromAnti, hjB, ↓reduceDIte, hjU, ↓reduceIte] at hfq
                  cases hfq
            · simp only [fromAnti, hiB, ↓reduceDIte, hiU, ↓reduceIte] at hfp
              cases hfp
        · intro i
          by_cases hiB : i ∈ B
          · have hiA : i ∈ A := hB_sub_A i hiB
            simp only [fromAnti, hiB, ↓reduceDIte, decide_eq_true hiA]
            cases f ⟨i, hiB⟩ <;> rfl
          · by_cases hiU : i ∈ U
            · have hiA : i ∈ A := hU_sub_A i hiU
              simp only [fromAnti, hiB, ↓reduceDIte, hiU, ↓reduceIte, decide_eq_true hiA]
              cases decide (i ∈ up ∨ ∃ r ∈ S, path r i) <;> rfl
            · have hiA : i ∉ A := by
                intro hA
                rcases hA_cases i hA with h | h
                · exact hiB h
                · exact hiU h
              simp only [fromAnti, hiB, ↓reduceDIte, hiU, ↓reduceIte, decide_eq_false hiA]
              rfl
      · funext j
        simp only [fromAnti, j.property, ↓reduceDIte]
        cases f j <;> rfl
    · intro x hxf
      have hx : x ∈ covers := (Finset.mem_filter.mp hxf).1
      have hfeq : (fun j : ↥B => x (j.val, false)) = f := (Finset.mem_filter.mp hxf).2
      funext ⟨i, c⟩
      by_cases hiB : i ∈ B
      · simp only [fromAnti, hiB, ↓reduceDIte]
        have hbf : f ⟨i, hiB⟩ = x (i, false) := (congrFun hfeq ⟨i, hiB⟩).symm
        have ht := hx_inA_true x hx i (hB_sub_A i hiB)
        rw [hbf]
        cases c <;> cases h0 : x (i, false) <;> simp [h0, ht]
      · by_cases hiU : i ∈ U
        · simp only [fromAnti, hiB, ↓reduceDIte, hiU, ↓reduceIte]
          have hiff : (i ∈ up ∨ ∃ r ∈ toAnti x, path r i) ↔ x (i, false) = true := by
            constructor
            · rintro (hiup | ⟨r, hr, hri⟩)
              · exact hx_up x hxf i hiup
              · have hxr : x (r, false) = true :=
                  (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
                exact hx_U_path x hx r i hri hxr
            · intro hxi
              by_cases hiup : i ∈ up
              · exact Or.inl hiup
              · right
                have hidn : i ∉ down := by
                  intro hdn
                  have h2 := hx_down x hxf i hdn
                  rw [hxi] at h2
                  cases h2
                have hifree : i ∈ free :=
                  Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hiU, hiup⟩, hidn⟩
                let scc := free.filter (fun j => path i j ∧ path j i)
                have hscc_ne : scc.Nonempty :=
                  ⟨i, Finset.mem_filter.mpr ⟨hifree, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩⟩
                let r0 := scc.min' hscc_ne
                have hr0_mem : r0 ∈ scc := Finset.min'_mem scc hscc_ne
                have hr0_free : r0 ∈ free := (Finset.mem_filter.mp hr0_mem).1
                have hr0_path : path i r0 ∧ path r0 i := (Finset.mem_filter.mp hr0_mem).2
                have hr0_reps : r0 ∈ reps := by
                  rw [Finset.mem_filter]
                  refine ⟨hr0_free, fun j hjfree hr0j hjr0 => ?_⟩
                  have hj_scc : j ∈ scc :=
                    Finset.mem_filter.mpr ⟨hjfree, hr0_path.1.trans hr0j, hjr0.trans hr0_path.2⟩
                  exact Finset.min'_le scc j hj_scc
                have hxr0 : x (r0, false) = true := hx_U_path x hx i r0 hr0_path.1 hxi
                let Qr := reps.filter (fun r => x (r, false) = true)
                let D : Fin m → Finset (Fin m) := fun u => Qr.filter (fun y => path y u)
                have hr0_D : r0 ∈ D r0 :=
                  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr0_reps, hxr0⟩, Relation.ReflTransGen.refl⟩
                rcases Finset.exists_min_image (D r0) (fun u => (D u).card) ⟨r0, hr0_D⟩ with
                  ⟨r, hrD, hrmin⟩
                have hrQr : r ∈ Qr := (Finset.mem_filter.mp hrD).1
                have hr_reps : r ∈ reps := (Finset.mem_filter.mp hrQr).1
                have hxr : x (r, false) = true := (Finset.mem_filter.mp hrQr).2
                have hrr0 : path r r0 := (Finset.mem_filter.mp hrD).2
                refine ⟨r, ?_, hrr0.trans hr0_path.2⟩
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_filter.mpr ⟨hr_reps, hxr⟩, ?_⟩
                intro r' hr'_reps hxr' hr'r
                by_contra hne
                have hr'_D : r' ∈ D r0 :=
                  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr'_reps, hxr'⟩, hr'r.trans hrr0⟩
                have hssub : D r' ⊂ D r := by
                  rw [Finset.ssubset_iff_subset_ne]
                  refine ⟨?_, ?_⟩
                  · intro y hy
                    have hy' := Finset.mem_filter.mp hy
                    exact Finset.mem_filter.mpr ⟨hy'.1, hy'.2.trans hr'r⟩
                  · intro heq
                    have hr_in_Dr : r ∈ D r :=
                      Finset.mem_filter.mpr ⟨hrQr, Relation.ReflTransGen.refl⟩
                    rw [← heq] at hr_in_Dr
                    have hrr' : path r r' := (Finset.mem_filter.mp hr_in_Dr).2
                    exact hne (hreps_antisymm r' hr'_reps r hr_reps hr'r hrr')
                have hlt : (D r').card < (D r).card := Finset.card_lt_card hssub
                have hle : (D r).card ≤ (D r').card := hrmin r' hr'_D
                exact Nat.not_lt_of_ge hle hlt
          have hdec : decide (i ∈ up ∨ ∃ r ∈ toAnti x, path r i) = x (i, false) := by
            cases h0 : x (i, false)
            · exact decide_eq_false (fun h => by have := hiff.mp h; rw [h0] at this; cases this)
            · exact decide_eq_true (hiff.mpr h0)
          have ht := hx_inA_true x hx i (hU_sub_A i hiU)
          rw [hdec]
          cases c <;> cases h0 : x (i, false) <;> simp [h0, ht]
        · simp only [fromAnti, hiB, ↓reduceDIte, hiU, ↓reduceIte]
          have hiA : i ∉ A := by
            intro hA
            rcases hA_cases i hA with h | h
            · exact hiB h
            · exact hiU h
          exact (hx_notA x hx i hiA c).symm
    · intro S hS
      have hS_sub_reps : S ⊆ reps := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hS_anti : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ path i j := (Finset.mem_filter.mp hS).2
      have hval_reps : ∀ r ∈ reps, fromAnti S (r, false) = true ↔ ∃ s ∈ S, path s r := by
        intro r hr
        have hrfree : r ∈ free := hreps_sub_free r hr
        have hrU : r ∈ U := hfree_sub_U r hrfree
        have hr_notB : r ∉ B := fun hB => hUB_disj r hB hrU
        have hr_notup : r ∉ up := hfree_not_up r hrfree
        simp only [fromAnti, hr_notB, ↓reduceDIte, hrU, ↓reduceIte]
        constructor
        · intro h
          have hdec : decide (r ∈ up ∨ ∃ s ∈ S, path s r) = true := by
            cases hd : decide (r ∈ up ∨ ∃ s ∈ S, path s r)
            · rw [hd] at h; cases h
            · rfl
          rcases of_decide_eq_true hdec with hup | hex
          · exact absurd hup hr_notup
          · exact hex
        · intro hex
          have hdec : decide (r ∈ up ∨ ∃ s ∈ S, path s r) = true := decide_eq_true (Or.inr hex)
          rw [hdec]
          rfl
      ext r
      constructor
      · intro hr
        have hr1 := Finset.mem_filter.mp (Finset.mem_filter.mp hr).1
        have hrmin := (Finset.mem_filter.mp hr).2
        rcases (hval_reps r hr1.1).mp hr1.2 with ⟨s, hsS, hsr⟩
        have hs_reps : s ∈ reps := hS_sub_reps hsS
        have hs_val : fromAnti S (s, false) = true :=
          (hval_reps s hs_reps).mpr ⟨s, hsS, Relation.ReflTransGen.refl⟩
        have hsr_eq : s = r := hrmin s hs_reps hs_val hsr
        rw [← hsr_eq]
        exact hsS
      · intro hrS
        have hr_reps : r ∈ reps := hS_sub_reps hrS
        have hr_val : fromAnti S (r, false) = true :=
          (hval_reps r hr_reps).mpr ⟨r, hrS, Relation.ReflTransGen.refl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_filter.mpr ⟨hr_reps, hr_val⟩, ?_⟩
        intro r' hr'_reps hr'_val hr'r
        rcases (hval_reps r' hr'_reps).mp hr'_val with ⟨s, hsS, hsr'⟩
        have hsr : path s r := hsr'.trans hr'r
        have hsr_eq : s = r := by
          by_contra hne
          exact hS_anti s hsS r hrS hne hsr
        rw [hsr_eq] at hsr'
        exact hreps_antisymm r' hr'_reps r hr_reps hr'r hsr'

end PEqualNP.Outside.L_lib_1198_aux

theorem PEqualNP.Outside.L_lib_1198 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (T A : Finset (Fin m)),
      (∀ p, p ∉ nb p) → (∀ p q, q ∈ nb p ↔ p ∈ nb q) → (∀ i, (i,true) ∈ nb (i,false)) →
      (∀ c i j, (j,c) ∈ nb (i,c) → i ∈ T ∨ j ∈ T) →
      let U := A \ T
      let B := A ∩ T
      let path := Relation.ReflTransGen (fun (i j : Fin m) => i ∈ U ∧ j ∈ U ∧ (j,false) ∈ nb (i,true))
      let covers := (Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        ∀ i, xor (x (i,false)) (x (i,true)) = decide (i ∈ A))
      let branch := fun (f : ↥B → Bool) =>
        let hit := fun (i : Fin m) (c : Bool) => ∃ j : ↥B, (i,c) ∈ nb (j.val,f j)
        let up := U.filter (fun i => ∃ j ∈ U, hit j false ∧ path j i)
        let down := U.filter (fun i => ∃ j ∈ U, hit j true ∧ path i j)
        let free := (U \ up) \ down
        let reps := free.filter (fun i => ∀ j ∈ free, path i j → path j i → i ≤ j)
        let anti := reps.powerset.filter (fun S => ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ path i j)
        if (∃ i j : ↥B, (j.val,f j) ∈ nb (i.val,f i)) ∨ ¬ Disjoint up down
        then 0 else anti.card
      covers.card = ∑ f : ↥B → Bool, branch f :=
  PEqualNP.Outside.L_lib_1198_aux.main_aux
