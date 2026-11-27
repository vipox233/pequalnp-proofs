import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_474_aux

lemma filterMap_length_add_filter_length {α β : Type*} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filterMap (fun a => if p a = true then none else some (f a))).length +
      (l.filter p).length = l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    cases hp : p a
    · simp only [List.filterMap_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        List.filter_cons]
      omega
    · simp only [List.filterMap_cons, hp, ↓reduceIte, List.filter_cons, List.length_cons]
      omega

lemma finRange_split (n r : ℕ) (hr : r < n) :
    List.finRange n =
      (List.finRange n).take r ++ [⟨r, hr⟩] ++ (List.finRange n).drop (r + 1) := by
  have hlen : r < (List.finRange n).length := by simp [hr]
  have hdrop : (List.finRange n).drop r =
      (List.finRange n)[r]'hlen :: (List.finRange n).drop (r + 1) :=
    List.drop_eq_getElem_cons hlen
  have hget : (List.finRange n)[r]'hlen = ⟨r, hr⟩ := List.getElem_finRange hlen
  rw [hget] at hdrop
  calc List.finRange n
      = (List.finRange n).take r ++ (List.finRange n).drop r :=
          (List.take_append_drop r (List.finRange n)).symm
    _ = (List.finRange n).take r ++ (⟨r, hr⟩ :: (List.finRange n).drop (r + 1)) := by
          rw [hdrop]
    _ = (List.finRange n).take r ++ [⟨r, hr⟩] ++ (List.finRange n).drop (r + 1) := by
          rw [List.append_assoc, List.singleton_append]

lemma filterMap_eq_of_forall {α β : Type*} (l : List α) (f g : α → Option β)
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

end PEqualNP.Outside.L_lib_474_aux

theorem PEqualNP.Outside.L_lib_474 : ∀ n : Nat,
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  let Order := Equiv.Perm V
  ∀ F : Finset Clause,
    let forced := fun (s : Point) (order : Order) =>
      (Finset.univ : Finset V).filter (fun i =>
        ∃ c ∈ F, (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨
          ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))
    let code := fun (s : Point) (order : Order) =>
      (List.finRange n).filterMap (fun rank =>
        let v := order.symm rank
        if v ∈ forced s order then none else some (s v))
    ∀ (order : Order) (s z : Point), sat F s → sat F z →
      (code s order).length + (forced s order).card = n ∧
      ((∃ tail : List Bool, code s order ++ tail = code z order) → s = z) := by
  intro n V Point Clause sat Order F forced code order s z hsatz_s hsatz_z
  classical
  constructor
  · let p : Fin n → Bool := fun rank => decide (order.symm rank ∈ forced s order)
    have hfm : code s order =
        (List.finRange n).filterMap (fun rank => if p rank = true then none else some (s (order.symm rank))) := by
      dsimp only [code, p]
      congr 1
      funext rank
      simp only [decide_eq_true_eq]
    have hsum := PEqualNP.Outside.L_lib_474_aux.filterMap_length_add_filter_length
      (List.finRange n) p (fun rank => s (order.symm rank))
    rw [← hfm, List.length_finRange] at hsum
    have hfilt_eq : ((List.finRange n).filter p).length = (forced s order).card := by
      have hnd : ((List.finRange n).filter p).Nodup := (List.nodup_finRange n).filter p
      rw [← List.toFinset_card_of_nodup hnd]
      have hto : ((List.finRange n).filter p).toFinset =
          (forced s order).image order := by
        ext r
        simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, p,
          decide_eq_true_eq, Finset.mem_image]
        constructor
        · intro hr
          exact ⟨order.symm r, hr, order.apply_symm_apply r⟩
        · rintro ⟨v, hv, rfl⟩
          rwa [order.symm_apply_apply]
      rw [hto, Finset.card_image_of_injective _ order.injective]
    omega
  · rintro ⟨tail, hcode⟩
    have hrank : ∀ r : ℕ, (hr : r < n) → s (order.symm ⟨r, hr⟩) = z (order.symm ⟨r, hr⟩) := by
      intro r
      induction r using Nat.strong_induction_on with
      | ind r ih =>
        intro hr
        have hagree : ∀ u : V, (order u).val < r → s u = z u := by
          intro u hu
          have hru : order.symm ⟨(order u).val, (order u).isLt⟩ = u := by
            have : (⟨(order u).val, (order u).isLt⟩ : Fin n) = order u := Fin.eta _ _
            rw [this, order.symm_apply_apply]
          have h := ih (order u).val hu (order u).isLt
          rwa [hru] at h
        have hforced_iff : ∀ u : V, (order u).val < r →
            (u ∈ forced s order ↔ u ∈ forced z order) := by
          intro u hu
          have hsu : s u = z u := hagree u hu
          simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> (
            rintro ⟨c, hcF, hmem, hall⟩
            refine ⟨c, hcF, ?_, ?_⟩
            · first | (rwa [← hsu]) | (rwa [hsu])
            · intro e he
              rcases hall e he with rfl | ⟨hlt, hne⟩
              · left; first | (rw [hsu]) | (rw [← hsu])
              · right
                have hse : s e.1 = z e.1 := hagree e.1 (lt_trans hlt hu)
                exact ⟨hlt, by first | (rwa [← hse]) | (rwa [hse])⟩)
        set v : V := order.symm ⟨r, hr⟩
        have hov : (order v).val = r := by
          have hv : order v = ⟨r, hr⟩ := order.apply_symm_apply ⟨r, hr⟩
          rw [hv]
        by_cases hfs : v ∈ forced s order
        · simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and] at hfs
          rcases hfs with ⟨c, hcF, hmem, hall⟩
          rcases hsatz_z c hcF with ⟨lit, hlitc, hlit_z⟩
          rcases hall lit hlitc with rfl | ⟨hlt, hne⟩
          · exact hlit_z.symm
          · exfalso
            rw [hov] at hlt
            have hse := hagree lit.1 hlt
            rw [hse, hlit_z] at hne
            exact hne rfl
        · by_cases hfz : v ∈ forced z order
          · simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and] at hfz
            rcases hfz with ⟨c, hcF, hmem, hall⟩
            rcases hsatz_s c hcF with ⟨lit, hlitc, hlit_s⟩
            rcases hall lit hlitc with rfl | ⟨hlt, hne⟩
            · exact hlit_s
            · exfalso
              rw [hov] at hlt
              have hse := hagree lit.1 hlt
              rw [← hse, hlit_s] at hne
              exact hne rfl
          · have hsplit := PEqualNP.Outside.L_lib_474_aux.finRange_split n r hr
            let fs : Fin n → Option Bool := fun rank =>
              if order.symm rank ∈ forced s order then none else some (s (order.symm rank))
            let fz : Fin n → Option Bool := fun rank =>
              if order.symm rank ∈ forced z order then none else some (z (order.symm rank))
            have hpref_eq : ((List.finRange n).take r).filterMap fs =
                ((List.finRange n).take r).filterMap fz := by
              have hcongr : ∀ rank ∈ (List.finRange n).take r, fs rank = fz rank := by
                intro rank hmem
                have hlt_r : rank.val < r := by
                  rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
                  have hi_r : i < r := by
                    have htl := List.length_take (i := r) (l := List.finRange n)
                    omega
                  have hi_n : i < (List.finRange n).length := by simp; omega
                  rw [List.getElem_take] at hget
                  have hfr : (List.finRange n)[i]'hi_n = ⟨i, by simp at hi_n; exact hi_n⟩ :=
                    List.getElem_finRange hi_n
                  rw [hfr] at hget
                  rw [← hget]
                  exact hi_r
                have hord_lt : (order (order.symm rank)).val < r := by
                  rw [order.apply_symm_apply]
                  exact hlt_r
                have hiff := hforced_iff (order.symm rank) hord_lt
                have hval := hagree (order.symm rank) hord_lt
                dsimp only [fs, fz]
                by_cases hf : order.symm rank ∈ forced s order
                · simp [hf, hiff.mp hf]
                · have hfz' : order.symm rank ∉ forced z order := fun h => hf (hiff.mpr h)
                  simp [hf, hfz', hval]
              exact PEqualNP.Outside.L_lib_474_aux.filterMap_eq_of_forall
                ((List.finRange n).take r) fs fz hcongr
            have hcs : code s order =
                ((List.finRange n).take r).filterMap fs ++
                  (s v :: ((List.finRange n).drop (r + 1)).filterMap fs) := by
              have hmid : [⟨r, hr⟩].filterMap fs = [s v] := by
                simp [fs, v, hfs]
              calc code s order
                  = (List.finRange n).filterMap fs := rfl
                _ = (((List.finRange n).take r ++ [(⟨r, hr⟩ : Fin n)]) ++
                      (List.finRange n).drop (r + 1)).filterMap fs := by
                        conv_lhs => rw [hsplit]
                _ = ((List.finRange n).take r).filterMap fs ++ [(⟨r, hr⟩ : Fin n)].filterMap fs ++
                      ((List.finRange n).drop (r + 1)).filterMap fs := by
                        rw [List.filterMap_append, List.filterMap_append]
                _ = ((List.finRange n).take r).filterMap fs ++
                      (s v :: ((List.finRange n).drop (r + 1)).filterMap fs) := by
                        rw [hmid, List.append_assoc, List.singleton_append]
            have hcz : code z order =
                ((List.finRange n).take r).filterMap fz ++
                  (z v :: ((List.finRange n).drop (r + 1)).filterMap fz) := by
              have hmid : [⟨r, hr⟩].filterMap fz = [z v] := by
                simp [fz, v, hfz]
              calc code z order
                  = (List.finRange n).filterMap fz := rfl
                _ = (((List.finRange n).take r ++ [(⟨r, hr⟩ : Fin n)]) ++
                      (List.finRange n).drop (r + 1)).filterMap fz := by
                        conv_lhs => rw [hsplit]
                _ = ((List.finRange n).take r).filterMap fz ++ [(⟨r, hr⟩ : Fin n)].filterMap fz ++
                      ((List.finRange n).drop (r + 1)).filterMap fz := by
                        rw [List.filterMap_append, List.filterMap_append]
                _ = ((List.finRange n).take r).filterMap fz ++
                      (z v :: ((List.finRange n).drop (r + 1)).filterMap fz) := by
                        rw [hmid, List.append_assoc, List.singleton_append]
            rw [hcs, hcz, hpref_eq, List.append_assoc, List.cons_append] at hcode
            have htail_eq := List.append_cancel_left hcode
            exact (List.cons.inj htail_eq).1
    funext u
    have h := hrank (order u).val (order u).isLt
    have hru : order.symm ⟨(order u).val, (order u).isLt⟩ = u := by
      have : (⟨(order u).val, (order u).isLt⟩ : Fin n) = order u := Fin.eta _ _
      rw [this, order.symm_apply_apply]
    rwa [hru] at h
