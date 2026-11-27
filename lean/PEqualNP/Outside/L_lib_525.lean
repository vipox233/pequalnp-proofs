import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_525_aux

open scoped BigOperators

lemma unary_code_prefix {m : ℕ} :
    ∀ i j : Fin m, (∃ tail : List Bool,
      List.replicate j.val true ++ [false] =
        (List.replicate i.val true ++ [false]) ++ tail) → i = j := by
  intro i j ⟨tail, h⟩
  have h1 : List.replicate j.val true ++ [false] =
      List.replicate i.val true ++ (false :: tail) := by
    simpa [List.append_assoc] using h
  have hlen : i.val ≤ j.val := by
    have hcard := congrArg List.length h1
    simp at hcard
    omega
  by_cases heq : i.val = j.val
  · exact Fin.ext heq
  · have hlt : i.val < j.val := by omega
    have hget := congrArg (fun l : List Bool => l[i.val]?) h1
    rw [List.getElem?_append_left (by simp [hlt]),
      List.getElem?_replicate] at hget
    simp only [hlt, ↓reduceIte] at hget
    rw [List.getElem?_append_right (by simp)] at hget
    simp at hget

lemma prefix_comp_perm {m : ℕ} (c : Fin m → List Bool) (σ : Equiv.Perm (Fin m))
    (hc : ∀ i j, (∃ tail : List Bool, c j = c i ++ tail) → i = j) :
    ∀ i j, (∃ tail : List Bool, c (σ j) = c (σ i) ++ tail) → i = j := by
  intro i j h
  exact σ.injective (hc (σ i) (σ j) h)

lemma cost_swap_le {m : ℕ} (w : Fin m → ℕ) (c : Fin m → List Bool) (x y : Fin m)
    (hw : w x ≤ w y) (hl : (c x).length ≤ (c y).length) :
    (∑ i : Fin m, w i * (c (Equiv.swap x y i)).length) ≤ ∑ i : Fin m, w i * (c i).length := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have hsplit : ∀ f : Fin m → ℕ,
        (∑ i : Fin m, f i) =
          f x + f y + ∑ i ∈ (Finset.univ.erase x).erase y, f i := by
      intro f
      have hy_mem : y ∈ Finset.univ.erase x :=
        Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ y⟩
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ x),
        ← Finset.add_sum_erase (Finset.univ.erase x) f hy_mem]
      omega
    rw [hsplit (fun i => w i * (c (Equiv.swap x y i)).length),
      hsplit (fun i => w i * (c i).length)]
    have hrest :
        (∑ i ∈ (Finset.univ.erase x).erase y, w i * (c (Equiv.swap x y i)).length) =
        ∑ i ∈ (Finset.univ.erase x).erase y, w i * (c i).length := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiy : i ≠ y := Finset.ne_of_mem_erase hi
      have hix : i ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      rw [Equiv.swap_apply_of_ne_of_ne hix hiy]
    rw [hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hmul : w x * (c y).length + w y * (c x).length ≤
        w x * (c x).length + w y * (c y).length := by
      nlinarith
    omega

lemma cost_swap_eq_of_len_eq {m : ℕ} (w : Fin m → ℕ) (c : Fin m → List Bool) (x y : Fin m)
    (hl : (c x).length = (c y).length) :
    (∑ i : Fin m, w i * (c (Equiv.swap x y i)).length) = ∑ i : Fin m, w i * (c i).length := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hix : i = x
  · subst hix; simp [hl]
  · by_cases hiy : i = y
    · subst hiy; simp [hl]
    · rw [Equiv.swap_apply_of_ne_of_ne hix hiy]

end PEqualNP.Outside.L_lib_525_aux

open PEqualNP.Outside.L_lib_525_aux

theorem PEqualNP.Outside.L_lib_525 :
    ∀ (m : ℕ) (w : Fin m → ℕ) (a b : Fin m), a ≠ b →
      (∀ i, 0 < w i) → (∀ i, i ≠ a → i ≠ b → w a ≤ w i ∧ w b ≤ w i) →
      let prefixCode := fun (code : Fin m → List Bool) =>
        ∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j
      let cost := fun (c : Fin m → List Bool) => ∑ i, w i * (c i).length
      ∃ (c : Fin m → List Bool) (parent : List Bool), prefixCode c ∧
        c a = parent ++ [false] ∧ c b = parent ++ [true] ∧
        (∀ i, (c i).length ≤ (c a).length) ∧ (∀ other, prefixCode other → cost c ≤ cost other) := by
  intro m w a b hab hwpos hwmin prefixCode cost
  classical
  have hex_cost : ∃ n : ℕ, ∃ c : Fin m → List Bool, prefixCode c ∧ cost c = n :=
    ⟨cost (fun i => List.replicate i.val true ++ [false]),
      fun i => List.replicate i.val true ++ [false], unary_code_prefix, rfl⟩
  let minCost := Nat.find hex_cost
  rcases Nat.find_spec hex_cost with ⟨c0, hc0_pref, hc0_cost⟩
  have hc0_opt : ∀ other, prefixCode other → cost c0 ≤ cost other := by
    intro other hother
    rw [hc0_cost]
    exact Nat.find_min' hex_cost ⟨other, hother, rfl⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨a, Finset.mem_univ a⟩
  rcases Finset.exists_max_image Finset.univ (fun i : Fin m => (c0 i).length) hne with
    ⟨i0, _, hi0_max⟩
  have hi0_ne_nil : c0 i0 ≠ [] := by
    intro hnil
    have hj : ∃ j : Fin m, j ≠ i0 := by
      by_cases h : a = i0
      · exact ⟨b, by rw [← h]; exact Ne.symm hab⟩
      · exact ⟨a, h⟩
    rcases hj with ⟨j, hji⟩
    exact hji (hc0_pref i0 j ⟨c0 j, by simp [hnil]⟩).symm
  let parent : List Bool := (c0 i0).dropLast
  let bit : Bool := (c0 i0).getLast hi0_ne_nil
  have hi0_eq : c0 i0 = parent ++ [bit] := (List.dropLast_append_getLast hi0_ne_nil).symm
  have hsib : ∃ j0 : Fin m, c0 j0 = parent ++ [!bit] := by
    by_contra hno
    push Not at hno
    let c' : Fin m → List Bool := Function.update c0 i0 parent
    have hc'_pref : prefixCode c' := by
      intro i j ⟨tail, htail⟩
      by_cases hi : i = i0
      · subst i
        by_cases hj : j = i0
        · exact hj.symm
        · exfalso
          simp only [c', Function.update_self, Function.update_of_ne hj] at htail
          cases tail with
          | nil =>
            simp only [List.append_nil] at htail
            have := hc0_pref j i0 ⟨[bit], by rw [hi0_eq, htail]⟩
            exact hj this
          | cons b' t' =>
            by_cases hb' : b' = bit
            · subst b'
              have h1 : c0 j = c0 i0 ++ t' := by
                rw [hi0_eq, List.append_assoc]; exact htail
              exact hj (hc0_pref i0 j ⟨t', h1⟩).symm
            · have hb'2 : b' = !bit := by cases b' <;> cases hbit : bit <;> simp_all
              subst b'
              have hlen_j : (c0 j).length ≤ (c0 i0).length := hi0_max j (Finset.mem_univ j)
              have hlen_eq := congrArg List.length htail
              have hlen_i0 := congrArg List.length hi0_eq
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen_eq hlen_i0
              have ht'nil : t' = [] := List.eq_nil_of_length_eq_zero (by omega)
              subst t'
              exact hno j htail
      · by_cases hj : j = i0
        · subst j
          simp only [c', Function.update_self, Function.update_of_ne hi] at htail
          have h1 : c0 i0 = c0 i ++ (tail ++ [bit]) := by
            rw [hi0_eq, htail, List.append_assoc]
          exact absurd (hc0_pref i i0 ⟨tail ++ [bit], h1⟩) hi
        · simp only [c', Function.update_of_ne hi, Function.update_of_ne hj] at htail
          exact hc0_pref i j ⟨tail, htail⟩
    have hcost_lt : cost c' < cost c0 := by
      dsimp only [cost]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0),
        ← Finset.add_sum_erase Finset.univ (fun i => w i * (c0 i).length) (Finset.mem_univ i0)]
      have hrest :
          (∑ i ∈ Finset.univ.erase i0, w i * (c' i).length) =
          ∑ i ∈ Finset.univ.erase i0, w i * (c0 i).length := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [show c' i = c0 i from Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
      rw [hrest]
      simp only [c', Function.update_self]
      have hlen_lt : parent.length < (c0 i0).length := by
        have h1 := congrArg List.length hi0_eq
        simp at h1
        omega
      have hwi0 : 0 < w i0 := hwpos i0
      have hmul_lt : w i0 * parent.length < w i0 * (c0 i0).length :=
        Nat.mul_lt_mul_of_pos_left hlen_lt hwi0
      omega
    have hle := hc0_opt c' hc'_pref
    omega
  rcases hsib with ⟨j0, hj0_eq⟩
  have hpair : ∃ u v : Fin m, u ≠ v ∧ c0 u = parent ++ [false] ∧ c0 v = parent ++ [true] ∧
      ∀ i, (c0 i).length ≤ (c0 u).length := by
    cases hbit : bit with
    | false =>
      rw [hbit] at hi0_eq hj0_eq
      simp only [Bool.not_false] at hj0_eq
      have hne_uv : i0 ≠ j0 := by
        intro h; subst h
        have := hi0_eq.symm.trans hj0_eq
        simp at this
      exact ⟨i0, j0, hne_uv, hi0_eq, hj0_eq, fun i => hi0_max i (Finset.mem_univ i)⟩
    | true =>
      rw [hbit] at hi0_eq hj0_eq
      simp only [Bool.not_true] at hj0_eq
      have hne_uv : j0 ≠ i0 := by
        intro h; subst h
        have := hi0_eq.symm.trans hj0_eq
        simp at this
      have hlen_eq : (c0 j0).length = (c0 i0).length := by
        rw [hj0_eq, hi0_eq]; simp
      exact ⟨j0, i0, hne_uv, hj0_eq, hi0_eq, fun i => by rw [hlen_eq]; exact hi0_max i (Finset.mem_univ i)⟩
  rcases hpair with ⟨u0, v0, huv0, hu0, hv0, hmax0⟩
  have hprep : ∃ (c1 : Fin m → List Bool) (u v : Fin m),
      prefixCode c1 ∧ cost c1 ≤ cost c0 ∧ u ≠ v ∧ u ≠ b ∧
      c1 u = parent ++ [false] ∧ c1 v = parent ++ [true] ∧
      ∀ i, (c1 i).length ≤ (c1 u).length := by
    by_cases hub : u0 = b
    · let c1 : Fin m → List Bool := fun i => c0 (Equiv.swap u0 v0 i)
      have hlen_uv : (c0 u0).length = (c0 v0).length := by rw [hu0, hv0]; simp
      refine ⟨c1, v0, u0, prefix_comp_perm c0 (Equiv.swap u0 v0) hc0_pref,
        le_of_eq (cost_swap_eq_of_len_eq w c0 u0 v0 hlen_uv), Ne.symm huv0,
        by rw [← hub]; exact Ne.symm huv0,
        by simp [c1, hu0], by simp [c1, hv0], fun i => ?_⟩
      simp only [c1, Equiv.swap_apply_right]
      exact hmax0 (Equiv.swap u0 v0 i)
    · exact ⟨c0, u0, v0, hc0_pref, le_refl _, huv0, hub, hu0, hv0, hmax0⟩
  rcases hprep with ⟨c1, u, v, hc1_pref, hc1_cost, huv, hub, hu1, hv1, hmax1⟩
  let c2 : Fin m → List Bool := fun i => c1 (Equiv.swap a u i)
  have hc2_pref : prefixCode c2 := prefix_comp_perm c1 (Equiv.swap a u) hc1_pref
  have hc2_cost : cost c2 ≤ cost c1 := by
    by_cases hau : a = u
    · subst hau; simp [c2]
    · exact cost_swap_le w c1 a u (hwmin u (Ne.symm hau) hub).1 (hmax1 a)
  have hc2_a : c2 a = parent ++ [false] := by simp [c2, hu1]
  have hmax2 : ∀ i, (c2 i).length ≤ (c2 a).length := fun i => by
    simp only [c2, Equiv.swap_apply_left]
    exact hmax1 (Equiv.swap a u i)
  let v' : Fin m := Equiv.swap a u v
  have hv'_ne_a : v' ≠ a := by
    intro h
    have h1 := congrArg (Equiv.swap a u) h
    simp only [v', Equiv.swap_apply_self, Equiv.swap_apply_left] at h1
    exact huv h1.symm
  have hc2_v' : c2 v' = parent ++ [true] := by
    simp only [c2, v', Equiv.swap_apply_self, hv1]
  have hlen_v' : (c2 v').length = (c2 a).length := by rw [hc2_v', hc2_a]; simp
  let c3 : Fin m → List Bool := fun i => c2 (Equiv.swap b v' i)
  have hc3_pref : prefixCode c3 := prefix_comp_perm c2 (Equiv.swap b v') hc2_pref
  have hc3_cost : cost c3 ≤ cost c2 := by
    by_cases hbv' : b = v'
    · subst hbv'; simp [c3]
    · refine cost_swap_le w c2 b v' (hwmin v' hv'_ne_a (Ne.symm hbv')).2 ?_
      rw [hlen_v']
      exact hmax2 b
  have hc3_a : c3 a = parent ++ [false] := by
    simp only [c3, Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hv'_ne_a), hc2_a]
  have hc3_b : c3 b = parent ++ [true] := by
    simp only [c3, Equiv.swap_apply_left, hc2_v']
  refine ⟨c3, parent, hc3_pref, hc3_a, hc3_b, fun i => ?_, fun other hother => ?_⟩
  · rw [hc3_a, ← hc2_a]
    exact hmax2 (Equiv.swap b v' i)
  · exact le_trans (le_trans (le_trans hc3_cost hc2_cost) hc1_cost) (hc0_opt other hother)
