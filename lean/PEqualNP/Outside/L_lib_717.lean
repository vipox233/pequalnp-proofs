import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_717_aux

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

private lemma half_mul_sub_half (N : ℕ) :
    (N / 2) * (N - N / 2) = N ^ 2 / 4 := by
  have hmod : N % 2 = 0 ∨ N % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · have hq : 4 * ((N / 2) * (N - N / 2)) = N ^ 2 := by
      have ha : N = 2 * (N / 2) := by omega
      have hb : N - N / 2 = N / 2 := by omega
      nlinarith
    omega
  · have hq : 4 * ((N / 2) * (N - N / 2)) + 1 = N ^ 2 := by
      have ha : N = 2 * (N / 2) + 1 := by omega
      have hb : N - N / 2 = N / 2 + 1 := by omega
      nlinarith
    omega

private lemma prod_le_sq_div_four (N d : ℕ) (hd : d ≤ N) :
    (N - d) * d ≤ N ^ 2 / 4 := by
  have h4 : 4 * ((N - d) * d) ≤ N ^ 2 := by
    zify [hd]
    nlinarith [sq_nonneg ((N : ℤ) - 2 * (d : ℤ))]
  omega

private lemma prod_eq_sq_div_four_iff (N d : ℕ) (hd : d ≤ N)
    (hEq : (N - d) * d = N ^ 2 / 4) :
    d = N / 2 ∨ N - d = N / 2 := by
  have hmod : N ^ 2 % 4 ≤ 1 := by
    have h2 : N % 2 = 0 ∨ N % 2 = 1 := by omega
    rcases h2 with h0 | h1
    · set k := N / 2
      have hN : N = 2 * k := by omega
      rw [hN, show (2 * k) ^ 2 = 4 * (k * k) by ring]
      omega
    · set k := N / 2
      have hN : N = 2 * k + 1 := by omega
      rw [hN, show (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 by ring]
      omega
  have h4 : N ^ 2 ≤ 4 * ((N - d) * d) + 1 := by omega
  have hdiff : ((N : ℤ) - 2 * (d : ℤ)) ^ 2 ≤ 1 := by
    zify [hd] at h4
    nlinarith
  have h1 : -1 ≤ (N : ℤ) - 2 * (d : ℤ) ∧ (N : ℤ) - 2 * (d : ℤ) ≤ 1 := by
    constructor <;> nlinarith
  omega

private lemma mantel_dirEdges {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ a b, adj a b → adj b a) (hirr : ∀ a, ¬ adj a a)
    (U : Finset (Fin n)) (htf : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, adj a b → adj b d → ¬ adj d a) :
    let Edir := ((U ×ˢ U).filter (fun p => adj p.1 p.2)).card
    Edir ≤ 2 * (U.card ^ 2 / 4) ∧
    (Edir = 2 * (U.card ^ 2 / 4) →
      ∃ A : Finset (Fin n), A ⊆ U ∧ A.card = U.card / 2 ∧
        ∀ i ∈ U, ∀ j ∈ U, i ≠ j → (adj i j ↔ (i ∈ A ∧ j ∉ A) ∨ (i ∉ A ∧ j ∈ A))) := by
  intro Edir
  by_cases hUemp : U = ∅
  · subst hUemp
    refine ⟨by simp [Edir], fun _ => ⟨∅, by simp, by simp, fun i hi => by simp at hi⟩⟩
  · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUemp
    let deg : Fin n → ℕ := fun u => (U.filter (fun w => adj u w)).card
    have hEdir_sum : Edir = ∑ u ∈ U, deg u := by
      dsimp only [Edir, deg]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    obtain ⟨v, hvU, hvmax⟩ := Finset.exists_max_image U deg hUne
    set d := deg v
    let S : Finset (Fin n) := U.filter (fun w => adj v w)
    let T : Finset (Fin n) := U \ S
    have hSsub : S ⊆ U := Finset.filter_subset _ _
    have hTsub : T ⊆ U := Finset.sdiff_subset
    have hScard : S.card = d := rfl
    have hTcard : T.card = U.card - d := by
      rw [Finset.card_sdiff_of_subset hSsub, hScard]
    have hd_le : d ≤ U.card := by
      rw [← hScard]; exact Finset.card_le_card hSsub
    have hSind : ∀ x ∈ S, ∀ y ∈ S, ¬ adj x y := by
      intro x hx y hy hxy
      exact htf v hvU x (hSsub hx) y (hSsub hy) (Finset.mem_filter.mp hx).2 hxy
        (hsymm v y (Finset.mem_filter.mp hy).2)
    have hST_sum : ∑ u ∈ S, deg u = ((S ×ˢ T).filter (fun p => adj p.1 p.2)).card := by
      have hpt : ∀ u ∈ S, deg u = (T.filter (fun w => adj u w)).card := by
        intro u hu
        dsimp only [deg]
        congr 1
        ext w
        simp only [T, Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hwU, huw⟩
          exact ⟨⟨hwU, fun hwS => hSind u hu w hwS huw⟩, huw⟩
        · rintro ⟨⟨hwU, _⟩, huw⟩
          exact ⟨hwU, huw⟩
      rw [Finset.sum_congr rfl hpt]
      rw [Finset.card_filter]
      rw [Finset.sum_product (s := S) (t := T) (f := fun p : Fin n × Fin n => if adj p.1 p.2 then 1 else 0)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.card_filter]
    have hTS_card : ((S ×ˢ T).filter (fun p => adj p.1 p.2)).card =
        ((T ×ˢ S).filter (fun p => adj p.1 p.2)).card := by
      have heq : (T ×ˢ S).filter (fun p => adj p.1 p.2) =
          ((S ×ˢ T).filter (fun p => adj p.1 p.2)).image Prod.swap := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.exists, Prod.swap_prod_mk]
        constructor
        · rintro ⟨⟨hp1, hp2⟩, hadj⟩
          exact ⟨p.2, p.1, ⟨⟨hp2, hp1⟩, hsymm _ _ hadj⟩, Prod.ext rfl rfl⟩
        · rintro ⟨a, b, ⟨⟨ha, hb⟩, hadj⟩, hEq⟩
          cases hEq
          exact ⟨⟨hb, ha⟩, hsymm _ _ hadj⟩
      rw [heq, Finset.card_image_of_injective _ Prod.swap_injective]
    have hT_split : ∑ u ∈ T, deg u =
        ((T ×ˢ S).filter (fun p => adj p.1 p.2)).card +
        ((T ×ˢ T).filter (fun p => adj p.1 p.2)).card := by
      have hpt : ∀ u ∈ T, deg u = (S.filter (fun w => adj u w)).card + (T.filter (fun w => adj u w)).card := by
        intro u _
        dsimp only [deg]
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext w
          simp only [T, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
          by_cases hwS : w ∈ S
          · simp [hwS, hSsub hwS]
          · simp [hwS]
        · rw [Finset.disjoint_left]
          intro w h1 h2
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h2).1).2 (Finset.mem_filter.mp h1).1
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      · rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hEdir_split : Edir = (∑ u ∈ S, deg u) + ∑ u ∈ T, deg u := by
      rw [hEdir_sum, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hSsub]
    have hTdeg_le : ∑ u ∈ T, deg u ≤ (U.card - d) * d := by
      calc
        ∑ u ∈ T, deg u ≤ ∑ _u ∈ T, d := Finset.sum_le_sum fun u hu => hvmax u (hTsub hu)
        _ = (U.card - d) * d := by rw [Finset.sum_const, smul_eq_mul, hTcard]
    have hprod_le : (U.card - d) * d ≤ U.card ^ 2 / 4 := prod_le_sq_div_four U.card d hd_le
    refine ⟨by omega, ?_⟩
    intro hEq
    have hTT_zero : ((T ×ˢ T).filter (fun p => adj p.1 p.2)).card = 0 := by omega
    have hTdeg_eq : ∑ u ∈ T, deg u = (U.card - d) * d := by omega
    have hprod_eq : (U.card - d) * d = U.card ^ 2 / 4 := by omega
    have hTind : ∀ x ∈ T, ∀ y ∈ T, ¬ adj x y := by
      intro x hx y hy hxy
      have hmem : (x, y) ∈ (T ×ˢ T).filter (fun p => adj p.1 p.2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩
      have hpos := Finset.card_pos.mpr ⟨(x, y), hmem⟩
      omega
    have hTS_all : ∀ x ∈ T, ∀ y ∈ S, adj x y := by
      have hdeg_all : ∀ u ∈ T, deg u = d := by
        intro u hu
        by_contra hne
        have hlt : deg u < d := lt_of_le_of_ne (hvmax u (hTsub hu)) hne
        have hsum_lt : ∑ w ∈ T, deg w < ∑ _w ∈ T, d :=
          Finset.sum_lt_sum (fun w hw => hvmax w (hTsub hw)) ⟨u, hu, hlt⟩
        rw [Finset.sum_const, smul_eq_mul, hTcard] at hsum_lt
        omega
      intro x hx y hy
      have hsub : U.filter (fun w => adj x w) ⊆ S := by
        intro w hw
        rcases Finset.mem_filter.mp hw with ⟨hwU, hxw⟩
        by_contra hnotS
        exact hTind x hx w (Finset.mem_sdiff.mpr ⟨hwU, hnotS⟩) hxw
      have hcard_eq : (U.filter (fun w => adj x w)).card = S.card := by
        rw [hScard]; exact hdeg_all x hx
      have hEqSet : U.filter (fun w => adj x w) = S :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
      rw [← hEqSet] at hy
      exact (Finset.mem_filter.mp hy).2
    have hbij_ST : ∀ i ∈ U, ∀ j ∈ U, i ≠ j →
        (adj i j ↔ (i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S)) := by
      intro i hi j hj _
      by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S
      · simp [hiS, hjS, hSind i hiS j hjS]
      · have hjT : j ∈ T := Finset.mem_sdiff.mpr ⟨hj, hjS⟩
        simp [hiS, hjS, hsymm j i (hTS_all j hjT i hiS)]
      · have hiT : i ∈ T := Finset.mem_sdiff.mpr ⟨hi, hiS⟩
        simp [hiS, hjS, hTS_all i hiT j hjS]
      · have hiT : i ∈ T := Finset.mem_sdiff.mpr ⟨hi, hiS⟩
        have hjT : j ∈ T := Finset.mem_sdiff.mpr ⟨hj, hjS⟩
        simp [hiS, hjS, hTind i hiT j hjT]
    rcases prod_eq_sq_div_four_iff U.card d hd_le hprod_eq with hd_half | hTd_half
    · exact ⟨S, hSsub, by rw [hScard, hd_half], hbij_ST⟩
    · refine ⟨T, hTsub, by rw [hTcard, hTd_half], ?_⟩
      intro i hi j hj hij
      rw [hbij_ST i hi j hj hij]
      have hmemT : ∀ x ∈ U, (x ∈ T ↔ x ∉ S) := fun x hx => by simp [T, hx]
      rw [hmemT i hi, hmemT j hj]
      tauto

end PEqualNP.Outside.L_lib_717_aux

theorem PEqualNP.Outside.L_lib_717 : (∀ n : Nat, 0 < n →
  let V := Fin n → ZMod 2
  let unit := fun (i j : Fin n) => if j = i then (1 : ZMod 2) else 0
  let arc := fun (c : V) (z : Fin n → V) (i j : Fin n) =>
    i ≠ j ∧ c + z i + z j = unit i
  let total := fun (c : V) (z : Fin n → V) =>
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => arc c z p.1 p.2)).card
  let m := n - 1 + (n - 1)^2 / 4
  (∀ c z, total c z ≤ m) ∧ (∃ c z, total c z = m) ∧
    ∀ c z, total c z = m →
      ∃ (t : Fin n) (A : Finset (Fin n)), t ∉ A ∧ A.card = (n-1)/2 ∧
        (∀ i, i ≠ t → arc c z t i ∨ arc c z i t) ∧
        ∀ i j, i ≠ t → j ≠ t → i ≠ j →
          ((arc c z i j ∨ arc c z j i) ↔ ((i ∈ A ∧ j ∉ A) ∨ (i ∉ A ∧ j ∈ A)))) := by
  classical
  intro n hn V unit arc total m
  have hunit_ne : ∀ i j : Fin n, i ≠ j → unit i ≠ unit j := by
    intro i j hij hEq
    have hv := congrFun hEq i
    dsimp only [unit] at hv
    simp only [↓reduceIte, hij] at hv
    exact absurd hv (by decide)
  have harc_asym : ∀ c z i j, arc c z i j → ¬ arc c z j i := by
    intro c z i j h1 h2
    have hEq : unit i = unit j := by
      rw [← h1.2, ← h2.2]; abel
    exact hunit_ne i j h1.1 hEq
  have hmain : ∀ c z, total c z ≤ m ∧
      (total c z = m →
        ∃ (t : Fin n) (A : Finset (Fin n)), t ∉ A ∧ A.card = (n - 1) / 2 ∧
          (∀ i, i ≠ t → arc c z t i ∨ arc c z i t) ∧
          ∀ i j, i ≠ t → j ≠ t → i ≠ j →
            ((arc c z i j ∨ arc c z j i) ↔ ((i ∈ A ∧ j ∉ A) ∨ (i ∉ A ∧ j ∈ A)))) := by
    intro c z
    let adj : Fin n → Fin n → Prop := fun i j => arc c z i j ∨ arc c z j i
    have hsymm : ∀ a b, adj a b → adj b a := fun a b h => h.symm
    have hirr : ∀ a, ¬ adj a a := by
      intro a h; rcases h with h | h <;> exact h.1 rfl
    have h2tot : 2 * total c z = (Finset.univ.filter (fun p : Fin n × Fin n => adj p.1 p.2)).card := by
      let A1 := Finset.univ.filter (fun p : Fin n × Fin n => arc c z p.1 p.2)
      let A2 := Finset.univ.filter (fun p : Fin n × Fin n => arc c z p.2 p.1)
      have hdisj : Disjoint A1 A2 := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        exact harc_asym c z p.1 p.2 (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hunion : A1 ∪ A2 = Finset.univ.filter (fun p : Fin n × Fin n => adj p.1 p.2) := by
        ext p; simp [A1, A2, adj]
      have hA2 : A2.card = A1.card := by
        have hEq : A2 = A1.image Prod.swap := by
          ext p
          simp only [A1, A2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Prod.exists, Prod.swap_prod_mk]
          constructor
          · intro h; exact ⟨p.2, p.1, h, Prod.ext rfl rfl⟩
          · rintro ⟨a, b, h, hEq⟩; cases hEq; exact h
        rw [hEq, Finset.card_image_of_injective _ Prod.swap_injective]
      rw [← hunion, Finset.card_union_of_disjoint hdisj, hA2]
      change 2 * A1.card = A1.card + A1.card
      ring
    have htri : ∀ a b d : Fin n, adj a b → adj b d → adj d a →
        ∃ x1 x2 x3 : Fin n, (x1 = a ∨ x1 = b) ∧ (x2 = b ∨ x2 = d) ∧ (x3 = d ∨ x3 = a) ∧
          c = unit x1 + unit x2 + unit x3 := by
      intro a b d hab hbd hda
      have h1 : ∃ x1, (x1 = a ∨ x1 = b) ∧ c + z a + z b = unit x1 := by
        rcases hab with h | h
        · exact ⟨a, Or.inl rfl, h.2⟩
        · exact ⟨b, Or.inr rfl, by rw [← h.2]; abel⟩
      have h2 : ∃ x2, (x2 = b ∨ x2 = d) ∧ c + z b + z d = unit x2 := by
        rcases hbd with h | h
        · exact ⟨b, Or.inl rfl, h.2⟩
        · exact ⟨d, Or.inr rfl, by rw [← h.2]; abel⟩
      have h3 : ∃ x3, (x3 = d ∨ x3 = a) ∧ c + z d + z a = unit x3 := by
        rcases hda with h | h
        · exact ⟨d, Or.inl rfl, h.2⟩
        · exact ⟨a, Or.inr rfl, by rw [← h.2]; abel⟩
      rcases h1 with ⟨x1, hx1, he1⟩
      rcases h2 with ⟨x2, hx2, he2⟩
      rcases h3 with ⟨x3, hx3, he3⟩
      refine ⟨x1, x2, x3, hx1, hx2, hx3, ?_⟩
      funext u
      have e1 : c u + z a u + z b u = unit x1 u := congrFun he1 u
      have e2 : c u + z b u + z d u = unit x2 u := congrFun he2 u
      have e3 : c u + z d u + z a u = unit x3 u := congrFun he3 u
      have h20 := PEqualNP.Outside.L_lib_717_aux.zmod2_add_self
      change c u = unit x1 u + unit x2 u + unit x3 u
      calc
        c u = (c u + c u) + c u + (z a u + z a u) + (z b u + z b u) + (z d u + z d u) := by
              rw [h20 (c u), h20 (z a u), h20 (z b u), h20 (z d u)]; ring
        _ = (c u + z a u + z b u) + (c u + z b u + z d u) + (c u + z d u + z a u) := by ring
        _ = unit x1 u + unit x2 u + unit x3 u := by rw [e1, e2, e3]
    let t : Fin n :=
      if h : ∃ u : Fin n, c u = 1 then Classical.choose h else ⟨0, hn⟩
    let U : Finset (Fin n) := Finset.univ.erase t
    have hUcard : U.card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
    have htf : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, adj a b → adj b d → ¬ adj d a := by
      intro a ha b hb d hd hab hbd hda
      obtain ⟨x1, x2, x3, hx1, hx2, hx3, hc_eq⟩ := htri a b d hab hbd hda
      have hsum_c : ∑ u : Fin n, c u = 1 := by
        rw [hc_eq]
        have hunit_sum : ∀ x : Fin n, ∑ u : Fin n, unit x u = 1 := by
          intro x; simp [unit]
        simp only [Pi.add_apply, Finset.sum_add_distrib, hunit_sum]
        decide
      have hex1 : ∃ u : Fin n, c u = 1 := by
        by_contra hall
        push Not at hall
        have h0 : ∑ u : Fin n, c u = 0 := by
          refine Finset.sum_eq_zero fun u _ => ?_
          generalize hcu : c u = v
          fin_cases v
          · rfl
          · exact absurd hcu (hall u)
        rw [h0] at hsum_c
        exact absurd hsum_c (by decide)
      have hct : c t = 1 := by
        dsimp only [t]
        simp only [hex1, ↓reduceDIte]
        exact Classical.choose_spec hex1
      have hct_eq : c t = unit x1 t + unit x2 t + unit x3 t := congrFun hc_eq t
      rw [hct] at hct_eq
      have hta : t ≠ a := (Finset.mem_erase.mp ha).1.symm
      have htb : t ≠ b := (Finset.mem_erase.mp hb).1.symm
      have htd : t ≠ d := (Finset.mem_erase.mp hd).1.symm
      have hzero_x : ∀ x : Fin n, (x = a ∨ x = b ∨ x = d) → unit x t = 0 := by
        intro x hx
        dsimp only [unit]
        have hne : t ≠ x := by rcases hx with rfl | rfl | rfl <;> assumption
        simp [hne]
      have hu1 : unit x1 t = 0 := hzero_x x1 (hx1.elim Or.inl (fun h => Or.inr (Or.inl h)))
      have hu2 : unit x2 t = 0 := hzero_x x2 (hx2.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
      have hu3 : unit x3 t = 0 := hzero_x x3 (hx3.elim (fun h => Or.inr (Or.inr h)) Or.inl)
      rw [hu1, hu2, hu3] at hct_eq
      exact absurd hct_eq (by decide)
    have hsplit_all : (Finset.univ.filter (fun p : Fin n × Fin n => adj p.1 p.2)).card =
        2 * (U.filter (fun i => adj t i)).card + ((U ×ˢ U).filter (fun p => adj p.1 p.2)).card := by
      let Eall := Finset.univ.filter (fun p : Fin n × Fin n => adj p.1 p.2)
      let E1 := Eall.filter (fun p => p.1 = t)
      let E2 := Eall.filter (fun p => p.2 = t)
      let E3 := (U ×ˢ U).filter (fun p => adj p.1 p.2)
      have hd12 : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        have a1 := (Finset.mem_filter.mp h1).2
        have a2 := (Finset.mem_filter.mp h2).2
        have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
        rw [a1, a2] at ha
        exact hirr t ha
      have hd13 : Disjoint E1 E3 := by
        rw [Finset.disjoint_left]
        intro p h1 h3
        exact (Finset.mem_erase.mp (Finset.mem_product.mp (Finset.mem_filter.mp h3).1).1).1
          (Finset.mem_filter.mp h1).2
      have hd23 : Disjoint E2 E3 := by
        rw [Finset.disjoint_left]
        intro p h2 h3
        exact (Finset.mem_erase.mp (Finset.mem_product.mp (Finset.mem_filter.mp h3).1).2).1
          (Finset.mem_filter.mp h2).2
      have hunion : E1 ∪ E2 ∪ E3 = Eall := by
        ext p
        simp only [E1, E2, E3, Eall, U, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        by_cases h1 : p.1 = t <;> by_cases h2 : p.2 = t <;> simp [h1, h2]
      have hE1_card : E1.card = (U.filter (fun i => adj t i)).card := by
        refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpE, hp1⟩
          have hadj := (Finset.mem_filter.mp hpE).2
          rw [hp1] at hadj
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hirr t (h ▸ hadj), Finset.mem_univ _⟩, hadj⟩
        · intro p1 hp1 p2 hp2 hEq
          exact Prod.ext ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm) hEq
        · intro i hi
          rcases Finset.mem_filter.mp hi with ⟨_, hadj⟩
          exact ⟨(t, i), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩, rfl⟩
      have hE2_card : E2.card = (U.filter (fun i => adj t i)).card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpE, hp2⟩
          have hadj := (Finset.mem_filter.mp hpE).2
          rw [hp2] at hadj
          have hadj' := hsymm _ _ hadj
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hirr t (h ▸ hadj'), Finset.mem_univ _⟩, hadj'⟩
        · intro p1 hp1 p2 hp2 hEq
          exact Prod.ext hEq ((Finset.mem_filter.mp hp1).2.trans (Finset.mem_filter.mp hp2).2.symm)
        · intro i hi
          rcases Finset.mem_filter.mp hi with ⟨_, hadj⟩
          exact ⟨(i, t), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm _ _ hadj⟩, rfl⟩, rfl⟩
      change Eall.card = 2 * (U.filter (fun i => adj t i)).card + E3.card
      rw [← hunion, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12, hE1_card, hE2_card]
      ring
    have hdeg_t_le : (U.filter (fun i => adj t i)).card ≤ n - 1 := by
      rw [← hUcard]; exact Finset.card_le_card (Finset.filter_subset _ _)
    have hmantel := PEqualNP.Outside.L_lib_717_aux.mantel_dirEdges adj hsymm hirr U htf
    dsimp only at hmantel
    rw [hUcard] at hmantel
    have hle : total c z ≤ m := by
      dsimp only [m]
      omega
    refine ⟨hle, ?_⟩
    intro hEq
    have hdeg_t_eq : (U.filter (fun i => adj t i)).card = n - 1 := by dsimp only [m] at hEq; omega
    have hEdir_eq : ((U ×ˢ U).filter (fun p => adj p.1 p.2)).card = 2 * ((n - 1) ^ 2 / 4) := by
      dsimp only [m] at hEq; omega
    obtain ⟨A, hAsub, hAcard, hAadj⟩ := hmantel.2 hEdir_eq
    have ht_notA : t ∉ A := fun h => (Finset.mem_erase.mp (hAsub h)).1 rfl
    have hdeg_all : ∀ i : Fin n, i ≠ t → adj t i := by
      have hEqSet : U.filter (fun i => adj t i) = U :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hUcard, hdeg_t_eq])
      intro i hi
      have hiU : i ∈ U := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      rw [← hEqSet] at hiU
      exact (Finset.mem_filter.mp hiU).2
    refine ⟨t, A, ht_notA, hAcard, hdeg_all, ?_⟩
    intro i j hi hj hij
    exact hAadj i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
      j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) hij
  refine ⟨fun c z => (hmain c z).1, ?_, fun c z => (hmain c z).2⟩
  let t : Fin n := ⟨0, hn⟩
  let U : Finset (Fin n) := Finset.univ.erase t
  have hUcard : U.card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (s := U) (n := (n - 1) / 2) (by omega)
  let B : Finset (Fin n) := U \ A
  have hBcard : B.card = (n - 1) - (n - 1) / 2 := by
    rw [Finset.card_sdiff_of_subset hAsub, hUcard, hAcard]
  let c : V := unit t
  let z : Fin n → V := fun i => if i ∈ A then unit t + unit i else 0
  refine ⟨c, z, le_antisymm (hmain c z).1 ?_⟩
  let S1 : Finset (Fin n × Fin n) := A.image (fun i => (i, t))
  let S2 : Finset (Fin n × Fin n) := B.image (fun j => (t, j))
  let S3 : Finset (Fin n × Fin n) := A ×ˢ B
  have ht_notA : t ∉ A := fun h => (Finset.mem_erase.mp (hAsub h)).1 rfl
  have ht_notB : t ∉ B := fun h => (Finset.mem_erase.mp (Finset.sdiff_subset h)).1 rfl
  have hAB_disj : Disjoint A B := Finset.disjoint_sdiff
  have hS1_sub : S1 ⊆ Finset.univ.filter (fun p : Fin n × Fin n => arc c z p.1 p.2) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hiA, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h; dsimp only at h; rw [h] at hiA; exact ht_notA hiA
    · dsimp only [c, z]
      rw [if_pos hiA, if_neg ht_notA, add_zero]
      funext u
      change unit t u + (unit t u + unit i u) = unit i u
      have h20 := PEqualNP.Outside.L_lib_717_aux.zmod2_add_self (unit t u)
      calc
        unit t u + (unit t u + unit i u) = (unit t u + unit t u) + unit i u := by ring
        _ = unit i u := by rw [h20, zero_add]
  have hS2_sub : S2 ⊆ Finset.univ.filter (fun p : Fin n × Fin n => arc c z p.1 p.2) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, hjB, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h; dsimp only at h; rw [← h] at hjB; exact ht_notB hjB
    · have hj_notA : j ∉ A := (Finset.mem_sdiff.mp hjB).2
      dsimp only [c, z]
      rw [if_neg ht_notA, if_neg hj_notA, add_zero, add_zero]
  have hS3_sub : S3 ⊆ Finset.univ.filter (fun p : Fin n × Fin n => arc c z p.1 p.2) := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hiA, hjB⟩
    have hj_notA : p.2 ∉ A := (Finset.mem_sdiff.mp hjB).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h; rw [h] at hiA; exact hj_notA hiA
    · dsimp only [c, z]
      rw [if_pos hiA, if_neg hj_notA, add_zero]
      funext u
      change unit t u + (unit t u + unit p.1 u) = unit p.1 u
      have h20 := PEqualNP.Outside.L_lib_717_aux.zmod2_add_self (unit t u)
      calc
        unit t u + (unit t u + unit p.1 u) = (unit t u + unit t u) + unit p.1 u := by ring
        _ = unit p.1 u := by rw [h20, zero_add]
  have hd12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, hiA, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j, _, hEq⟩
    have := congrArg Prod.fst hEq
    dsimp only at this
    rw [← this] at hiA
    exact ht_notA hiA
  have hd13 : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro p h1 h3
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    exact ht_notB (Finset.mem_product.mp h3).2
  have hd23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro p h2 h3
    rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
    exact ht_notA (Finset.mem_product.mp h3).1
  have hS1_card : S1.card = A.card := Finset.card_image_of_injective A (fun _ _ h => congrArg Prod.fst h)
  have hS2_card : S2.card = B.card := Finset.card_image_of_injective B (fun _ _ h => congrArg Prod.snd h)
  have hS3_card : S3.card = A.card * B.card := Finset.card_product A B
  have hcard_union : (S1 ∪ S2 ∪ S3).card = m := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
      Finset.card_union_of_disjoint hd12, hS1_card, hS2_card, hS3_card, hAcard, hBcard]
    have hhalf := PEqualNP.Outside.L_lib_717_aux.half_mul_sub_half (n - 1)
    rw [hhalf]
    dsimp only [m]
    omega
  rw [← hcard_union]
  exact Finset.card_le_card (Finset.union_subset (Finset.union_subset hS1_sub hS2_sub) hS3_sub)
