import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1269

def chainOf {α : Type} (g : Finset α → α → Bool) : Nat → Finset α → Prop :=
  Nat.rec (motive := fun _ => Finset α → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)

lemma chainOf_mono {α : Type} {g : Finset α → α → Bool} {k : Nat} {x y : Finset α}
    (hxy : x ⊆ y) (h : chainOf g k x) : chainOf g k y := by
  cases k with
  | zero => trivial
  | succ k =>
    rcases h with ⟨u, v, j, hu, huv, hvx, hgu, hgv⟩
    exact ⟨u, v, j, hu, huv, Finset.Subset.trans hvx hxy, hgu, hgv⟩

lemma R_insert_le {α : Type} [DecidableEq α] {R : Finset α → Nat}
    (hRcard : ∀ x, R x ≤ x.card)
    (hRsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x : Finset α) (j : α) : R (insert j x) ≤ R x + 1 := by
  have h1 : insert j x = x ∪ {j} := by
    rw [Finset.union_comm, ← Finset.insert_eq]
  have h2 := hRsub x {j}
  have h3 := hRcard {j}
  simp only [Finset.card_singleton] at h3
  rw [h1]
  omega

lemma R_insert_eq_of_subset {α : Type} [DecidableEq α] {R : Finset α → Nat}
    (hRmono : Monotone R)
    (hRsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    {u v : Finset α} (j : α) (huv : u ⊆ v)
    (hu : R (insert j u) = R u) : R (insert j v) = R v := by
  have h1 : v ∪ insert j u = insert j v := by
    ext k
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · intro hk
      rcases hk with hkv | hkj | hku
      · exact Or.inr hkv
      · exact Or.inl hkj
      · exact Or.inr (huv hku)
    · intro hk
      rcases hk with hkj | hkv
      · exact Or.inr (Or.inl hkj)
      · exact Or.inl hkv
  have h2 : u ⊆ v ∩ insert j u := by
    intro k hk
    exact Finset.mem_inter.mpr ⟨huv hk, Finset.mem_insert_of_mem hk⟩
  have h3 := hRmono h2
  have h4 := hRsub v (insert j u)
  rw [h1, hu] at h4
  have h5 := hRmono (Finset.subset_insert j v)
  omega

lemma R_union_eq_of_forall_insert_eq {α : Type} [DecidableEq α] {R : Finset α → Nat}
    (hRmono : Monotone R)
    (hRsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x s : Finset α)
    (hs : ∀ j ∈ s, R (insert j x) = R x) : R (x ∪ s) = R x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' : R (x ∪ s) = R x := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    have ha_eq : R (insert a x) = R x := hs a (Finset.mem_insert_self a s)
    have hstep : R (insert a (x ∪ s)) = R (x ∪ s) :=
      R_insert_eq_of_subset hRmono hRsub a (Finset.subset_union_left (s₁ := x) (s₂ := s)) ha_eq
    rw [Finset.union_insert, hstep, ih']

lemma exists_gain_of_lt {α : Type} [DecidableEq α] {R : Finset α → Nat}
    (hRmono : Monotone R)
    (hRsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    {x y : Finset α} (hxy : x ⊆ y) (hlt : R x < R y) :
    ∃ j ∈ y, j ∉ x ∧ R x < R (insert j x) := by
  by_contra h
  have hall : ∀ j ∈ y, R (insert j x) = R x := by
    intro j hj
    by_cases hjx : j ∈ x
    · rw [Finset.insert_eq_of_mem hjx]
    · have hnlt : ¬ R x < R (insert j x) := fun hlt => h ⟨j, hj, hjx, hlt⟩
      have hge := hRmono (Finset.subset_insert j x)
      omega
  have hunion := R_union_eq_of_forall_insert_eq hRmono hRsub x y hall
  rw [Finset.union_eq_right.mpr hxy] at hunion
  omega

lemma exists_subset_rank {α : Type} [DecidableEq α] {R : Finset α → Nat}
    (hR0 : R ∅ = 0) (hRmono : Monotone R)
    (hRcard : ∀ x, R x ≤ x.card)
    (hRsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x : Finset α) : ∀ k ≤ R x, ∃ u ⊆ x, R u = k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨∅, Finset.empty_subset x, hR0⟩
  | succ k ih =>
    intro hk1
    rcases ih (by omega) with ⟨u, hux, hRu⟩
    rcases exists_gain_of_lt hRmono hRsub hux (by omega) with ⟨j, hjx, _, hlt⟩
    have hle := R_insert_le hRcard hRsub u j
    exact ⟨insert j u, Finset.insert_subset hjx hux, by omega⟩

end PEqualNP.Outside.L_lib_1269

theorem PEqualNP.Outside.L_lib_1269 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (R : Finset (Fin n) → Nat),
  R ∅ = 0 → Monotone R → (∀ x, R x ≤ x.card) →
  (∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) →
  let D := R Finset.univ
  let gain := fun (x : Finset (Fin n)) (j : Fin n) => decide (R x < R (insert j x))
  let runs := fun (g : Finset (Fin n) → Fin n → Bool) =>
    Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)
  (∀ g, (∀ x j, gain x j = true → g x j = true) → (∀ x j, j ∈ x → g x j = false) →
    runs g D Finset.univ ∧ (¬ runs g (D+1) Finset.univ ↔ g = gain)) ∧
  let Flag := {p : Fin n × Finset (Fin n) // p.1 ∉ p.2 ∧ R p.2 + 1 = D ∧
    ∀ j, j ∉ p.2 → R p.2 < R (insert j p.2)}
  let carrier := fun (v : Flag) => v.val.1
  let plane := fun (v : Flag) => v.val.2
  let sat := fun (x : Finset (Fin n)) => (Finset.univ : Finset Flag).filter (fun v => carrier v ∈ x)
  let fits := fun (g : Finset Flag → Flag → Bool) =>
    (∀ x j, (∀ v ∈ x, carrier v ∈ plane j) → g x j = true) ∧
    (∀ x j, j ∈ x → g x j = false)
  let walk := fun (g : Finset Flag → Flag → Bool) =>
    Nat.rec (motive := fun _ => Finset Flag → Prop) (fun _ => True)
      (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)
  (∃ g, fits g ∧ (∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true) ∧
    ¬ walk g (D+1) Finset.univ) ∧
  ∀ g, fits g → walk g D Finset.univ ∧
    (¬ walk g (D+1) Finset.univ → ∀ x j,
      (∃ v, carrier v = j ∧ g (sat x) v = true) ↔ gain x j = true)) := by
  intro n R hR0 hRmono hRcard hRsub
  let _ : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  intro D gain runs
  have hgain_true : ∀ x j, gain x j = true ↔ R x < R (insert j x) := fun x j =>
    @decide_eq_true_iff _ (Classical.propDecidable _)
  have hgain_false : ∀ x j, gain x j = false ↔ ¬ R x < R (insert j x) := fun x j =>
    @decide_eq_false_iff_not _ (Classical.propDecidable _)
  have hconj1 : ∀ g, (∀ x j, gain x j = true → g x j = true) →
      (∀ x j, j ∈ x → g x j = false) →
      runs g D Finset.univ ∧ (¬ runs g (D + 1) Finset.univ ↔ g = gain) := by
    intro g hg_gain hg_in
    have hruns_of_le_rank : ∀ k (x : Finset (Fin n)), k ≤ R x → runs g k x := by
      intro k
      induction k with
      | zero => intro _ _; trivial
      | succ k ih =>
        intro x hk1
        rcases PEqualNP.Outside.L_lib_1269.exists_subset_rank hR0 hRmono hRcard hRsub x k (by omega) with
          ⟨u, hux, hRu⟩
        rcases PEqualNP.Outside.L_lib_1269.exists_gain_of_lt hRmono hRsub hux (by omega) with
          ⟨j, hjx, _, hlt⟩
        refine ⟨u, insert j u, j, ih u (by omega), Finset.subset_insert j u,
          Finset.insert_subset hjx hux, hg_gain u j ((hgain_true u j).mpr hlt),
          hg_in (insert j u) j (Finset.mem_insert_self j u)⟩
    have hruns_gain_le_rank : ∀ k (x : Finset (Fin n)), runs gain k x → k ≤ R x := by
      intro k
      induction k with
      | zero => intro _ _; exact Nat.zero_le _
      | succ k ih =>
        intro x hx
        rcases hx with ⟨u, v, j, hu, huv, hvx, hgu, hgv⟩
        have hku := ih u hu
        have hlt := (hgain_true u j).mp hgu
        have hnlt := (hgain_false v j).mp hgv
        have hle1 := hRmono (Finset.subset_insert j v)
        have hle2 := hRmono (Finset.insert_subset_insert j huv)
        have hle3 := hRmono hvx
        omega
    have hruns_extend : ∀ d m (w : Finset (Fin n)), runs g m w → R w + d ≤ D →
        runs g (m + d) Finset.univ := by
      intro d
      induction d with
      | zero =>
        intro m w hmw _
        exact PEqualNP.Outside.L_lib_1269.chainOf_mono (Finset.subset_univ w) hmw
      | succ d ih =>
        intro m w hmw hwd
        rcases PEqualNP.Outside.L_lib_1269.exists_gain_of_lt hRmono hRsub (Finset.subset_univ w)
          (by omega) with ⟨j, _, _, hlt⟩
        have hle := PEqualNP.Outside.L_lib_1269.R_insert_le hRcard hRsub w j
        have hmv : runs g (m + 1) (insert j w) :=
          ⟨w, insert j w, j, hmw, Finset.subset_insert j w, Finset.Subset.refl _,
            hg_gain w j ((hgain_true w j).mpr hlt),
            hg_in (insert j w) j (Finset.mem_insert_self j w)⟩
        have hres := ih (m + 1) (insert j w) hmv (by omega)
        have heq_idx : m + 1 + d = m + (d + 1) := by omega
        rw [← heq_idx]
        exact hres
    refine ⟨hruns_of_le_rank D Finset.univ le_rfl, ?_⟩
    constructor
    · intro hnr
      funext x j
      cases hgx : gain x j with
      | true => exact hg_gain x j hgx
      | false =>
        cases hval : g x j with
        | false => rfl
        | true =>
          exfalso
          have hnlt := (hgain_false x j).mp hgx
          have hge := hRmono (Finset.subset_insert j x)
          have hRx_le : R x ≤ D := hRmono (Finset.subset_univ x)
          have hrun_x : runs g (R x) x := hruns_of_le_rank (R x) x le_rfl
          have hrun_v : runs g (R x + 1) (insert j x) :=
            ⟨x, insert j x, j, hrun_x, Finset.subset_insert j x, Finset.Subset.refl _,
              hval, hg_in (insert j x) j (Finset.mem_insert_self j x)⟩
          have hrun_ext := hruns_extend (D - R x) (R x + 1) (insert j x) hrun_v (by omega)
          have heq_idx : R x + 1 + (D - R x) = D + 1 := by omega
          rw [heq_idx] at hrun_ext
          exact hnr hrun_ext
    · intro heq hrun
      rw [heq] at hrun
      have hle := hruns_gain_le_rank (D + 1) Finset.univ hrun
      omega
  refine ⟨hconj1, ?_⟩
  intro Flag carrier plane sat fits walk
  let _ : DecidablePred (fun p : Fin n × Finset (Fin n) =>
      p.1 ∉ p.2 ∧ R p.2 + 1 = D ∧ ∀ j, j ∉ p.2 → R p.2 < R (insert j p.2)) :=
    fun p => Classical.propDecidable _
  have hflag_iff_gain : ∀ (x : Finset (Fin n)) (j : Fin n),
      (∃ v : Flag, carrier v = j ∧ x ⊆ plane v) ↔ gain x j = true := by
    intro x j
    rw [hgain_true]
    constructor
    · rintro ⟨v, hcv, hxp⟩
      by_contra hnlt
      have hge := hRmono (Finset.subset_insert j x)
      have heq_x : R (insert j x) = R x := by omega
      have heq_p := PEqualNP.Outside.L_lib_1269.R_insert_eq_of_subset hRmono hRsub j hxp heq_x
      dsimp only [plane] at heq_p
      have hv_lt := v.property.2.2 j (by simpa [carrier, hcv] using v.property.1)
      omega
    · intro hlt
      have hle_ins := PEqualNP.Outside.L_lib_1269.R_insert_le hRcard hRsub x j
      have hle_D : R (insert j x) ≤ D := hRmono (Finset.subset_univ (insert j x))
      have hext : ∀ d (y : Finset (Fin n)), x ⊆ y → R (insert j y) = R y + 1 →
          R y + 1 + d = D →
          ∃ y_star : Finset (Fin n), x ⊆ y_star ∧ R y_star + 1 = D ∧ R (insert j y_star) = D := by
        intro d
        induction d with
        | zero =>
          intro y hxy hRy hD
          exact ⟨y, hxy, by omega, by omega⟩
        | succ d ih =>
          intro y hxy hRy hD
          rcases PEqualNP.Outside.L_lib_1269.exists_gain_of_lt hRmono hRsub
            (Finset.subset_univ (insert j y)) (by omega) with ⟨k, _, _, hklt⟩
          have hcomm : insert k (insert j y) = insert j (insert k y) := Finset.insert_comm k j y
          rw [hcomm] at hklt
          have hle1 := PEqualNP.Outside.L_lib_1269.R_insert_le hRcard hRsub y k
          have hle2 := PEqualNP.Outside.L_lib_1269.R_insert_le hRcard hRsub (insert k y) j
          exact ih (insert k y) (Finset.Subset.trans hxy (Finset.subset_insert k y))
            (by omega) (by omega)
      rcases hext (D - (R x + 1)) x (Finset.Subset.refl x) (by omega) (by omega) with
        ⟨y_star, hxy_star, hRy_star, hRj_star⟩
      let H : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => R (insert i y_star) = R y_star)
      have hyH : y_star ⊆ H := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by rw [Finset.insert_eq_of_mem hi]⟩
      have hjH : j ∉ H := by
        intro hj
        have heq := (Finset.mem_filter.mp hj).2
        omega
      have hRH_eq : R H = R y_star := by
        have hu := PEqualNP.Outside.L_lib_1269.R_union_eq_of_forall_insert_eq hRmono hRsub y_star H
          (fun i hi => (Finset.mem_filter.mp hi).2)
        rw [Finset.union_eq_right.mpr hyH] at hu
        exact hu
      have hRH : R H + 1 = D := by omega
      have hH_max : ∀ i, i ∉ H → R H < R (insert i H) := by
        intro i hi
        have hne : R (insert i y_star) ≠ R y_star := fun heq =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩)
        have hge1 := hRmono (Finset.subset_insert i y_star)
        have hge2 := hRmono (Finset.insert_subset_insert i hyH)
        omega
      exact ⟨⟨(j, H), ⟨hjH, hRH, hH_max⟩⟩, rfl, Finset.Subset.trans hxy_star hyH⟩
  constructor
  · let g0 : Finset Flag → Flag → Bool := fun S v => gain (S.image carrier) (carrier v)
    have hg0_fits : fits g0 := by
      constructor
      · intro S v hS
        have hsub : S.image carrier ⊆ plane v := Finset.image_subset_iff.mpr hS
        exact (hflag_iff_gain (S.image carrier) (carrier v)).mp ⟨v, rfl, hsub⟩
      · intro S v hv
        have hmem : carrier v ∈ S.image carrier := Finset.mem_image_of_mem carrier hv
        exact (hgain_false (S.image carrier) (carrier v)).mpr (by
          rw [Finset.insert_eq_of_mem hmem]
          omega)
    have hg0_anti : ∀ S1 S2, S1 ⊆ S2 → ∀ v, g0 S2 v = true → g0 S1 v = true := by
      intro S1 S2 h12 v h2
      have hlt2 := (hgain_true (S2.image carrier) (carrier v)).mp h2
      refine (hgain_true (S1.image carrier) (carrier v)).mpr ?_
      by_contra hnlt1
      have hge1 := hRmono (Finset.subset_insert (carrier v) (S1.image carrier))
      have heq1 : R (insert (carrier v) (S1.image carrier)) = R (S1.image carrier) := by omega
      have heq2 := PEqualNP.Outside.L_lib_1269.R_insert_eq_of_subset hRmono hRsub (carrier v)
        (Finset.image_subset_image h12) heq1
      omega
    have hwalk_g0_le : ∀ k (S : Finset Flag), walk g0 k S → k ≤ R (S.image carrier) := by
      intro k
      induction k with
      | zero => intro _ _; exact Nat.zero_le _
      | succ k ih =>
        intro S hS
        rcases hS with ⟨U, V, v, hU, hUV, hVS, hgU, hgV⟩
        have hkU := ih U hU
        have hltU := (hgain_true (U.image carrier) (carrier v)).mp hgU
        have hnltV := (hgain_false (V.image carrier) (carrier v)).mp hgV
        have hle1 := hRmono (Finset.subset_insert (carrier v) (V.image carrier))
        have hle2 := hRmono (Finset.insert_subset_insert (carrier v)
          (Finset.image_subset_image (f := carrier) hUV))
        have hle3 := hRmono (Finset.image_subset_image (f := carrier) hVS)
        omega
    refine ⟨g0, hg0_fits, hg0_anti, ?_⟩
    intro hwalk
    have hle1 := hwalk_g0_le (D + 1) Finset.univ hwalk
    have hle2 : R ((Finset.univ : Finset Flag).image carrier) ≤ D := hRmono (Finset.subset_univ _)
    omega
  · intro g hfit
    rcases hfit with ⟨hfit_pos, hfit_in⟩
    let g_down : Finset (Fin n) → Fin n → Bool :=
      fun x j => @decide (∃ v : Flag, carrier v = j ∧ g (sat x) v = true) (Classical.propDecidable _)
    have hg_down_true : ∀ x j, g_down x j = true ↔ ∃ v : Flag, carrier v = j ∧ g (sat x) v = true :=
      fun x j => @decide_eq_true_iff _ (Classical.propDecidable _)
    have hg_down_false : ∀ x j, g_down x j = false ↔ ¬ ∃ v : Flag, carrier v = j ∧ g (sat x) v = true :=
      fun x j => @decide_eq_false_iff_not _ (Classical.propDecidable _)
    have hmem_sat : ∀ {x : Finset (Fin n)} {v : Flag}, v ∈ sat x ↔ carrier v ∈ x := by
      intro x v
      dsimp only [sat]
      rw [@Finset.mem_filter _ _ (fun a => Classical.propDecidable _)]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩
    have hg_down_gain : ∀ x j, gain x j = true → g_down x j = true := by
      intro x j hgx
      rcases (hflag_iff_gain x j).mpr hgx with ⟨v, hcv, hxp⟩
      refine (hg_down_true x j).mpr ⟨v, hcv, hfit_pos (sat x) v ?_⟩
      intro w hw
      exact hxp (hmem_sat.mp hw)
    have hg_down_in : ∀ x j, j ∈ x → g_down x j = false := by
      intro x j hjx
      refine (hg_down_false x j).mpr ?_
      rintro ⟨v, hcv, hgv⟩
      have hv_mem : v ∈ sat x := hmem_sat.mpr (by rw [hcv]; exact hjx)
      have hv_false := hfit_in (sat x) v hv_mem
      rw [hv_false] at hgv
      cases hgv
    have hsat_mono : ∀ {x y : Finset (Fin n)}, x ⊆ y → sat x ⊆ sat y := by
      intro x y hxy w hw
      exact hmem_sat.mpr (hxy (hmem_sat.mp hw))
    have hruns_to_walk : ∀ k (x : Finset (Fin n)), runs g_down k x → walk g k (sat x) := by
      intro k
      induction k with
      | zero => intro _ _; trivial
      | succ k ih =>
        intro x hx
        rcases hx with ⟨u, v, j, hu, huv, hvx, hgu, hgv⟩
        rcases (hg_down_true u j).mp hgu with ⟨vf, hcv, hgf_u⟩
        have hnot_v := (hg_down_false v j).mp hgv
        have hgf_v : g (sat v) vf = false := by
          cases hval : g (sat v) vf with
          | false => rfl
          | true => exact False.elim (hnot_v ⟨vf, hcv, hval⟩)
        exact ⟨sat u, sat v, vf, ih u hu, hsat_mono huv, hsat_mono hvx, hgf_u, hgf_v⟩
    have hwalk_mono : ∀ (k : Nat) {S1 S2 : Finset Flag}, S1 ⊆ S2 → walk g k S1 → walk g k S2 :=
      fun k _ _ hS h => PEqualNP.Outside.L_lib_1269.chainOf_mono (g := g) (k := k) hS h
    have h1 := hconj1 g_down hg_down_gain hg_down_in
    refine ⟨hwalk_mono D (Finset.subset_univ (sat Finset.univ)) (hruns_to_walk D Finset.univ h1.1), ?_⟩
    intro hno_walk x j
    have hno_runs : ¬ runs g_down (D + 1) Finset.univ := fun hr =>
      hno_walk (hwalk_mono (D + 1) (Finset.subset_univ (sat Finset.univ))
        (hruns_to_walk (D + 1) Finset.univ hr))
    have heq : g_down = gain := h1.2.mp hno_runs
    have hxj : g_down x j = gain x j := congrFun (congrFun heq x) j
    rw [← hg_down_true x j, hxj]
