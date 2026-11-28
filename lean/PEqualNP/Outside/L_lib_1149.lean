import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1149_aux

def Str {n m : ℕ} (a b : Fin m → Fin n) (i : Fin m) : Prop :=
  ∀ S : Finset (Fin n), ¬ (a i ∈ S ↔ b i ∈ S) →
    ∃ k1 k2 : Fin m, k1 ≠ i ∧ k2 ≠ i ∧ k1 ≠ k2 ∧
      ¬ (a k1 ∈ S ↔ b k1 ∈ S) ∧ ¬ (a k2 ∈ S ↔ b k2 ∈ S)

def tl {n m : ℕ} (a b : Fin m → Fin n) (o : Fin m → Bool) (k : Fin m) : Fin n :=
  if o k = true then a k else b k

def hd {n m : ℕ} (a b : Fin m → Fin n) (o : Fin m → Bool) (k : Fin m) : Fin n :=
  if o k = true then b k else a k

def Closed {n m : ℕ} (a b : Fin m → Fin n) (N : Fin m → Prop) (o : Fin m → Bool)
    (D : Finset (Fin n)) : Prop :=
  ∀ k, ¬ N k → tl a b o k ∈ D → hd a b o k ∈ D

def Rch {n m : ℕ} (a b : Fin m → Fin n) (N : Fin m → Prop) (o : Fin m → Bool)
    (x c : Fin n) : Prop :=
  ∀ D : Finset (Fin n), Closed a b N o D → x ∈ D → c ∈ D

def RootP {n m : ℕ} (a b : Fin m → Fin n) (N : Fin m → Prop) (o : Fin m → Bool)
    (x : Fin n) : Prop :=
  ∀ D : Finset (Fin n), Closed a b N o D → x ∈ D → ∃ i, N i ∧ a i ∈ D

def flip {m : ℕ} (o : Fin m → Bool) (g : Fin m) : Fin m → Bool :=
  fun k => if k = g then !o g else o k

lemma tl_flip_self {n m : ℕ} (a b : Fin m → Fin n) (o : Fin m → Bool) (g : Fin m) :
    tl a b (flip o g) g = hd a b o g := by
  unfold tl hd flip
  cases o g <;> simp

lemma hd_flip_self {n m : ℕ} (a b : Fin m → Fin n) (o : Fin m → Bool) (g : Fin m) :
    hd a b (flip o g) g = tl a b o g := by
  unfold tl hd flip
  cases o g <;> simp

lemma tl_flip_ne {n m : ℕ} (a b : Fin m → Fin n) (o : Fin m → Bool) {g k : Fin m}
    (h : k ≠ g) : tl a b (flip o g) k = tl a b o k := by
  unfold tl flip
  simp [h]

lemma hd_flip_ne {n m : ℕ} (a b : Fin m → Fin n) (o : Fin m → Bool) {g k : Fin m}
    (h : k ≠ g) : hd a b (flip o g) k = hd a b o k := by
  unfold hd flip
  simp [h]

lemma closed_union {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop} {o : Fin m → Bool}
    {g : Fin m} {D Z : Finset (Fin n)} (hD : Closed a b N (flip o g) D)
    (hZ : Closed a b N o Z) (hg : hd a b o g ∈ Z) : Closed a b N o (D ∪ Z) := by
  intro k hk ht
  by_cases hkg : k = g
  · subst hkg
    exact Finset.mem_union_right _ hg
  · rcases Finset.mem_union.mp ht with h | h
    · have h1 := hD k hk (by rw [tl_flip_ne a b o hkg]; exact h)
      rw [hd_flip_ne a b o hkg] at h1
      exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ (hZ k hk h)

lemma closed_inter {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop} {o : Fin m → Bool}
    {g : Fin m} {D Z : Finset (Fin n)} (hD : Closed a b N (flip o g) D)
    (hZ : Closed a b N o Z) (hg : tl a b o g ∉ Z) : Closed a b N o (D ∩ Z) := by
  intro k hk ht
  have ht' := Finset.mem_inter.mp ht
  by_cases hkg : k = g
  · subst hkg
    exact absurd ht'.2 hg
  · have h1 := hD k hk (by rw [tl_flip_ne a b o hkg]; exact ht'.1)
    rw [hd_flip_ne a b o hkg] at h1
    exact Finset.mem_inter.mpr ⟨h1, hZ k hk ht'.2⟩

lemma flip_back {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop} {o : Fin m → Bool}
    {g : Fin m} {D : Finset (Fin n)} (hD : Closed a b N (flip o g) D) (hN : ¬ N g)
    (h : hd a b o g ∈ D) : tl a b o g ∈ D := by
  have h1 := hD g hN (by rw [tl_flip_self]; exact h)
  rw [hd_flip_self] at h1
  exact h1

lemma closed_of_flip {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop} {o : Fin m → Bool}
    {g : Fin m} {D : Finset (Fin n)} (hD : Closed a b N (flip o g) D)
    (h : tl a b o g ∈ D → hd a b o g ∈ D) : Closed a b N o D := by
  intro k hk ht
  by_cases hkg : k = g
  · subst hkg
    exact h ht
  · have h1 := hD k hk (by rw [tl_flip_ne a b o hkg]; exact ht)
    rw [hd_flip_ne a b o hkg] at h1
    exact h1

lemma cross_closed {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop} {o : Fin m → Bool}
    {g : Fin m} {Z : Finset (Fin n)} (hZ : Closed a b N o Z) (hN : ¬ N g)
    (hc : ¬ (a g ∈ Z ↔ b g ∈ Z)) : tl a b o g ∉ Z ∧ hd a b o g ∈ Z := by
  have h := hZ g hN
  unfold tl hd at h ⊢
  cases ho : o g <;> simp [ho] at h ⊢ <;> tauto

lemma cross_of_arc {n m : ℕ} {a b : Fin m → Fin n} {o : Fin m → Bool}
    {g : Fin m} {S : Finset (Fin n)} (h1 : tl a b o g ∈ S) (h2 : hd a b o g ∉ S) :
    ¬ (a g ∈ S ↔ b g ∈ S) := by
  unfold tl at h1
  unfold hd at h2
  cases ho : o g <;> simp [ho] at h1 h2 <;> tauto

lemma cf_closed {n m : ℕ} {a b : Fin m → Fin n} (N : Fin m → Prop) (o : Fin m → Bool)
    {C : Finset (Fin n)} (hC : ∀ i, a i ∈ C ↔ b i ∈ C) : Closed a b N o C := by
  intro k _ ht
  have h := hC k
  unfold tl at ht
  unfold hd
  cases ho : o k <;> simp [ho] at ht ⊢ <;> tauto

lemma cf_compl {n m : ℕ} {a b : Fin m → Fin n} {C : Finset (Fin n)}
    (hC : ∀ i, a i ∈ C ↔ b i ∈ C) : ∀ i, a i ∈ Cᶜ ↔ b i ∈ Cᶜ := by
  intro i
  simp [hC i]

lemma f1step {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop}
    (N1 : ∀ i, N i → Str a b i)
    (N2 : ∀ S : Finset (Fin n), S.Nonempty → (∀ i, a i ∈ S ↔ b i ∈ S) → ∃ i, N i ∧ a i ∈ S)
    (N3 : ∀ i, N i → ∃ C : Finset (Fin n), (∀ k, a k ∈ C ↔ b k ∈ C) ∧ a i ∈ C ∧
      ∀ k, N k → k ≠ i → a k ∉ C)
    (o : Fin m → Bool) (w0 : Fin n) (hw0 : ¬ RootP a b N o w0) :
    ∃ (o' : Fin m → Bool) (w : Fin n), (∀ x, RootP a b N o x → RootP a b N o' x) ∧
      ¬ RootP a b N o w ∧ RootP a b N o' w := by
  classical
  obtain ⟨Z, hZm⟩ : ∃ Z : Finset (Fin n), ∀ x, x ∈ Z ↔ ¬ RootP a b N o x :=
    ⟨Finset.univ.filter (fun x => ¬ RootP a b N o x), fun x => by simp⟩
  have hZc : Closed a b N o Z := by
    intro k hk ht
    rw [hZm] at ht ⊢
    intro hR
    exact ht (fun D hD hx => hR D hD (hD k hk hx))
  have hroot : ∀ i, N i → a i ∉ Z := by
    intro i hi
    rw [hZm]
    exact fun h => h (fun D _ hx => ⟨i, hi, hx⟩)
  by_cases hex : ∃ g, ¬ N g ∧ ¬ (a g ∈ Z ↔ b g ∈ Z)
  · obtain ⟨g, hNg, hcr⟩ := hex
    obtain ⟨htl, hhd⟩ := cross_closed hZc hNg hcr
    have hmono : ∀ x, RootP a b N o x → RootP a b N (flip o g) x := by
      intro x hx D hD hxD
      obtain ⟨i, hi, hiD⟩ := hx (D ∪ Z) (closed_union hD hZc hhd) (Finset.mem_union_left _ hxD)
      rcases Finset.mem_union.mp hiD with h | h
      · exact ⟨i, hi, h⟩
      · exact absurd h (hroot i hi)
    refine ⟨flip o g, hd a b o g, hmono, (hZm _).mp hhd, ?_⟩
    intro D hD hxD
    have h1 : tl a b o g ∈ D := flip_back hD hNg hxD
    have h2 : RootP a b N o (tl a b o g) := by
      by_contra h
      exact htl ((hZm _).mpr h)
    exact hmono _ h2 D hD h1
  · exfalso
    have hall : ∀ g, ¬ (a g ∈ Z ↔ b g ∈ Z) → N g := by
      intro g hg
      by_contra hN
      exact hex ⟨g, hN, hg⟩
    have hZne : Z.Nonempty := ⟨w0, (hZm _).mpr hw0⟩
    by_cases hcf : ∀ i, a i ∈ Z ↔ b i ∈ Z
    · obtain ⟨i, hi, hiZ⟩ := N2 Z hZne hcf
      exact hroot i hi hiZ
    · obtain ⟨i, hi⟩ := not_forall.mp hcf
      have hNi := hall i hi
      obtain ⟨C, hCcf, haC, hCother⟩ := N3 i hNi
      have hbC : b i ∈ C := (hCcf i).mp haC
      have hcrS : ¬ (a i ∈ Z ∩ C ↔ b i ∈ Z ∩ C) := by
        simp only [Finset.mem_inter, haC, hbC, and_true]
        exact hi
      obtain ⟨k1, _, hk1, _, _, hc1, _⟩ := N1 i hNi (Z ∩ C) hcrS
      have hk1C := hCcf k1
      simp only [Finset.mem_inter] at hc1
      have hk1Z : ¬ (a k1 ∈ Z ↔ b k1 ∈ Z) := by
        intro hz
        exact hc1 ⟨fun x => ⟨hz.mp x.1, hk1C.mp x.2⟩, fun x => ⟨hz.mpr x.1, hk1C.mpr x.2⟩⟩
      have hak1 : a k1 ∈ C := by
        by_contra h
        have hb : b k1 ∉ C := fun hb => h (hk1C.mpr hb)
        exact hc1 ⟨fun x => absurd x.2 h, fun x => absurd x.2 hb⟩
      exact hCother k1 (hall k1 hk1Z) hk1 hak1

lemma f2step {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop}
    (N1 : ∀ i, N i → Str a b i)
    (N3 : ∀ i, N i → ∃ C : Finset (Fin n), (∀ k, a k ∈ C ↔ b k ∈ C) ∧ a i ∈ C ∧
      ∀ k, N k → k ≠ i → a k ∉ C)
    (o : Fin m → Bool) (hP : ∀ x, RootP a b N o x) (j : Fin m) (hj : N j)
    (hnr : ¬ Rch a b N o (a j) (b j)) :
    ∃ o' : Fin m → Bool, (∀ x, RootP a b N o' x) ∧
      (∀ k x, N k → Rch a b N o x (b k) → Rch a b N o' x (b k)) ∧
      ∃ w, ¬ Rch a b N o w (b j) ∧ Rch a b N o' w (b j) := by
  classical
  obtain ⟨Z, hZm⟩ : ∃ Z : Finset (Fin n), ∀ x, x ∈ Z ↔ ¬ Rch a b N o x (b j) :=
    ⟨Finset.univ.filter (fun x => ¬ Rch a b N o x (b j)), fun x => by simp⟩
  have hZc : Closed a b N o Z := by
    intro k hk ht
    rw [hZm] at ht ⊢
    intro hR
    exact ht (fun D hD hx => hR D hD (hD k hk hx))
  have haZ : a j ∈ Z := (hZm _).mpr hnr
  have hbZ : b j ∉ Z := by
    rw [hZm]
    exact fun h => h (fun D _ hx => hx)
  obtain ⟨C, hCcf, haC, hCother⟩ := N3 j hj
  have hbC : b j ∈ C := (hCcf j).mp haC

  have hnotN : ∀ g, g ≠ j → ¬ (a g ∈ Z ↔ b g ∈ Z) → ¬ N g := by
    intro g hgj hcr hNg
    have hag : a g ∉ C := hCother g hNg hgj
    have hbg : b g ∉ C := fun h => hag ((hCcf g).mpr h)
    have hCc : Closed a b N o Cᶜ := cf_closed N o (cf_compl hCcf)
    by_cases h1 : a g ∈ Z
    · have h2 : b g ∉ Z := fun h => hcr ⟨fun _ => h, fun _ => h1⟩
      have h3 : Rch a b N o (b g) (b j) := by
        by_contra h
        exact h2 ((hZm _).mpr h)
      have h4 := h3 Cᶜ hCc (by simpa using hbg)
      simp at h4
      exact h4 hbC
    · have h3 : Rch a b N o (a g) (b j) := by
        by_contra h
        exact h1 ((hZm _).mpr h)
      have h4 := h3 Cᶜ hCc (by simpa using hag)
      simp at h4
      exact h4 hbC
  have hcrj : ¬ (a j ∈ Z ↔ b j ∈ Z) := fun h => hbZ (h.mp haZ)
  obtain ⟨k1, k2, hk1, hk2, hk12, hc1, hc2⟩ := N1 j hj Z hcrj
  have hN1 := hnotN k1 hk1 hc1
  have hN2 := hnotN k2 hk2 hc2
  obtain ⟨htl1, hhd1⟩ := cross_closed hZc hN1 hc1
  obtain ⟨htl2, hhd2⟩ := cross_closed hZc hN2 hc2

  have hmono : ∀ g, tl a b o g ∉ Z → hd a b o g ∈ Z → ∀ k x, N k →
      Rch a b N o x (b k) → Rch a b N (flip o g) x (b k) := by
    intro g htl hhd k x hk hx D hD hxD
    by_cases hxZ : x ∈ Z
    · have h := hx (D ∩ Z) (closed_inter hD hZc htl) (Finset.mem_inter.mpr ⟨hxD, hxZ⟩)
      exact (Finset.mem_inter.mp h).1
    · have h := hx (D ∪ Z) (closed_union hD hZc hhd) (Finset.mem_union_left _ hxD)
      rcases Finset.mem_union.mp h with h | h
      · exact h
      · exfalso
        have hxj : Rch a b N o x (b j) := by
          by_contra h'
          exact hxZ ((hZm _).mpr h')
        by_cases hkj : k = j
        · subst hkj
          exact hbZ h
        · have hak : a k ∉ C := hCother k hk hkj
          have hbk : b k ∉ C := fun h' => hak ((hCcf k).mpr h')
          by_cases hxC : x ∈ C
          · exact hbk (hx C (cf_closed N o hCcf) hxC)
          · have h4 := hxj Cᶜ (cf_closed N o (cf_compl hCcf)) (by simpa using hxC)
            simp at h4
            exact h4 hbC
  have hgain : ∀ g, ¬ N g → tl a b o g ∉ Z → hd a b o g ∈ Z →
      ∃ w, ¬ Rch a b N o w (b j) ∧ Rch a b N (flip o g) w (b j) := by
    intro g hNg htl hhd
    refine ⟨hd a b o g, (hZm _).mp hhd, ?_⟩
    intro D hD hxD
    have h1 : tl a b o g ∈ D := flip_back hD hNg hxD
    have h2 : Rch a b N o (tl a b o g) (b j) := by
      by_contra h
      exact htl ((hZm _).mpr h)
    exact hmono g htl hhd j _ hj h2 D hD h1

  have hbad : ∀ g, ¬ N g → tl a b o g ∉ Z → hd a b o g ∈ Z → ∀ D : Finset (Fin n),
      Closed a b N (flip o g) D → D.Nonempty → (∀ i, N i → a i ∉ D) →
      (∀ x, x ∈ D → x ∉ Z) ∧ b j ∈ D := by
    intro g hNg htl hhd D hD hDne hDroot
    have hdis : ∀ x, x ∈ D → x ∉ Z := by
      intro x hxD hxZ
      obtain ⟨i, hi, hiD⟩ := hP x (D ∩ Z) (closed_inter hD hZc htl)
        (Finset.mem_inter.mpr ⟨hxD, hxZ⟩)
      exact hDroot i hi (Finset.mem_inter.mp hiD).1
    have htlD : tl a b o g ∈ D := by
      by_contra hnot
      obtain ⟨x, hxD⟩ := hDne
      obtain ⟨i, hi, hiD⟩ := hP x D (closed_of_flip hD (fun h => absurd h hnot)) hxD
      exact hDroot i hi hiD
    refine ⟨hdis, ?_⟩
    have h2 : Rch a b N o (tl a b o g) (b j) := by
      by_contra h
      exact htl ((hZm _).mpr h)
    have h3 := h2 (D ∪ Z) (closed_union hD hZc hhd) (Finset.mem_union_left _ htlD)
    rcases Finset.mem_union.mp h3 with h | h
    · exact h
    · exact absurd h hbZ
  by_cases hP1 : ∀ x, RootP a b N (flip o k1) x
  · exact ⟨flip o k1, hP1, hmono k1 htl1 hhd1, hgain k1 hN1 htl1 hhd1⟩
  by_cases hP2 : ∀ x, RootP a b N (flip o k2) x
  · exact ⟨flip o k2, hP2, hmono k2 htl2 hhd2, hgain k2 hN2 htl2 hhd2⟩
  exfalso
  obtain ⟨x1, hx1⟩ := not_forall.mp hP1
  obtain ⟨x2, hx2⟩ := not_forall.mp hP2
  unfold RootP at hx1 hx2
  push Not at hx1 hx2
  obtain ⟨D1, hD1, hx1D, hroot1⟩ := hx1
  obtain ⟨D2, hD2, hx2D, hroot2⟩ := hx2
  obtain ⟨hdis1, hb1⟩ := hbad k1 hN1 htl1 hhd1 D1 hD1 ⟨x1, hx1D⟩ hroot1
  obtain ⟨hdis2, hb2⟩ := hbad k2 hN2 htl2 hhd2 D2 hD2 ⟨x2, hx2D⟩ hroot2
  have hE : Closed a b N o (D1 ∩ D2) := by
    intro k hk ht
    have ht' := Finset.mem_inter.mp ht
    by_cases hk1' : k = k1
    · subst hk1'
      exfalso
      have h1 := hD2 k hk (by rw [tl_flip_ne a b o hk12]; exact ht'.2)
      rw [hd_flip_ne a b o hk12] at h1
      exact hdis2 _ h1 hhd1
    · by_cases hk2' : k = k2
      · subst hk2'
        exfalso
        have h1 := hD1 k hk (by rw [tl_flip_ne a b o (Ne.symm hk12)]; exact ht'.1)
        rw [hd_flip_ne a b o (Ne.symm hk12)] at h1
        exact hdis1 _ h1 hhd2
      · have h1 := hD1 k hk (by rw [tl_flip_ne a b o hk1']; exact ht'.1)
        rw [hd_flip_ne a b o hk1'] at h1
        have h2 := hD2 k hk (by rw [tl_flip_ne a b o hk2']; exact ht'.2)
        rw [hd_flip_ne a b o hk2'] at h2
        exact Finset.mem_inter.mpr ⟨h1, h2⟩
  obtain ⟨i, hi, hiE⟩ := hP (b j) (D1 ∩ D2) hE (Finset.mem_inter.mpr ⟨hb1, hb2⟩)
  exact hroot1 i hi (Finset.mem_inter.mp hiE).1

lemma exists_P {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop}
    (N1 : ∀ i, N i → Str a b i)
    (N2 : ∀ S : Finset (Fin n), S.Nonempty → (∀ i, a i ∈ S ↔ b i ∈ S) → ∃ i, N i ∧ a i ∈ S)
    (N3 : ∀ i, N i → ∃ C : Finset (Fin n), (∀ k, a k ∈ C ↔ b k ∈ C) ∧ a i ∈ C ∧
      ∀ k, N k → k ≠ i → a k ∉ C) :
    ∃ o : Fin m → Bool, ∀ x, RootP a b N o x := by
  classical
  obtain ⟨o, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m → Bool))
    (fun o => (Finset.univ.filter (fun x => RootP a b N o x)).card)
    ⟨fun _ => true, Finset.mem_univ _⟩
  refine ⟨o, fun x => ?_⟩
  by_contra hx
  obtain ⟨o', w, hmono, hw, hw'⟩ := f1step N1 N2 N3 o x hx
  have hlt : (Finset.univ.filter (fun x => RootP a b N o x)).card <
      (Finset.univ.filter (fun x => RootP a b N o' x)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨w, by simpa using hw', by simpa using hw⟩
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hmono y hy
  have := hmax o' (Finset.mem_univ _)
  omega

lemma exists_good {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop}
    (N1 : ∀ i, N i → Str a b i)
    (N2 : ∀ S : Finset (Fin n), S.Nonempty → (∀ i, a i ∈ S ↔ b i ∈ S) → ∃ i, N i ∧ a i ∈ S)
    (N3 : ∀ i, N i → ∃ C : Finset (Fin n), (∀ k, a k ∈ C ↔ b k ∈ C) ∧ a i ∈ C ∧
      ∀ k, N k → k ≠ i → a k ∉ C) :
    ∃ o : Fin m → Bool, (∀ x, RootP a b N o x) ∧ ∀ j, N j → Rch a b N o (a j) (b j) := by
  classical
  obtain ⟨o0, ho0⟩ := exists_P N1 N2 N3
  obtain ⟨o, ho, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun o => ∀ x, RootP a b N o x))
    (fun o => ((Finset.univ : Finset (Fin m × Fin n)).filter
      (fun p => N p.1 ∧ Rch a b N o p.2 (b p.1))).card)
    ⟨o0, by simpa using ho0⟩
  have hPo : ∀ x, RootP a b N o x := by simpa using ho
  refine ⟨o, hPo, fun j hj => ?_⟩
  by_contra hnr
  obtain ⟨o', hP', hmono, w, hw, hw'⟩ := f2step N1 N3 o hPo j hj hnr
  have hlt : ((Finset.univ : Finset (Fin m × Fin n)).filter
      (fun p => N p.1 ∧ Rch a b N o p.2 (b p.1))).card <
      ((Finset.univ : Finset (Fin m × Fin n)).filter
      (fun p => N p.1 ∧ Rch a b N o' p.2 (b p.1))).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(j, w), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hj, hw'⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => hw h.2
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, hmono p.1 p.2 hp.1 hp.2⟩
  have := hmax o' (by simpa using hP')
  omega

lemma suff {n m : ℕ} {a b : Fin m → Fin n} {N : Fin m → Prop}
    (N1 : ∀ i, N i → Str a b i)
    (N2 : ∀ S : Finset (Fin n), S.Nonempty → (∀ i, a i ∈ S ↔ b i ∈ S) → ∃ i, N i ∧ a i ∈ S)
    (N3 : ∀ i, N i → ∃ C : Finset (Fin n), (∀ k, a k ∈ C ↔ b k ∈ C) ∧ a i ∈ C ∧
      ∀ k, N k → k ≠ i → a k ∉ C) :
    ∃ q : Fin m → Bool × Bool, ∀ D : Finset (Fin n),
      (∀ i, (decide (a i ∈ D), decide (b i ∈ D)) ≠ q i) ↔ D = ∅ := by
  classical
  obtain ⟨o, hP, hR⟩ := exists_good N1 N2 N3
  refine ⟨fun i => if N i then (true, true) else if o i = true then (true, false)
    else (false, true), fun D => ⟨fun hsol => ?_, fun hD i => ?_⟩⟩
  · by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hDc : Closed a b N o D := by
      intro k hk ht
      have h := hsol k
      unfold tl at ht
      unfold hd
      by_contra hnot
      cases ho : o k <;> simp [hk, ho] at h ht hnot ⊢ <;> tauto
    obtain ⟨j, hj, hjD⟩ := hP x D hDc hx
    have hbD := hR j hj D hDc hjD
    have h := hsol j
    simp [hj, hjD, hbD] at h
  · subst hD
    by_cases hN : N i
    · simp [hN]
    · cases ho : o i <;> simp [hN, ho]

def IsComp {n m : ℕ} (a b : Fin m → Fin n) (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧ (∀ i, a i ∈ C ↔ b i ∈ C) ∧
    ∀ D : Finset (Fin n), D ⊆ C → D.Nonempty → (∀ i, a i ∈ D ↔ b i ∈ D) → D = C

lemma exists_comp {n m : ℕ} (a b : Fin m → Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hcf : ∀ i, a i ∈ S ↔ b i ∈ S) : ∃ C, C ⊆ S ∧ IsComp a b C := by
  classical
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image
    (S.powerset.filter (fun D => D.Nonempty ∧ ∀ i, a i ∈ D ↔ b i ∈ D)) Finset.card
    ⟨S, by simp [hS, hcf]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hC
  refine ⟨C, hC.1, hC.2.1, hC.2.2, fun D hDC hDne hDcf => ?_⟩
  have h := hmin D (by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hDC.trans hC.1, hDne, hDcf⟩)
  exact Finset.eq_of_subset_of_card_le hDC h

lemma comp_eq {n m : ℕ} {a b : Fin m → Fin n} {C C' : Finset (Fin n)}
    (hC : IsComp a b C) (hC' : IsComp a b C') {x : Fin n} (hx : x ∈ C) (hx' : x ∈ C') :
    C = C' := by
  classical
  have hne : (C ∩ C').Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hx, hx'⟩⟩
  have hcf : ∀ i, a i ∈ C ∩ C' ↔ b i ∈ C ∩ C' := by
    intro i
    simp only [Finset.mem_inter, hC.2.1 i, hC'.2.1 i]
  have h1 := hC.2.2 (C ∩ C') Finset.inter_subset_left hne hcf
  have h2 := hC'.2.2 (C ∩ C') Finset.inter_subset_right hne hcf
  exact h1.symm.trans h2

lemma suff' {n m : ℕ} (a b : Fin m → Fin n)
    (H : ∀ C : Finset (Fin n), C.Nonempty → (∀ i, a i ∈ C ↔ b i ∈ C) →
      ∃ i, Str a b i ∧ a i ∈ C) :
    ∃ q : Fin m → Bool × Bool, ∀ D : Finset (Fin n),
      (∀ i, (decide (a i ∈ D), decide (b i ∈ D)) ≠ q i) ↔ D = ∅ := by
  classical
  choose f hf using fun (C : Finset (Fin n)) (hC : IsComp a b C) => H C hC.1 hC.2.1
  refine suff (N := fun i => ∃ (C : Finset (Fin n)) (hC : IsComp a b C), f C hC = i) ?_ ?_ ?_
  · rintro i ⟨C, hC, rfl⟩
    exact (hf C hC).1
  · intro S hS hcf
    obtain ⟨C, hCS, hC⟩ := exists_comp a b S hS hcf
    exact ⟨f C hC, ⟨C, hC, rfl⟩, hCS (hf C hC).2⟩
  · rintro i ⟨C, hC, rfl⟩
    refine ⟨C, hC.2.1, (hf C hC).2, ?_⟩
    rintro k ⟨C', hC', rfl⟩ hne hk
    have hCC : C = C' := comp_eq hC hC' hk (hf C' hC').2
    subst hCC
    exact hne rfl

lemma nec {n m : ℕ} (a b : Fin m → Fin n) (q : Fin m → Bool × Bool)
    (hq : ∀ D : Finset (Fin n), (∀ i, (decide (a i ∈ D), decide (b i ∈ D)) ≠ q i) ↔ D = ∅)
    (C : Finset (Fin n)) (hCne : C.Nonempty) (hCcf : ∀ i, a i ∈ C ↔ b i ∈ C) :
    ∃ i, Str a b i ∧ a i ∈ C := by
  classical
  obtain ⟨N, hNd⟩ : ∃ N : Fin m → Prop,
      ∀ i, N i ↔ ¬ (q i = (true, false) ∨ q i = (false, true)) :=
    ⟨fun i => ¬ (q i = (true, false) ∨ q i = (false, true)), fun _ => Iff.rfl⟩
  obtain ⟨o, hod⟩ : ∃ o : Fin m → Bool, ∀ i, o i = (q i).1 := ⟨fun i => (q i).1, fun _ => rfl⟩
  have h0 : ∀ i, q i ≠ (false, false) := by
    intro i
    have h := (hq ∅).mpr rfl i
    simpa using h.symm
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image
    (C.powerset.filter (fun D => D.Nonempty ∧ Closed a b N o D)) Finset.card
    ⟨C, by simp [hCne, cf_closed N o hCcf]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hT
  obtain ⟨hTC, hTne, hTc⟩ := hT
  have hnotsol : ¬ ∀ i, (decide (a i ∈ T), decide (b i ∈ T)) ≠ q i :=
    fun h => (Finset.nonempty_iff_ne_empty.mp hTne) ((hq T).mp h)
  obtain ⟨i, hi⟩ := not_forall.mp hnotsol
  have hi' : (decide (a i ∈ T), decide (b i ∈ T)) = q i := not_not.mp hi
  have hqi : q i = (true, true) ∧ a i ∈ T ∧ b i ∈ T := by
    have h00 := h0 i
    have hcl := hTc i
    by_cases hN : N i
    · rw [hNd, not_or] at hN
      rcases hqv : q i with ⟨q1, q2⟩
      rw [hqv] at hi' hN h00
      cases q1 <;> cases q2 <;> simp_all
    · exfalso
      have hcl' := hcl hN
      rw [hNd, not_not] at hN
      unfold tl hd at hcl'
      have ho := hod i
      rcases hN with hN | hN
      · rw [hN] at hi' ho
        simp [ho] at hcl' hi'
        tauto
      · rw [hN] at hi' ho
        simp [ho] at hcl' hi'
        tauto
  obtain ⟨hqi1, haT, hbT⟩ := hqi
  have hNi : N i := by
    rw [hNd, hqi1]
    simp
  refine ⟨i, ?_, hTC haT⟩
  intro S hcr

  have hsub : ∀ D : Finset (Fin n), D ⊆ T → D.Nonempty → (∃ x, x ∈ T ∧ x ∉ D) →
      ∃ k, ¬ N k ∧ tl a b o k ∈ D ∧ hd a b o k ∉ D := by
    intro D hDT hDne hprop
    by_contra hno
    have hDc : Closed a b N o D := by
      intro k hk ht
      by_contra hh
      exact hno ⟨k, hk, ht, hh⟩
    have h := hmin D (by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hDT.trans hTC, hDne, hDc⟩)
    obtain ⟨x, hxT, hxD⟩ := hprop
    have hlt : D.card < T.card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset hDT).mpr ⟨x, hxT, hxD⟩)
    omega
  have hin : ∃ x, x ∈ T ∧ x ∈ S := by
    by_cases h : a i ∈ S
    · exact ⟨a i, haT, h⟩
    · exact ⟨b i, hbT, by tauto⟩
  have hout : ∃ x, x ∈ T ∧ x ∉ S := by
    by_cases h : a i ∈ S
    · exact ⟨b i, hbT, by tauto⟩
    · exact ⟨a i, haT, h⟩
  obtain ⟨xin, hxinT, hxinS⟩ := hin
  obtain ⟨xout, hxoutT, hxoutS⟩ := hout
  obtain ⟨k1, hNk1, ht1, hh1⟩ := hsub (T ∩ S) Finset.inter_subset_left
    ⟨xin, Finset.mem_inter.mpr ⟨hxinT, hxinS⟩⟩
    ⟨xout, hxoutT, fun h => hxoutS (Finset.mem_inter.mp h).2⟩
  obtain ⟨k2, hNk2, ht2, hh2⟩ := hsub (T \ S) Finset.sdiff_subset
    ⟨xout, Finset.mem_sdiff.mpr ⟨hxoutT, hxoutS⟩⟩
    ⟨xin, hxinT, fun h => (Finset.mem_sdiff.mp h).2 hxinS⟩
  have ht1' := Finset.mem_inter.mp ht1
  have ht2' := Finset.mem_sdiff.mp ht2
  have hhd1T : hd a b o k1 ∈ T := hTc k1 hNk1 ht1'.1
  have hhd2T : hd a b o k2 ∈ T := hTc k2 hNk2 ht2'.1
  have hhd1S : hd a b o k1 ∉ S := fun h => hh1 (Finset.mem_inter.mpr ⟨hhd1T, h⟩)
  have hhd2S : hd a b o k2 ∈ S := by
    by_contra h
    exact hh2 (Finset.mem_sdiff.mpr ⟨hhd2T, h⟩)
  refine ⟨k1, k2, ?_, ?_, ?_, cross_of_arc ht1'.2 hhd1S, ?_⟩
  · rintro rfl
    exact hNk1 hNi
  · rintro rfl
    exact hNk2 hNi
  · rintro rfl
    exact ht2'.2 ht1'.2
  · intro h
    unfold tl at ht2'
    unfold hd at hhd2S
    cases ho : o k2 <;> simp [ho] at ht2' hhd2S <;> tauto

lemma core {n m : ℕ} (a b : Fin m → Fin n) :
    (∃ q : Fin m → Bool × Bool, ∀ D : Finset (Fin n),
      (∀ i, (decide (a i ∈ D), decide (b i ∈ D)) ≠ q i) ↔ D = ∅) ↔
    (∀ C : Finset (Fin n), C.Nonempty → (∀ i, a i ∈ C ↔ b i ∈ C) →
      ∃ i, Str a b i ∧ a i ∈ C) := by
  constructor
  · rintro ⟨q, hq⟩ C hC hcf
    exact nec a b q hq C hC hcf
  · exact suff' a b

lemma count {n m : ℕ} (a b : Fin m → Fin n) (k : ℕ) :
    (∃ Q : Finset (Fin m → Bool × Bool), Q.card ≤ k ∧
      ∀ A B : Finset (Finset (Fin n)),
        (∀ p ∈ Q, ((∃ x ∈ A, ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i) ↔
          (∃ x ∈ B, ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i))) → A = B) ↔
    ((∃ q : Fin m → Bool × Bool, ∀ D : Finset (Fin n),
      (∀ i, (decide (a i ∈ D), decide (b i ∈ D)) ≠ q i) ↔ D = ∅) ∧ 2 ^ n ≤ k) := by
  classical
  constructor
  · rintro ⟨Q, hQk, hinj⟩
    have key : ∀ x : Finset (Fin n), ∃ p, p ∈ Q ∧ ∀ y : Finset (Fin n),
        (∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ p i) ↔ y = x := by
      intro x
      have hne : (Finset.univ : Finset (Finset (Fin n))) ≠ Finset.univ.erase x := by
        intro h
        have hx : x ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ x
        rw [h] at hx
        exact (Finset.notMem_erase x _) hx
      have h1 : ¬ ∀ p ∈ Q,
          ((∃ y ∈ (Finset.univ : Finset (Finset (Fin n))),
            ∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ p i) ↔
          (∃ y ∈ (Finset.univ : Finset (Finset (Fin n))).erase x,
            ∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ p i)) :=
        fun h => hne (hinj _ _ h)
      obtain ⟨p, hp⟩ := not_forall.mp h1
      obtain ⟨hpQ, hniff⟩ := Classical.not_imp.mp hp
      refine ⟨p, hpQ, ?_⟩
      have hB : ¬ ∃ y ∈ (Finset.univ : Finset (Finset (Fin n))).erase x,
          ∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ p i := by
        intro hB
        apply hniff
        refine ⟨fun _ => hB, fun _ => ?_⟩
        obtain ⟨y, _, hsol⟩ := hB
        exact ⟨y, Finset.mem_univ y, hsol⟩
      have hA : ∃ y ∈ (Finset.univ : Finset (Finset (Fin n))),
          ∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ p i := by
        by_contra hA
        exact hniff ⟨fun h => absurd h hA, fun h => absurd h hB⟩
      have honly : ∀ y : Finset (Fin n),
          (∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ p i) → y = x := by
        intro y hy
        by_contra hyx
        exact hB ⟨y, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩, hy⟩
      intro y
      constructor
      · exact honly y
      · rintro rfl
        obtain ⟨z, _, hz⟩ := hA
        have hzy := honly z hz
        subst hzy
        exact hz
    choose P hPQ hP using key
    refine ⟨⟨P ∅, hP ∅⟩, ?_⟩
    have hPinj : Function.Injective P := by
      intro x x' hxx
      have h1 := (hP x x).mpr rfl
      rw [hxx] at h1
      exact (hP x' x).mp h1
    have hcard : (Finset.univ : Finset (Finset (Fin n))).card ≤ Q.card :=
      Finset.card_le_card_of_injOn P (fun x _ => hPQ x) hPinj.injOn
    have h2 : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
      simp
    omega
  · rintro ⟨⟨q, hq⟩, hk⟩
    let P : Finset (Fin n) → (Fin m → Bool × Bool) := fun x i =>
      ((q i).1 != decide (a i ∈ x), (q i).2 != decide (b i ∈ x))
    have hP : ∀ x y : Finset (Fin n),
        (∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ P x i) ↔ y = x := by
      intro x y
      have h1 : (∀ i, (decide (a i ∈ y), decide (b i ∈ y)) ≠ P x i) ↔
          (∀ i, (decide (a i ∈ symmDiff y x), decide (b i ∈ symmDiff y x)) ≠ q i) := by
        refine forall_congr' (fun i => ?_)
        rcases hqv : q i with ⟨q1, q2⟩
        simp only [P, hqv, Finset.mem_symmDiff]
        by_cases h1 : a i ∈ y <;> by_cases h2 : a i ∈ x <;> by_cases h3 : b i ∈ y <;>
          by_cases h4 : b i ∈ x <;> cases q1 <;> cases q2 <;> simp [h1, h2, h3, h4]
      rw [h1, hq]
      rw [← Finset.bot_eq_empty, symmDiff_eq_bot]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · calc (Finset.univ.image P).card
          ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_image_le
        _ = 2 ^ n := by simp
        _ ≤ k := hk
    · intro A B h
      ext x
      have hx := h (P x) (Finset.mem_image_of_mem P (Finset.mem_univ x))
      simp only [hP] at hx
      simpa using hx

end PEqualNP.Outside.L_lib_1149_aux

open PEqualNP.Outside.L_lib_1149_aux

theorem PEqualNP.Outside.L_lib_1149 : (∀ (n m : Nat) (u v : Fin m → Fin n), (∀ i, u i ≠ v i) →
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let labels := (Finset.univ : Finset (Fin m))
  let cut := fun (S : Bits) => labels.filter
    (fun i => decide (u i ∈ S) != decide (v i ∈ S))
  let components := cube.filter (fun C => C.Nonempty ∧ (cut C).card = 0 ∧
    ∀ D ∈ C.powerset, D.Nonempty → (cut D).card = 0 → D = C)
  let strong := labels.filter (fun i => ∀ S ∈ cube,
    (decide (u i ∈ S) != decide (v i ∈ S)) = true → 3 ≤ (cut S).card)
  let good := fun (C : Bits) => strong.toList.any (fun i => decide (u i ∈ C))
  let Signing := Fin m → Bool × Bool
  let sat := fun (A : Finset Bits) (p : Signing) =>
    ∃ x ∈ A, ∀ i, (decide (u i ∈ x), decide (v i ∈ x)) ≠ p i
  ∀ k : Nat,
    (∃ Q : Finset Signing, Q.card ≤ k ∧
      ∀ A B : Finset Bits, (∀ p ∈ Q, (sat A p ↔ sat B p)) → A = B) ↔
      (∀ C ∈ components, good C = true) ∧ 2 ^ n ≤ k) := by
  intro n m u v _ Bits cube labels cut components strong good Signing sat k
  have hcutm : ∀ (S : Finset (Fin n)) (i : Fin m), i ∈ cut S ↔ ¬ (u i ∈ S ↔ v i ∈ S) := by
    intro S i
    simp [cut, labels]
  have hcut0 : ∀ S : Finset (Fin n), (cut S).card = 0 ↔ ∀ i, u i ∈ S ↔ v i ∈ S := by
    intro S
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    refine forall_congr' (fun i => ?_)
    rw [hcutm]
    exact not_not
  have hstrong : ∀ i : Fin m, i ∈ strong ↔ Str u v i := by
    intro i
    simp only [strong, labels, cube, Finset.mem_filter, Finset.mem_univ, true_and,
      forall_const]
    constructor
    · intro h S hcr
      have hiS : i ∈ cut S := (hcutm S i).mpr hcr
      have h3 := h S (by simpa using hcr)
      have h2 : 1 < ((cut S).erase i).card := by
        rw [Finset.card_erase_of_mem hiS]
        omega
      obtain ⟨k1, hk1, k2, hk2, hne⟩ := Finset.one_lt_card.mp h2
      rw [Finset.mem_erase] at hk1 hk2
      exact ⟨k1, k2, hk1.1, hk2.1, hne, (hcutm S k1).mp hk1.2, (hcutm S k2).mp hk2.2⟩
    · intro h S hcr
      obtain ⟨k1, k2, hk1, hk2, hk12, hc1, hc2⟩ := h S (by simpa using hcr)
      have hsub : ({i, k1, k2} : Finset (Fin m)) ⊆ cut S := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact (hcutm S _).mpr (by simpa using hcr)
        · exact (hcutm S _).mpr hc1
        · exact (hcutm S _).mpr hc2
      have hc : ({i, k1, k2} : Finset (Fin m)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_singleton]
        · simpa using hk12
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hk1, Ne.symm hk2⟩
      calc 3 = ({i, k1, k2} : Finset (Fin m)).card := hc.symm
        _ ≤ (cut S).card := Finset.card_le_card hsub
  have hgood : ∀ C : Finset (Fin n), good C = true ↔ ∃ i, Str u v i ∧ u i ∈ C := by
    intro C
    simp only [good, List.any_eq_true, Finset.mem_toList, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hiC⟩
      exact ⟨i, (hstrong i).mp hi, hiC⟩
    · rintro ⟨i, hi, hiC⟩
      exact ⟨i, (hstrong i).mpr hi, hiC⟩
  have hcomp : ∀ C : Finset (Fin n), C ∈ components ↔ IsComp u v C := by
    intro C
    simp only [components, cube, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powerset, hcut0, IsComp]
  have hbridge : (∀ C ∈ components, good C = true) ↔
      (∀ C : Finset (Fin n), C.Nonempty → (∀ i, u i ∈ C ↔ v i ∈ C) →
        ∃ i, Str u v i ∧ u i ∈ C) := by
    constructor
    · intro h S hS hcf
      obtain ⟨C, hCS, hC⟩ := exists_comp u v S hS hcf
      obtain ⟨i, hi, hiC⟩ := (hgood C).mp (h C ((hcomp C).mpr hC))
      exact ⟨i, hi, hCS hiC⟩
    · intro h C hC
      have hC' := (hcomp C).mp hC
      exact (hgood C).mpr (h C hC'.1 hC'.2.1)
  rw [hbridge, ← core u v]
  exact count u v k
