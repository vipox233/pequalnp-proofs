import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_453_aux

def parts {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) : Finset (Finset (Finset ι)) :=
  Finset.univ.filter (fun P : Finset (Finset ι) =>
    ∅ ∉ P ∧ (∀ B ∈ P, B ⊆ S) ∧ ∀ i ∈ S, (P.filter (fun B => i ∈ B)).card = 1)

theorem mem_parts_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ι}
    {P : Finset (Finset ι)} :
    P ∈ parts S ↔ ∅ ∉ P ∧ (∀ B ∈ P, B ⊆ S) ∧ (∀ i ∈ S, ∃ B ∈ P, i ∈ B) ∧
      (∀ B₁ ∈ P, ∀ B₂ ∈ P, ∀ i, i ∈ B₁ → i ∈ B₂ → B₁ = B₂) := by
  simp only [parts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h0, hs, hc⟩
    refine ⟨h0, hs, fun i hi => ?_, fun B₁ h1 B₂ h2 i hi1 hi2 => ?_⟩
    · obtain ⟨B, hB⟩ := Finset.card_eq_one.1 (hc i hi)
      have : B ∈ P.filter (fun B => i ∈ B) := by rw [hB]; exact Finset.mem_singleton_self B
      rw [Finset.mem_filter] at this
      exact ⟨B, this.1, this.2⟩
    · have hle := (hc i (hs B₁ h1 hi1)).le
      exact Finset.card_le_one.1 hle B₁ (Finset.mem_filter.2 ⟨h1, hi1⟩) B₂
        (Finset.mem_filter.2 ⟨h2, hi2⟩)
  · rintro ⟨h0, hs, hc, hu⟩
    refine ⟨h0, hs, fun i hi => ?_⟩
    obtain ⟨B, hB, hiB⟩ := hc i hi
    rw [Finset.card_eq_one]
    refine ⟨B, ?_⟩
    ext C
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hC, hiC⟩
      exact hu C hC B hB i hiC hiB
    · rintro rfl
      exact ⟨hB, hiB⟩

theorem decomp {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (a : ι) (ha : a ∉ S)
    (F : Finset (Finset ι) → ℤ) :
    ∑ P ∈ parts (insert a S), F P =
      ∑ Q ∈ parts S, (F (insert {a} Q) + ∑ B ∈ Q, F (insert (insert a B) (Q.erase B))) := by
  have haB : ∀ {Q : Finset (Finset ι)}, Q ∈ parts S → ∀ C ∈ Q, a ∉ C := by
    intro Q hQ C hC haC
    exact ha ((mem_parts_iff.1 hQ).2.1 C hC haC)
  rw [← Finset.sum_filter_add_sum_filter_not (parts (insert a S)) (fun P => {a} ∈ P),
    Finset.sum_add_distrib]
  congr 1
  · symm
    apply Finset.sum_nbij' (fun Q => insert {a} Q) (fun P => P.erase {a})
    · intro Q hQ
      obtain ⟨h0, hs, hc, hu⟩ := mem_parts_iff.1 hQ
      refine Finset.mem_filter.2 ⟨mem_parts_iff.2 ⟨?_, ?_, ?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro h
        rcases Finset.mem_insert.1 h with h | h
        · exact Finset.singleton_ne_empty a h.symm
        · exact h0 h
      · intro B hB
        rcases Finset.mem_insert.1 hB with rfl | hB
        · exact Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)
        · exact (hs B hB).trans (Finset.subset_insert _ _)
      · intro i hi
        rcases Finset.mem_insert.1 hi with h | hi
        · exact ⟨{a}, Finset.mem_insert_self _ _, by rw [h]; exact Finset.mem_singleton_self _⟩
        · obtain ⟨B, hB, hiB⟩ := hc i hi
          exact ⟨B, Finset.mem_insert_of_mem hB, hiB⟩
      · intro B₁ h1 B₂ h2 i hi1 hi2
        rcases Finset.mem_insert.1 h1 with rfl | h1 <;>
          rcases Finset.mem_insert.1 h2 with rfl | h2
        · rfl
        · rw [Finset.mem_singleton] at hi1
          rw [hi1] at hi2
          exact absurd hi2 (haB hQ _ h2)
        · rw [Finset.mem_singleton] at hi2
          rw [hi2] at hi1
          exact absurd hi1 (haB hQ _ h1)
        · exact hu B₁ h1 B₂ h2 i hi1 hi2
    · intro P hP
      obtain ⟨hP, hP1⟩ := Finset.mem_filter.1 hP
      obtain ⟨h0, hs, hc, hu⟩ := mem_parts_iff.1 hP
      refine mem_parts_iff.2 ⟨fun h => h0 (Finset.mem_of_mem_erase h), ?_, ?_,
        fun B₁ h1 B₂ h2 =>
          hu B₁ (Finset.mem_of_mem_erase h1) B₂ (Finset.mem_of_mem_erase h2)⟩
      · intro B hB x hx
        have hB' := Finset.mem_erase.1 hB
        rcases Finset.mem_insert.1 (hs B hB'.2 hx) with h | h
        · exact absurd
            (hu B hB'.2 {a} hP1 x hx (by rw [h]; exact Finset.mem_singleton_self _)) hB'.1
        · exact h
      · intro i hi
        obtain ⟨B, hB, hiB⟩ := hc i (Finset.mem_insert_of_mem hi)
        refine ⟨B, Finset.mem_erase.2 ⟨?_, hB⟩, hiB⟩
        rintro rfl
        rw [Finset.mem_singleton] at hiB
        rw [hiB] at hi
        exact ha hi
    · intro Q hQ
      exact Finset.erase_insert (fun h => haB hQ _ h (Finset.mem_singleton_self a))
    · intro P hP
      exact Finset.insert_erase (Finset.mem_filter.1 hP).2
    · intro Q _
      rfl
  · rw [show (∑ Q ∈ parts S, ∑ B ∈ Q, F (insert (insert a B) (Q.erase B))) =
      ∑ x ∈ (parts S).sigma (fun Q => Q), F (insert (insert a x.2) (x.1.erase x.2)) from
      (Finset.sum_sigma (parts S) (fun Q => Q)
        (fun x => F (insert (insert a x.2) (x.1.erase x.2)))).symm]
    symm
    apply Finset.sum_nbij (fun x => insert (insert a x.2) (x.1.erase x.2))
    · rintro ⟨Q, B⟩ hx
      simp only [Finset.mem_sigma] at hx
      obtain ⟨hQ, hB⟩ := hx
      obtain ⟨h0, hs, hc, hu⟩ := mem_parts_iff.1 hQ
      have haB' : a ∉ B := haB hQ B hB
      have hBS := hs B hB
      refine Finset.mem_filter.2 ⟨mem_parts_iff.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro h
        rcases Finset.mem_insert.1 h with h | h
        · exact Finset.insert_ne_empty a B h.symm
        · exact h0 (Finset.mem_of_mem_erase h)
      · intro C hC
        rcases Finset.mem_insert.1 hC with rfl | hC
        · exact Finset.insert_subset_insert a hBS
        · exact (hs C (Finset.mem_of_mem_erase hC)).trans (Finset.subset_insert _ _)
      · intro i hi
        rcases Finset.mem_insert.1 hi with h | hi
        · exact ⟨insert a B, Finset.mem_insert_self _ _,
            by rw [h]; exact Finset.mem_insert_self _ _⟩
        · obtain ⟨C, hC, hiC⟩ := hc i hi
          by_cases hCB : C = B
          · refine ⟨insert a B, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
            rw [← hCB]
            exact hiC
          · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hCB, hC⟩), hiC⟩
      · intro C₁ h1 C₂ h2 i hi1 hi2
        rcases Finset.mem_insert.1 h1 with rfl | h1 <;>
          rcases Finset.mem_insert.1 h2 with rfl | h2
        · rfl
        · exfalso
          obtain ⟨hne, h2'⟩ := Finset.mem_erase.1 h2
          have hia : i ≠ a := fun h => haB hQ C₂ h2' (by rw [← h]; exact hi2)
          have hiB : i ∈ B := (Finset.mem_insert.1 hi1).resolve_left hia
          exact hne (hu C₂ h2' B hB i hi2 hiB)
        · exfalso
          obtain ⟨hne, h1'⟩ := Finset.mem_erase.1 h1
          have hia : i ≠ a := fun h => haB hQ C₁ h1' (by rw [← h]; exact hi1)
          have hiB : i ∈ B := (Finset.mem_insert.1 hi2).resolve_left hia
          exact hne (hu C₁ h1' B hB i hi1 hiB)
        · exact hu C₁ (Finset.mem_of_mem_erase h1) C₂ (Finset.mem_of_mem_erase h2) i hi1 hi2
      · intro h
        rcases Finset.mem_insert.1 h with h | h
        · obtain ⟨x, hx⟩ :=
            Finset.nonempty_iff_ne_empty.2 (fun hB0 : B = ∅ => h0 (by rw [← hB0]; exact hB))
          have : x ∈ ({a} : Finset ι) := by rw [h]; exact Finset.mem_insert_of_mem hx
          rw [Finset.mem_singleton] at this
          exact haB' (by rw [← this]; exact hx)
        · exact haB hQ _ (Finset.mem_of_mem_erase h) (Finset.mem_singleton_self a)
    · rintro ⟨Q₁, B₁⟩ h1 ⟨Q₂, B₂⟩ h2 hE
      simp only [Finset.mem_coe, Finset.mem_sigma] at h1 h2
      simp only at hE
      obtain ⟨hQ1, hB1⟩ := h1
      obtain ⟨hQ2, hB2⟩ := h2
      have hX1 : insert a B₁ ∉ Q₁.erase B₁ :=
        fun h => haB hQ1 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a B₁)
      have hX2 : insert a B₂ ∉ Q₂.erase B₂ :=
        fun h => haB hQ2 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a B₂)
      have hB : B₁ = B₂ := by
        have hm : insert a B₁ ∈ insert (insert a B₂) (Q₂.erase B₂) := by
          rw [← hE]
          exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.1 hm with h | h
        · rw [← Finset.erase_insert (haB hQ1 _ hB1), h, Finset.erase_insert (haB hQ2 _ hB2)]
        · exact absurd h
            (fun h' => haB hQ2 _ (Finset.mem_of_mem_erase h') (Finset.mem_insert_self a B₁))
      subst hB
      have hQ : Q₁.erase B₁ = Q₂.erase B₁ := by
        rw [← Finset.erase_insert hX1, hE, Finset.erase_insert hX2]
      have hQQ : Q₁ = Q₂ := by
        rw [← Finset.insert_erase hB1, hQ, Finset.insert_erase hB2]
      subst hQQ
      rfl
    · intro P hP
      rw [Finset.mem_coe, Finset.mem_filter] at hP
      obtain ⟨hP, hPa⟩ := hP
      obtain ⟨h0, hs, hc, hu⟩ := mem_parts_iff.1 hP
      obtain ⟨B0, hB0, haB0⟩ := hc a (Finset.mem_insert_self a S)
      have hne : B0.erase a ≠ ∅ := by
        intro h
        rcases (Finset.erase_eq_empty_iff B0 a).1 h with h | h
        · exact h0 (by rw [← h]; exact hB0)
        · exact hPa (by rw [← h]; exact hB0)
      obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hnot : B0.erase a ∉ P.erase B0 := by
        intro h
        have := hu _ (Finset.mem_of_mem_erase h) B0 hB0 y hy (Finset.mem_of_mem_erase hy)
        rw [this] at h
        exact (Finset.mem_erase.1 h).1 rfl
      have hS : ∀ C ∈ P, C ≠ B0 → C ⊆ S := by
        intro C hC hCB x hx
        rcases Finset.mem_insert.1 (hs C hC hx) with h | h
        · rw [h] at hx
          exact absurd (hu C hC B0 hB0 a hx haB0) hCB
        · exact h
      rw [Set.mem_image]
      refine ⟨⟨insert (B0.erase a) (P.erase B0), B0.erase a⟩, ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_sigma]
        refine ⟨?_, Finset.mem_insert_self _ _⟩
        refine mem_parts_iff.2 ⟨?_, ?_, ?_, ?_⟩
        · intro h
          rcases Finset.mem_insert.1 h with h | h
          · exact hne h.symm
          · exact h0 (Finset.mem_of_mem_erase h)
        · intro C hC
          rcases Finset.mem_insert.1 hC with rfl | hC
          · intro x hx
            obtain ⟨hxa, hx⟩ := Finset.mem_erase.1 hx
            exact (Finset.mem_insert.1 (hs B0 hB0 hx)).resolve_left hxa
          · obtain ⟨hCB, hC⟩ := Finset.mem_erase.1 hC
            exact hS C hC hCB
        · intro i hi
          obtain ⟨C, hC, hiC⟩ := hc i (Finset.mem_insert_of_mem hi)
          by_cases hCB : C = B0
          · refine ⟨B0.erase a, Finset.mem_insert_self _ _, Finset.mem_erase.2 ⟨?_, ?_⟩⟩
            · intro h
              rw [h] at hi
              exact ha hi
            · rw [← hCB]
              exact hiC
          · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hCB, hC⟩), hiC⟩
        · intro C₁ h1 C₂ h2 i hi1 hi2
          rcases Finset.mem_insert.1 h1 with rfl | h1 <;>
            rcases Finset.mem_insert.1 h2 with rfl | h2
          · rfl
          · obtain ⟨hne2, h2'⟩ := Finset.mem_erase.1 h2
            exact absurd (hu C₂ h2' B0 hB0 i hi2 (Finset.mem_of_mem_erase hi1)) hne2
          · obtain ⟨hne1, h1'⟩ := Finset.mem_erase.1 h1
            exact absurd (hu C₁ h1' B0 hB0 i hi1 (Finset.mem_of_mem_erase hi2)) hne1
          · exact hu C₁ (Finset.mem_of_mem_erase h1) C₂ (Finset.mem_of_mem_erase h2) i hi1 hi2
      · show insert (insert a (B0.erase a))
            ((insert (B0.erase a) (P.erase B0)).erase (B0.erase a)) = P
        rw [Finset.insert_erase haB0, Finset.erase_insert hnot, Finset.insert_erase hB0]
    · intro x _
      rfl

section main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def mu (B : Finset ι) : ℤ := (-1 : ℤ)^(B.card-1) * (Nat.factorial (B.card-1) : ℤ)

def w (A : ι → Fin n → ℤ) (B : Finset ι) : ℤ := mu B * ∑ c : Fin n, ∏ j ∈ B, A j c

def v (A : ι → Fin n → ℤ) (a : ι) (B : Finset ι) : ℤ :=
  mu B * ∑ c : Fin n, A a c * ∏ j ∈ B, A j c

def RR (A : ι → Fin n → ℤ) (S : Finset ι) : ℤ := ∑ P ∈ parts S, ∏ B ∈ P, w A B

def injS (f : ι → Fin n) (S : Finset ι) : Prop := ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y

instance (f : ι → Fin n) (S : Finset ι) : Decidable (injS f S) := by
  unfold injS
  infer_instance

def LL (A : ι → Fin n → ℤ) (S : Finset ι) : ℤ :=
  ∑ f : ι → Fin n, if injS f S then ∏ i ∈ S, A i (f i) else 0

def mrg (A : ι → Fin n → ℤ) (a k : ι) : ι → Fin n → ℤ :=
  fun i c => A i c * (if i = k then A a c else 1)

theorem fiber_eq (a : ι) (X : (ι → Fin n) → ℤ)
    (hX : ∀ f d, X (Function.update f a d) = X f) (c c' : Fin n) :
    ∑ f ∈ Finset.univ.filter (fun f : ι → Fin n => f a = c), X f
      = ∑ f ∈ Finset.univ.filter (fun f : ι → Fin n => f a = c'), X f := by
  refine Finset.sum_nbij' (fun f => Function.update f a c') (fun f => Function.update f a c)
    ?_ ?_ ?_ ?_ ?_
  · intro f _
    simp
  · intro f _
    simp
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp [← hf]
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp [← hf]
  · intro f _
    rw [hX]

theorem gsum (a : ι) (G : (ι → Fin n) → Fin n → ℤ)
    (hG : ∀ f d c, G (Function.update f a d) c = G f c) :
    (n:ℤ) * ∑ f : ι → Fin n, G f (f a) = ∑ f : ι → Fin n, ∑ c : Fin n, G f c := by
  have h1 : ∑ f : ι → Fin n, G f (f a)
      = ∑ c : Fin n, ∑ f ∈ Finset.univ.filter (fun f : ι → Fin n => f a = c), G f c := by
    rw [← Finset.sum_fiberwise Finset.univ (fun f : ι → Fin n => f a)]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun f hf => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [hf]
  have h2 : ∀ c : Fin n, ∑ f : ι → Fin n, G f c
      = (n:ℤ) * ∑ f ∈ Finset.univ.filter (fun f : ι → Fin n => f a = c), G f c := by
    intro c
    rw [← Finset.sum_fiberwise Finset.univ (fun f : ι → Fin n => f a)]
    rw [Finset.sum_congr rfl fun c' _ => fiber_eq a (fun f => G f c) (fun f d => hG f d c) c' c]
    simp
  rw [Finset.sum_comm, h1, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun c _ => h2 c).symm

theorem injS_update (f : ι → Fin n) (S : Finset ι) (a : ι) (ha : a ∉ S) (d : Fin n) :
    injS (Function.update f a d) S ↔ injS f S := by
  have e : ∀ x ∈ S, Function.update f a d x = f x := by
    intro x hx
    rw [Function.update_of_ne]
    intro h
    exact ha (h ▸ hx)
  unfold injS
  constructor
  · intro h x hx y hy hxy
    exact h x hx y hy (by rw [e x hx, e y hy]; exact hxy)
  · intro h x hx y hy hxy
    exact h x hx y hy (by rw [← e x hx, ← e y hy]; exact hxy)

theorem prod_update (A : ι → Fin n → ℤ) (f : ι → Fin n) (S : Finset ι) (a : ι) (ha : a ∉ S)
    (d : Fin n) : ∏ i ∈ S, A i (Function.update f a d i) = ∏ i ∈ S, A i (f i) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Function.update_of_ne]
  intro h
  exact ha (h ▸ hx)

theorem ind_insert (f : ι → Fin n) (S : Finset ι) (a : ι) (ha : a ∉ S) (h : injS f S) :
    (if injS f (insert a S) then (1:ℤ) else 0)
      = 1 - ∑ k ∈ S, (if f a = f k then (1:ℤ) else 0) := by
  by_cases hk : ∃ k ∈ S, f a = f k
  · obtain ⟨k, hkS, hfk⟩ := hk
    have hs : ∑ k ∈ S, (if f a = f k then (1:ℤ) else 0) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp [hfk]
      · intro b hb hbk
        have : f a ≠ f b := by
          intro hab
          exact hbk (h b hb k hkS (hab.symm.trans hfk))
        simp [this]
      · intro hk'
        exact absurd hkS hk'
    have hn : ¬ injS f (insert a S) := by
      intro hi
      have := hi a (Finset.mem_insert_self a S) k (Finset.mem_insert_of_mem hkS) hfk
      exact ha (this ▸ hkS)
    rw [if_neg hn, hs]
    ring
  · have hk' : ∀ k ∈ S, f a ≠ f k := fun k hkS hfk => hk ⟨k, hkS, hfk⟩
    have hs : ∑ k ∈ S, (if f a = f k then (1:ℤ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun k hkS => ?_
      simp [hk' k hkS]
    have hi : injS f (insert a S) := by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · rfl
        · exact absurd hxy (hk' y hy')
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact absurd hxy.symm (hk' x hx')
        · exact h x hx' y hy' hxy
    rw [if_pos hi, hs]
    ring

theorem LL_rec (A : ι → Fin n → ℤ) (S : Finset ι) (a : ι) (ha : a ∉ S) :
    (n:ℤ) * LL A (insert a S) = (∑ c, A a c) * LL A S - ∑ k ∈ S, LL (mrg A a k) S := by
  let H : (ι → Fin n) → ℤ := fun f => if injS f S then ∏ i ∈ S, A i (f i) else 0
  have hpt : ∀ f : ι → Fin n,
      (if injS f (insert a S) then ∏ i ∈ insert a S, A i (f i) else 0)
        = H f * A a (f a) - ∑ k ∈ S, H f * A a (f a) * (if f a = f k then 1 else 0) := by
    intro f
    by_cases h : injS f S
    · have e := ind_insert f S a ha h
      have e2 : (if injS f (insert a S) then ∏ i ∈ insert a S, A i (f i) else 0)
          = (if injS f (insert a S) then (1:ℤ) else 0) * (A a (f a) * ∏ i ∈ S, A i (f i)) := by
        rw [Finset.prod_insert ha]
        split_ifs <;> ring
      rw [e2, e]
      simp only [H, if_pos h]
      rw [sub_mul, one_mul, Finset.sum_mul]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun k _ => ?_
        ring
    · have hn : ¬ injS f (insert a S) := by
        intro hi
        exact h fun x hx y hy hxy =>
          hi x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      simp [H, h, hn]
  have hHu : ∀ f d, H (Function.update f a d) = H f := by
    intro f d
    simp only [H, injS_update f S a ha d, prod_update A f S a ha d]
  have t1 : (n:ℤ) * ∑ f : ι → Fin n, H f * A a (f a) = (∑ c, A a c) * LL A S := by
    rw [gsum a (fun f c => H f * A a c) (fun f d c => by simp only [hHu])]
    unfold LL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.mul_sum, mul_comm]
  have t2 : ∀ k ∈ S, (n:ℤ) * ∑ f : ι → Fin n, H f * A a (f a) * (if f a = f k then 1 else 0)
      = LL (mrg A a k) S := by
    intro k hk
    have hka : k ≠ a := fun e => ha (e ▸ hk)
    rw [gsum a (fun f c => H f * A a c * (if c = f k then 1 else 0)) (fun f d c => by
      simp only [hHu, Function.update_of_ne hka])]
    unfold LL
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [H, mrg]
    split_ifs with hf
    · rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' S k, if_pos hk]
    · simp
  unfold LL
  rw [Finset.sum_congr rfl fun f _ => hpt f, Finset.sum_sub_distrib,
    Finset.sum_comm (s := Finset.univ) (t := S), mul_sub, t1, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k hk => t2 k hk]
  rfl

theorem mu_insert (B : Finset ι) (a : ι) (ha : a ∉ B) (hne : B ≠ ∅) :
    mu (insert a B) = -(B.card : ℤ) * mu B := by
  have hpos : 1 ≤ B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, B.card = t + 1 := ⟨B.card - 1, (Nat.sub_add_cancel hpos).symm⟩
  have hcard : (insert a B).card = B.card + 1 := by simp [ha]
  unfold mu
  rw [hcard, ht]
  simp only [Nat.add_sub_cancel, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  ring

theorem w_singleton (A : ι → Fin n → ℤ) (a : ι) :
    w A {a} = ∑ c : Fin n, A a c := by
  unfold w mu
  simp

theorem w_insert (A : ι → Fin n → ℤ) (B : Finset ι) (a : ι) (ha : a ∉ B) (hne : B ≠ ∅) :
    w A (insert a B) = -(B.card : ℤ) * v A a B := by
  unfold w v
  rw [mu_insert B a ha hne]
  have hp : ∀ c : Fin n, ∏ j ∈ insert a B, A j c = A a c * ∏ j ∈ B, A j c :=
    fun c => Finset.prod_insert ha
  simp only [hp]
  ring

theorem w_mrg_mem (A : ι → Fin n → ℤ) (a k : ι) (B : Finset ι) (hk : k ∈ B) :
    w (mrg A a k) B = v A a B := by
  unfold w v mrg
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' B k, if_pos hk]
  ring

theorem w_mrg_not_mem (A : ι → Fin n → ℤ) (a k : ι) (C : Finset ι) (hk : k ∉ C) :
    w (mrg A a k) C = w A C := by
  unfold w mrg
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun j hj => ?_
  have hjk : j ≠ k := fun e => hk (e ▸ hj)
  simp [hjk]

theorem prod_w_mrg (A : ι → Fin n → ℤ) (S : Finset ι) (a : ι)
    {Q : Finset (Finset ι)} (hQ : Q ∈ parts S) {B : Finset ι} (hB : B ∈ Q) {k : ι} (hk : k ∈ B) :
    ∏ C ∈ Q, w (mrg A a k) C = v A a B * ∏ C ∈ Q.erase B, w A C := by
  obtain ⟨_, _, _, hu⟩ := mem_parts_iff.1 hQ
  rw [← Finset.mul_prod_erase Q _ hB, w_mrg_mem A a k B hk]
  congr 1
  refine Finset.prod_congr rfl fun C hC => ?_
  obtain ⟨hCB, hCQ⟩ := Finset.mem_erase.1 hC
  have hkC : k ∉ C := fun hk' => hCB (hu C hCQ B hB k hk' hk)
  exact w_mrg_not_mem A a k C hkC

theorem sum_parts_eq (S : Finset ι) {Q : Finset (Finset ι)} (hQ : Q ∈ parts S) (g : ι → ℤ) :
    ∑ k ∈ S, g k = ∑ B ∈ Q, ∑ k ∈ B, g k := by
  obtain ⟨_, hs, hc, hu⟩ := mem_parts_iff.1 hQ
  have hS : S = Q.biUnion id := by
    ext i
    simp only [Finset.mem_biUnion, id_eq]
    constructor
    · exact hc i
    · rintro ⟨B, hB, hiB⟩
      exact hs B hB hiB
  have hdisj : (Q : Set (Finset ι)).PairwiseDisjoint id := by
    intro B₁ h1 B₂ h2 hne
    rw [Function.onFun, id_eq, id_eq, Finset.disjoint_left]
    intro i hi1 hi2
    exact hne (hu B₁ h1 B₂ h2 i hi1 hi2)
  rw [hS, Finset.sum_biUnion hdisj]
  rfl

theorem RR_rec (A : ι → Fin n → ℤ) (S : Finset ι) (a : ι) (ha : a ∉ S) :
    RR A (insert a S) = (∑ c, A a c) * RR A S - ∑ k ∈ S, RR (mrg A a k) S := by
  unfold RR
  rw [decomp S a ha (fun P => ∏ B ∈ P, w A B), Finset.sum_add_distrib]
  have haB : ∀ {Q : Finset (Finset ι)}, Q ∈ parts S → ∀ C ∈ Q, a ∉ C :=
    fun hQ C hC haC => ha ((mem_parts_iff.1 hQ).2.1 C hC haC)
  have t1 : ∑ Q ∈ parts S, ∏ B ∈ insert {a} Q, w A B
      = (∑ c, A a c) * ∑ Q ∈ parts S, ∏ B ∈ Q, w A B := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    have hnot : {a} ∉ Q := fun h => haB hQ {a} h (Finset.mem_singleton_self a)
    rw [Finset.prod_insert hnot, w_singleton]
  have t2 : ∑ Q ∈ parts S, ∑ B ∈ Q, ∏ C ∈ insert (insert a B) (Q.erase B), w A C
      = -∑ k ∈ S, ∑ Q ∈ parts S, ∏ C ∈ Q, w (mrg A a k) C := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [sum_parts_eq S hQ (fun k => ∏ C ∈ Q, w (mrg A a k) C), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hnot : insert a B ∉ Q.erase B :=
      fun h => haB hQ _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a B)
    have hne : B ≠ ∅ := fun h => (mem_parts_iff.1 hQ).1 (h ▸ hB)
    rw [Finset.prod_insert hnot, w_insert A B a (haB hQ B hB) hne]
    have hs : ∑ k ∈ B, ∏ C ∈ Q, w (mrg A a k) C
        = (B.card : ℤ) * (v A a B * ∏ C ∈ Q.erase B, w A C) := by
      rw [Finset.sum_congr rfl fun k hk => prod_w_mrg A S a hQ hB hk]
      simp
    rw [hs]
    ring
  rw [t1, t2]
  ring

theorem RR_empty (A : ι → Fin n → ℤ) : RR A ∅ = 1 := by
  have hp : parts (∅ : Finset ι) = {∅} := by
    ext P
    rw [mem_parts_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, hs, _, _⟩
      ext B
      simp only [Finset.notMem_empty, iff_false]
      intro hB
      have : B = ∅ := Finset.subset_empty.mp (hs B hB)
      exact h0 (this ▸ hB)
    · rintro rfl
      simp
  unfold RR
  rw [hp]
  simp

theorem LL_empty (A : ι → Fin n → ℤ) : LL A ∅ = (n : ℤ) ^ Fintype.card ι := by
  unfold LL injS
  simp [Fintype.card_fun]

theorem LL_eq_RR (hn : n ≠ 0) (S : Finset ι) :
    ∀ A : ι → Fin n → ℤ, LL A S = (n : ℤ) ^ (Fintype.card ι - S.card) * RR A S := by
  induction S using Finset.induction with
  | empty =>
    intro A
    rw [LL_empty, RR_empty]
    simp
  | @insert a S ha ih =>
    intro A
    have hnZ : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    apply mul_left_cancel₀ hnZ
    rw [LL_rec A S a ha, ih A]
    have hlt : S.card < Fintype.card ι := by
      have : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr fun h => ha (h ▸ Finset.mem_univ a)
      exact Finset.card_lt_card this
    have hcard : (insert a S).card = S.card + 1 := by simp [ha]
    have hexp : Fintype.card ι - S.card = (Fintype.card ι - (insert a S).card) + 1 := by
      omega
    rw [RR_rec A S a ha]
    have hsum : ∑ k ∈ S, LL (mrg A a k) S
        = ∑ k ∈ S, (n : ℤ) ^ (Fintype.card ι - S.card) * RR (mrg A a k) S :=
      Finset.sum_congr rfl fun k _ => ih (mrg A a k)
    rw [hsum, ← Finset.mul_sum, hexp, pow_succ]
    ring

theorem main_zero (m : ℕ) (A : Fin m → Fin 0 → ℤ) :
    LL A Finset.univ = RR A Finset.univ := by
  by_cases hm : m = 0
  · subst hm
    have hu : (Finset.univ : Finset (Fin 0)) = ∅ := rfl
    rw [hu, LL_empty, RR_empty]
    simp
  · have hL : LL A Finset.univ = 0 := by
      unfold LL
      haveI : IsEmpty (Fin m → Fin 0) :=
        ⟨fun f => Fin.elim0 (f ⟨0, Nat.pos_of_ne_zero hm⟩)⟩
      simp
    have hR : RR A Finset.univ = 0 := by
      unfold RR
      refine Finset.sum_eq_zero fun P hP => ?_
      obtain ⟨B, hB, _⟩ := (mem_parts_iff.1 hP).2.2.1 ⟨0, Nat.pos_of_ne_zero hm⟩ (Finset.mem_univ _)
      refine Finset.prod_eq_zero hB ?_
      unfold w
      simp
    rw [hL, hR]

theorem main_all (m n : ℕ) (A : Fin m → Fin n → ℤ) :
    LL A Finset.univ = RR A Finset.univ := by
  by_cases hn : n = 0
  · subst hn
    exact main_zero m A
  · have h := LL_eq_RR hn (Finset.univ : Finset (Fin m)) A
    simp only [Finset.card_univ, Nat.sub_self, pow_zero, one_mul] at h
    exact h

end main

end PEqualNP.Outside.L_lib_453_aux

theorem PEqualNP.Outside.L_lib_453 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ),
  let parts := Finset.univ.filter (fun P : Finset (Finset (Fin m)) =>
    ∅ ∉ P ∧ ∀ i : Fin m, (P.filter (fun B => i ∈ B)).card = 1)
  (∑ f ∈ Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f),
    ∏ i : Fin m, A i (f i)) =
    ∑ P ∈ parts, ∏ B ∈ P,
      ((-1 : ℤ)^(B.card-1) * (Nat.factorial (B.card-1) : ℤ) *
        ∑ c : Fin n, ∏ j ∈ B, A j c) := by
  intro m n A parts
  have hL : (∑ f ∈ Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f),
      ∏ i : Fin m, A i (f i)) = PEqualNP.Outside.L_lib_453_aux.LL A Finset.univ := by
    rw [Finset.sum_filter]
    unfold PEqualNP.Outside.L_lib_453_aux.LL
    refine Finset.sum_congr rfl fun f _ => ?_
    have hi : Function.Injective f ↔ PEqualNP.Outside.L_lib_453_aux.injS f Finset.univ := by
      unfold PEqualNP.Outside.L_lib_453_aux.injS
      constructor
      · intro h x _ y _ hxy
        exact h hxy
      · intro h x y hxy
        exact h x (Finset.mem_univ x) y (Finset.mem_univ y) hxy
    simp only [hi]
  have hP : parts = PEqualNP.Outside.L_lib_453_aux.parts (Finset.univ : Finset (Fin m)) := by
    ext P
    simp only [parts, PEqualNP.Outside.L_lib_453_aux.parts, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.subset_univ, implies_true, true_implies]
  rw [hL, PEqualNP.Outside.L_lib_453_aux.main_all m n A]
  unfold PEqualNP.Outside.L_lib_453_aux.RR PEqualNP.Outside.L_lib_453_aux.w
    PEqualNP.Outside.L_lib_453_aux.mu
  rw [hP]
