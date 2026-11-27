import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_750
def q_sg (f : ZMod 2) : ℤ := if f = 0 then 1 else -1
theorem q_sg_add (f g : ZMod 2) : q_sg (f + g) = q_sg f * q_sg g := by
  revert f g
  decide
theorem q_sg_one_add (f : ZMod 2) : q_sg (f + 1) = - q_sg f := by
  revert f
  decide
theorem q_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide
theorem q_char {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ZMod 2) :
    ∑ b : ι → ZMod 2, q_sg (∑ i, b i * m i) =
      if (∀ i, m i = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0 := by
  by_cases h : ∀ i, m i = 0
  · rw [ite_eq_left h]
    have h1 : ∀ b : ι → ZMod 2, q_sg (∑ i, b i * m i) = 1 := by
      intro b
      simp [h, q_sg]
    rw [Finset.sum_congr rfl (fun b _ => h1 b)]
    simp [ZMod.card]
  · rw [ite_eq_right h]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp h
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    have hm : m i₀ = 1 := key _ hi₀
    obtain ⟨v, hv⟩ : ∃ v : ι → ZMod 2, v = fun i => if i = i₀ then 1 else 0 := ⟨_, rfl⟩
    have hshift : ∀ b : ι → ZMod 2,
        q_sg (∑ i, (b + v) i * m i) = - q_sg (∑ i, b i * m i) := by
      intro b
      have h2 : ∑ i, (b + v) i * m i = (∑ i, b i * m i) + 1 := by
        simp only [hv, Pi.add_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, hm]
      rw [h2, q_sg_one_add]
    have h1 := Fintype.sum_equiv (Equiv.addRight v)
      (fun b => q_sg (∑ i, (b + v) i * m i))
      (fun b => q_sg (∑ i, b i * m i)) (fun _ => rfl)
    simp only [hshift, Finset.sum_neg_distrib] at h1
    linarith
theorem q_gauss {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (q : (ι → ZMod 2) → ZMod 2)
    (hq : ∀ b c : ι → ZMod 2, q (b + c) = q b + q c + q 0 + ∑ i, b i * ∑ l ∈ nbr i, c l) :
    (∑ b : ι → ZMod 2, (if q b = 0 then (1 : ℤ) else -1)) ^ 2 =
      if (∀ c : ι → ZMod 2, (∀ i, (∑ l ∈ nbr i, c l) = 0) → q c = q 0) then
        (2 : ℤ) ^ (Fintype.card ι) *
          (((Finset.univ : Finset (ι → ZMod 2)).filter
            (fun c => ∀ i, (∑ l ∈ nbr i, c l) = 0)).card : ℤ)
      else 0 := by
  have hS : (∑ b : ι → ZMod 2, (if q b = 0 then (1 : ℤ) else -1)) =
      ∑ b : ι → ZMod 2, q_sg (q b) := rfl
  have hmain : (∑ b : ι → ZMod 2, q_sg (q b)) ^ 2 =
      ∑ c : ι → ZMod 2, q_sg (q c + q 0) *
        (if (∀ i, (∑ l ∈ nbr i, c l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0) := by
    rw [sq, Finset.sum_mul]
    have step : ∀ b : ι → ZMod 2, q_sg (q b) * ∑ c : ι → ZMod 2, q_sg (q c) =
        ∑ c : ι → ZMod 2, q_sg (q c + q 0) * q_sg (∑ i, b i * ∑ l ∈ nbr i, c l) := by
      intro b
      rw [Finset.mul_sum]
      have e : ∑ c : ι → ZMod 2, q_sg (q b) * q_sg (q c) =
          ∑ c : ι → ZMod 2, q_sg (q b) * q_sg (q (b + c)) :=
        Eq.symm (Fintype.sum_equiv (Equiv.addLeft b) (fun c => q_sg (q b) * q_sg (q (b + c)))
          (fun c => q_sg (q b) * q_sg (q c)) (fun _ => rfl))
      rw [e]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← q_sg_add, ← q_sg_add, hq b c]
      congr 1
      linear_combination q_add_self (q b)
    rw [Finset.sum_congr rfl (fun b _ => step b), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    exact q_char (fun i => ∑ l ∈ nbr i, c l)
  rw [hS, hmain]
  by_cases hK : ∀ c : ι → ZMod 2, (∀ i, (∑ l ∈ nbr i, c l) = 0) → q c = q 0
  · rw [ite_eq_left hK]
    have h1 : ∀ c : ι → ZMod 2, q_sg (q c + q 0) *
        (if (∀ i, (∑ l ∈ nbr i, c l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0) =
        (if (∀ i, (∑ l ∈ nbr i, c l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0) := by
      intro c
      by_cases hc : ∀ i, (∑ l ∈ nbr i, c l) = 0
      · rw [ite_eq_left hc, hK c hc, q_add_self]
        simp [q_sg]
      · rw [ite_eq_right hc, mul_zero]
    rw [Finset.sum_congr rfl (fun c _ => h1 c), ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_comm]
  · rw [ite_eq_right hK]
    obtain ⟨c₀, hc₀'⟩ := not_forall.mp hK
    obtain ⟨hc₀, hq₀⟩ := not_imp.mp hc₀'
    have key : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide
    have hg₀ : q c₀ + q 0 = 1 := key _ _ hq₀
    have hP : ∀ c : ι → ZMod 2,
        (∀ i, (∑ l ∈ nbr i, (c + c₀) l) = 0) ↔ (∀ i, (∑ l ∈ nbr i, c l) = 0) := by
      intro c
      simp only [Pi.add_apply, Finset.sum_add_distrib, hc₀, add_zero]
    have hflip : ∀ c : ι → ZMod 2, q_sg (q (c + c₀) + q 0) *
        (if (∀ i, (∑ l ∈ nbr i, (c + c₀) l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0) =
        - (q_sg (q c + q 0) *
        (if (∀ i, (∑ l ∈ nbr i, c l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0)) := by
      intro c
      by_cases hc : ∀ i, (∑ l ∈ nbr i, c l) = 0
      · rw [ite_eq_left ((hP c).2 hc), ite_eq_left hc]
        have hβ : ∑ i, c i * ∑ l ∈ nbr i, c₀ l = 0 := by simp [hc₀]
        rw [hq c c₀, hβ]
        have h3 : q c + q c₀ + q 0 + 0 + q 0 = (q c + q 0) + 1 := by
          linear_combination hg₀
        rw [h3, q_sg_one_add]
        ring
      · rw [ite_eq_right (fun h => hc ((hP c).1 h)), ite_eq_right hc]
        simp
    have h1 := Fintype.sum_equiv (Equiv.addRight c₀)
      (fun c => q_sg (q (c + c₀) + q 0) *
        (if (∀ i, (∑ l ∈ nbr i, (c + c₀) l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0))
      (fun c => q_sg (q c + q 0) *
        (if (∀ i, (∑ l ∈ nbr i, c l) = 0) then (2 : ℤ) ^ (Fintype.card ι) else 0))
      (fun _ => rfl)
    simp only [hflip, Finset.sum_neg_distrib] at h1
    linarith
def g_KA {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ZMod 2) (s : Finset ι) :
    Finset (ι → ZMod 2) :=
  (Finset.univ : Finset (ι → ZMod 2)).filter
    (fun c => (∀ x, x ∉ s → c x = 0) ∧ ∀ x ∈ s, ∑ l ∈ s, A x l * c l = 0)
theorem g_two : ∀ a : ZMod 2, a + a = 0 := by decide
theorem g_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
theorem g_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
theorem g_mem_KA {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ZMod 2) (s : Finset ι)
    (c : ι → ZMod 2) :
    c ∈ g_KA A s ↔ (∀ x, x ∉ s → c x = 0) ∧ ∀ x ∈ s, ∑ l ∈ s, A x l * c l = 0 := by
  simp [g_KA]
theorem g_iso {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ZMod 2) (s : Finset ι) (u : ι)
    (hu : u ∈ s) (hA : ∀ x y, A x y = A y x) (h0 : ∀ l ∈ s, A u l = 0) :
    (g_KA A s).card = (g_KA A (s.erase u)).card * 2 := by
  have h2 : (Finset.univ : Finset (ZMod 2)).card = 2 := by simp
  suffices H : (g_KA A s).card =
      ((g_KA A (s.erase u)) ×ˢ (Finset.univ : Finset (ZMod 2))).card by
    rw [H, Finset.card_product, h2]
  apply Finset.card_nbij' (fun c => (Function.update c u 0, c u))
    (fun p => Function.update p.1 u p.2)
  · intro c hc
    rw [Finset.mem_coe, g_mem_KA] at hc
    obtain ⟨hs, he⟩ := hc
    rw [Finset.mem_coe, Finset.mem_product, g_mem_KA]
    try dsimp only
    refine ⟨⟨?_, ?_⟩, Finset.mem_univ _⟩
    · intro x hx
      by_cases hxu : x = u
      · subst hxu; simp
      · rw [Function.update_of_ne hxu]
        apply hs
        intro hxs; exact hx (Finset.mem_erase.mpr ⟨hxu, hxs⟩)
    · intro x hx
      have hxs := Finset.mem_of_mem_erase hx
      have := he x hxs
      rw [← Finset.add_sum_erase s _ hu, hA x u, h0 x hxs, zero_mul, zero_add] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, g_mem_KA] at hp
    obtain ⟨⟨hs, he⟩, -⟩ := hp
    rw [Finset.mem_coe, g_mem_KA]
    try dsimp only
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxu : x ≠ u := fun h => hx (h ▸ hu)
      rw [Function.update_of_ne hxu]
      apply hs
      intro h; exact hx (Finset.mem_of_mem_erase h)
    · intro x hx
      rw [← Finset.add_sum_erase s _ hu]
      have hrest : ∑ l ∈ s.erase u, A x l * Function.update p.1 u p.2 l
          = ∑ l ∈ s.erase u, A x l * p.1 l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
      rw [hrest]
      by_cases hxu : x = u
      · rw [hxu, h0 u hu, zero_mul, zero_add]
        apply Finset.sum_eq_zero
        intro l hl
        rw [h0 l (Finset.mem_of_mem_erase hl), zero_mul]
      · rw [hA x u, h0 x hx, zero_mul, zero_add]
        exact he x (Finset.mem_erase.mpr ⟨hxu, hx⟩)
  · intro c _
    simp
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, g_mem_KA] at hp
    obtain ⟨⟨hs, _⟩, -⟩ := hp
    have hpu : p.1 u = 0 := hs u (Finset.notMem_erase u s)
    obtain ⟨p1, p2⟩ := p
    simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
    funext x
    by_cases hx : x = u
    · rw [hx, Function.update_self]; exact hpu.symm
    · rw [Function.update_of_ne hx]
theorem g_split2 {ι : Type} [DecidableEq ι] (s : Finset ι) (u v : ι) (hu : u ∈ s) (hv : v ∈ s)
    (huv : u ≠ v) (f : ι → ZMod 2) :
    ∑ l ∈ s, f l = f u + f v + ∑ l ∈ (s.erase u).erase v, f l := by
  rw [← Finset.add_sum_erase s f hu, ← Finset.add_sum_erase (s.erase u) f
    (Finset.mem_erase.mpr ⟨huv.symm, hv⟩), add_assoc]
theorem g_piv {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ZMod 2) (s : Finset ι)
    (u v : ι) (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) (hA : ∀ x y, A x y = A y x)
    (hd : ∀ x, A x x = 0) (h1 : A u v = 1) :
    (g_KA A s).card = (g_KA (fun x l => A x l + A x u * A v l + A x v * A u l)
      ((s.erase u).erase v)).card := by
  have hut : u ∉ (s.erase u).erase v :=
    fun h => Finset.notMem_erase u s (Finset.mem_of_mem_erase h)
  have hvt : v ∉ (s.erase u).erase v := Finset.notMem_erase v _
  have hts : ∀ x, x ∈ (s.erase u).erase v → x ∈ s :=
    fun x h => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  have hmt : ∀ x, x ∈ s → x ≠ u → x ≠ v → x ∈ (s.erase u).erase v := fun x h h1 h2 =>
    Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, h⟩⟩
  have hsp : ∀ f : ι → ZMod 2, ∑ l ∈ s, f l = f u + f v + ∑ l ∈ (s.erase u).erase v, f l :=
    fun f => g_split2 s u v hu hv huv f
  generalize (s.erase u).erase v = t at hut hvt hts hmt hsp ⊢
  have h1' : A v u = 1 := by rw [hA]; exact h1
  have hfac : ∀ c ∈ g_KA A s, c v = ∑ l ∈ t, A u l * c l ∧ c u = ∑ l ∈ t, A v l * c l := by
    intro c hc
    rw [g_mem_KA] at hc
    have heu := hc.2 u hu
    rw [hsp, hd u, h1, zero_mul, one_mul, zero_add] at heu
    have hev := hc.2 v hv
    rw [hsp, hd v, h1', zero_mul, one_mul, add_zero] at hev
    exact ⟨g_eq _ _ heu, g_eq _ _ hev⟩
  have hct : ∀ c : ι → ZMod 2, ∀ l ∈ t,
      (if l = u ∨ l = v then (0 : ZMod 2) else c l) = c l := by
    intro c l hl
    rw [if_neg]
    rintro (h | h)
    · exact hut (h ▸ hl)
    · exact hvt (h ▸ hl)
  apply Finset.card_nbij' (fun c => fun x => if x = u ∨ x = v then 0 else c x)
    (fun d => Function.update (Function.update d u (∑ l ∈ t, A v l * d l)) v
      (∑ l ∈ t, A u l * d l))
  · intro c hc
    obtain ⟨hcv, hcu⟩ := hfac c hc
    rw [Finset.mem_coe, g_mem_KA] at hc
    obtain ⟨hs, he⟩ := hc
    rw [Finset.mem_coe, g_mem_KA]
    try dsimp only
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases h : x = u ∨ x = v
      · rw [if_pos h]
      · rw [if_neg h]
        push_neg at h
        apply hs
        intro hxs
        exact hx (hmt x hxs h.1 h.2)
    · intro x hx
      have hex := he x (hts x hx)
      rw [hsp] at hex
      have hs1 : ∑ l ∈ t, (A x l + A x u * A v l + A x v * A u l) *
          (if l = u ∨ l = v then (0 : ZMod 2) else c l) =
          ∑ l ∈ t, (A x l + A x u * A v l + A x v * A u l) * c l :=
        Finset.sum_congr rfl (fun l hl => by rw [hct c l hl])
      rw [hs1]
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [← hcu, ← hcv]
      linear_combination hex
  · intro d hd'
    rw [Finset.mem_coe, g_mem_KA] at hd'
    obtain ⟨hs, he⟩ := hd'
    rw [Finset.mem_coe, g_mem_KA]
    try dsimp only
    have hdt : ∀ l ∈ t, Function.update (Function.update d u (∑ l ∈ t, A v l * d l)) v
          (∑ l ∈ t, A u l * d l) l = d l := by
      intro l hl
      have hlu : l ≠ u := fun h => hut (h ▸ hl)
      have hlv : l ≠ v := fun h => hvt (h ▸ hl)
      rw [Function.update_of_ne hlv, Function.update_of_ne hlu]
    have hdu : Function.update (Function.update d u (∑ l ∈ t, A v l * d l)) v
          (∑ l ∈ t, A u l * d l) u = ∑ l ∈ t, A v l * d l := by
      rw [Function.update_of_ne huv, Function.update_self]
    have hdv : Function.update (Function.update d u (∑ l ∈ t, A v l * d l)) v
          (∑ l ∈ t, A u l * d l) v = ∑ l ∈ t, A u l * d l := by
      rw [Function.update_self]
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxu : x ≠ u := fun h => hx (h ▸ hu)
      have hxv : x ≠ v := fun h => hx (h ▸ hv)
      rw [Function.update_of_ne hxv, Function.update_of_ne hxu]
      apply hs
      intro h; exact hx (hts x h)
    · intro x hx
      have hs1 : ∑ l ∈ t, A x l * Function.update (Function.update d u (∑ l ∈ t, A v l * d l)) v
          (∑ l ∈ t, A u l * d l) l = ∑ l ∈ t, A x l * d l :=
        Finset.sum_congr rfl (fun l hl => by rw [hdt l hl])
      rw [hsp, hdu, hdv, hs1]
      by_cases hxu : x = u
      · rw [hxu, hd u, h1, zero_mul, one_mul, zero_add, g_two]
      · by_cases hxv : x = v
        · rw [hxv, hd v, h1', zero_mul, one_mul, add_zero, g_two]
        · have hex := he x (hmt x hx hxu hxv)
          simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hex
          linear_combination hex
  · intro c hc
    obtain ⟨hcv, hcu⟩ := hfac c hc
    try dsimp only
    have hs1 : ∑ l ∈ t, A v l * (if l = u ∨ l = v then (0 : ZMod 2) else c l) =
        ∑ l ∈ t, A v l * c l :=
      Finset.sum_congr rfl (fun l hl => by rw [hct c l hl])
    have hs2 : ∑ l ∈ t, A u l * (if l = u ∨ l = v then (0 : ZMod 2) else c l) =
        ∑ l ∈ t, A u l * c l :=
      Finset.sum_congr rfl (fun l hl => by rw [hct c l hl])
    rw [hs1, hs2, ← hcu, ← hcv]
    funext x
    by_cases hxv : x = v
    · rw [hxv, Function.update_self]
    · rw [Function.update_of_ne hxv]
      by_cases hxu : x = u
      · rw [hxu, Function.update_self]
      · rw [Function.update_of_ne hxu]
        try dsimp only
        rw [if_neg]
        rintro (h | h)
        · exact hxu h
        · exact hxv h
  · intro d hd'
    rw [Finset.mem_coe, g_mem_KA] at hd'
    obtain ⟨hs, _⟩ := hd'
    funext x
    try dsimp only
    by_cases h : x = u ∨ x = v
    · rw [if_pos h]
      rcases h with h | h
      · rw [h]; exact (hs u hut).symm
      · rw [h]; exact (hs v hvt).symm
    · rw [if_neg h]
      push_neg at h
      rw [Function.update_of_ne h.2, Function.update_of_ne h.1]
theorem g_par {ι : Type} [Fintype ι] [DecidableEq ι] : ∀ (n : ℕ) (A : ι → ι → ZMod 2)
    (s : Finset ι), s.card = n → (∀ x y, A x y = A y x) → (∀ x, A x x = 0) →
    ∃ k, (g_KA A s).card = 2 ^ k ∧ k % 2 = n % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A s hn hA hd
  rcases s.eq_empty_or_nonempty with h | ⟨u, hu⟩
  · subst h
    refine ⟨0, ?_, ?_⟩
    · have : g_KA A ∅ = {0} := by
        ext c
        rw [g_mem_KA, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, -⟩; funext x; exact h1 x (Finset.notMem_empty x)
        · rintro rfl; exact ⟨fun _ _ => rfl, fun x hx => absurd hx (Finset.notMem_empty x)⟩
      rw [this]; rfl
    · simp at hn; omega
  · by_cases h0 : ∀ l ∈ s, A u l = 0
    · have hc : (s.erase u).card = n - 1 := by rw [Finset.card_erase_of_mem hu, hn]
      have hpos : 0 < n := by rw [← hn]; exact Finset.card_pos.mpr ⟨u, hu⟩
      obtain ⟨k, hk1, hk2⟩ := ih (n - 1) (by omega) A (s.erase u) hc hA hd
      refine ⟨k + 1, ?_, ?_⟩
      · rw [g_iso A s u hu hA h0, hk1, pow_succ]
      · omega
    · push_neg at h0
      obtain ⟨v, hv, hne⟩ := h0
      have huv : u ≠ v := by
        rintro rfl; exact hne (hd u)
      have h1 := g_one _ hne
      have hn2 : 2 ≤ n := by
        rw [← hn]
        have hsub : ({u, v} : Finset ι) ⊆ s := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_pair huv] at h2
        exact h2
      have hc : ((s.erase u).erase v).card = n - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hv⟩),
          Finset.card_erase_of_mem hu, hn]
        omega
      obtain ⟨k, hk1, hk2⟩ := ih (n - 2) (by omega)
        (fun x l => A x l + A x u * A v l + A x v * A u l) ((s.erase u).erase v) hc
        (by
          intro x y
          show A x y + A x u * A v y + A x v * A u y = A y x + A y u * A v x + A y v * A u x
          rw [hA y x, hA y u, hA v x, hA y v, hA u x]
          ring)
        (by
          intro x
          show A x x + A x u * A v x + A x v * A u x = 0
          rw [hd x, hA v x, hA u x, zero_add, mul_comm (A x v), g_two])
      exact ⟨k, by rw [g_piv A s u v hu hv huv hA hd h1, hk1], by omega⟩
def g_K {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι) (s : Finset ι) :
    Finset (ι → ZMod 2) :=
  (Finset.univ : Finset (ι → ZMod 2)).filter
    (fun c => (∀ x, x ∉ s → c x = 0) ∧ ∀ x, ∑ l ∈ nbr x, c l = 0)
theorem g_mem_K {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι) (s : Finset ι)
    (c : ι → ZMod 2) :
    c ∈ g_K nbr s ↔ (∀ x, x ∉ s → c x = 0) ∧ ∀ x, ∑ l ∈ nbr x, c l = 0 := by
  simp only [g_K, Finset.mem_filter, Finset.mem_univ, true_and]
theorem g_K_eq {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (s : Finset ι) (hcl : ∀ x ∈ s, nbr x ⊆ s) :
    g_K nbr s = g_KA (fun x l => if l ∈ nbr x then (1 : ZMod 2) else 0) s := by
  ext c
  rw [g_mem_K, g_mem_KA]
  have key : ∀ x ∈ s, ∑ l ∈ s, (if l ∈ nbr x then (1 : ZMod 2) else 0) * c l
      = ∑ l ∈ nbr x, c l := by
    intro x hx
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hcl x hx)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => by rw [key x hx]; exact h2 x⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x => ?_⟩
    by_cases hx : x ∈ s
    · rw [← key x hx]; exact h2 x hx
    · apply Finset.sum_eq_zero
      intro l hl
      apply h1
      intro hls
      exact hx (hcl l hls (hsymm x l hl))
theorem g_split {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (s t : Finset ι) (hst : Disjoint s t)
    (hs : ∀ x ∈ s, nbr x ⊆ s) (ht : ∀ x ∈ t, nbr x ⊆ t) :
    (g_K nbr (s ∪ t)).card = (g_K nbr s).card * (g_K nbr t).card := by
  rw [← Finset.card_product]
  have hres : ∀ (w : Finset ι), (∀ x ∈ w, nbr x ⊆ w) → ∀ c : ι → ZMod 2,
      (∀ x, ∑ l ∈ nbr x, c l = 0) → (fun x => if x ∈ w then c x else 0) ∈ g_K nbr w := by
    intro w hw c hc
    rw [g_mem_K]
    refine ⟨fun x hx => if_neg hx, fun x => ?_⟩
    by_cases hx : x ∈ w
    · rw [← hc x]
      apply Finset.sum_congr rfl
      intro l hl
      rw [if_pos (hw x hx hl)]
    · apply Finset.sum_eq_zero
      intro l hl
      rw [if_neg]
      intro hlw
      exact hx (hw l hlw (hsymm x l hl))
  apply Finset.card_nbij'
    (fun c => ((fun x => if x ∈ s then c x else 0), (fun x => if x ∈ t then c x else 0)))
    (fun p => p.1 + p.2)
  · intro c hc
    rw [Finset.mem_coe, g_mem_K] at hc
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨hres s hs c hc.2, hres t ht c hc.2⟩
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, g_mem_K, g_mem_K] at hp
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
    rw [Finset.mem_coe, g_mem_K]
    try dsimp only
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · rw [Finset.mem_union, not_or] at hx
      rw [Pi.add_apply, h1 x hx.1, h3 x hx.2, add_zero]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, h2 x, h4 x, add_zero]
  · intro c hc
    rw [Finset.mem_coe, g_mem_K] at hc
    funext x
    simp only [Pi.add_apply]
    by_cases hxs : x ∈ s
    · have hxt : x ∉ t := Finset.disjoint_left.mp hst hxs
      rw [if_pos hxs, if_neg hxt, add_zero]
    · rw [if_neg hxs, zero_add]
      by_cases hxt : x ∈ t
      · rw [if_pos hxt]
      · rw [if_neg hxt]
        exact (hc.1 x (by rw [Finset.mem_union]; tauto)).symm
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, g_mem_K, g_mem_K] at hp
    obtain ⟨⟨h1, _⟩, ⟨h3, _⟩⟩ := hp
    refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
    · show (if x ∈ s then p.1 x + p.2 x else 0) = p.1 x
      by_cases hxs : x ∈ s
      · rw [if_pos hxs, h3 x (Finset.disjoint_left.mp hst hxs), add_zero]
      · rw [if_neg hxs, h1 x hxs]
    · show (if x ∈ t then p.1 x + p.2 x else 0) = p.2 x
      by_cases hxt : x ∈ t
      · rw [if_pos hxt, h1 x (Finset.disjoint_right.mp hst hxt), zero_add]
      · rw [if_neg hxt, h3 x hxt]
theorem g_clos {ι : Type} (R : ι → ι → Prop) (Q : ι → Prop) (h : ∀ a b, R a b → (Q a ↔ Q b)) :
    ∀ a b, Relation.EqvGen R a b → (Q a ↔ Q b) := by
  intro a b hab
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
theorem g_L2 {ι : Type} [DecidableEq ι] (N : Finset ι) (hN : N.card ≤ 2) (d : ι → ZMod 2)
    (z : ι) (hz : z ∈ N) (hdz : d z = 0) (hsum : ∑ l ∈ N, d l = 0) : ∀ w ∈ N, d w = 0 := by
  intro w hw
  by_cases hwz : w = z
  · rw [hwz]; exact hdz
  · have hsub : ({z, w} : Finset ι) ⊆ N := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have heq : ({z, w} : Finset ι) = N := Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_pair (Ne.symm hwz)]; exact hN)
    rw [← heq, Finset.sum_pair (Ne.symm hwz), hdz, zero_add] at hsum
    exact hsum
theorem g_prop {ι : Type} [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (hdeg : ∀ i, (nbr i).card ≤ 2) (d : ι → ZMod 2)
    (hd : ∀ x, ∑ l ∈ nbr x, d l = 0) (y : ι) (hy : d y = 0) (hyn : ∀ w ∈ nbr y, d w = 0) :
    ∀ z, Relation.EqvGen (fun u v => v ∈ nbr u) y z → d z = 0 := by
  have key := g_clos (fun u v => v ∈ nbr u) (fun z => d z = 0 ∧ ∀ w ∈ nbr z, d w = 0) (by
    intro a b hab
    constructor
    · rintro ⟨ha, han⟩
      have hb := han b hab
      exact ⟨hb, g_L2 (nbr b) (hdeg b) d a (hsymm a b hab) ha (hd b)⟩
    · rintro ⟨hb, hbn⟩
      have ha := hbn a (hsymm a b hab)
      exact ⟨ha, g_L2 (nbr a) (hdeg a) d b hab hb (hd a)⟩)
  intro z hz
  exact ((key y z hz).mp ⟨hy, hyn⟩).1
theorem g_inj {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (hdeg : ∀ i, (nbr i).card ≤ 2)
    (C : Finset ι) (hC : ∀ y ∈ C, ∀ z ∈ C, Relation.EqvGen (fun u v => v ∈ nbr u) y z)
    (c c' : ι → ZMod 2) (hc : c ∈ g_K nbr C) (hc' : c' ∈ g_K nbr C) (y : ι) (hy : y ∈ C)
    (h1 : c y = c' y) (h2 : ∀ w ∈ nbr y, c w = c' w) : c = c' := by
  rw [g_mem_K] at hc hc'
  have hd : ∀ x, ∑ l ∈ nbr x, (c - c') l = 0 := by
    intro x
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hc.2 x, hc'.2 x, sub_zero]
  have hp := g_prop nbr hsymm hdeg (c - c') hd y (by rw [Pi.sub_apply, h1, sub_self])
    (by intro w hw; rw [Pi.sub_apply, h2 w hw, sub_self])
  funext z
  by_cases hz : z ∈ C
  · have := hp z (hC y hy z hz)
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  · rw [hc.1 z hz, hc'.1 z hz]
theorem g_B1 {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (hdeg : ∀ i, (nbr i).card ≤ 2)
    (C : Finset ι) (hC : ∀ y ∈ C, ∀ z ∈ C, Relation.EqvGen (fun u v => v ∈ nbr u) y z)
    (x : ι) (hx : x ∈ C) : (g_K nbr C).card ≤ 4 := by
  have h4 : (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4 := by simp
  rw [← h4]
  rcases (nbr x).eq_empty_or_nonempty with h | ⟨a, ha⟩
  · apply Finset.card_le_card_of_injOn (fun c => (c x, c x))
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro c hc c' hc' heq
      simp only [Prod.mk.injEq] at heq
      exact g_inj nbr hsymm hdeg C hC c c' hc hc' x hx heq.1
        (by rw [h]; intro w hw; exact absurd hw (Finset.notMem_empty w))
  · apply Finset.card_le_card_of_injOn (fun c => (c x, c a))
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro c hc c' hc' heq
      simp only [Prod.mk.injEq] at heq
      apply g_inj nbr hsymm hdeg C hC c c' hc hc' x hx heq.1
      have hc2 : c ∈ g_K nbr C := hc
      have hc2' : c' ∈ g_K nbr C := hc'
      rw [g_mem_K] at hc2 hc2'
      intro w hw
      have := g_L2 (nbr x) (hdeg x) (c - c') a ha (by rw [Pi.sub_apply, heq.2, sub_self])
        (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, hc2.2 x, hc2'.2 x, sub_zero]) w hw
      rw [Pi.sub_apply, sub_eq_zero] at this
      exact this
theorem g_B2 {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (hdeg : ∀ i, (nbr i).card ≤ 2)
    (C : Finset ι) (hC : ∀ y ∈ C, ∀ z ∈ C, Relation.EqvGen (fun u v => v ∈ nbr u) y z)
    (y : ι) (hy : y ∈ C) (hdy : (nbr y).card ≤ 1) : (g_K nbr C).card ≤ 2 := by
  have h2 : (Finset.univ : Finset (ZMod 2)).card = 2 := by simp
  refine le_trans ?_ (le_of_eq h2)
  apply Finset.card_le_card_of_injOn (fun c => c y)
  · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro c hc c' hc' heq
    apply g_inj nbr hsymm hdeg C hC c c' hc hc' y hy heq
    have hc2 : c ∈ g_K nbr C := hc
    have hc2' : c' ∈ g_K nbr C := hc'
    rw [g_mem_K] at hc2 hc2'
    intro w hw
    have hN : nbr y = {w} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hw, fun z hz => Finset.card_le_one.mp hdy z hz w hw⟩
    have e1 := hc2.2 y
    have e2 := hc2'.2 y
    rw [hN, Finset.sum_singleton] at e1 e2
    rw [e1, e2]
theorem g_B3 {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (C : Finset ι) (hcl : ∀ y ∈ C, nbr y ⊆ C)
    (x : ι) (hx : x ∈ C) (h2 : ∀ l ∈ C, (nbr l).card = 2) : 2 ≤ (g_K nbr C).card := by
  have h0 : (0 : ι → ZMod 2) ∈ g_K nbr C := by
    rw [g_mem_K]
    exact ⟨fun _ _ => rfl, fun _ => by simp⟩
  have h1 : (fun l => if l ∈ C then (1 : ZMod 2) else 0) ∈ g_K nbr C := by
    rw [g_mem_K]
    refine ⟨fun l hl => if_neg hl, fun y => ?_⟩
    by_cases hy : y ∈ C
    · rw [Finset.sum_congr rfl (fun l hl => if_pos (hcl y hy hl)), Finset.sum_const, h2 y hy]
      decide
    · apply Finset.sum_eq_zero
      intro l hl
      rw [if_neg]
      intro hlC
      exact hy (hcl l hlC (hsymm y l hl))
  have hne : (0 : ι → ZMod 2) ≠ (fun l => if l ∈ C then (1 : ZMod 2) else 0) := by
    intro h
    have := congrFun h x
    rw [if_pos hx, Pi.zero_apply] at this
    exact absurd this (by decide : ¬ ((0 : ZMod 2) = 1))
  calc 2 = ({0, fun l => if l ∈ C then (1 : ZMod 2) else 0} : Finset (ι → ZMod 2)).card :=
        (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card (by
        intro c hc
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption)
theorem g_comp {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι)
    (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (hirr : ∀ i, i ∉ nbr i)
    (hdeg : ∀ i, (nbr i).card ≤ 2) (C : Finset ι) (x : ι)
    (hC : ∀ l, l ∈ C ↔ Relation.EqvGen (fun u v => v ∈ nbr u) x l) :
    (g_K nbr C).card = 2 ^ (if C.card % 2 = 1 then 1 else
      if ∀ l ∈ C, (nbr l).card = 2 then 2 else 0) := by
  have hxC : x ∈ C := (hC x).mpr (Relation.EqvGen.refl x)
  have hcl : ∀ y ∈ C, nbr y ⊆ C := by
    intro y hy l hl
    exact (hC l).mpr (Relation.EqvGen.trans _ _ _ ((hC y).mp hy) (Relation.EqvGen.rel _ _ hl))
  have hEq : ∀ y ∈ C, ∀ z ∈ C, Relation.EqvGen (fun u v => v ∈ nbr u) y z := by
    intro y hy z hz
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ((hC y).mp hy)) ((hC z).mp hz)
  obtain ⟨k, hk1, hk2⟩ := g_par C.card (fun x l => if l ∈ nbr x then (1 : ZMod 2) else 0) C rfl
    (by
      intro a b
      by_cases h : b ∈ nbr a
      · rw [if_pos h, if_pos (hsymm a b h)]
      · rw [if_neg h, if_neg (fun h' => h (hsymm b a h'))])
    (by intro a; rw [if_neg (hirr a)])
  have hk : (g_K nbr C).card = 2 ^ k := by rw [g_K_eq nbr hsymm C hcl]; exact hk1
  rw [hk]
  have hB1 := g_B1 nbr hsymm hdeg C hEq x hxC
  rw [hk] at hB1
  have hk2' : k ≤ 2 := by
    by_contra h
    push_neg at h
    have := le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) h) hB1
    norm_num at this
  split_ifs with hodd hall
  · have : k = 1 := by omega
    rw [this]
  · have hB3 := g_B3 nbr hsymm C hcl x hxC hall
    rw [hk] at hB3
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hB3
    have : k = 2 := by omega
    rw [this]
  · push_neg at hall
    obtain ⟨y, hy, hy2⟩ := hall
    have hy1 : (nbr y).card ≤ 1 := by have := hdeg y; omega
    have hB2 := g_B2 nbr hsymm hdeg C hEq y hy hy1
    rw [hk] at hB2
    have hk1' : k ≤ 1 := by
      by_contra h
      push_neg at h
      have := le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) h) hB2
      norm_num at this
    have : k = 0 := by omega
    rw [this]
theorem g_K_empty {ι : Type} [Fintype ι] [DecidableEq ι] (nbr : ι → Finset ι) :
    (g_K nbr ∅).card = 1 := by
  have : g_K nbr ∅ = {0} := by
    ext c
    rw [g_mem_K, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩; funext x; exact h1 x (Finset.notMem_empty x)
    · rintro rfl; exact ⟨fun _ _ => rfl, fun x => by simp⟩
  rw [this, Finset.card_singleton]
theorem g_ker {ι : Type} [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (hr : Function.Injective r)
    (nbr : ι → Finset ι) (hsymm : ∀ i l, l ∈ nbr i → i ∈ nbr l) (hirr : ∀ i, i ∉ nbr i)
    (hdeg : ∀ i, (nbr i).card ≤ 2) :
    let same := fun (i l : ι) => @decide (Relation.EqvGen (fun u v => v ∈ nbr u) i l)
      (Classical.propDecidable _)
    let groupAt := fun i => (Finset.univ : Finset ι).filter (fun l => same i l = true)
    let reps := (Finset.univ : Finset ι).filter (fun i => ∀ l ∈ groupAt i, r i ≤ r l)
    let nullity : Nat := ∑ i ∈ reps,
      if (groupAt i).card % 2 = 1 then 1 else
      if ∀ l ∈ groupAt i, (nbr l).card = 2 then 2 else 0
    ((Finset.univ : Finset (ι → ZMod 2)).filter
      (fun c => ∀ i, (∑ l ∈ nbr i, c l) = 0)).card = 2 ^ nullity := by
  intro same groupAt reps nullity
  have hmem : ∀ i l, l ∈ groupAt i ↔ Relation.EqvGen (fun u v => v ∈ nbr u) i l := by
    intro i l
    simp only [groupAt, same, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff]
  have hrep : ∀ i, i ∈ reps ↔ ∀ l ∈ groupAt i, r i ≤ r l := by
    intro i
    simp only [reps, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcl : ∀ i, ∀ y ∈ groupAt i, nbr y ⊆ groupAt i := by
    intro i y hy l hl
    exact (hmem i l).mpr
      (Relation.EqvGen.trans _ _ _ ((hmem i y).mp hy) (Relation.EqvGen.rel _ _ hl))
  have hdisj : ∀ i ∈ reps, ∀ j ∈ reps, i ≠ j → Disjoint (groupAt i) (groupAt j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hij' : Relation.EqvGen (fun u v => v ∈ nbr u) i j :=
      Relation.EqvGen.trans _ _ _ ((hmem i z).mp hzi)
        (Relation.EqvGen.symm _ _ ((hmem j z).mp hzj))
    have h1 := (hrep i).mp hi j ((hmem i j).mpr hij')
    have h2 := (hrep j).mp hj i ((hmem j i).mpr (Relation.EqvGen.symm _ _ hij'))
    exact hij (hr (le_antisymm h1 h2))
  have main : ∀ T : Finset ι, T ⊆ reps → (g_K nbr (T.biUnion groupAt)).card =
      2 ^ (∑ i ∈ T, (if (groupAt i).card % 2 = 1 then 1 else
        if ∀ l ∈ groupAt i, (nbr l).card = 2 then 2 else 0)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; rw [Finset.biUnion_empty, g_K_empty, Finset.sum_empty, pow_zero]
    | insert j T hj ih =>
      intro hT
      have hjr : j ∈ reps := hT (Finset.mem_insert_self j T)
      have hTr : T ⊆ reps := fun x hx => hT (Finset.mem_insert_of_mem hx)
      have hd : Disjoint (groupAt j) (T.biUnion groupAt) := by
        rw [Finset.disjoint_biUnion_right]
        intro i hi
        exact hdisj j hjr i (hTr hi) (fun h => hj (by rw [h]; exact hi))
      have hc : ∀ y ∈ T.biUnion groupAt, nbr y ⊆ T.biUnion groupAt := by
        intro y hy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨i, hi, hyi⟩ := hy
        intro l hl
        rw [Finset.mem_biUnion]
        exact ⟨i, hi, hcl i y hyi hl⟩
      rw [Finset.biUnion_insert, g_split nbr hsymm _ _ hd (hcl j) hc,
        g_comp nbr hsymm hirr hdeg (groupAt j) j (hmem j), ih hTr, Finset.sum_insert hj, pow_add]
  have hU : reps.biUnion groupAt = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    rw [Finset.mem_biUnion]
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (groupAt z) r
      ⟨z, (hmem z z).mpr (Relation.EqvGen.refl z)⟩
    refine ⟨m, (hrep m).mpr ?_, (hmem m z).mpr (Relation.EqvGen.symm _ _ ((hmem z m).mp hm))⟩
    intro l hl
    exact hmin l ((hmem z l).mpr
      (Relation.EqvGen.trans _ _ _ ((hmem z m).mp hm) ((hmem m l).mp hl)))
  have hK : g_K nbr Finset.univ = (Finset.univ : Finset (ι → ZMod 2)).filter
      (fun c => ∀ i, (∑ l ∈ nbr i, c l) = 0) := by
    ext c
    rw [g_mem_K, Finset.mem_filter]
    simp
  have hfin := main reps (Finset.Subset.refl _)
  rw [hU, hK] at hfin
  exact hfin
theorem m_z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
theorem m_add_self : ∀ a : ZMod 2, a + a = 0 := by decide
theorem m_addeq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
theorem m_ne01 : (0 : ZMod 2) ≠ 1 := by decide
theorem m_two : (2 : ZMod 2) = 0 := by decide
theorem m_loc {s : ℕ} (cu cv : Fin s → ZMod 2) (a b : ZMod 2) :
    (∀ p, a * cv p + cu p * b = 0) ↔
      ((cu = cv ∧ cu ≠ 0 → a = b) ∧ (cu ≠ cv → (cv ≠ 0 → a = 0) ∧ (cu ≠ 0 → b = 0))) := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases m_z2 a with rfl | rfl <;> rcases m_z2 b with rfl | rfl
  · constructor
    · intro _
      exact ⟨fun _ => rfl, fun _ => ⟨fun _ => rfl, fun _ => rfl⟩⟩
    · intro _ p
      ring
  · constructor
    · intro h
      have hc : cu = 0 := funext (fun p => by simpa using h p)
      exact ⟨fun h' => absurd hc h'.2, fun _ => ⟨fun _ => rfl, fun h' => absurd hc h'⟩⟩
    · rintro ⟨h1, h2⟩ p
      by_cases hp : cu p = 0
      · rw [hp]; ring
      · have hcu : cu ≠ 0 := fun h => hp (congrFun h p)
        by_cases he : cu = cv
        · exact absurd (h1 ⟨he, hcu⟩) h01
        · exact absurd ((h2 he).2 hcu) h10
  · constructor
    · intro h
      have hc : cv = 0 := funext (fun p => by simpa using h p)
      exact ⟨fun h' => absurd (h'.1.trans hc) h'.2, fun _ => ⟨fun h' => absurd hc h', fun _ => rfl⟩⟩
    · rintro ⟨h1, h2⟩ p
      by_cases hp : cv p = 0
      · rw [hp]; ring
      · have hcv : cv ≠ 0 := fun h => hp (congrFun h p)
        by_cases he : cu = cv
        · exact absurd (h1 ⟨he, by rw [he]; exact hcv⟩) h10
        · exact absurd ((h2 he).1 hcv) h10
  · constructor
    · intro h
      have hc : cu = cv := funext (fun p => m_addeq _ _ (by simpa [add_comm] using h p))
      exact ⟨fun _ => rfl, fun h' => absurd hc h'⟩
    · rintro ⟨h1, h2⟩ p
      by_cases he : cu = cv
      · rw [he, one_mul, mul_one]; exact m_add_self _
      · by_cases hcv : cv = 0
        · have hcu : cu ≠ 0 := fun h => he (h.trans hcv.symm)
          exact absurd ((h2 he).2 hcu) h10
        · exact absurd ((h2 he).1 hcv) h10
theorem m_glob {k s : ℕ} (U V : Fin k → Fin k) (c : Fin k → Fin s → ZMod 2)
    (test : Finset (Fin k)) (y : Fin k → ZMod 2) :
    (∀ j ∈ test, ∀ p, y (U j) * c (V j) p + c (U j) p * y (V j) = 0) ↔
    ((∀ u v, (∃ j ∈ test, u = U j ∧ v = V j ∧ c u = c v ∧ c u ≠ 0) → y u = y v) ∧
     (∀ z, (∃ j ∈ test, c (U j) ≠ c (V j) ∧ (z = U j ∧ c (V j) ≠ 0 ∨ z = V j ∧ c (U j) ≠ 0)) →
        y z = 0)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro u v ⟨j, hj, rfl, rfl, he, hn⟩
      exact ((m_loc _ _ _ _).1 (h j hj)).1 ⟨he, hn⟩
    · rintro z ⟨j, hj, hne, ⟨rfl, hv⟩ | ⟨rfl, hu⟩⟩
      · exact (((m_loc _ _ _ _).1 (h j hj)).2 hne).1 hv
      · exact (((m_loc _ _ _ _).1 (h j hj)).2 hne).2 hu
  · rintro ⟨h1, h2⟩ j hj
    apply (m_loc _ _ _ _).2
    exact ⟨fun hh => h1 _ _ ⟨j, hj, rfl, rfl, hh.1, hh.2⟩,
      fun hne => ⟨fun hv => h2 _ ⟨j, hj, hne, Or.inl ⟨rfl, hv⟩⟩,
        fun hu => h2 _ ⟨j, hj, hne, Or.inr ⟨rfl, hu⟩⟩⟩⟩
theorem m_inv {α : Type} (r : α → α → Prop) (f : α → Prop) (h : ∀ a b, r a b → (f a ↔ f b)) :
    ∀ a b, Relation.EqvGen r a b → (f a ↔ f b) := by
  intro a b hab
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
theorem m_inv_eq {α β : Type} (r : α → α → Prop) (f : α → β) (h : ∀ a b, r a b → f a = f b) :
    ∀ a b, Relation.EqvGen r a b → f a = f b := by
  intro a b hab
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
theorem m_cut_lt (k : ℕ) (hk : 0 < k) (r : Fin k → Fin k → Prop) (t1 t2 : Fin k)
    (hlt : t1.val < t2.val)
    (hr : ∀ a b, r a b → b = (⟨(a.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) ∧ a ≠ t1 ∧ a ≠ t2) :
    ¬ Relation.EqvGen r t1 t2 ∧
      ¬ Relation.EqvGen r (⟨(t1.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k)
        (⟨(t2.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) := by
  have ht2 := t2.isLt
  have key : ∀ a b, Relation.EqvGen r a b →
      ((t1.val < a.val ∧ a.val ≤ t2.val) ↔ (t1.val < b.val ∧ b.val ≤ t2.val)) := by
    apply m_inv r (fun w => t1.val < w.val ∧ w.val ≤ t2.val)
    intro a b hab
    obtain ⟨hb, ha1, ha2⟩ := hr a b hab
    subst hb
    have ha1' : a.val ≠ t1.val := fun h => ha1 (Fin.ext h)
    have ha2' : a.val ≠ t2.val := fun h => ha2 (Fin.ext h)
    have hak := a.isLt
    show (t1.val < a.val ∧ a.val ≤ t2.val) ↔ (t1.val < (a.val + 1) % k ∧ (a.val + 1) % k ≤ t2.val)
    rcases Nat.lt_or_ge (a.val + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]
      constructor
      · intro h'; omega
      · intro h'; omega
    · rw [show a.val + 1 = k by omega, Nat.mod_self]
      constructor
      · intro h'; omega
      · intro h'; omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h3 := (key _ _ h).2 ⟨hlt, le_refl _⟩
    exact absurd h3.1 (lt_irrefl _)
  · have e1 : (t1.val + 1) % k = t1.val + 1 := Nat.mod_eq_of_lt (by omega)
    have h3 := (key _ _ h).1
      (by show t1.val < (t1.val + 1) % k ∧ (t1.val + 1) % k ≤ t2.val; rw [e1]; omega)
    have h4 : t1.val < (t2.val + 1) % k ∧ (t2.val + 1) % k ≤ t2.val := h3
    rcases Nat.lt_or_ge (t2.val + 1) k with h5 | h5
    · rw [Nat.mod_eq_of_lt h5] at h4
      omega
    · rw [show t2.val + 1 = k by omega, Nat.mod_self] at h4
      omega
theorem m_cut (k : ℕ) (hk : 0 < k) (r : Fin k → Fin k → Prop) (t1 t2 : Fin k) (hne : t1 ≠ t2)
    (hr : ∀ a b, r a b → b = (⟨(a.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) ∧ a ≠ t1 ∧ a ≠ t2) :
    ¬ Relation.EqvGen r t1 t2 ∧
      ¬ Relation.EqvGen r (⟨(t1.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k)
        (⟨(t2.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) := by
  rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · exact m_cut_lt k hk r t1 t2 h hr
  · have := m_cut_lt k hk r t2 t1 h
      (fun a b hab => ⟨(hr a b hab).1, (hr a b hab).2.2, (hr a b hab).2.1⟩)
    exact ⟨fun h' => this.1 (Relation.EqvGen.symm _ _ h'),
      fun h' => this.2 (Relation.EqvGen.symm _ _ h')⟩
theorem m_card2 {ι : Type} [DecidableEq ι] (N : Finset ι) (PA PB : ι → Prop)
    (hcov : ∀ l ∈ N, PA l ∨ PB l) (hA : ∀ a b, PA a → PA b → a = b)
    (hB : ∀ a b, PB a → PB b → a = b) : N.card ≤ 2 := by
  classical
  have h1 : (N.filter PA).card ≤ 1 := Finset.card_le_one.mpr
    (fun a ha b hb => hA a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  have h2 : (N.filter PB).card ≤ 1 := Finset.card_le_one.mpr
    (fun a ha b hb => hB a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  have h3 : N ⊆ N.filter PA ∪ N.filter PB := by
    intro l hl
    rcases hcov l hl with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl, h⟩)
  have h4 := Finset.card_le_card h3
  have h5 := Finset.card_union_le (N.filter PA) (N.filter PB)
  omega
end PEqualNP.Outside.L_lib_750
theorem PEqualNP.Outside.L_lib_750 : 
  ∀ (k s : Nat) (hk : 0 < k),
    let F := ZMod 2
    let W := Fin k → F
    let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
    ∀ (D : Fin s → W) (test : Finset (Fin k)),
    let color := fun (j : Fin k) (p : Fin s) => D p j
    let chi := fun (x : W) (j : Fin k) => x j + (1+x (ix (j.val+1))) * x (ix (j.val+2))
    let out := fun (x : W) (p : Fin s) (j : Fin k) => chi (x+D p) j - chi x j
    let edge := fun (u v : Fin k) => ∃ j ∈ test,
      u = ix (j.val+1) ∧ v = ix (j.val+2) ∧ color u = color v ∧ color u ≠ 0
    let joined := fun u v => @decide (Relation.EqvGen edge u v) (Classical.propDecidable _)
    let pinned := fun (z : Fin k) => ∃ j ∈ test,
      let u := ix (j.val+1)
      let v := ix (j.val+2)
      color u ≠ color v ∧ ((z = u ∧ color v ≠ 0) ∨ (z = v ∧ color u ≠ 0))
    let free := (Finset.univ : Finset (Fin k)).filter (fun i =>
      (∀ j, joined i j = true → i.val ≤ j.val) ∧ (∀ j, joined i j = true → ¬pinned j))
    let block := fun (i : ↥free) (j : Fin k) => (if joined i.val j then 1 else 0 : F)
    let liftBits := fun (b : ↥free → F) (j : Fin k) => ∑ i, b i * block i j
    ∀ (base lin outMask : W),
      let phase := fun x : W => dotProduct lin x + dotProduct outMask (chi x)
      let sign := fun f : F => if f = 0 then (1 : ℤ) else -1
      let fiber := (Finset.univ : Finset W).filter (fun x => ∀ p, ∀ j ∈ test, out x p j = out base p j)
      let coeff := fun (i l : ↥free) =>
        ∑ j : Fin k, outMask j * (block i (ix (j.val+1)) * block l (ix (j.val+2)) +
                                   block l (ix (j.val+1)) * block i (ix (j.val+2)))
      let nbr := fun (i : ↥free) => (Finset.univ : Finset ↥free).filter (fun l => coeff i l = 1)
      let same := fun (i l : ↥free) => @decide (Relation.EqvGen (fun u v => v ∈ nbr u) i l)
        (Classical.propDecidable _)
      let groupAt := fun i => (Finset.univ : Finset ↥free).filter (fun l => same i l = true)
      let reps := (Finset.univ : Finset ↥free).filter (fun i => ∀ l ∈ groupAt i, i.val.val ≤ l.val.val)
      let nullity : Nat := ∑ i ∈ reps,
        if (groupAt i).card % 2 = 1 then 1 else
        if ∀ l ∈ groupAt i, (nbr l).card = 2 then 2 else 0
      let good := ∀ b : ↥free → F, (∀ i, (∑ l ∈ nbr i, b l) = 0) →
        phase (base+liftBits b) = phase base
      (∀ i : ↥free, (nbr i).card ≤ 2) ∧
      (∑ x ∈ fiber, sign (phase x))^2 =
        (if good then (2 : ℤ)^(free.card+nullity) else 0) := by
  intro k s hk F W ix D test color chi out edge joined pinned free block liftBits base lin outMask
    phase sign fiber coeff nbr same groupAt reps nullity good
  have z2 : ∀ a : F, a = 0 ∨ a = 1 := PEqualNP.Outside.L_lib_750.m_z2
  have hself : ∀ a : F, a + a = 0 := PEqualNP.Outside.L_lib_750.m_add_self
  have h01 : (0 : F) ≠ 1 := PEqualNP.Outside.L_lib_750.m_ne01
  have htwo : (2 : F) = 0 := PEqualNP.Outside.L_lib_750.m_two
  have hJ : ∀ u v, joined u v = true ↔ Relation.EqvGen edge u v := fun u v => @decide_eq_true_iff _ (Classical.propDecidable _)
  have hsc : ∀ j : Fin k, ix (j.val + 2) = ix ((ix (j.val + 1)).val + 1) := by
    intro j
    apply Fin.ext
    show (j.val + 1 + 1) % k = ((j.val + 1) % k + 1) % k
    exact (Nat.mod_add_mod _ _ _).symm
  have hEdge : ∀ u v, edge u v → v = ix (u.val + 1) := by
    rintro u v ⟨j, -, rfl, rfl, -, -⟩
    exact hsc j
  have hfr : ∀ i : ↥free, (∀ j, Relation.EqvGen edge i.val j → i.val.val ≤ j.val) ∧
      (∀ j, Relation.EqvGen edge i.val j → ¬pinned j) := by
    intro i
    have h := i.2
    simp only [free, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨fun j hj => h.1 j ((hJ _ _).2 hj), fun j hj => h.2 j ((hJ _ _).2 hj)⟩
  have hfr' : ∀ m : Fin k, (∀ j, Relation.EqvGen edge m j → m.val ≤ j.val) →
      (∀ j, Relation.EqvGen edge m j → ¬pinned j) → m ∈ free := by
    intro m h1 h2
    simp only [free, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun j hj => h1 j ((hJ _ _).1 hj), fun j hj => h2 j ((hJ _ _).1 hj)⟩
  have huniq : ∀ i l : ↥free, Relation.EqvGen edge i.val l.val → i = l := by
    intro i l h
    apply Subtype.ext
    apply Fin.ext
    exact le_antisymm ((hfr i).1 _ h) ((hfr l).1 _ (Relation.EqvGen.symm _ _ h))
  have hB1 : ∀ (i : ↥free) (w : Fin k), Relation.EqvGen edge i.val w → block i w = 1 :=
    fun i w h => if_pos ((hJ _ _).2 h)
  have hB0 : ∀ (i : ↥free) (w : Fin k), ¬Relation.EqvGen edge i.val w → block i w = 0 :=
    fun i w h => if_neg (fun h' => h ((hJ _ _).1 h'))
  have hLdef : ∀ (b : ↥free → F) (w : Fin k), liftBits b w = ∑ i, b i * block i w :=
    fun b w => rfl
  have hLc : ∀ (b : ↥free → F) (u v : Fin k), Relation.EqvGen edge u v →
      liftBits b u = liftBits b v := by
    intro b u v h
    rw [hLdef, hLdef]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : Relation.EqvGen edge i.val u
    · rw [hB1 i u hi, hB1 i v (Relation.EqvGen.trans _ _ _ hi h)]
    · rw [hB0 i u hi, hB0 i v (fun h' => hi (Relation.EqvGen.trans _ _ _ h'
        (Relation.EqvGen.symm _ _ h)))]
  have hLp : ∀ (b : ↥free → F) (z : Fin k), pinned z → liftBits b z = 0 := by
    intro b z hz
    rw [hLdef]
    exact Finset.sum_eq_zero (fun i _ => by rw [hB0 i z (fun h => (hfr i).2 z h hz), mul_zero])
  have hLv : ∀ (b : ↥free → F) (i : ↥free), liftBits b i.val = b i := by
    intro b i
    rw [hLdef, Finset.sum_eq_single i]
    · rw [hB1 i i.val (Relation.EqvGen.refl _), mul_one]
    · intro l _ hl
      rw [hB0 l i.val (fun h => hl (huniq l i h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hLy : ∀ y : W, (∀ u v, edge u v → y u = y v) → (∀ z, pinned z → y z = 0) →
      liftBits (fun l => y l.val) = y := by
    intro y hy1 hy2
    have hyJ : ∀ u v, Relation.EqvGen edge u v → y u = y v :=
      PEqualNP.Outside.L_lib_750.m_inv_eq edge y hy1
    funext w
    by_cases hex : ∃ i : ↥free, Relation.EqvGen edge i.val w
    · obtain ⟨i, hi⟩ := hex
      rw [hLdef, Finset.sum_eq_single i]
      · rw [hB1 i w hi, mul_one]
        exact hyJ _ _ hi
      · intro l _ hl
        rw [hB0 l w (fun h => hl (huniq l i (Relation.EqvGen.trans _ _ _ h
          (Relation.EqvGen.symm _ _ hi)))), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · have hz : liftBits (fun l => y l.val) w = 0 := by
        rw [hLdef]
        exact Finset.sum_eq_zero (fun i _ => by rw [hB0 i w (fun h => hex ⟨i, h⟩), mul_zero])
      rw [hz]
      classical
      have hexn : ∃ n, ∃ t : Fin k, t.val = n ∧ Relation.EqvGen edge w t :=
        ⟨w.val, w, rfl, Relation.EqvGen.refl _⟩
      obtain ⟨m, hm1, hm2⟩ := Nat.find_spec hexn
      have hmin : ∀ t : Fin k, Relation.EqvGen edge w t → m.val ≤ t.val := by
        intro t ht
        rw [hm1]
        exact Nat.find_min' hexn ⟨t, rfl, ht⟩
      by_contra hyw
      have hnp : ∀ j, Relation.EqvGen edge m j → ¬pinned j := by
        intro j hj hpj
        apply hyw
        rw [hyJ w j (Relation.EqvGen.trans _ _ _ hm2 hj), hy2 j hpj]
      have hmf : m ∈ free := hfr' m (fun j hj => hmin j (Relation.EqvGen.trans _ _ _ hm2 hj)) hnp
      exact hex ⟨⟨m, hmf⟩, Relation.EqvGen.symm _ _ hm2⟩
  have hpa : ∀ (f g : W) (j : Fin k), (f + g) j = f j + g j := fun _ _ _ => rfl
  have hout : ∀ (y : W) (p : Fin s) (j : Fin k), out (base + y) p j - out base p j =
      y (ix (j.val+1)) * D p (ix (j.val+2)) + D p (ix (j.val+1)) * y (ix (j.val+2)) := by
    intro y p j
    simp only [out, chi, hpa]
    ring
  have hfibchar : ∀ y : W, (∀ p, ∀ j ∈ test, out (base + y) p j = out base p j) ↔
      ((∀ u v, edge u v → y u = y v) ∧ (∀ z, pinned z → y z = 0)) := by
    intro y
    refine Iff.trans ?_ (PEqualNP.Outside.L_lib_750.m_glob (fun j => ix (j.val+1))
      (fun j => ix (j.val+2)) color test y)
    constructor
    · intro h j hj p
      have h2 := hout y p j
      rw [h p j hj, sub_self] at h2
      exact h2.symm
    · intro h p j hj
      rw [← sub_eq_zero, hout]
      exact h j hj p
  have hfib : ∑ x ∈ fiber, sign (phase x) =
      ∑ b : ↥free → ZMod 2, (if phase (base + liftBits b) = 0 then (1:ℤ) else -1) := by
    have hmem : ∀ x, x ∈ fiber ↔ ∀ p, ∀ j ∈ test, out x p j = out base p j := by
      intro x
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    have hli : ∀ x ∈ fiber, base + liftBits (fun l => (x - base) l.val) = x := by
      intro x hx
      have hy : ∀ p, ∀ j ∈ test, out (base + (x - base)) p j = out base p j := by
        rw [add_sub_cancel]
        exact (hmem x).1 hx
      obtain ⟨h1, h2⟩ := (hfibchar (x - base)).1 hy
      rw [hLy (x - base) h1 h2, add_sub_cancel]
    refine Finset.sum_nbij' (fun x => fun l => (x - base) l.val) (fun b => base + liftBits b)
      ?_ ?_ ?_ ?_ ?_
    · intro x _
      exact Finset.mem_univ _
    · intro b _
      exact (hmem _).2 ((hfibchar (liftBits b)).2
        ⟨fun u v h => hLc b u v (Relation.EqvGen.rel _ _ h), fun z hz => hLp b z hz⟩)
    · exact hli
    · intro b _
      funext l
      show (base + liftBits b - base) l.val = b l
      rw [add_sub_cancel_left]
      exact hLv b l
    · intro x hx
      show (if phase x = 0 then (1:ℤ) else -1) =
        if phase (base + liftBits (fun l => (x - base) l.val)) = 0 then 1 else -1
      rw [hli x hx]
  have hL0 : liftBits 0 = 0 := by
    funext w
    rw [hLdef]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  have h0 : phase (base + liftBits 0) = phase base := by rw [hL0, add_zero]
  have hLadd : ∀ b c : ↥free → F, liftBits (b + c) = liftBits b + liftBits c := by
    intro b c
    funext w
    simp only [hLdef, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hph : ∀ x : W, phase x = ∑ j, (lin j * x j + outMask j * chi x j) := by
    intro x
    simp only [phase, dotProduct, Finset.sum_add_distrib]
  have hquad : ∀ x y z : W, phase (x + (y + z)) = phase (x + y) + phase (x + z) + phase x +
      ∑ j, outMask j * (y (ix (j.val+1)) * z (ix (j.val+2)) + z (ix (j.val+1)) * y (ix (j.val+2))) := by
    intro x y z
    rw [hph, hph, hph, hph]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [chi, hpa]
    linear_combination (-(lin j * x j) - outMask j * x j -
      outMask j * (x (ix (j.val+2)) + x (ix (j.val+1)) * x (ix (j.val+2)))) * htwo
  have hnbrsum : ∀ (i : ↥free) (c : ↥free → F), ∑ l ∈ nbr i, c l = ∑ l, coeff i l * c l := by
    intro i c
    simp only [nbr]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rcases z2 (coeff i l) with h | h
    · rw [if_neg (show ¬ (coeff i l = 1) from fun h' => h01 (h.symm.trans h')), h, zero_mul]
    · rw [if_pos h, h, one_mul]
  have hbil : ∀ b c : ↥free → F, ∑ j, outMask j * (liftBits b (ix (j.val+1)) *
      liftBits c (ix (j.val+2)) + liftBits c (ix (j.val+1)) * liftBits b (ix (j.val+2))) =
      ∑ i, b i * ∑ l ∈ nbr i, c l := by
    intro b c
    have st1 : ∀ j : Fin k, outMask j * (liftBits b (ix (j.val+1)) * liftBits c (ix (j.val+2)) +
        liftBits c (ix (j.val+1)) * liftBits b (ix (j.val+2))) =
        ∑ i, b i * (outMask j * (block i (ix (j.val+1)) * liftBits c (ix (j.val+2)) +
          liftBits c (ix (j.val+1)) * block i (ix (j.val+2)))) := by
      intro j
      rw [hLdef b (ix (j.val+1)), hLdef b (ix (j.val+2)), Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have st3 : ∀ i : ↥free, ∑ j, outMask j * (block i (ix (j.val+1)) * liftBits c (ix (j.val+2)) +
        liftBits c (ix (j.val+1)) * block i (ix (j.val+2))) = ∑ l ∈ nbr i, c l := by
      intro i
      rw [hnbrsum]
      simp only [coeff, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hLdef c (ix (j.val+1)), hLdef c (ix (j.val+2)), Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [Finset.sum_congr rfl (fun j _ => st1 j), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum, st3 i]
  have hq : ∀ b c : ↥free → F, phase (base + liftBits (b + c)) = phase (base + liftBits b) +
      phase (base + liftBits c) + phase (base + liftBits 0) + ∑ i, b i * ∑ l ∈ nbr i, c l := by
    intro b c
    rw [hLadd, h0, ← hbil b c]
    exact hquad base (liftBits b) (liftBits c)
  have hsymm : ∀ i l : ↥free, l ∈ nbr i → i ∈ nbr l := by
    intro i l h
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    rw [← h]
    simp only [coeff]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hirr : ∀ i : ↥free, i ∉ nbr i := by
    intro i hi
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hc0 : coeff i i = 0 := by
      simp only [coeff]
      exact Finset.sum_eq_zero (fun j _ => by rw [hself, mul_zero])
    rw [hc0] at hi
    exact h01 hi
  have hexit : ∀ (i : ↥free) (t1 t2 : Fin k), Relation.EqvGen edge i.val t1 →
      ¬Relation.EqvGen edge i.val (ix (t1.val+1)) → Relation.EqvGen edge i.val t2 →
      ¬Relation.EqvGen edge i.val (ix (t2.val+1)) → t1 = t2 := by
    intro i t1 t2 h1 h1' h2 h2'
    by_contra hne
    have hc := PEqualNP.Outside.L_lib_750.m_cut k hk edge t1 t2 hne (by
      intro a b hab
      have hb := hEdge a b hab
      subst hb
      refine ⟨rfl, ?_, ?_⟩
      · rintro rfl
        exact h1' (Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.rel _ _ hab))
      · rintro rfl
        exact h2' (Relation.EqvGen.trans _ _ _ h2 (Relation.EqvGen.rel _ _ hab)))
    exact hc.1 (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) h2)
  have hentry : ∀ (i : ↥free) (t1 t2 : Fin k), ¬Relation.EqvGen edge i.val t1 →
      Relation.EqvGen edge i.val (ix (t1.val+1)) → ¬Relation.EqvGen edge i.val t2 →
      Relation.EqvGen edge i.val (ix (t2.val+1)) → t1 = t2 := by
    intro i t1 t2 h1 h1' h2 h2'
    by_contra hne
    have hc := PEqualNP.Outside.L_lib_750.m_cut k hk edge t1 t2 hne (by
      intro a b hab
      have hb := hEdge a b hab
      subst hb
      refine ⟨rfl, ?_, ?_⟩
      · rintro rfl
        exact h1 (Relation.EqvGen.trans _ _ _ h1' (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ hab)))
      · rintro rfl
        exact h2 (Relation.EqvGen.trans _ _ _ h2' (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ hab))))
    exact hc.2 (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1') h2')
  have hnbr : ∀ i l : ↥free, l ∈ nbr i → ∃ t : Fin k,
      (Relation.EqvGen edge i.val t ∧ ¬Relation.EqvGen edge i.val (ix (t.val+1)) ∧
        Relation.EqvGen edge l.val (ix (t.val+1))) ∨
      (¬Relation.EqvGen edge i.val t ∧ Relation.EqvGen edge i.val (ix (t.val+1)) ∧
        Relation.EqvGen edge l.val t) := by
    intro i l hl
    have hli : l ≠ i := by
      rintro rfl
      exact hirr _ hl
    have hnj : ¬Relation.EqvGen edge i.val l.val := fun h => hli (huniq i l h).symm
    have hc1 : coeff i l = 1 := by
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact hl
    have hne : coeff i l ≠ 0 := by
      rw [hc1]
      exact fun h => h01 h.symm
    obtain ⟨j, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hj : outMask j * (block i (ix (j.val+1)) * block l (ix (j.val+2)) +
        block l (ix (j.val+1)) * block i (ix (j.val+2))) ≠ 0 := hj0
    have hor : (Relation.EqvGen edge i.val (ix (j.val+1)) ∧
        Relation.EqvGen edge l.val (ix (j.val+2))) ∨
        (Relation.EqvGen edge l.val (ix (j.val+1)) ∧
        Relation.EqvGen edge i.val (ix (j.val+2))) := by
      by_contra hcon
      push_neg at hcon
      apply hj
      have e1 : block i (ix (j.val+1)) * block l (ix (j.val+2)) = 0 := by
        by_cases ha : Relation.EqvGen edge i.val (ix (j.val+1))
        · rw [hB0 l _ (hcon.1 ha), mul_zero]
        · rw [hB0 i _ ha, zero_mul]
      have e2 : block l (ix (j.val+1)) * block i (ix (j.val+2)) = 0 := by
        by_cases ha : Relation.EqvGen edge l.val (ix (j.val+1))
        · rw [hB0 i _ (hcon.2 ha), mul_zero]
        · rw [hB0 l _ ha, zero_mul]
      rw [e1, e2, add_zero, mul_zero]
    refine ⟨ix (j.val+1), ?_⟩
    rw [← hsc j]
    rcases hor with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨ha, fun h => hnj (Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.symm _ _ hb)), hb⟩
    · exact Or.inr ⟨fun h => hnj (Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.symm _ _ ha)), hb, ha⟩
  have hdeg : ∀ i : ↥free, (nbr i).card ≤ 2 := by
    intro i
    refine PEqualNP.Outside.L_lib_750.m_card2 (nbr i)
      (fun l => ∃ t : Fin k, Relation.EqvGen edge i.val t ∧
        ¬Relation.EqvGen edge i.val (ix (t.val+1)) ∧ Relation.EqvGen edge l.val (ix (t.val+1)))
      (fun l => ∃ t : Fin k, ¬Relation.EqvGen edge i.val t ∧
        Relation.EqvGen edge i.val (ix (t.val+1)) ∧ Relation.EqvGen edge l.val t) ?_ ?_ ?_
    · intro l hl
      obtain ⟨t, ht | ht⟩ := hnbr i l hl
      · exact Or.inl ⟨t, ht⟩
      · exact Or.inr ⟨t, ht⟩
    · intro a b ha hb
      obtain ⟨t1, h1, h1', h1''⟩ := ha
      obtain ⟨t2, h2, h2', h2''⟩ := hb
      obtain rfl := hexit i t1 t2 h1 h1' h2 h2'
      exact huniq a b (Relation.EqvGen.trans _ _ _ h1'' (Relation.EqvGen.symm _ _ h2''))
    · intro a b ha hb
      obtain ⟨t1, h1, h1', h1''⟩ := ha
      obtain ⟨t2, h2, h2', h2''⟩ := hb
      obtain rfl := hentry i t1 t2 h1 h1' h2 h2'
      exact huniq a b (Relation.EqvGen.trans _ _ _ h1'' (Relation.EqvGen.symm _ _ h2''))
  have hr : Function.Injective (fun i : ↥free => i.val.val) :=
    fun a b h => Subtype.ext (Fin.ext h)
  refine ⟨hdeg, ?_⟩
  have hG : (∑ b : ↥free → ZMod 2, (if phase (base + liftBits b) = 0 then (1:ℤ) else -1)) ^ 2 =
      if (∀ c : ↥free → ZMod 2, (∀ i, (∑ l ∈ nbr i, c l) = 0) →
        phase (base + liftBits c) = phase (base + liftBits 0)) then
        (2 : ℤ) ^ (Fintype.card ↥free) *
          (((Finset.univ : Finset (↥free → ZMod 2)).filter
            (fun c => ∀ i, (∑ l ∈ nbr i, c l) = 0)).card : ℤ)
      else 0 :=
    PEqualNP.Outside.L_lib_750.q_gauss nbr (fun b => phase (base + liftBits b)) hq
  have hK : ((Finset.univ : Finset (↥free → ZMod 2)).filter
      (fun c => ∀ i, (∑ l ∈ nbr i, c l) = 0)).card = 2 ^ nullity :=
    PEqualNP.Outside.L_lib_750.g_ker (fun i : ↥free => i.val.val) hr nbr hsymm hirr hdeg
  rw [hfib, hG, hK, Fintype.card_coe]
  by_cases hc : good
  · have hc' : ∀ c : ↥free → ZMod 2, (∀ i, (∑ l ∈ nbr i, c l) = 0) →
        phase (base + liftBits c) = phase (base + liftBits 0) :=
      fun c hcc => (hc c hcc).trans h0.symm
    rw [if_pos hc', if_pos hc, pow_add, Nat.cast_pow, Nat.cast_ofNat]
  · have hc' : ¬ ∀ c : ↥free → ZMod 2, (∀ i, (∑ l ∈ nbr i, c l) = 0) →
        phase (base + liftBits c) = phase (base + liftBits 0) :=
      fun h => hc (fun b hb => (h b hb).trans h0)
    rw [if_neg hc', if_neg hc]
