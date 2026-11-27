import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_317

def stepM (w : ℕ) (f : (Fin (w + 1) → Bool) → Bool) :
    Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2) :=
  fun a c => ∑ x : Fin (w + 1) → Bool,
    if (Fin.init x = a ∧ Fin.tail x = c ∧ f x = true) then 1 else 0

def transN (w : ℕ) (g : ℕ → (Fin (w + 1) → Bool) → Bool) :
    ℕ → Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2)
  | 0 => 1
  | t + 1 => transN w g t * stepM w (g t)

def gExt (w h : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool) (i : ℕ) :
    (Fin (w + 1) → Bool) → Bool :=
  fun x => if hi : i < h then P (⟨i, hi⟩, x) else false

def trans (w h : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool) :
    Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2) :=
  transN w (gExt w h P) h

theorem Z_card_mat (w : ℕ) :
    Fintype.card (Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2)) = 2 ^ (2 ^ w * 2 ^ w) := by
  have h1 : Fintype.card (Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2)) =
      Fintype.card ((Fin w → Bool) × (Fin w → Bool) → ZMod 2) :=
    Fintype.card_congr (Equiv.curry _ _ _).symm
  rw [h1]
  simp

theorem A_basic (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    0 < 2 ^ Nat.gcd m s - 1 ∧
    (2 ^ m - 1) = (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) * (2 ^ Nat.gcd m s - 1) ∧
    (2 ^ (m - s) - 1) = (2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1) * (2 ^ Nat.gcd m s - 1) ∧
    Nat.Coprime ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) ∧
    0 < (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) := by
  have hg : 0 < Nat.gcd m s := Nat.gcd_pos_of_pos_left _ hm
  have hgg : Nat.gcd m (m - s) = Nat.gcd m s := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
    rw [Nat.add_sub_cancel_left]
    rw [Nat.gcd_comm (s + t) t, Nat.gcd_comm (s + t) s]
    simp [Nat.gcd_comm]
  have hgcd : Nat.gcd (2 ^ m - 1) (2 ^ (m - s) - 1) = 2 ^ Nat.gcd m s - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hgg]
  have hpos : 0 < 2 ^ Nat.gcd m s - 1 := by
    have : 2 ^ 1 ≤ 2 ^ Nat.gcd m s := Nat.pow_le_pow_right (by norm_num) hg
    omega
  have hN : 0 < 2 ^ m - 1 := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have d1 : (2 ^ Nat.gcd m s - 1) ∣ (2 ^ m - 1) := by
    rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have d2 : (2 ^ Nat.gcd m s - 1) ∣ (2 ^ (m - s) - 1) := by
    rw [← hgcd]; exact Nat.gcd_dvd_right _ _
  refine ⟨hpos, (Nat.div_mul_cancel d1).symm, (Nat.div_mul_cancel d2).symm, ?_, ?_⟩
  · have := Nat.coprime_div_gcd_div_gcd (m := 2 ^ m - 1) (n := 2 ^ (m - s) - 1) (by rw [hgcd]; exact hpos)
    rw [hgcd] at this
    exact this
  · exact Nat.div_pos (Nat.le_of_dvd hN d1) hpos

theorem nt_dvd (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) (r errors : ℕ)
    (he : errors * (2 ^ m - 1) = r * (2 ^ (m - s) - 1)) :
    (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) ∣ r := by
  obtain ⟨hpos, e1, e2, hc, -⟩ := A_basic m s hm hs
  generalize (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) = p at *
  generalize (2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1) = q at *
  generalize (2 ^ Nat.gcd m s - 1) = dv at *
  rw [e1, e2] at he
  have h2 : errors * p = r * q := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc errors * p * dv = errors * (p * dv) := by ring
      _ = r * (q * dv) := he
      _ = r * q * dv := by ring
  have : p ∣ r * q := ⟨errors, by rw [← h2]; ring⟩
  exact hc.dvd_of_dvd_mul_right this

theorem nt_eq (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) (r : ℕ)
    (hr : (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) ∣ r) :
    (r / ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) * ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) +
      min (r % ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1))) ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)))
      * (2 ^ m - 1) = r * (2 ^ (m - s) - 1) := by
  obtain ⟨hpos, e1, e2, -, hp⟩ := A_basic m s hm hs
  generalize (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) = p at *
  generalize (2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1) = q at *
  generalize (2 ^ Nat.gcd m s - 1) = dv at *
  obtain ⟨t, rfl⟩ := hr
  rw [Nat.mul_div_cancel_left _ hp, Nat.mul_mod_right, Nat.zero_min, e1, e2]
  ring

theorem A_bucket (X : Type) [Fintype X] [DecidableEq X] (m s : ℕ) (hs : s ≤ m)
    (hX : Fintype.card X = 2 ^ m) (z : X → (Fin s → Bool)) :
    2 ^ m * 2 ^ (m - s) ≤
      (Finset.univ.filter (fun p : X × X => z p.1 = z p.2)).card := by
  classical
  have h1 : (Finset.univ.filter (fun p : X × X => z p.1 = z p.2)).card
      = ∑ b : Fin s → Bool, (Finset.univ.filter (fun x : X => z x = b)).card ^ 2 := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    have : ∀ x : X, (∑ y : X, if z x = z y then 1 else 0)
        = (Finset.univ.filter (fun y : X => z y = z x)).card := by
      intro x
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl (fun y _ => by simp [eq_comm])
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := z)]
    apply Finset.sum_congr rfl
    intro b _
    rw [pow_two, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have h2 : ∑ b : Fin s → Bool, (Finset.univ.filter (fun x : X => z x = b)).card = 2 ^ m := by
    rw [← hX, ← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := z) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)).symm
  have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin s → Bool)))
    (f := fun b => (Finset.univ.filter (fun x : X => z x = b)).card)
  rw [h2] at h3
  have hc : (Finset.univ : Finset (Fin s → Bool)).card = 2 ^ s := by
    simp
  rw [hc, ← h1] at h3
  have hpow : (2:ℕ) ^ m = 2 ^ s * 2 ^ (m - s) := by
    rw [← pow_add]; congr 1; omega
  have h4 : 2 ^ s * (2 ^ m * 2 ^ (m - s)) ≤
      2 ^ s * (Finset.univ.filter (fun p : X × X => z p.1 = z p.2)).card := by
    calc 2 ^ s * (2 ^ m * 2 ^ (m - s)) = (2 ^ m) ^ 2 := by rw [pow_two]; nth_rewrite 3 [hpow]; ring
      _ ≤ _ := h3
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

theorem lower_count (X : Type) [Fintype X] [DecidableEq X] (m s : ℕ) (hs : s ≤ m)
    (hX : Fintype.card X = 2 ^ m) (r errors : ℕ)
    (acc : Fin r → X → X → Prop) (z : Fin r → X → (Fin s → Bool))
    (hz : ∀ c x y, z c x = z c y → acc c x y)
    (herr : ∀ x y, x ≠ y →
      (@Finset.filter _ (fun c => acc c x y) (Classical.decPred _) Finset.univ).card ≤ errors) :
    r * (2 ^ (m - s) - 1) ≤ errors * (2 ^ m - 1) := by
  classical
  have hoff : (Finset.univ : Finset X).offDiag.card = 2 ^ m * 2 ^ m - 2 ^ m := by
    rw [Finset.offDiag_card, Finset.card_univ, hX]
  have hK : 1 ≤ 2 ^ (m - s) := Nat.one_le_two_pow
  have hNp : 0 < 2 ^ m := by positivity

  have hper : ∀ c : Fin r, 2 ^ m * (2 ^ (m - s) - 1) ≤
      ((Finset.univ : Finset X).offDiag.filter (fun p => acc c p.1 p.2)).card := by
    intro c
    have hb := A_bucket X m s hs hX (z c)
    have hsub : Finset.univ.filter (fun p : X × X => z c p.1 = z c p.2) ⊆
        ((Finset.univ : Finset X).offDiag.filter (fun p => acc c p.1 p.2)) ∪
          (Finset.univ : Finset X).diag := by
      intro p hp
      rw [Finset.mem_filter] at hp
      by_cases hpe : p.1 = p.2
      · exact Finset.mem_union_right _ (Finset.mem_diag.mpr ⟨Finset.mem_univ _, hpe⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hpe⟩, hz c _ _ hp.2⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.diag_card, Finset.card_univ, hX] at h1
    have h2 : 2 ^ m * (2 ^ (m - s) - 1) = 2 ^ m * 2 ^ (m - s) - 2 ^ m := by
      rw [Nat.mul_sub, mul_one]
    omega
  have hsum : r * (2 ^ m * (2 ^ (m - s) - 1)) ≤
      ∑ c : Fin r, ((Finset.univ : Finset X).offDiag.filter (fun p => acc c p.1 p.2)).card := by
    calc r * (2 ^ m * (2 ^ (m - s) - 1))
        = ∑ _c : Fin r, 2 ^ m * (2 ^ (m - s) - 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c _ => hper c)
  have hswap : ∑ c : Fin r, ((Finset.univ : Finset X).offDiag.filter (fun p => acc c p.1 p.2)).card
      = ∑ p ∈ (Finset.univ : Finset X).offDiag,
          (Finset.univ.filter (fun c : Fin r => acc c p.1 p.2)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hle : ∑ p ∈ (Finset.univ : Finset X).offDiag,
      (Finset.univ.filter (fun c : Fin r => acc c p.1 p.2)).card
      ≤ (2 ^ m * 2 ^ m - 2 ^ m) * errors := by
    rw [← hoff, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    have := herr p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
    convert this using 2
  have hfin : 2 ^ m * (r * (2 ^ (m - s) - 1)) ≤ 2 ^ m * (errors * (2 ^ m - 1)) := by
    calc 2 ^ m * (r * (2 ^ (m - s) - 1)) = r * (2 ^ m * (2 ^ (m - s) - 1)) := by ring
      _ ≤ (2 ^ m * 2 ^ m - 2 ^ m) * errors := by rw [hswap] at hsum; exact hsum.trans hle
      _ = 2 ^ m * (errors * (2 ^ m - 1)) := by
        rw [← Nat.mul_sub_one]; ring
  exact Nat.le_of_mul_le_mul_left hfin hNp

open Finset in
theorem B_count (p : ℕ) (_hp : 0 < p) (A : Finset ℕ) (r : ℕ) (Pr : Fin r → Prop)
    [DecidablePred Pr] (hA : ∀ c : Fin r, Pr c → c.val % p ∈ A) :
    (univ.filter Pr).card ≤ r / p * A.card + min (r % p) A.card := by
  classical
  have h1 : (univ.filter Pr).card ≤
      ((range (r / p) ×ˢ A) ∪ (({r / p} : Finset ℕ) ×ˢ (A.filter (· < r % p)))).card := by
    apply Finset.card_le_card_of_injOn (fun c : Fin r => (c.val / p, c.val % p))
    · intro c hc
      have hc' : Pr c := by simpa using hc
      have hcA := hA c hc'
      have hlt := c.isLt
      have hdm := Nat.div_add_mod c.val p
      have hdm' := Nat.div_add_mod r p
      have hle : c.val / p ≤ r / p := Nat.div_le_div_right hlt.le
      simp only [coe_union, coe_product, Set.mem_union, Set.mem_prod, mem_coe, mem_range,
        mem_singleton, mem_filter]
      rcases Nat.lt_or_ge (c.val / p) (r / p) with h | h
      · exact Or.inl ⟨h, hcA⟩
      · have heq : c.val / p = r / p := le_antisymm hle h
        refine Or.inr ⟨heq, hcA, ?_⟩
        rw [heq] at hdm
        omega
    · intro c1 _ c2 _ h
      simp only [Prod.mk.injEq] at h
      have h1 := Nat.div_add_mod c1.val p
      have h2 := Nat.div_add_mod c2.val p
      rw [h.1, h.2] at h1
      exact Fin.ext (by omega)
  refine h1.trans ((Finset.card_union_le _ _).trans ?_)
  rw [card_product, card_product, card_range, card_singleton, one_mul]
  refine Nat.add_le_add_left (le_min ?_ (Finset.card_filter_le _ _)) _
  calc (A.filter (· < r % p)).card ≤ (range (r % p)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [mem_filter] at hx
        simpa using hx.2
    _ = r % p := card_range _

def B_k (F : Type) [Field F] [CharP F 2] (g : ℕ) : Subfield F :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (iterateFrobenius F 2 g).eqLocusField (RingHom.id F)

theorem B_mem_k (F : Type) [Field F] [CharP F 2] (g : ℕ) (x : F) :
    x ∈ B_k F g ↔ x ^ 2 ^ g = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show (iterateFrobenius F 2 g) x = (RingHom.id F) x ↔ _
  rw [iterateFrobenius_def]
  rfl

theorem B_kcard (F : Type) [Field F] [Fintype F] [CharP F 2] (g : ℕ) (hg : 0 < g)
    (ζ : F) (p : ℕ) (hord : orderOf ζ = p * (2 ^ g - 1)) (hp : 0 < p) :
    Nat.card (B_k F g) = 2 ^ g := by
  classical
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  apply le_antisymm
  · have hne : (Polynomial.X ^ 2 ^ g - Polynomial.X : Polynomial F) ≠ 0 :=
      Polynomial.X_pow_sub_X_ne_zero (by omega)
    have hdeg : (Polynomial.X ^ 2 ^ g - Polynomial.X : Polynomial F).natDegree = 2 ^ g :=
      Polynomial.natDegree_X_pow_sub_X (by omega)
    have hsub : ((B_k F g : Set F)) ⊆
        ↑((Polynomial.X ^ 2 ^ g - Polynomial.X : Polynomial F).roots.toFinset) := by
      intro x hx
      have hx' : x ^ 2 ^ g = x := (B_mem_k F g x).1 hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne,
        Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hx', sub_self]
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 := Multiset.toFinset_card_le (Polynomial.X ^ 2 ^ g - Polynomial.X : Polynomial F).roots
    have h3 := Polynomial.card_roots' (Polynomial.X ^ 2 ^ g - Polynomial.X : Polynomial F)
    rw [hdeg] at h3
    exact h1.trans (h2.trans h3)
  · have hinj : Set.InjOn (fun j : ℕ => ζ ^ (p * j)) ↑(Finset.range (2 ^ g - 1)) := by
      intro j1 h1 j2 h2 h
      simp only [Finset.coe_range, Set.mem_Iio] at h1 h2
      have hI := pow_injOn_Iio_orderOf (G := F) (x := ζ)
      have := hI
        (by rw [Set.mem_Iio, hord]; exact Nat.mul_lt_mul_of_pos_left h1 hp)
        (by rw [Set.mem_Iio, hord]; exact Nat.mul_lt_mul_of_pos_left h2 hp) h
      exact Nat.eq_of_mul_eq_mul_left hp this
    have hζ0 : ζ ≠ 0 := by
      intro h0
      rw [h0] at hord
      have : orderOf (0 : F) = 0 := by
        rw [orderOf_eq_zero_iff']
        intro n hn
        simp [hn.ne']
      rw [this] at hord
      have : 0 < p * (2 ^ g - 1) := Nat.mul_pos hp (by omega)
      omega
    have hsub : (↑(insert (0 : F) ((Finset.range (2 ^ g - 1)).image (fun j : ℕ => ζ ^ (p * j)))) : Set F)
        ⊆ (B_k F g : Set F) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image] at hx
      rcases hx with rfl | ⟨j, _, rfl⟩
      · exact (B_k F g).zero_mem
      · show ζ ^ (p * j) ∈ B_k F g
        rw [B_mem_k, ← pow_mul]
        have e : p * j * 2 ^ g = p * (2 ^ g - 1) * j + p * j := by
          have : 2 ^ g = (2 ^ g - 1) + 1 := by omega
          nth_rewrite 1 [this]
          ring
        rw [e, pow_add, pow_mul, ← hord, pow_orderOf_eq_one, one_pow, one_mul]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem, Finset.card_image_of_injOn hinj,
      Finset.card_range] at h1
    · have : Nat.card (B_k F g) = ((B_k F g : Set F)).ncard := rfl
      rw [this]
      omega
    · simp only [Finset.mem_image, not_exists, not_and]
      intro j _ h
      exact pow_ne_zero _ hζ0 h

theorem B_core (F : Type) [Field F] [Fintype F] [CharP F 2] (m s : ℕ) (hm : 0 < m) (hs : s ≤ m)
    (hF : Fintype.card F = 2 ^ m) :
    ∃ (ζ : F) (W : AddSubgroup F), ζ ≠ 0 ∧ Nat.card W = 2 ^ (m - s) ∧
      0 < (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) ∧
      (∀ (c : ℕ) (x : F), ζ ^ c * x ∈ W → ζ ^ (c % ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1))) * x ∈ W) ∧
      ∀ x : F, x ≠ 0 →
        (@Finset.filter _ (fun c : ℕ => ζ ^ c * x ∈ W) (Classical.decPred _)
          (Finset.range ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)))).card ≤
        (2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1) := by
  classical
  have hg : 0 < Nat.gcd m s := Nat.gcd_pos_of_pos_left s hm
  have hgm : Nat.gcd m s ∣ m := Nat.gcd_dvd_left m s
  have hgs : Nat.gcd m s ∣ m - s := Nat.dvd_sub hgm (Nat.gcd_dvd_right m s)
  generalize Nat.gcd m s = g at *
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hdm : 2 ^ g - 1 ∣ 2 ^ m - 1 := by
    have h := Nat.pow_sub_one_gcd_pow_sub_one 2 m g
    rw [Nat.gcd_eq_right hgm] at h
    rw [← h]
    exact Nat.gcd_dvd_left _ _
  have hdk : 2 ^ g - 1 ∣ 2 ^ (m - s) - 1 := by
    have h := Nat.pow_sub_one_gcd_pow_sub_one 2 (m - s) g
    rw [Nat.gcd_eq_right hgs] at h
    rw [← h]
    exact Nat.gcd_dvd_left _ _
  set dv := 2 ^ g - 1 with hdv
  have hdvpos : 0 < dv := by omega
  set p := (2 ^ m - 1) / dv with hpdef
  have hpd : p * dv = 2 ^ m - 1 := Nat.div_mul_cancel hdm
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0, zero_mul] at hpd; omega
    · exact h0
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hou : orderOf u = 2 ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, Fintype.card_units, hF]
  have hord : orderOf (u : F) = p * dv := by rw [orderOf_units, hou, hpd]
  have hζ0 : (u : F) ≠ 0 := u.ne_zero
  set ζ : F := (u : F) with hζ
  have hkc : Nat.card (B_k F g) = 2 ^ g := B_kcard F g hg ζ p hord hp
  have hu0 : ∀ j : ℕ, ζ ^ (p * j) ∈ B_k F g := by
    intro j
    rw [B_mem_k, ← pow_mul]
    have e : p * j * 2 ^ g = p * dv * j + p * j := by
      have : 2 ^ g = dv + 1 := by omega
      rw [this]
      ring
    rw [e, pow_add, pow_mul, ← hord, pow_orderOf_eq_one, one_pow, one_mul]
  have hcF : Nat.card F = Nat.card (B_k F g) ^ Module.finrank (B_k F g) F :=
    Module.natCard_eq_pow_finrank
  rw [Nat.card_eq_fintype_card, hF, hkc, ← pow_mul] at hcF
  have hmn : m = g * Module.finrank (B_k F g) F := Nat.pow_right_injective (le_refl 2) hcF
  obtain ⟨t, ht⟩ := hgs
  have htn : t ≤ Module.finrank (B_k F g) F := by
    have : g * t ≤ g * Module.finrank (B_k F g) F := by omega
    exact Nat.le_of_mul_le_mul_left this hg
  let b := Module.finBasis (B_k F g) F
  let W : Submodule (B_k F g) F :=
    Submodule.span (B_k F g) (Set.range (fun i : Fin t => b (Fin.castLE htn i)))
  have hfW : Module.finrank (B_k F g) W = t := by
    have hli : LinearIndependent (B_k F g) (fun i : Fin t => b (Fin.castLE htn i)) :=
      b.linearIndependent.comp _ (Fin.castLE_injective htn)
    have := finrank_span_eq_card hli
    simpa using this
  have hcW : Nat.card W = 2 ^ (m - s) := by
    have h : Nat.card W = Nat.card (B_k F g) ^ Module.finrank (B_k F g) W :=
      Module.natCard_eq_pow_finrank
    rw [h, hkc, hfW, ← pow_mul, ht]
  have hsm : ∀ (a : F), a ∈ B_k F g → ∀ x : F, x ∈ W → a * x ∈ W := by
    intro a ha x hx
    exact W.smul_mem (⟨a, ha⟩ : B_k F g) hx
  refine ⟨ζ, W.toAddSubgroup, hζ0, hcW, hp, ?_, ?_⟩
  · intro c x hx
    have e1 : ζ ^ (c % p) * x = (ζ ^ (p * (c / p)))⁻¹ * (ζ ^ c * x) := by
      have : ζ ^ c = ζ ^ (p * (c / p)) * ζ ^ (c % p) := by
        rw [← pow_add, Nat.div_add_mod]
      rw [this]
      field_simp
    rw [e1]
    exact hsm _ ((B_k F g).inv_mem (hu0 _)) _ hx
  · intro x hx
    rw [Nat.le_div_iff_mul_le hdvpos]
    set A := @Finset.filter _ (fun c : ℕ => ζ ^ c * x ∈ W.toAddSubgroup) (Classical.decPred _)
      (Finset.range p) with hA
    have hT : ((Finset.univ.filter (fun y : F => y ∈ W)).erase 0).card = 2 ^ (m - s) - 1 := by
      rw [Finset.card_erase_of_mem (by simp), ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      rw [← hcW]
    rw [← hT, ← Finset.card_range dv, ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun cj : ℕ × ℕ => ζ ^ (cj.1 + p * cj.2) * x)
    · rintro ⟨c, j⟩ hcj
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hA, Finset.mem_filter,
        Finset.mem_range] at hcj
      simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
        Set.mem_ofPred_eq, Set.mem_singleton_iff]
      refine ⟨?_, mul_ne_zero (pow_ne_zero _ hζ0) hx⟩
      have : ζ ^ (c + p * j) * x = ζ ^ (p * j) * (ζ ^ c * x) := by
        rw [pow_add]; ring
      rw [this]
      exact hsm _ (hu0 j) _ hcj.1.2
    · rintro ⟨c1, j1⟩ h1 ⟨c2, j2⟩ h2 h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hA, Finset.mem_filter,
        Finset.mem_range] at h1 h2
      have h' : ζ ^ (c1 + p * j1) = ζ ^ (c2 + p * j2) := mul_right_cancel₀ hx h
      have hb : ∀ c j : ℕ, c < p → j < dv → c + p * j ∈ Set.Iio (orderOf ζ) := by
        intro c j hc hj
        rw [Set.mem_Iio, hord]
        calc c + p * j < p + p * j := by omega
          _ = p * (j + 1) := by ring
          _ ≤ p * dv := Nat.mul_le_mul_left _ hj
      have hI := pow_injOn_Iio_orderOf (G := F) (x := ζ)
      have e := hI (hb c1 j1 h1.1.1 h1.2) (hb c2 j2 h2.1.1 h2.2) h'
      have m1 : (c1 + p * j1) % p = c1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1.1.1]
      have m2 : (c2 + p * j2) % p = c2 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2.1.1]
      have hc : c1 = c2 := by rw [← m1, ← m2, e]
      subst hc
      have : p * j1 = p * j2 := by omega
      rw [Nat.eq_of_mul_eq_mul_left hp this]

theorem hash_exists (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) (E : Type) [Fintype E] [DecidableEq E]
    (hE : Fintype.card E = m) (r : ℕ) :
    ∃ H : Fin r → Fin s → E → ZMod 2, ∀ v : E → ZMod 2, v ≠ 0 →
      (@Finset.filter _ (fun c : Fin r => ∀ j, ∑ e, H c j e * v e = 0) (Classical.decPred _)
        Finset.univ).card ≤
      r / ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) * ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) +
      min (r % ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1))) ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 m hm.ne'
  obtain ⟨ζ, W, hζ, hW, hper, hclos, hcnt⟩ := B_core (GaloisField 2 m) m s hm hs hF
  let W' : Submodule (ZMod 2) (GaloisField 2 m) := AddSubgroup.toZModSubmodule 2 W
  have hmemW : ∀ x, x ∈ W' ↔ x ∈ W := fun x => Iff.rfl
  have hfF : Module.finrank (ZMod 2) (GaloisField 2 m) = m := GaloisField.finrank 2 hm.ne'
  have hfW : Module.finrank (ZMod 2) W' = m - s := by
    have h : Nat.card W' = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) W' :=
      Module.natCard_eq_pow_finrank
    have h' : Nat.card W' = 2 ^ (m - s) := hW
    rw [h', Nat.card_eq_fintype_card, ZMod.card] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hfQ : Module.finrank (ZMod 2) (GaloisField 2 m ⧸ W') = s := by
    have := Submodule.finrank_quotient_add_finrank W'
    omega
  let eQ : (GaloisField 2 m ⧸ W') ≃ₗ[ZMod 2] (Fin s → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfQ, Module.finrank_fin_fun])
  let ι : (E → ZMod 2) ≃ₗ[ZMod 2] GaloisField 2 m :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfF, Module.finrank_fintype_fun_eq_card, hE])
  let φ : Fin r → ((E → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) := fun c =>
    eQ.toLinearMap ∘ₗ W'.mkQ ∘ₗ LinearMap.mulLeft (ZMod 2) (ζ ^ c.val) ∘ₗ ι.toLinearMap
  refine ⟨fun c j e => φ c (fun e' => if e = e' then 1 else 0) j, ?_⟩
  intro v hv
  have hx : ι v ≠ 0 := by
    intro h
    exact hv (ι.map_eq_zero_iff.1 h)
  have hsum : ∀ (c : Fin r) (j : Fin s),
      ∑ e, φ c (fun e' => if e = e' then 1 else 0) j * v e = φ c v j := by
    intro c j
    have h := LinearMap.pi_apply_eq_sum_univ (φ c) v
    rw [h, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro e _
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have key : ∀ c : Fin r, (∀ j, ∑ e, φ c (fun e' => if e = e' then 1 else 0) j * v e = 0) →
      c.val % ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) ∈
        (@Finset.filter _ (fun c : ℕ => ζ ^ c * ι v ∈ W) (Classical.decPred _)
          (Finset.range ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)))) := by
    intro c hc
    have h0 : φ c v = 0 := by
      funext j
      rw [← hsum c j]
      exact hc j
    have h1 : W'.mkQ (ζ ^ c.val * ι v) = 0 := by
      have : eQ (W'.mkQ (ζ ^ c.val * ι v)) = 0 := h0
      exact eQ.map_eq_zero_iff.1 this
    have h2 : ζ ^ c.val * ι v ∈ W := by
      rw [← hmemW]
      simpa using h1
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hper, hclos _ _ h2⟩
  beta_reduce
  refine (@B_count _ hper _ r _ (Classical.decPred _) key).trans ?_
  have hA := hcnt (ι v) hx
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hA) (min_le_min le_rfl hA)

def C_st (w : ℕ) (y : ℕ → Bool) (i : ℕ) : Fin w → Bool := fun j => y (i + j.val)

def C_str (w t : ℕ) (a : Fin w → Bool) (e : Fin t → Bool) : ℕ → Bool :=
  fun j => if h : j < w then a ⟨j, h⟩ else if h2 : j - w < t then e ⟨j - w, h2⟩ else false

lemma C_init_st (w : ℕ) (y : ℕ → Bool) (i : ℕ) :
    Fin.init (C_st (w + 1) y i) = C_st w y i := by
  funext j; simp [Fin.init, C_st]

lemma C_tail_st (w : ℕ) (y : ℕ → Bool) (i : ℕ) :
    Fin.tail (C_st (w + 1) y i) = C_st w y (i + 1) := by
  funext j; simp only [Fin.tail, C_st, Fin.val_succ]; congr 1; omega

lemma C_stepM_alt (w : ℕ) (f : (Fin (w + 1) → Bool) → Bool) (b c : Fin w → Bool) :
    stepM w f b c = ∑ bit : Bool,
      if (Fin.tail (Fin.snoc (α := fun _ => Bool) b bit) = c ∧
          f (Fin.snoc (α := fun _ => Bool) b bit) = true) then 1 else 0 := by
  unfold stepM
  let E : Bool × (Fin w → Bool) ≃ (Fin (w + 1) → Bool) :=
    ⟨fun p => Fin.snoc (α := fun _ => Bool) p.2 p.1, fun x => (x (Fin.last w), Fin.init x),
      fun p => by simp, fun x => by simp⟩
  rw [← Equiv.sum_comp E, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro bit _
  rw [Finset.sum_eq_single b]
  · simp [E]
  · intro s _ hs
    simp [E, hs]
  · simp

lemma C_str_snoc_lt (w t : ℕ) (a : Fin w → Bool) (e : Fin t → Bool) (bit : Bool) (j : ℕ)
    (hj : j < w + t) :
    C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit) j = C_str w t a e j := by
  unfold C_str
  by_cases h : j < w
  · simp [h]
  · have h2 : j - w < t := by omega
    have h3 : j - w < t + 1 := by omega
    simp only [h, h2, h3, dite_false, dite_true]
    have : (⟨j - w, h3⟩ : Fin (t + 1)) = Fin.castSucc ⟨j - w, h2⟩ := rfl
    rw [this, Fin.snoc_castSucc]

lemma C_str_snoc_last (w t : ℕ) (a : Fin w → Bool) (e : Fin t → Bool) (bit : Bool) :
    C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit) (t + w) = bit := by
  unfold C_str
  have h : ¬ (t + w < w + 0) ∨ t = 0 := by omega
  by_cases h1 : t + w < w
  · omega
  · have h3 : t + w - w < t + 1 := by omega
    simp only [h1, h3, dite_false, dite_true]
    have : (⟨t + w - w, h3⟩ : Fin (t + 1)) = Fin.last t := by
      apply Fin.ext; simp
    rw [this, Fin.snoc_last]

lemma C_win_snoc_lt (w t : ℕ) (a : Fin w → Bool) (e : Fin t → Bool) (bit : Bool) (i : ℕ)
    (hi : i < t) :
    C_st (w + 1) (C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit)) i =
      C_st (w + 1) (C_str w t a e) i := by
  funext j
  simp only [C_st]
  apply C_str_snoc_lt
  have := j.2
  omega

lemma C_win_snoc_last (w t : ℕ) (a : Fin w → Bool) (e : Fin t → Bool) (bit : Bool) :
    C_st (w + 1) (C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit)) t =
      Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [C_st, Fin.snoc_last, Fin.val_last]
    exact C_str_snoc_last w t a e bit
  · intro j'
    simp only [C_st, Fin.snoc_castSucc, Fin.val_castSucc]
    apply C_str_snoc_lt
    have := j'.2
    omega

lemma C_path (w : ℕ) (G : ℕ → (Fin (w + 1) → Bool) → Bool) (t : ℕ) (a c : Fin w → Bool) :
    transN w G t a c = ∑ e : Fin t → Bool,
      if (C_st w (C_str w t a e) t = c ∧
          ∀ i, i < t → G i (C_st (w + 1) (C_str w t a e) i) = true) then 1 else 0 := by
  induction t generalizing c with
  | zero =>
    have h0 : ∀ e : Fin 0 → Bool, C_st w (C_str w 0 a e) 0 = a := by
      intro e; funext j; simp [C_st, C_str]
    simp only [transN, Matrix.one_apply, h0]
    simp
  | succ t ih =>
    simp only [transN, Matrix.mul_apply]
    simp_rw [ih, C_stepM_alt]
    let E : Bool × (Fin t → Bool) ≃ (Fin (t + 1) → Bool) :=
      ⟨fun p => Fin.snoc (α := fun _ => Bool) p.2 p.1, fun x => (x (Fin.last t), Fin.init x),
        fun p => by simp, fun x => by simp⟩
    rw [← Equiv.sum_comp E, Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bit _
    rw [Finset.sum_eq_single (C_st w (C_str w t a e) t)]
    · have hlast := C_win_snoc_last w t a e bit
      have hlt := fun i (hi : i < t) => C_win_snoc_lt w t a e bit i hi
      have hst : C_st w (C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit)) (t + 1) =
          Fin.tail (Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit) := by
        rw [← hlast, C_tail_st]
      have hall : (∀ i, i < t + 1 →
          G i (C_st (w + 1) (C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit)) i) = true) ↔
          ((∀ i, i < t → G i (C_st (w + 1) (C_str w t a e) i) = true) ∧
            G t (Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit) = true) := by
        constructor
        · intro H
          refine ⟨fun i hi => ?_, ?_⟩
          · rw [← hlt i hi]; exact H i (by omega)
          · rw [← hlast]; exact H t (by omega)
        · rintro ⟨H1, H2⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · rw [hlt i h]; exact H1 i h
          · subst h; rw [hlast]; exact H2
      have hE : E (bit, e) = Fin.snoc (α := fun _ => Bool) e bit := rfl
      have hc : (C_st w (C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit)) (t + 1) = c ∧
          ∀ i, i < t + 1 →
          G i (C_st (w + 1) (C_str w (t + 1) a (Fin.snoc (α := fun _ => Bool) e bit)) i) = true) ↔
          ((∀ i, i < t → G i (C_st (w + 1) (C_str w t a e) i) = true) ∧
            Fin.tail (Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit) = c ∧
            G t (Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit) = true) := by
        rw [hst, hall]; tauto
      rw [hE, if_congr hc rfl rfl]
      by_cases h1 : ∀ i, i < t → G i (C_st (w + 1) (C_str w t a e) i) = true
      · by_cases h2 : Fin.tail (Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit) = c
        · by_cases h3 : G t (Fin.snoc (α := fun _ => Bool) (C_st w (C_str w t a e) t) bit) = true
          · simp [h1, h2, h3]
          · simp [h1, h2, h3]
        · simp [h1, h2]
      · simp [h1]
    · intro b _ hb
      have : ¬ (C_st w (C_str w t a e) t = b ∧
          ∀ i, i < t → G i (C_st (w + 1) (C_str w t a e) i) = true) := fun h => hb h.1.symm
      simp [this]
    · simp

lemma C_F1 (w n : ℕ) (hn0 : 0 < n) (x : Fin n → Bool) (j : ℕ) (hj : j < w + n) :
    C_str w n (fun j : Fin w => x ⟨j.val % n, Nat.mod_lt _ hn0⟩)
      (fun i : Fin n => x ⟨(w + i.val) % n, Nat.mod_lt _ hn0⟩) j = x ⟨j % n, Nat.mod_lt _ hn0⟩ := by
  unfold C_str
  by_cases h : j < w
  · simp [h]
  · have h2 : j - w < n := by omega
    simp only [h, h2, dite_false, dite_true]
    have h3 : w + (j - w) = j := by omega
    simp only [h3]

lemma C_F2 (w n : ℕ) (hn : w ≤ n) (a : Fin w → Bool) (e : Fin n → Bool)
    (hc : C_st w (C_str w n a e) n = a) (j : ℕ) (hj : j < w + n) :
    C_str w n a e (j % n) = C_str w n a e j := by
  by_cases h : j < n
  · rw [Nat.mod_eq_of_lt h]
  · have hj' : j - n < w := by omega
    have h1 : j % n = j - n := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 := congrFun hc ⟨j - n, hj'⟩
    simp only [C_st] at h2
    have h3 : n + (j - n) = j := by omega
    rw [h3] at h2
    rw [h1, h2]
    simp [C_str, hj']

lemma C_cyc (w n : ℕ) (hn : w ≤ n) (hn0 : 0 < n) (G : ℕ → (Fin (w + 1) → Bool) → Bool) :
    (((Finset.univ.filter (fun x : Fin n → Bool => ∀ i, i < n →
        G i (fun j : Fin (w + 1) => x ⟨(i + j.val) % n, Nat.mod_lt _ hn0⟩) = true)).card : ℕ) :
          ZMod 2) = ∑ a, transN w G n a a := by
  simp_rw [C_path]
  rw [← Fintype.sum_prod_type', Finset.sum_boole]
  congr 1
  refine Finset.card_bij'
    (fun x _ => ((fun j : Fin w => x ⟨j.val % n, Nat.mod_lt _ hn0⟩),
      (fun i : Fin n => x ⟨(w + i.val) % n, Nat.mod_lt _ hn0⟩)))
    (fun p _ => fun i : Fin n => C_str w n p.1 p.2 i.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, ?_⟩
    · funext j
      simp only [C_st]
      rw [C_F1 w n hn0 x _ (by have := j.2; omega)]
      congr 2
      exact Nat.add_mod_left n j.val
    · intro i hi
      have hw : C_st (w + 1) (C_str w n (fun j : Fin w => x ⟨j.val % n, Nat.mod_lt _ hn0⟩)
          (fun i : Fin n => x ⟨(w + i.val) % n, Nat.mod_lt _ hn0⟩)) i =
          (fun j : Fin (w + 1) => x ⟨(i + j.val) % n, Nat.mod_lt _ hn0⟩) := by
        funext j
        simp only [C_st]
        exact C_F1 w n hn0 x _ (by have := j.2; omega)
      rw [hw]
      exact hx i hi
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro i hi
    have hw : (fun j : Fin (w + 1) => C_str w n p.1 p.2 ((i + j.val) % n)) =
        C_st (w + 1) (C_str w n p.1 p.2) i := by
      funext j
      simp only [C_st]
      exact C_F2 w n hn p.1 p.2 hp.1 _ (by have := j.2; omega)
    rw [hw]
    exact hp.2 i hi
  · intro x _
    funext i
    simp only
    rw [C_F1 w n hn0 x _ (by have := i.2; omega)]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    apply Prod.ext
    · funext j
      simp only
      rw [C_F2 w n hn p.1 p.2 hp.1 _ (by have := j.2; omega)]
      simp [C_str]
    · funext i
      simp only
      rw [C_F2 w n hn p.1 p.2 hp.1 _ (by have := i.2; omega)]
      have h1 : ¬ (w + i.val < w) := by omega
      have h2 : w + i.val - w < n := by have := i.2; omega
      simp only [C_str, h1, h2, dite_false, dite_true]
      exact congrArg p.2 (Fin.ext (by show w + i.val - w = i.val; omega))

lemma C_transN_congr (w : ℕ) (g g' : ℕ → (Fin (w + 1) → Bool) → Bool) (t : ℕ)
    (hg : ∀ i, i < t → g i = g' i) : transN w g t = transN w g' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [transN]
    rw [ih (fun i hi => hg i (by omega)), hg t (by omega)]

lemma C_transN_add (w : ℕ) (g : ℕ → (Fin (w + 1) → Bool) → Bool) (s t : ℕ) :
    transN w g (s + t) = transN w g s * transN w (fun i => g (s + i)) t := by
  induction t with
  | zero => simp [transN]
  | succ t ih =>
    rw [← Nat.add_assoc]
    simp only [transN]
    rw [ih, Matrix.mul_assoc]

def C_G (w h k : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (R : Fin k × (Fin (w + 1) → Bool) → Bool) (i : ℕ) : (Fin (w + 1) → Bool) → Bool :=
  fun x => if i < h then gExt w h P i x else gExt w k R (i - h) x

lemma C_G_trans (w h k : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (R : Fin k × (Fin (w + 1) → Bool) → Bool) :
    transN w (C_G w h k P R) (h + k) = trans w h P * trans w k R := by
  rw [C_transN_add]
  unfold trans
  congr 1
  · apply C_transN_congr
    intro i hi
    funext x
    simp [C_G, hi]
  · apply C_transN_congr
    intro i hi
    funext x
    simp [C_G]

lemma C_G_good (w h k : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (R : Fin k × (Fin (w + 1) → Bool) → Bool) (W : ℕ → (Fin (w + 1) → Bool)) :
    (∀ i, i < h + k → C_G w h k P R i (W i) = true) ↔
      ((∀ i : Fin h, P (i, W i.val) = true) ∧ ∀ i : Fin k, R (i, W (h + i.val)) = true) := by
  constructor
  · intro H
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := H i.val (by have := i.2; omega)
      simpa [C_G, gExt, i.2] using this
    · have := H (h + i.val) (by have := i.2; omega)
      simpa [C_G, gExt, i.2] using this
  · rintro ⟨H1, H2⟩ i hi
    by_cases h1 : i < h
    · have := H1 ⟨i, h1⟩
      simpa [C_G, gExt, h1] using this
    · have h2 : i - h < k := by omega
      have := H2 ⟨i - h, h2⟩
      have h3 : h + (i - h) = i := by omega
      simp only [h3] at this
      simpa [C_G, gExt, h1, h2] using this

lemma C_par (w h k : ℕ) (hw : w ≤ h + k) (hn : 0 < h + k)
    (P : Fin h × (Fin (w + 1) → Bool) → Bool) (R : Fin k × (Fin (w + 1) → Bool) → Bool) :
    (((Finset.univ.filter (fun x : Fin (h + k) → Bool =>
        (∀ i : Fin h, P (i, fun j => x ⟨(i.val + j.val) % (h + k), Nat.mod_lt _ hn⟩) = true) ∧
        ∀ i : Fin k, R (i, fun j => x ⟨(h + i.val + j.val) % (h + k), Nat.mod_lt _ hn⟩) = true)).card
          : ℕ) : ZMod 2) = ∑ a, ∑ b, trans w h P a b * trans w k R b a := by
  have h1 := C_cyc w (h + k) hw hn (C_G w h k P R)
  rw [C_G_trans] at h1
  simp only [Matrix.mul_apply] at h1
  rw [← h1]
  congr 2
  apply Finset.filter_congr
  intro x _
  exact (C_G_good w h k P R
    (fun i => fun j : Fin (w + 1) => x ⟨(i + j.val) % (h + k), Nat.mod_lt _ hn⟩)).symm

lemma C_tb (m n : ℕ) : m.testBit 0 = n.testBit 0 ↔ (m : ZMod 2) = (n : ZMod 2) := by
  rw [Nat.testBit_zero, Nat.testBit_zero, ZMod.natCast_eq_natCast_iff']
  rcases Nat.mod_two_eq_zero_or_one m with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h1, h2]

lemma C_stepM_unit (w : ℕ) (u : Fin (w + 1) → Bool) (b c : Fin w → Bool) :
    stepM w (fun x => decide (x = u)) b c =
      if (b = Fin.init u ∧ c = Fin.tail u) then 1 else 0 := by
  unfold stepM
  rw [Finset.sum_eq_single u]
  · simp [eq_comm]
  · intro x _ hx
    simp [hx]
  · simp

lemma C_walk (w : ℕ) (y : ℕ → Bool) (t : ℕ) (b c : Fin w → Bool) :
    transN w (fun i x => decide (x = C_st (w + 1) y i)) (t + 1) b c =
      if (b = C_st w y 0 ∧ c = C_st w y (t + 1)) then 1 else 0 := by
  induction t generalizing c with
  | zero =>
    simp only [transN, Matrix.one_mul]
    rw [C_stepM_unit, C_init_st, C_tail_st]
  | succ t ih =>
    rw [transN, Matrix.mul_apply]
    simp_rw [ih, C_stepM_unit, C_init_st, C_tail_st]
    rw [Finset.sum_eq_single (C_st w y (t + 1))]
    · by_cases h1 : b = C_st w y 0 <;> by_cases h2 : c = C_st w y (t + 1 + 1) <;> simp [h1, h2]
    · intro m _ hm
      simp [hm]
    · simp

lemma C_unitR (w k : ℕ) (hk : w ≤ k) (hk1 : 1 ≤ k) (a b : Fin w → Bool) :
    ∃ R : Fin k × (Fin (w + 1) → Bool) → Bool, ∀ b' a',
      trans w k R b' a' = if (b' = b ∧ a' = a) then 1 else 0 := by
  let y0 : ℕ → Bool := fun j =>
    if h : j < w then b ⟨j, h⟩ else if h2 : j - k < w then a ⟨j - k, h2⟩ else false
  refine ⟨fun p => decide (p.2 = C_st (w + 1) y0 p.1.val), ?_⟩
  intro b' a'
  have h1 : trans w k (fun p => decide (p.2 = C_st (w + 1) y0 p.1.val)) =
      transN w (fun i x => decide (x = C_st (w + 1) y0 i)) k := by
    unfold trans
    apply C_transN_congr
    intro i hi
    funext x
    simp [gExt, hi]
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  rw [h1, C_walk]
  have e1 : C_st w y0 0 = b := by
    funext j
    simp [C_st, y0]
  have e2 : C_st w y0 (t + 1) = a := by
    funext j
    have h3 : ¬ (t + 1 + j.val < w) := by omega
    have h4 : t + 1 + j.val - (t + 1) < w := by have := j.2; omega
    simp only [C_st, y0, h3, h4, dite_false, dite_true]
    congr 1
    apply Fin.ext
    simp
  rw [e1, e2]

lemma C_tr_unit (w : ℕ) (T : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2))
    (U : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2)) (a b : Fin w → Bool)
    (hU : ∀ b' a', U b' a' = if (b' = b ∧ a' = a) then 1 else 0) :
    ∑ a', ∑ b', T a' b' * U b' a' = T a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hU]
    · intro b' _ hb
      simp [hU, hb]
    · simp
  · intro a' _ ha
    apply Finset.sum_eq_zero
    intro b' _
    simp [hU, ha]
  · simp

theorem same_iff (d h k : ℕ) (hh : d + 2 ≤ h) (hk : d + 2 ≤ k) (hn : 0 < h + k)
    (P Q : Fin h × (Fin (d + 1 + 1) → Bool) → Bool) :
    (∀ R : Fin k × (Fin (d + 1 + 1) → Bool) → Bool,
      (Finset.univ.filter (fun x : Fin (h + k) → Bool =>
        (∀ i : Fin h, P (i, fun j => x ⟨(i.val + j.val) % (h + k), Nat.mod_lt _ hn⟩) = true) ∧
        ∀ i : Fin k, R (i, fun j => x ⟨(h + i.val + j.val) % (h + k), Nat.mod_lt _ hn⟩) = true)).card.testBit 0
      = (Finset.univ.filter (fun x : Fin (h + k) → Bool =>
        (∀ i : Fin h, Q (i, fun j => x ⟨(i.val + j.val) % (h + k), Nat.mod_lt _ hn⟩) = true) ∧
        ∀ i : Fin k, R (i, fun j => x ⟨(h + i.val + j.val) % (h + k), Nat.mod_lt _ hn⟩) = true)).card.testBit 0)
    ↔ trans (d + 1) h P = trans (d + 1) h Q := by
  constructor
  · intro H
    ext a b
    obtain ⟨R, hR⟩ := C_unitR (d + 1) k (by omega) (by omega) a b
    have h1 := H R
    rw [C_tb, C_par (d + 1) h k (by omega) hn, C_par (d + 1) h k (by omega) hn,
      C_tr_unit (d + 1) _ _ a b hR, C_tr_unit (d + 1) _ _ a b hR] at h1
    exact h1
  · intro heq R
    rw [C_tb, C_par (d + 1) h k (by omega) hn, C_par (d + 1) h k (by omega) hn, heq]

theorem D_transN_congr (w : ℕ) (g g' : ℕ → (Fin (w + 1) → Bool) → Bool) :
    ∀ t, (∀ i, i < t → g i = g' i) → transN w g t = transN w g' t
  | 0, _ => rfl
  | t + 1, h => by
      simp only [transN]
      rw [D_transN_congr w g g' t (fun i hi => h i (Nat.lt_succ_of_lt hi)), h t (Nat.lt_succ_self t)]

theorem D_transN_add (w : ℕ) (g g' : ℕ → (Fin (w + 1) → Bool) → Bool) (s : ℕ) : ∀ t,
    transN w (fun i => if i < s then g i else g' (i - s)) (s + t) = transN w g s * transN w g' t
  | 0 => by
      simp only [Nat.add_zero, transN, mul_one]
      exact D_transN_congr w _ _ s (fun i hi => by simp [hi])
  | t + 1 => by
      rw [← Nat.add_assoc]
      simp only [transN]
      rw [D_transN_add w g g' s t, mul_assoc]
      simp

def D_Rz (d t : ℕ) (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) : Prop :=
  ∃ g : ℕ → (Fin (d + 1 + 1) → Bool) → Bool, transN (d + 1) g t = M

theorem D_Rz_mul (d s t : ℕ) (A B : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hA : D_Rz d s A) (hB : D_Rz d t B) : D_Rz d (s + t) (A * B) := by
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨g', rfl⟩ := hB
  exact ⟨_, D_transN_add (d + 1) g g' s t⟩

def D_rotE (d : ℕ) (j : Fin (d + 1)) : (Fin (d + 1) → Bool) ≃ (Fin (d + 1) → Bool) where
  toFun a := fun i => a (i + j)
  invFun a := fun i => a (i - j)
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

def D_Pm (d : ℕ) (e : (Fin (d + 1) → Bool) ≃ (Fin (d + 1) → Bool)) :
    Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2) :=
  fun a c => if c = e a then 1 else 0

theorem D_Pm_mul (d : ℕ) (e : (Fin (d + 1) → Bool) ≃ (Fin (d + 1) → Bool))
    (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) (a c : Fin (d + 1) → Bool) :
    (D_Pm d e * M) a c = M (e a) c := by
  simp [Matrix.mul_apply, D_Pm]

theorem D_mul_Pm (d : ℕ) (e : (Fin (d + 1) → Bool) ≃ (Fin (d + 1) → Bool))
    (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) (a c : Fin (d + 1) → Bool) :
    (M * D_Pm d e) a c = M a (e.symm c) := by
  simp only [Matrix.mul_apply, D_Pm, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (e.symm c)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    rw [h]
    simp
  · simp

theorem D_step (d : ℕ) (G : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hG : ∀ a b, G a b ≠ 0 → ∀ i : Fin (d + 1), i ≠ 0 → b i = a i) :
    D_Rz d 1 (G * D_Pm d (D_rotE d 1)) := by
  refine ⟨fun _ x => decide (G (Fin.init x) (fun i => Fin.tail x (i - 1)) = 1), ?_⟩
  simp only [transN, one_mul]
  ext a c
  rw [D_mul_Pm]
  have hsymm : (D_rotE d 1).symm c = fun i => c (i - 1) := rfl
  rw [hsymm]
  simp only [stepM]
  by_cases h0 : G a (fun i => c (i - 1)) = 0
  · rw [h0]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    rintro ⟨e1, e2, e3⟩
    subst e1
    subst e2
    simp [h0] at e3
  · have h1 : G a (fun i => c (i - 1)) = 1 := by
      have := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (G a (fun i => c (i - 1)))
      tauto
    have hloc := hG _ _ h0
    have hinit : Fin.init (Fin.snoc a (c (Fin.last d)) : Fin (d + 1 + 1) → Bool) = a :=
      Fin.init_snoc _ _
    have htail : Fin.tail (Fin.snoc a (c (Fin.last d)) : Fin (d + 1 + 1) → Bool) = c := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · show (Fin.snoc a (c (Fin.last d)) : Fin (d + 1 + 1) → Bool) (Fin.last d).succ = _
        rw [Fin.succ_last, Fin.snoc_last]
      · intro k
        show (Fin.snoc a (c (Fin.last d)) : Fin (d + 1 + 1) → Bool) k.castSucc.succ = _
        rw [Fin.succ_castSucc, Fin.snoc_castSucc]
        have h2 := hloc k.succ (Fin.succ_ne_zero k)
        have h3 : (k.succ : Fin (d + 1)) - 1 = k.castSucc :=
          (eq_sub_of_add_eq Fin.coeSucc_eq_succ).symm
        simp only [h3] at h2
        exact h2.symm
    rw [h1, Finset.sum_eq_single (Fin.snoc a (c (Fin.last d)) : Fin (d + 1 + 1) → Bool)]
    · rw [if_pos]
      refine ⟨hinit, htail, ?_⟩
      simp [hinit, htail, h1]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨e1, e2, _⟩
      apply hx
      rw [← e1, ← e2]
      have h4 : Fin.tail x (Fin.last d) = x (Fin.last (d + 1)) := by
        simp [Fin.tail, Fin.succ_last]
      rw [h4]
      exact (Fin.snoc_init_self x).symm
    · simp

def D_cast (d t : ℕ) : Fin (d + 1) := ⟨t % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

theorem D_cast_add (d s t : ℕ) : D_cast d (s + t) = D_cast d s + D_cast d t := by
  apply Fin.ext
  simp [D_cast, Fin.val_add]

theorem D_cast_one (d : ℕ) : D_cast d 1 = 1 := by
  apply Fin.ext
  simp [D_cast]

theorem D_cast_zero (d : ℕ) : D_cast d 0 = 0 := by
  apply Fin.ext
  simp [D_cast]

theorem D_cast_val (d : ℕ) (j : Fin (d + 1)) : D_cast d j.val = j := by
  apply Fin.ext
  simp [D_cast, Nat.mod_eq_of_lt j.isLt]

theorem D_cast_mul (d p : ℕ) : D_cast d ((d + 1) * p) = 0 := by
  apply Fin.ext
  simp [D_cast]

def D_Rz' (d t : ℕ) (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) : Prop :=
  D_Rz d t (M * D_Pm d (D_rotE d (D_cast d t)))

theorem D_comp (d s t : ℕ) (A B : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hA : D_Rz' d s A)
    (hB : D_Rz' d t (Matrix.of fun a c => B (D_rotE d (-(D_cast d s)) a) (D_rotE d (-(D_cast d s)) c))) :
    D_Rz' d (s + t) (A * B) := by
  have h := D_Rz_mul d s t _ _ hA hB
  unfold D_Rz'
  convert h using 1
  rw [mul_assoc, mul_assoc]
  congr 1
  ext a c
  rw [D_mul_Pm, D_Pm_mul, D_mul_Pm, Matrix.of_apply]
  show B a _ = B (D_rotE d (-(D_cast d s)) (D_rotE d (D_cast d s) a))
    (D_rotE d (-(D_cast d s)) ((D_rotE d (D_cast d t)).symm c))
  congr 1
  · funext i
    simp [D_rotE]
  · funext i
    simp only [D_rotE, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, D_cast_add]
    congr 1
    abel

theorem D_Rz'_one (d : ℕ) : D_Rz' d 1 1 := by
  unfold D_Rz'
  rw [D_cast_one]
  apply D_step
  intro a b hab i _
  rw [Matrix.one_apply] at hab
  by_contra hne
  apply hab
  rw [if_neg]
  intro e
  apply hne
  rw [e]

theorem D_Rz'_succ (d t : ℕ) (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (h : D_Rz' d t M) : D_Rz' d (t + 1) M := by
  have e : (Matrix.of fun a c => (1 : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
      (D_rotE d (-(D_cast d t)) a) (D_rotE d (-(D_cast d t)) c)) = 1 := by
    ext a c
    simp [Matrix.one_apply]
  have h2 := D_comp d t 1 M 1 h (by rw [e]; exact D_Rz'_one d)
  rwa [mul_one] at h2

theorem D_Rz'_mono (d s t : ℕ) (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hst : s ≤ t) (h : D_Rz' d s M) : D_Rz' d t M := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact D_Rz'_succ d n M ih

theorem D_Rz'_zero (d : ℕ) : D_Rz' d 0 1 := by
  refine ⟨fun _ _ => false, ?_⟩
  simp only [transN, D_cast_zero, one_mul]
  ext a c
  simp [D_Pm, D_rotE, Matrix.one_apply, eq_comm]

theorem D_loc (d : ℕ) (j : Fin (d + 1))
    (G : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hG : ∀ a b, G a b ≠ 0 → ∀ i : Fin (d + 1), i ≠ j → b i = a i) :
    D_Rz' d (d + 1) G := by
  have h0 : D_Rz' d j.val 1 := D_Rz'_mono d 0 _ 1 (Nat.zero_le _) (D_Rz'_zero d)
  have h1 : D_Rz' d 1 (Matrix.of fun a c => G (D_rotE d (-(D_cast d j.val)) a)
      (D_rotE d (-(D_cast d j.val)) c)) := by
    unfold D_Rz'
    rw [D_cast_one]
    apply D_step
    intro a b hab i hi
    rw [D_cast_val, Matrix.of_apply] at hab
    have h2 := hG _ _ hab (i + j) (by simpa using hi)
    simpa [D_rotE] using h2
  have h2 := D_comp d j.val 1 1 G h0 h1
  rw [one_mul] at h2
  exact D_Rz'_mono d _ _ G (by have := j.isLt; omega) h2

def D_Bk (d q : ℕ) (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) : Prop :=
  D_Rz' d ((d + 1) * q) M

theorem D_Bk_mul (d p q : ℕ) (A B : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hA : D_Bk d p A) (hB : D_Bk d q B) : D_Bk d (p + q) (A * B) := by
  unfold D_Bk at *
  rw [mul_add]
  apply D_comp d _ _ A B hA
  rw [D_cast_mul]
  have e : (Matrix.of fun a c => B (D_rotE d (-0) a) (D_rotE d (-0) c)) = B := by
    ext a c
    simp [D_rotE]
  rw [e]
  exact hB

theorem D_Bk_mono (d p q : ℕ) (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hpq : p ≤ q) (h : D_Bk d p M) : D_Bk d q M :=
  D_Rz'_mono d _ _ M (Nat.mul_le_mul_left _ hpq) h

theorem D_Bk_loc (d : ℕ) (j : Fin (d + 1))
    (G : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2))
    (hG : ∀ a b, G a b ≠ 0 → ∀ i : Fin (d + 1), i ≠ j → b i = a i) :
    D_Bk d 1 G := by
  unfold D_Bk
  rw [mul_one]
  exact D_loc d j G hG

theorem D_Bk_zero (d : ℕ) : D_Bk d 0 1 := by
  unfold D_Bk
  rw [mul_zero]
  exact D_Rz'_zero d

abbrev D_Mat (d : ℕ) : Type := Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)

def D_T (d : ℕ) (a b : Fin (d + 1) → Bool) : D_Mat d :=
  Matrix.of fun x y => (if x = y then 1 else 0) + (if x = a ∧ y = b then 1 else 0)

def D_Lm (d : ℕ) (A : Finset (Fin (d + 1) → Bool)) (p : Fin (d + 1) → Bool) : D_Mat d :=
  Matrix.of fun x y => (if x = y then 1 else 0) + (if x ∈ A ∧ y = p then 1 else 0)

def D_Um (d : ℕ) (p : Fin (d + 1) → Bool) (B : Finset (Fin (d + 1) → Bool)) : D_Mat d :=
  Matrix.of fun x y => (if x = y then 1 else 0) + (if x = p ∧ y ∈ B then 1 else 0)

theorem D_two (z : ZMod 2) : z + z = 0 := by
  revert z
  decide

theorem D_ne_zero (z : ZMod 2) (h : z ≠ 0) : z = 1 := by
  revert z
  decide

theorem D_Lm_mul (d : ℕ) (A : Finset (Fin (d + 1) → Bool)) (p : Fin (d + 1) → Bool) (N : D_Mat d)
    (x y : Fin (d + 1) → Bool) :
    (D_Lm d A p * N) x y = N x y + (if x ∈ A then N p y else 0) := by
  simp only [Matrix.mul_apply, D_Lm, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul]
  congr 1
  · simp
  · by_cases hx : x ∈ A <;> simp [hx]

theorem D_mul_Um (d : ℕ) (p : Fin (d + 1) → Bool) (B : Finset (Fin (d + 1) → Bool)) (N : D_Mat d)
    (x y : Fin (d + 1) → Bool) :
    (N * D_Um d p B) x y = N x y + (if y ∈ B then N x p else 0) := by
  simp only [Matrix.mul_apply, D_Um, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_one, mul_zero]
  congr 1
  · simp
  · by_cases hy : y ∈ B <;> simp [hy]

theorem D_Lm_single (d : ℕ) (a p : Fin (d + 1) → Bool) : D_Lm d {a} p = D_T d a p := by
  ext x y
  simp [D_Lm, D_T]

theorem D_Um_single (d : ℕ) (p b : Fin (d + 1) → Bool) : D_Um d p {b} = D_T d p b := by
  ext x y
  simp [D_Um, D_T]

theorem D_Bk_T_nb (d : ℕ) (j : Fin (d + 1)) (a b : Fin (d + 1) → Bool)
    (h : ∀ i, i ≠ j → a i = b i) : D_Bk d 1 (D_T d a b) := by
  apply D_Bk_loc d j
  intro x y hxy i hi
  simp only [D_T, Matrix.of_apply] at hxy
  by_cases e : x = y
  · rw [e]
  · simp only [e, if_false, zero_add] at hxy
    by_cases e2 : x = a ∧ y = b
    · rw [e2.1, e2.2]
      exact (h i hi).symm
    · simp [e2] at hxy

theorem D_Bk_swap_nb (d : ℕ) (j : Fin (d + 1)) (a b : Fin (d + 1) → Bool)
    (h : ∀ i, i ≠ j → a i = b i) : D_Bk d 1 (D_Pm d (Equiv.swap a b)) := by
  apply D_Bk_loc d j
  intro x y hxy i hi
  simp only [D_Pm] at hxy
  by_cases e : y = Equiv.swap a b x
  · rw [e, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1]
      exact (h i hi).symm
    · rw [h2]
      exact h i hi
    · rfl
  · simp [e] at hxy

theorem D_Bk_diag (d : ℕ) (v : (Fin (d + 1) → Bool) → ZMod 2) :
    D_Bk d 1 (Matrix.diagonal v : D_Mat d) := by
  apply D_Bk_loc d 0
  intro x y hxy i _
  rw [Matrix.diagonal_apply] at hxy
  by_cases e : x = y
  · rw [e]
  · simp [e] at hxy

theorem D_conj (d : ℕ) (a b b' : Fin (d + 1) → Bool) (hab : a ≠ b) (hab' : a ≠ b') :
    D_Pm d (Equiv.swap b b') * D_T d a b' * D_Pm d (Equiv.swap b b') = D_T d a b := by
  ext x y
  rw [D_mul_Pm, D_Pm_mul]
  simp only [D_T, Matrix.of_apply, Equiv.symm_swap]
  have h1 : (Equiv.swap b b' x = Equiv.swap b b' y) ↔ x = y := Equiv.apply_eq_iff_eq _
  have h2 : Equiv.swap b b' x = a ↔ x = a := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hab hab']
  have h3 : Equiv.swap b b' y = b' ↔ y = b := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  simp only [h1, h2, h3]

theorem D_Bk_T (d : ℕ) : ∀ S : Finset (Fin (d + 1)), ∀ a b : Fin (d + 1) → Bool, a ≠ b →
    (∀ i, a i ≠ b i → i ∈ S) → D_Bk d (2 * S.card) (D_T d a b) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro a b hab h
    exfalso
    apply hab
    funext i
    by_contra hne
    exact absurd (h i hne) (by simp)
  | insert j S hj ih =>
    intro a b hab h
    rw [Finset.card_insert_of_notMem hj]
    by_cases hjj : a j = b j
    · apply D_Bk_mono d (2 * S.card) _ _ (by omega)
      apply ih a b hab
      intro i hi
      have h' := h i hi
      rw [Finset.mem_insert] at h'
      rcases h' with rfl | h'
      · exact absurd hjj hi
      · exact h'
    · by_cases hnb : ∀ i, i ≠ j → a i = b i
      · exact D_Bk_mono d 1 _ _ (by omega) (D_Bk_T_nb d j a b hnb)
      · obtain ⟨b', hb'⟩ : ∃ b', b' = Function.update b j (a j) := ⟨_, rfl⟩
        have hab' : a ≠ b' := by
          intro e
          apply hnb
          intro i hi
          have h' := congrFun e i
          rw [hb', Function.update_of_ne hi] at h'
          exact h'
        have h1 := ih a b' hab' (by
          intro i hi
          by_cases hij : i = j
          · exfalso
            apply hi
            rw [hij, hb']
            simp
          · rw [hb', Function.update_of_ne hij] at hi
            have h' := h i hi
            rw [Finset.mem_insert] at h'
            rcases h' with h' | h'
            · exact absurd h' hij
            · exact h')
        have hsw : D_Bk d 1 (D_Pm d (Equiv.swap b b')) := D_Bk_swap_nb d j b b' (by
          intro i hi
          rw [hb', Function.update_of_ne hi])
        have h2 := D_Bk_mul _ _ _ _ _ (D_Bk_mul _ _ _ _ _ hsw h1) hsw
        rw [D_conj d a b b' hab hab'] at h2
        exact D_Bk_mono d _ _ _ (by omega) h2

theorem D_Bk_T' (d : ℕ) (a b : Fin (d + 1) → Bool) (hab : a ≠ b) :
    D_Bk d (2 * (d + 1)) (D_T d a b) := by
  have h := D_Bk_T d Finset.univ a b hab (fun i _ => Finset.mem_univ i)
  rwa [Finset.card_univ, Fintype.card_fin] at h

theorem D_Lm_sq (d : ℕ) (A : Finset (Fin (d + 1) → Bool)) (p : Fin (d + 1) → Bool) (hp : p ∉ A) :
    D_Lm d A p * D_Lm d A p = 1 := by
  ext x y
  rw [D_Lm_mul]
  simp only [D_Lm, Matrix.of_apply, Matrix.one_apply]
  by_cases hx : x ∈ A
  · by_cases hy : y = p
    · simp [hx, hy, hp, add_assoc, D_two]
    · simp [hx, hy, hp, Ne.symm hy]
  · simp [hx]

theorem D_Um_sq (d : ℕ) (p : Fin (d + 1) → Bool) (B : Finset (Fin (d + 1) → Bool)) (hp : p ∉ B) :
    D_Um d p B * D_Um d p B = 1 := by
  ext x y
  rw [D_mul_Um]
  simp only [D_Um, Matrix.of_apply, Matrix.one_apply]
  by_cases hy : y ∈ B
  · by_cases hx : x = p
    · simp [hx, hy, hp, add_assoc, D_two]
    · simp [hx, hy, hp]
  · simp [hy]

theorem D_T_sq (d : ℕ) (a b : Fin (d + 1) → Bool) (hab : a ≠ b) : D_T d a b * D_T d a b = 1 := by
  rw [← D_Lm_single]
  exact D_Lm_sq d {a} b (by simpa using hab.symm)

theorem D_Bk_Lm (d : ℕ) (p : Fin (d + 1) → Bool) : ∀ A : Finset (Fin (d + 1) → Bool), p ∉ A →
    D_Bk d (2 * (d + 1) * A.card) (D_Lm d A p) := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _
    have e : D_Lm d ∅ p = 1 := by
      ext x y
      simp [D_Lm, Matrix.one_apply]
    rw [e]
    exact D_Bk_mono d 0 _ _ (Nat.zero_le _) (D_Bk_zero d)
  | insert a A ha ih =>
    intro hp
    rw [Finset.mem_insert, not_or] at hp
    have e : D_Lm d (insert a A) p = D_T d a p * D_Lm d A p := by
      ext x y
      rw [← D_Lm_single, D_Lm_mul]
      simp only [D_Lm, Matrix.of_apply, Finset.mem_insert, Finset.mem_singleton]
      by_cases hxa : x = a
      · subst hxa
        simp [ha, hp.2, eq_comm]
      · simp [hxa]
    rw [e, Finset.card_insert_of_notMem ha]
    have h1 := D_Bk_mul _ _ _ _ _ (D_Bk_T' d a p (Ne.symm hp.1)) (ih hp.2)
    exact D_Bk_mono d _ _ _ (Nat.le_of_eq (by ring)) h1

theorem D_Bk_Um (d : ℕ) (p : Fin (d + 1) → Bool) : ∀ B : Finset (Fin (d + 1) → Bool), p ∉ B →
    D_Bk d (2 * (d + 1) * B.card) (D_Um d p B) := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _
    have e : D_Um d p ∅ = 1 := by
      ext x y
      simp [D_Um, Matrix.one_apply]
    rw [e]
    exact D_Bk_mono d 0 _ _ (Nat.zero_le _) (D_Bk_zero d)
  | insert b B hb ih =>
    intro hp
    rw [Finset.mem_insert, not_or] at hp
    have e : D_Um d p (insert b B) = D_Um d p B * D_T d p b := by
      ext x y
      rw [← D_Um_single, D_mul_Um]
      simp only [D_Um, Matrix.of_apply, Finset.mem_insert, Finset.mem_singleton]
      by_cases hyb : y = b
      · subst hyb
        simp [hb, hp.2]
      · simp [hyb]
    rw [e, Finset.card_insert_of_notMem hb]
    have h1 := D_Bk_mul _ _ _ _ _ (ih hp.2) (D_Bk_T' d p b hp.1)
    exact D_Bk_mono d _ _ _ (Nat.le_of_eq (by ring)) h1

def D_IdOut (d : ℕ) (S : Finset (Fin (d + 1) → Bool)) (M : D_Mat d) : Prop :=
  ∀ x y, (x ∉ S ∨ y ∉ S) → M x y = if x = y then 1 else 0

theorem D_pivot (d : ℕ) (S : Finset (Fin (d + 1) → Bool)) (M : D_Mat d) (hM : D_IdOut d S M)
    (a b : Fin (d + 1) → Bool) (ha : a ∈ S) (hb : b ∈ S) (hab : M a b ≠ 0) :
    ∃ M1 : D_Mat d, D_IdOut d S M1 ∧ M1 a a = 1 ∧
      ∀ q, D_Bk d q M1 → D_Bk d (q + 2 * (d + 1)) M := by
  by_cases haa : M a a = 0
  · have hne : b ≠ a := by
      rintro rfl
      exact hab haa
    refine ⟨M * D_T d b a, ?_, ?_, ?_⟩
    · intro x y hxy
      rw [← D_Um_single, D_mul_Um]
      by_cases hya : y = a
      · subst hya
        have hx : x ∉ S := by tauto
        have hxb : x ≠ b := by
          rintro rfl
          exact hx hb
        rw [hM x y hxy, hM x b (Or.inl hx)]
        simp [hxb]
      · rw [hM x y hxy]
        simp [hya]
    · rw [← D_Um_single, D_mul_Um, haa, D_ne_zero _ hab]
      simp
    · intro q hq
      have h1 := D_Bk_mul _ _ _ _ _ hq (D_Bk_T' d b a hne)
      rwa [mul_assoc, D_T_sq d b a hne, mul_one] at h1
  · exact ⟨M, hM, D_ne_zero _ haa, fun q hq => D_Bk_mono d _ _ _ (Nat.le_add_right _ _) hq⟩

theorem D_schur (d : ℕ) (S : Finset (Fin (d + 1) → Bool)) (M1 : D_Mat d) (hM : D_IdOut d S M1)
    (p : Fin (d + 1) → Bool) (hp : p ∈ S) (hpp : M1 p p = 1)
    (A B : Finset (Fin (d + 1) → Bool))
    (hA : ∀ x, x ∈ A ↔ x ∈ S ∧ x ≠ p ∧ M1 x p ≠ 0)
    (hB : ∀ y, y ∈ B ↔ y ∈ S ∧ y ≠ p ∧ M1 p y ≠ 0) :
    D_IdOut d (S.erase p) (D_Lm d A p * M1 * D_Um d p B) := by
  intro x y hxy
  rw [D_mul_Um, D_Lm_mul, D_Lm_mul]
  have hpA : p ∉ A := by
    rw [hA]
    tauto
  have hpB : p ∉ B := by
    rw [hB]
    tauto
  by_cases hxp : x = p
  · subst hxp
    by_cases hyp : y = x
    · subst hyp
      simp [hpA, hpB, hpp]
    · by_cases hyB : y ∈ B
      · have h1 := D_ne_zero _ ((hB y).1 hyB).2.2
        simp [hpA, hyB, hpp, h1, Ne.symm hyp, D_two]
      · have h1 : M1 x y = 0 := by
          by_cases hyS : y ∈ S
          · by_contra h0
            exact hyB ((hB y).2 ⟨hyS, hyp, h0⟩)
          · rw [hM x y (Or.inr hyS)]
            simp [Ne.symm hyp]
        simp [hpA, hyB, h1, Ne.symm hyp]
  · by_cases hyp : y = p
    · subst hyp
      by_cases hxA : x ∈ A
      · have h1 := D_ne_zero _ ((hA x).1 hxA).2.2
        simp [hpB, hxA, hpp, h1, hxp, D_two]
      · have h1 : M1 x y = 0 := by
          by_cases hxS : x ∈ S
          · by_contra h0
            exact hxA ((hA x).2 ⟨hxS, hxp, h0⟩)
          · rw [hM x y (Or.inl hxS)]
            simp [hxp]
        simp [hpB, hxA, h1, hxp]
    · have hxy' : x ∉ S ∨ y ∉ S := by
        simp only [Finset.mem_erase, not_and] at hxy
        tauto
      rcases hxy' with hxS | hyS
      · have hxA : x ∉ A := by
          rw [hA]
          tauto
        rw [hM x y (Or.inl hxS), hM x p (Or.inl hxS)]
        simp [hxA, hxp]
      · have hyB : y ∉ B := by
          rw [hB]
          tauto
        rw [hM x y (Or.inr hyS), hM p y (Or.inr hyS)]
        simp [hyB, Ne.symm hyp]

theorem D_elim (d : ℕ) : ∀ n : ℕ, ∀ S : Finset (Fin (d + 1) → Bool), S.card = n →
    ∀ M : D_Mat d, D_IdOut d S M → D_Bk d (2 * (d + 1) * (n * (n + 1)) + 1) M := by
  intro n
  induction n with
  | zero =>
    intro S hS M hM
    rw [Finset.card_eq_zero] at hS
    subst hS
    have e : M = 1 := by
      ext x y
      rw [hM x y (Or.inl (by simp)), Matrix.one_apply]
    rw [e]
    exact D_Bk_mono d 0 _ _ (Nat.zero_le _) (D_Bk_zero d)
  | succ n ih =>
    intro S hS M hM
    by_cases hz' : ∃ a ∈ S, ∃ b ∈ S, M a b ≠ 0
    · obtain ⟨p, hp, b, hb, hpb⟩ := hz'
      obtain ⟨M1, hM1, hpp, hback⟩ := D_pivot d S M hM p b hp hb hpb
      obtain ⟨A, hA⟩ : ∃ A : Finset (Fin (d + 1) → Bool),
          A = (S.erase p).filter (fun x => M1 x p ≠ 0) := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : Finset (Fin (d + 1) → Bool),
          B = (S.erase p).filter (fun y => M1 p y ≠ 0) := ⟨_, rfl⟩
      have hA' : ∀ x, x ∈ A ↔ x ∈ S ∧ x ≠ p ∧ M1 x p ≠ 0 := by
        intro x
        rw [hA, Finset.mem_filter, Finset.mem_erase]
        tauto
      have hB' : ∀ y, y ∈ B ↔ y ∈ S ∧ y ≠ p ∧ M1 p y ≠ 0 := by
        intro y
        rw [hB, Finset.mem_filter, Finset.mem_erase]
        tauto
      have hcard : (S.erase p).card = n := by
        rw [Finset.card_erase_of_mem hp, hS]
        rfl
      have hAc : A.card ≤ n := by
        rw [hA, ← hcard]
        exact Finset.card_filter_le _ _
      have hBc : B.card ≤ n := by
        rw [hB, ← hcard]
        exact Finset.card_filter_le _ _
      have hpA : p ∉ A := by
        rw [hA']
        tauto
      have hpB : p ∉ B := by
        rw [hB']
        tauto
      have h2 := ih (S.erase p) hcard _ (D_schur d S M1 hM1 p hp hpp A B hA' hB')
      have h3 := D_Bk_mul _ _ _ _ _ (D_Bk_mul _ _ _ _ _ (D_Bk_Lm d p A hpA) h2) (D_Bk_Um d p B hpB)
      have e : D_Lm d A p * (D_Lm d A p * M1 * D_Um d p B) * D_Um d p B = M1 := by
        rw [mul_assoc, mul_assoc, D_Um_sq d p B hpB, mul_one, ← mul_assoc, D_Lm_sq d A p hpA,
          one_mul]
      rw [e] at h3
      have h4 := hback _ h3
      refine D_Bk_mono d _ _ _ ?_ h4
      have hA2 : 2 * (d + 1) * A.card ≤ 2 * (d + 1) * n := Nat.mul_le_mul_left _ hAc
      have hB2 : 2 * (d + 1) * B.card ≤ 2 * (d + 1) * n := Nat.mul_le_mul_left _ hBc
      nlinarith [hA2, hB2]
    · have hz : ∀ a ∈ S, ∀ b ∈ S, M a b = 0 := fun a ha b hb => by
        by_contra h0
        exact hz' ⟨a, ha, b, hb, h0⟩
      have e : M = Matrix.diagonal (fun a => if a ∈ S then 0 else 1) := by
        ext x y
        rw [Matrix.diagonal_apply]
        by_cases hx : x ∈ S
        · by_cases hy : y ∈ S
          · rw [hz x hx y hy]
            simp [hx]
          · rw [hM x y (Or.inr hy)]
            have hne : x ≠ y := by
              rintro rfl
              exact hy hx
            simp [hne]
        · rw [hM x y (Or.inl hx)]
          simp [hx]
      rw [e]
      exact D_Bk_mono d 1 _ _ (by omega) (D_Bk_diag d _)

theorem D_all (d : ℕ) (M : D_Mat d) :
    D_Bk d (2 * (d + 1) * (2 ^ (d + 1) * (2 ^ (d + 1) + 1)) + 1) M :=
  D_elim d _ Finset.univ (by simp [Finset.card_univ]) M (by
    intro x y h
    simp at h)

theorem trans_surj (d h : ℕ)
    (hh : (12 * (d + 1) * 2 ^ (d + 1) * (2 ^ (d + 1) + 2) + 1) * (d + 1) ≤ h)
    (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) :
    ∃ P : Fin h × (Fin (d + 1 + 1) → Bool) → Bool, trans (d + 1) h P = M := by
  have hB := D_all d (M * D_Pm d (D_rotE d (D_cast d h)).symm)
  have hle : (d + 1) * (2 * (d + 1) * (2 ^ (d + 1) * (2 ^ (d + 1) + 1)) + 1) ≤ h := by
    revert hh
    generalize 2 ^ (d + 1) = D
    intro hh
    have h1 : 2 * (d + 1) * (D * (D + 1)) + 1 ≤ 12 * (d + 1) * D * (D + 2) + 1 := by
      nlinarith [Nat.zero_le ((d + 1) * D * D), Nat.zero_le ((d + 1) * D)]
    calc (d + 1) * (2 * (d + 1) * (D * (D + 1)) + 1)
        ≤ (d + 1) * (12 * (d + 1) * D * (D + 2) + 1) := Nat.mul_le_mul_left _ h1
      _ = (12 * (d + 1) * D * (D + 2) + 1) * (d + 1) := Nat.mul_comm _ _
      _ ≤ h := hh
  have hR := D_Rz'_mono d _ h _ hle hB
  unfold D_Rz' D_Rz at hR
  obtain ⟨g, hg⟩ := hR
  refine ⟨fun q => g q.1.val q.2, ?_⟩
  have h1 : transN (d + 1) (gExt (d + 1) h (fun q => g q.1.val q.2)) h = transN (d + 1) g h :=
    D_transN_congr _ _ _ h (fun i hi => by
      funext x
      simp [gExt, hi])
  have h2 : D_Pm d (D_rotE d (D_cast d h)).symm * D_Pm d (D_rotE d (D_cast d h)) = 1 := by
    ext a c
    rw [D_Pm_mul]
    simp [D_Pm, Matrix.one_apply, eq_comm]
  unfold trans
  rw [h1, hg, mul_assoc, h2, mul_one]

open PEqualNP.ProofComplexity in
theorem E_gc_sat {V : Type} [DecidableEq V] (α : V → Bool) (o x y : V) (op : Bool → Bool → Bool) :
    (∀ p : Bool × Bool, ClauseSat α ({(x, !p.1), (y, !p.2), (o, op p.1 p.2)} : Clause V)) ↔
      α o = op (α x) (α y) := by
  have key : ∀ p : Bool × Bool,
      ClauseSat α ({(x, !p.1), (y, !p.2), (o, op p.1 p.2)} : Clause V) ↔
        (α x = !p.1 ∨ α y = !p.2 ∨ α o = op p.1 p.2) := by
    intro p
    simp [ClauseSat]
  constructor
  · intro hall
    have h1 := (key (α x, α y)).1 (hall _)
    rcases h1 with h1 | h1 | h1
    · simp at h1
    · simp at h1
    · exact h1
  · intro ho p
    rw [key]
    by_cases hx : α x = p.1
    · by_cases hy : α y = p.2
      · right; right; rw [ho, hx, hy]
      · right; left
        revert hy; cases α y <;> cases p.2 <;> simp
    · left
      revert hx; cases α x <;> cases p.1 <;> simp

def E_gc {V : Type} [DecidableEq V] (g : V × V × V × (Bool → Bool → Bool)) :
    Finset (PEqualNP.ProofComplexity.Clause V) :=
  (Finset.univ : Finset (Bool × Bool)).image
    (fun p => {(g.2.1, !p.1), (g.2.2.1, !p.2), (g.1, g.2.2.2 p.1 p.2)})

def E_cnf {V Γ : Type} [DecidableEq V] [Fintype Γ]
    (gate : Γ → V × V × V × (Bool → Bool → Bool)) :
    Finset (PEqualNP.ProofComplexity.Clause V) :=
  Finset.univ.biUnion (fun g => E_gc (gate g))

theorem E_cnf_sat {V Γ : Type} [DecidableEq V] [Fintype Γ]
    (gate : Γ → V × V × V × (Bool → Bool → Bool)) (α : V → Bool) :
    PEqualNP.ProofComplexity.Satisfies α (↑(E_cnf gate) : Set _) ↔
      ∀ g, α (gate g).1 = (gate g).2.2.2 (α (gate g).2.1) (α (gate g).2.2.1) := by
  have h1 : PEqualNP.ProofComplexity.Satisfies α (↑(E_cnf gate) : Set _) ↔
      ∀ g, ∀ p : Bool × Bool, PEqualNP.ProofComplexity.ClauseSat α
        ({((gate g).2.1, !p.1), ((gate g).2.2.1, !p.2), ((gate g).1, (gate g).2.2.2 p.1 p.2)} :
          PEqualNP.ProofComplexity.Clause V) := by
    constructor
    · intro hs g p
      apply hs
      rw [Finset.mem_coe]
      exact Finset.mem_biUnion.2 ⟨g, Finset.mem_univ _,
        Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩⟩
    · intro hall C hC
      rw [Finset.mem_coe] at hC
      obtain ⟨g, -, hC⟩ := Finset.mem_biUnion.1 hC
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hC
      exact hall g p
  rw [h1]
  exact forall_congr' (fun g => E_gc_sat α _ _ _ _)

theorem E_cnf_card3 {V Γ : Type} [DecidableEq V] [Fintype Γ]
    (gate : Γ → V × V × V × (Bool → Bool → Bool)) :
    ∀ C ∈ E_cnf gate, C.card ≤ 3 := by
  intro C hC
  simp only [E_cnf, E_gc, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and] at hC
  obtain ⟨g, p, rfl⟩ := hC
  exact Finset.card_le_three

theorem E_cnf_sum {V Γ : Type} [DecidableEq V] [Fintype Γ]
    (gate : Γ → V × V × V × (Bool → Bool → Bool)) :
    ∑ C ∈ E_cnf gate, C.card ≤ 12 * Fintype.card Γ := by
  have h1 : ∑ C ∈ E_cnf gate, C.card ≤ ∑ _C ∈ E_cnf gate, 3 :=
    Finset.sum_le_sum (fun C hC => E_cnf_card3 gate C hC)
  have h2 : (E_cnf gate).card ≤ ∑ _g : Γ, 4 := by
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum (fun g _ => ?_)
    refine le_trans Finset.card_image_le ?_
    simp
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ] at h1 h2
  omega

abbrev E_A (w h s : ℕ) : Type :=
  Sum (Fin (h + 1) × (Fin w → Bool) × (Fin w → Bool))
    (Sum (Fin h × (Fin w → Bool) × (Fin w → Bool) × Bool) (Fin s × Fin (2 ^ w * 2 ^ w + 1)))

abbrev E_V (w h s : ℕ) : Type :=
  Sum (Fin h × (Fin (w + 1) → Bool)) (Sum (Fin s) (Fin (Fintype.card (E_A w h s))))

noncomputable def E_av (w h s : ℕ) (x : E_A w h s) : E_V w h s :=
  Sum.inr (Sum.inr (Fintype.equivFin _ x))

theorem E_card_SS (w : ℕ) :
    Fintype.card ((Fin w → Bool) × (Fin w → Bool)) = 2 ^ w * 2 ^ w := by
  simp

noncomputable def E_ent (w : ℕ) : Fin (2 ^ w * 2 ^ w) ≃ (Fin w → Bool) × (Fin w → Bool) :=
  (Fintype.equivFinOfCardEq (E_card_SS w)).symm

noncomputable def E_gate (w h s : ℕ) (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2) :
    Sum (E_A w h s) (Fin s) → E_V w h s × E_V w h s × E_V w h s × (Bool → Bool → Bool)
  | Sum.inl (Sum.inl (i, a, c)) =>
      Fin.cases (motive := fun _ => E_V w h s × E_V w h s × E_V w h s × (Bool → Bool → Bool))
        (E_av w h s (Sum.inl (0, a, c)), E_av w h s (Sum.inl (0, a, c)),
          E_av w h s (Sum.inl (0, a, c)), fun _ _ => decide (a = c))
        (fun i' => (E_av w h s (Sum.inl (i'.succ, a, c)),
          E_av w h s (Sum.inr (Sum.inl (i', a, c, false))),
          E_av w h s (Sum.inr (Sum.inl (i', a, c, true))), fun x y => xor x y)) i
  | Sum.inl (Sum.inr (Sum.inl (i, a, c, b))) =>
      (E_av w h s (Sum.inr (Sum.inl (i, a, c, b))),
        E_av w h s (Sum.inl (i.castSucc, a, Fin.init (Fin.cons b c : Fin (w + 1) → Bool))),
        Sum.inl (i, (Fin.cons b c : Fin (w + 1) → Bool)), fun x y => x && y)
  | Sum.inl (Sum.inr (Sum.inr (j, t))) =>
      Fin.cases (motive := fun _ => E_V w h s × E_V w h s × E_V w h s × (Bool → Bool → Bool))
        (E_av w h s (Sum.inr (Sum.inr (j, 0))), E_av w h s (Sum.inr (Sum.inr (j, 0))),
          E_av w h s (Sum.inr (Sum.inr (j, 0))), fun _ _ => false)
        (fun t' => (E_av w h s (Sum.inr (Sum.inr (j, t'.succ))),
          E_av w h s (Sum.inr (Sum.inr (j, t'.castSucc))),
          E_av w h s (Sum.inl (Fin.last h, (E_ent w t').1, (E_ent w t').2)),
          fun x y => xor x (decide (Hc j (E_ent w t') = 1) && y))) t
  | Sum.inr j =>
      (Sum.inr (Sum.inl j), E_av w h s (Sum.inr (Sum.inr (j, Fin.last _))),
        E_av w h s (Sum.inr (Sum.inr (j, Fin.last _))), fun x _ => x)

def E_good (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2)
    (z : Fin s → Bool) (β : E_A w h s → Bool) : Prop :=
  (∀ a c, β (Sum.inl (0, a, c)) = decide (a = c)) ∧
  (∀ (i : Fin h) a c, β (Sum.inl (i.succ, a, c)) =
    xor (β (Sum.inr (Sum.inl (i, a, c, false)))) (β (Sum.inr (Sum.inl (i, a, c, true))))) ∧
  (∀ (i : Fin h) a c b, β (Sum.inr (Sum.inl (i, a, c, b))) =
    (β (Sum.inl (i.castSucc, a, Fin.init (Fin.cons b c : Fin (w + 1) → Bool))) &&
      P (i, (Fin.cons b c : Fin (w + 1) → Bool)))) ∧
  (∀ j, β (Sum.inr (Sum.inr (j, 0))) = false) ∧
  (∀ j (t : Fin (2 ^ w * 2 ^ w)), β (Sum.inr (Sum.inr (j, t.succ))) =
    xor (β (Sum.inr (Sum.inr (j, t.castSucc))))
      (decide (Hc j (E_ent w t) = 1) && β (Sum.inl (Fin.last h, (E_ent w t).1, (E_ent w t).2)))) ∧
  (∀ j, z j = β (Sum.inr (Sum.inr (j, Fin.last _))))

theorem E_sat_iff (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2)
    (z : Fin s → Bool) (u : Fin (Fintype.card (E_A w h s)) → Bool) :
    PEqualNP.ProofComplexity.Satisfies (Sum.elim P (Sum.elim z u))
      (↑(E_cnf (E_gate w h s Hc)) : Set _) ↔
    E_good w h s P Hc z (fun x => u (Fintype.equivFin _ x)) := by
  rw [E_cnf_sat]
  constructor
  · intro hall
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a c
      simpa [E_gate, E_av] using hall (Sum.inl (Sum.inl (0, a, c)))
    · intro i a c
      simpa [E_gate, E_av] using hall (Sum.inl (Sum.inl (i.succ, a, c)))
    · intro i a c b
      simpa [E_gate, E_av] using hall (Sum.inl (Sum.inr (Sum.inl (i, a, c, b))))
    · intro j
      simpa [E_gate, E_av] using hall (Sum.inl (Sum.inr (Sum.inr (j, 0))))
    · intro j t
      simpa [E_gate, E_av] using hall (Sum.inl (Sum.inr (Sum.inr (j, t.succ))))
    · intro j
      simpa [E_gate, E_av] using hall (Sum.inr j)
  · rintro ⟨g1, g2, g3, g4, g5, g6⟩ g
    rcases g with ((⟨i, a, c⟩ | ⟨i, a, c, b⟩ | ⟨j, t⟩) | j)
    · refine Fin.cases ?_ (fun i' => ?_) i
      · simpa [E_gate, E_av] using g1 a c
      · simpa [E_gate, E_av] using g2 i' a c
    · simpa [E_gate, E_av] using g3 i a c b
    · refine Fin.cases ?_ (fun t' => ?_) t
      · simpa [E_gate, E_av] using g4 j
      · simpa [E_gate, E_av] using g5 j t'
    · simpa [E_gate, E_av] using g6 j

theorem E_step (w : ℕ) (M : Matrix (Fin w → Bool) (Fin w → Bool) (ZMod 2))
    (f : (Fin (w + 1) → Bool) → Bool) (a c : Fin w → Bool) :
    (M * stepM w f) a c =
      M a (Fin.init (Fin.cons true c : Fin (w + 1) → Bool)) *
        (if f (Fin.cons true c : Fin (w + 1) → Bool) = true then 1 else 0) +
      M a (Fin.init (Fin.cons false c : Fin (w + 1) → Bool)) *
        (if f (Fin.cons false c : Fin (w + 1) → Bool) = true then 1 else 0) := by
  have hin : ∀ (e : Bool) (b : Fin w → Bool),
      (∑ c' : Fin w → Bool,
        (if (Fin.init (Fin.cons e c' : Fin (w + 1) → Bool) = b ∧ c' = c ∧
          f (Fin.cons e c' : Fin (w + 1) → Bool) = true) then (1 : ZMod 2) else 0)) =
      if (Fin.init (Fin.cons e c : Fin (w + 1) → Bool) = b ∧
          f (Fin.cons e c : Fin (w + 1) → Bool) = true) then 1 else 0 := by
    intro e b
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hne
      simp [hne]
    · simp
  have hs : ∀ b, stepM w f b c =
      (if (Fin.init (Fin.cons true c : Fin (w + 1) → Bool) = b ∧
          f (Fin.cons true c : Fin (w + 1) → Bool) = true) then 1 else 0) +
      (if (Fin.init (Fin.cons false c : Fin (w + 1) → Bool) = b ∧
          f (Fin.cons false c : Fin (w + 1) → Bool) = true) then 1 else 0) := by
    intro b
    unfold stepM
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (w + 1) => Bool)), Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, Fin.tail_cons]
    rw [hin, hin]
  have h1 : ∀ (X : Fin w → Bool) (q : Prop) [Decidable q],
      (∑ b, M a b * (if (X = b ∧ q) then (1 : ZMod 2) else 0)) = M a X * (if q then 1 else 0) := by
    intro X q _
    rw [Finset.sum_eq_single X]
    · simp
    · intro b _ hne
      simp [Ne.symm hne]
    · simp
  rw [Matrix.mul_apply]
  simp only [hs, mul_add, Finset.sum_add_distrib]
  rw [h1, h1]

theorem E_dec1 : ∀ (z1 z2 : ZMod 2) (b1 b2 : Bool),
    decide (z1 * (if b1 = true then 1 else 0) + z2 * (if b2 = true then 1 else 0) = 1) =
      xor (decide (z2 = 1) && b2) (decide (z1 = 1) && b1) := by
  decide

theorem E_dec2 : ∀ (x hc tv : ZMod 2),
    decide (x + hc * tv = 1) = xor (decide (x = 1)) (decide (hc = 1) && decide (tv = 1)) := by
  decide

theorem E_dec3 : ∀ (x y : ZMod 2), decide (x = 1) = decide (y = 1) → x = y := by
  decide

theorem E_T0 (w : ℕ) (g : ℕ → (Fin (w + 1) → Bool) → Bool) (a c : Fin w → Bool) :
    decide (transN w g 0 a c = 1) = decide (a = c) := by
  by_cases hac : a = c <;> simp [transN, Matrix.one_apply, hac]

theorem E_Tsucc (w h : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool) (i : ℕ) (hi : i < h)
    (a c : Fin w → Bool) :
    decide (transN w (gExt w h P) (i + 1) a c = 1) =
      xor (decide (transN w (gExt w h P) i a (Fin.init (Fin.cons false c : Fin (w + 1) → Bool)) = 1)
            && P (⟨i, hi⟩, (Fin.cons false c : Fin (w + 1) → Bool)))
          (decide (transN w (gExt w h P) i a (Fin.init (Fin.cons true c : Fin (w + 1) → Bool)) = 1)
            && P (⟨i, hi⟩, (Fin.cons true c : Fin (w + 1) → Bool))) := by
  have : transN w (gExt w h P) (i + 1) = transN w (gExt w h P) i * stepM w (gExt w h P i) := rfl
  rw [this, E_step, E_dec1]
  simp [gExt, hi]

def E_S (w : ℕ) (f : Fin (2 ^ w * 2 ^ w) → ZMod 2) (t : ℕ) : ZMod 2 :=
  ∑ i : Fin (2 ^ w * 2 ^ w), if i.val < t then f i else 0

theorem E_S0 (w : ℕ) (f : Fin (2 ^ w * 2 ^ w) → ZMod 2) : E_S w f 0 = 0 := by
  simp [E_S]

theorem E_Ssucc (w : ℕ) (f : Fin (2 ^ w * 2 ^ w) → ZMod 2) (t : Fin (2 ^ w * 2 ^ w)) :
    E_S w f (t.val + 1) = E_S w f t.val + f t := by
  unfold E_S
  have : ∀ i : Fin (2 ^ w * 2 ^ w), (if i.val < t.val + 1 then f i else 0) =
      (if i.val < t.val then f i else 0) + (if i = t then f i else 0) := by
    intro i
    by_cases h1 : i.val < t.val
    · have h2 : i ≠ t := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h3 : i.val < t.val + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i = t
      · subst h2; simp
      · have h3 : ¬ i.val < t.val + 1 := by
          intro h3
          apply h2
          apply Fin.ext
          omega
        simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  simp

theorem E_Slast (w : ℕ) (f : Fin (2 ^ w * 2 ^ w) → ZMod 2) :
    E_S w f (2 ^ w * 2 ^ w) = ∑ i, f i := by
  unfold E_S
  exact Finset.sum_congr rfl (fun i _ => by simp [i.isLt])

def E_hsum (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2) (j : Fin s) : ZMod 2 :=
  ∑ e, Hc j e * trans w h P e.1 e.2

theorem E_hsum_eq (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2) (j : Fin s) :
    E_S w (fun t => Hc j (E_ent w t) * trans w h P (E_ent w t).1 (E_ent w t).2) (2 ^ w * 2 ^ w) =
      E_hsum w h s P Hc j := by
  rw [E_Slast]
  exact Equiv.sum_comp (E_ent w) (fun e => Hc j e * trans w h P e.1 e.2)

theorem E_good_fwd (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2)
    (z : Fin s → Bool) (β : E_A w h s → Bool) (hg : E_good w h s P Hc z β) :
    ∀ j, z j = decide (E_hsum w h s P Hc j = 1) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg
  have hM : ∀ (i : ℕ) (hi : i < h + 1) (a c : Fin w → Bool),
      β (Sum.inl (⟨i, hi⟩, a, c)) = decide (transN w (gExt w h P) i a c = 1) := by
    intro i
    induction i with
    | zero =>
      intro hi a c
      rw [E_T0]
      exact g1 a c
    | succ i ih =>
      intro hi a c
      have hi' : i < h := by omega
      have e1 := g2 ⟨i, hi'⟩ a c
      have e2 := g3 ⟨i, hi'⟩ a c false
      have e3 := g3 ⟨i, hi'⟩ a c true
      rw [E_Tsucc w h P i hi']
      rw [← ih (by omega), ← ih (by omega)]
      exact e1.trans (by rw [e2, e3]; rfl)
  intro j
  have hq : ∀ (t : ℕ) (ht : t < 2 ^ w * 2 ^ w + 1),
      β (Sum.inr (Sum.inr (j, ⟨t, ht⟩))) =
        decide (E_S w (fun t => Hc j (E_ent w t) * trans w h P (E_ent w t).1 (E_ent w t).2) t
          = 1) := by
    intro t
    induction t with
    | zero =>
      intro ht
      rw [E_S0]
      exact (g4 j).trans (by decide)
    | succ t ih =>
      intro ht
      have ht' : t < 2 ^ w * 2 ^ w := by omega
      have e1 := g5 j ⟨t, ht'⟩
      have e2 := E_Ssucc w (fun t => Hc j (E_ent w t) * trans w h P (E_ent w t).1 (E_ent w t).2)
        ⟨t, ht'⟩
      simp only at e2
      rw [e2, E_dec2, ← ih (by omega)]
      have e3 := hM h (by omega) (E_ent w ⟨t, ht'⟩).1 (E_ent w ⟨t, ht'⟩).2
      exact e1.trans (by
        congr 2)
  rw [g6 j, ← E_hsum_eq]
  exact hq _ _

noncomputable def E_beta (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2) : E_A w h s → Bool
  | Sum.inl (i, a, c) => decide (transN w (gExt w h P) i.val a c = 1)
  | Sum.inr (Sum.inl (i, a, c, b)) =>
      (decide (transN w (gExt w h P) i.val a (Fin.init (Fin.cons b c : Fin (w + 1) → Bool)) = 1)
        && P (i, (Fin.cons b c : Fin (w + 1) → Bool)))
  | Sum.inr (Sum.inr (j, t)) =>
      decide (E_S w (fun t => Hc j (E_ent w t) * trans w h P (E_ent w t).1 (E_ent w t).2) t.val
        = 1)

theorem E_good_bwd (w h s : ℕ) (P : Fin h × (Fin (w + 1) → Bool) → Bool)
    (Hc : Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2) :
    E_good w h s P Hc (fun j => decide (E_hsum w h s P Hc j = 1)) (E_beta w h s P Hc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c
    exact E_T0 w _ a c
  · intro i a c
    simp only [E_beta, Fin.val_succ]
    exact E_Tsucc w h P i.val i.isLt a c
  · intro i a c b
    simp only [E_beta, Fin.val_castSucc]
  · intro j
    simp only [E_beta, Fin.val_zero, E_S0]
    decide
  · intro j t
    simp only [E_beta, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    exact (congrArg (fun x : ZMod 2 => decide (x = 1)) (E_Ssucc w _ t)).trans (E_dec2 _ _ _)
  · intro j
    simp only [E_beta, Fin.val_last]
    exact congrArg (fun x : ZMod 2 => decide (x = 1)) (E_hsum_eq w h s P Hc j).symm

theorem E_cardA (w h s : ℕ) :
    Fintype.card (E_A w h s) =
      (h + 1) * (2 ^ w * 2 ^ w) + (h * (2 ^ w * 2 ^ w * 2) + s * (2 ^ w * 2 ^ w + 1)) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_pi, Finset.prod_const, Finset.card_univ]
  ring

theorem cnf_exists (w h s r : ℕ)
    (H : Fin r → Fin s → (Fin w → Bool) × (Fin w → Bool) → ZMod 2) :
    ∃ (a b : ℕ)
      (F : Fin r → Finset (PEqualNP.ProofComplexity.Clause
        (Sum (Fin h × (Fin (w + 1) → Bool)) (Sum (Fin s) (Fin a)))))
      (G : Fin r → Finset (PEqualNP.ProofComplexity.Clause
        (Sum (Fin h × (Fin (w + 1) → Bool)) (Sum (Fin s) (Fin b))))),
      (∀ c : Fin r,
        (∀ C ∈ F c, C.card ≤ 3) ∧ (∀ C ∈ G c, C.card ≤ 3) ∧
        a + b + (∑ C ∈ F c, C.card) + (∑ C ∈ G c, C.card) ≤
          96 * (h + s + 1) * (2 ^ w * 2 ^ w + 1)) ∧
      ∀ (P Q : Fin h × (Fin (w + 1) → Bool) → Bool) (coin : Fin r),
        (∃ (z : Fin s → Bool) (u : Fin a → Bool) (v : Fin b → Bool),
          PEqualNP.ProofComplexity.Satisfies (Sum.elim P (Sum.elim z u)) (↑(F coin) : Set _) ∧
          PEqualNP.ProofComplexity.Satisfies (Sum.elim Q (Sum.elim z v)) (↑(G coin) : Set _))
        ↔ ∀ j : Fin s, ∑ e, H coin j e * (trans w h P e.1 e.2 - trans w h Q e.1 e.2) = 0 := by
  refine ⟨Fintype.card (E_A w h s), Fintype.card (E_A w h s),
    fun c => E_cnf (E_gate w h s (H c)), fun c => E_cnf (E_gate w h s (H c)), ?_, ?_⟩
  · intro c
    refine ⟨E_cnf_card3 _, E_cnf_card3 _, ?_⟩
    have h1 := E_cnf_sum (E_gate w h s (H c))
    have h2 : Fintype.card (Sum (E_A w h s) (Fin s)) = Fintype.card (E_A w h s) + s := by
      rw [Fintype.card_sum, Fintype.card_fin]
    rw [h2] at h1
    clear h2
    beta_reduce
    have h3 := E_cardA w h s
    generalize (∑ C ∈ E_cnf (E_gate w h s (H c)), C.card) = S at *
    generalize Fintype.card (E_A w h s) = A at *
    generalize 2 ^ w * 2 ^ w = m at *
    subst h3
    have e1 : 96 * (h + s + 1) * (m + 1) =
        96 * (h * m) + 96 * h + 96 * (s * m) + 96 * s + 96 * m + 96 := by ring
    have e2 : (h + 1) * m + (h * (m * 2) + s * (m + 1)) = 3 * (h * m) + m + s * m + s := by ring
    rw [e1]
    rw [e2] at h1 ⊢
    omega
  · intro P Q coin
    have hsub : ∀ j : Fin s, (∑ e, H coin j e * (trans w h P e.1 e.2 - trans w h Q e.1 e.2) = 0) ↔
        E_hsum w h s P (H coin) j = E_hsum w h s Q (H coin) j := by
      intro j
      have e1 : (∑ e, H coin j e * (trans w h P e.1 e.2 - trans w h Q e.1 e.2)) =
          E_hsum w h s P (H coin) j - E_hsum w h s Q (H coin) j := by
        unfold E_hsum
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun e _ => mul_sub _ _ _)
      rw [e1, sub_eq_zero]
    constructor
    · rintro ⟨z, u, v, hF, hG⟩ j
      rw [hsub]
      have h1 := E_good_fwd w h s P (H coin) z _ ((E_sat_iff w h s P (H coin) z u).1 hF) j
      have h2 := E_good_fwd w h s Q (H coin) z _ ((E_sat_iff w h s Q (H coin) z v).1 hG) j
      exact E_dec3 _ _ (h1.symm.trans h2)
    · intro hall
      have hz : (fun j => decide (E_hsum w h s P (H coin) j = 1)) =
          (fun j => decide (E_hsum w h s Q (H coin) j = 1)) := by
        funext j
        rw [(hsub j).1 (hall j)]
      refine ⟨fun j => decide (E_hsum w h s P (H coin) j = 1),
        fun i => E_beta w h s P (H coin) ((Fintype.equivFin _).symm i),
        fun i => E_beta w h s Q (H coin) ((Fintype.equivFin _).symm i), ?_, ?_⟩
      · rw [E_sat_iff]
        simp only [Equiv.symm_apply_apply]
        exact E_good_bwd w h s P (H coin)
      · rw [hz, E_sat_iff]
        simp only [Equiv.symm_apply_apply]
        exact E_good_bwd w h s Q (H coin)

end PEqualNP.Outside.L_pcx_317

theorem PEqualNP.Outside.L_pcx_317 : (∀ (d paddingLeft paddingRight : ℕ),
  let w := d + 1
  let D := 2 ^ w
  let m := D * D
  let L := (12 * w * D * (D + 2) + 1) * w
  let h := L + paddingLeft
  let k := L + paddingRight
  let n := h + k
  let pos := fun idx : ℕ => (⟨idx % n, Nat.mod_lt _ (Nat.add_pos_left (Nat.add_pos_left (Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)) _) _)⟩ : Fin n)
  let Raw := fun length : ℕ => Fin length × (Fin (w + 1) → Bool)
  let parity := fun (P : Raw h → Bool) (R : Raw k → Bool) =>
    let good := fun x : Fin n → Bool =>
      (∀ i : Fin h, P (i, fun j => x (pos (i.val + j.val))) = true) ∧
      ∀ i : Fin k, R (i, fun j => x (pos (h + i.val + j.val))) = true
    (Finset.univ.filter good).card.testBit 0
  let same := fun (P Q : Raw h → Bool) => ∀ R : Raw k → Bool, parity P R = parity Q R
  ∀ s : ℕ, s ≤ m →
    let N := 2 ^ m
    let K := 2 ^ (m - s)
    let divisor := 2 ^ Nat.gcd m s - 1
    let period := (N - 1) / divisor
    let hits := (K - 1) / divisor
    let V := fun size : ℕ => Sum (Raw h) (Sum (Fin s) (Fin size))
    let possible := fun (r errors : ℕ) (small : Bool) =>
      ∃ (a b : ℕ)
        (F : Fin r → Finset (PEqualNP.ProofComplexity.Clause (V a)))
        (G : Fin r → Finset (PEqualNP.ProofComplexity.Clause (V b))),
        (small = true → ∀ c : Fin r,
          (∀ C ∈ F c, C.card ≤ 3) ∧ (∀ C ∈ G c, C.card ≤ 3) ∧
          a + b + (∑ C ∈ F c, C.card) + (∑ C ∈ G c, C.card) ≤
            96 * (h + s + 1) * (m + 1)) ∧
        ∀ P Q : Raw h → Bool,
          let accepts := fun coin : Fin r =>
            ∃ (z : Fin s → Bool) (u : Fin a → Bool) (v : Fin b → Bool),
              PEqualNP.ProofComplexity.Satisfies (Sum.elim P (Sum.elim z u)) (↑(F coin) : Set _) ∧
              PEqualNP.ProofComplexity.Satisfies (Sum.elim Q (Sum.elim z v)) (↑(G coin) : Set _)
          (same P Q → ∀ coin, accepts coin) ∧
          (¬same P Q → (@Finset.filter _ accepts (Classical.decPred _) Finset.univ).card ≤ errors)
    ∀ r : ℕ, 0 < r →
      (∀ errors, possible r errors false → r * (K - 1) ≤ errors * (N - 1)) ∧
      possible r (r / period * hits + min (r % period) hits) true ∧
      ((∃ errors, possible r errors false ∧ errors * (N - 1) = r * (K - 1)) ↔ period ∣ r)) := by
  intro d pl pr w D m L h k n pos Raw parity same s hs N K divisor period hits V possible r hr
  have hm : 0 < m := by
    show 0 < 2 ^ (d + 1) * 2 ^ (d + 1)
    positivity
  have hX1 : 2 * (d + 1) ≤ (12 * (d + 1) * 2 ^ (d + 1) * (2 ^ (d + 1) + 2) + 1) * (d + 1) := by
    apply Nat.mul_le_mul_right
    have : 0 < 12 * (d + 1) * 2 ^ (d + 1) * (2 ^ (d + 1) + 2) := by positivity
    omega
  have hLh : (12 * (d + 1) * 2 ^ (d + 1) * (2 ^ (d + 1) + 2) + 1) * (d + 1) ≤ h :=
    Nat.le_add_right _ _
  have hLk : (12 * (d + 1) * 2 ^ (d + 1) * (2 ^ (d + 1) + 2) + 1) * (d + 1) ≤ k :=
    Nat.le_add_right _ _
  have hd2h : d + 2 ≤ h := by omega
  have hd2k : d + 2 ≤ k := by omega
  have hsame : ∀ P Q : Raw h → Bool, same P Q ↔
      PEqualNP.Outside.L_pcx_317.trans (d + 1) h P = PEqualNP.Outside.L_pcx_317.trans (d + 1) h Q :=
    fun P Q => PEqualNP.Outside.L_pcx_317.same_iff d h k hd2h hd2k (Nat.add_pos_left (lt_of_lt_of_le (Nat.succ_pos _) hd2h) k) P Q
  have hpart2 : possible r (r / period * hits + min (r % period) hits) true := by
    obtain ⟨H, hH⟩ := PEqualNP.Outside.L_pcx_317.hash_exists m s hm hs
      ((Fin (d + 1) → Bool) × (Fin (d + 1) → Bool)) (by simp [m, D, w]) r
    obtain ⟨a, b, F, G, hsize, hacc⟩ := PEqualNP.Outside.L_pcx_317.cnf_exists (d + 1) h s r H
    refine ⟨a, b, F, G, fun _ => hsize, fun P Q => ⟨?_, ?_⟩⟩
    · intro hs' coin
      rw [hsame] at hs'
      exact (hacc P Q coin).2 (by intro j; simp [hs'])
    · intro hns
      rw [hsame] at hns
      have hv : (fun e : (Fin (d + 1) → Bool) × (Fin (d + 1) → Bool) =>
          PEqualNP.Outside.L_pcx_317.trans (d + 1) h P e.1 e.2 -
          PEqualNP.Outside.L_pcx_317.trans (d + 1) h Q e.1 e.2) ≠ 0 := by
        intro h0
        apply hns
        ext x y
        have := congrFun h0 (x, y)
        exact sub_eq_zero.mp this
      refine le_trans (le_of_eq ?_) (hH _ hv)
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hacc P Q c
  refine ⟨?_, hpart2, ?_⟩
  · rintro errors ⟨a, b, F, G, -, hPQ⟩
    choose PM hPM using fun M => PEqualNP.Outside.L_pcx_317.trans_surj d h hLh M
    have hacc : ∀ (M : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) (c : Fin r),
        ∃ (z : Fin s → Bool) (u : Fin a → Bool) (v : Fin b → Bool),
          PEqualNP.ProofComplexity.Satisfies (Sum.elim (PM M) (Sum.elim z u)) (↑(F c) : Set _) ∧
          PEqualNP.ProofComplexity.Satisfies (Sum.elim (PM M) (Sum.elim z v)) (↑(G c) : Set _) :=
      fun M c => (hPQ (PM M) (PM M)).1 (fun R => rfl) c
    choose zf uf vf hF hG using hacc
    have hX : Fintype.card (Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) (ZMod 2)) = 2 ^ m := by
      exact PEqualNP.Outside.L_pcx_317.Z_card_mat (d + 1)
    refine PEqualNP.Outside.L_pcx_317.lower_count _ m s hs hX r errors
      (fun c M M' => ∃ (z : Fin s → Bool) (u : Fin a → Bool) (v : Fin b → Bool),
          PEqualNP.ProofComplexity.Satisfies (Sum.elim (PM M) (Sum.elim z u)) (↑(F c) : Set _) ∧
          PEqualNP.ProofComplexity.Satisfies (Sum.elim (PM M') (Sum.elim z v)) (↑(G c) : Set _))
      (fun c M => zf M c) ?_ ?_
    · intro c x y hxy
      refine ⟨zf x c, uf x c, vf y c, hF x c, ?_⟩
      have hxy' : zf x c = zf y c := hxy
      rw [hxy']
      exact hG y c
    · intro x y hxy
      exact (hPQ (PM x) (PM y)).2 (by rw [hsame, hPM, hPM]; exact hxy)
  · constructor
    · rintro ⟨errors, -, he⟩
      exact PEqualNP.Outside.L_pcx_317.nt_dvd m s hm hs r errors he
    · intro hdvd
      obtain ⟨a, b, F, G, -, hPQ⟩ := hpart2
      exact ⟨_, ⟨a, b, F, G, fun hf => absurd hf (by decide), hPQ⟩,
        PEqualNP.Outside.L_pcx_317.nt_eq m s hm hs r hdvd⟩
