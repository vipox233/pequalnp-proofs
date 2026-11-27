import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_415

theorem card_X (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by
  simp

/-- For one map, the number of ordered pairs with equal images is large. -/
theorem one_map_bound {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (g : X → Y) :
    (Fintype.card X) ^ 2 ≤
      Fintype.card Y * ∑ u : X, ∑ v : X, (if g u = g v then 1 else 0) := by
  have h1 : ∑ y : Y, (Finset.univ.filter (fun u : X => g u = y)).card = Fintype.card X := by
    rw [← Finset.card_univ (α := X)]
    exact (Finset.card_eq_sum_card_fiberwise (fun u _ => Finset.mem_univ (g u))).symm
  have h2 : ∑ u : X, ∑ v : X, (if g u = g v then 1 else 0) =
      ∑ y : Y, ((Finset.univ.filter (fun u : X => g u = y)).card) ^ 2 := by
    rw [← Finset.sum_fiberwise Finset.univ g (fun u => ∑ v : X, (if g u = g v then 1 else 0))]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h3 : ∀ u ∈ Finset.univ.filter (fun u : X => g u = y),
        (∑ v : X, (if g u = g v then 1 else 0)) =
          (Finset.univ.filter (fun u : X => g u = y)).card := by
      intro u hu
      have hu' : g u = y := (Finset.mem_filter.mp hu).2
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hu']
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, sq]
  rw [h2, ← h1]
  have h4 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Y))
    (f := fun y => (Finset.univ.filter (fun u : X => g u = y)).card)
  rw [Finset.card_univ] at h4
  exact h4

/-- The counting half: the bound on the number of maps, and the case of equality. -/
theorem partB (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) (r errors : ℕ)
    (f : Fin r → (Fin m → Bool) → (Fin s → Bool))
    (hcoll : ∀ u v : Fin m → Bool, u ≠ v →
      (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card ≤ errors) :
    r * (2 ^ (m - s) - 1) ≤ errors * (2 ^ m - 1) ∧
    (errors * (2 ^ m - 1) = r * (2 ^ (m - s) - 1) →
      (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) ∣ r ∧
      ∀ u v : Fin m → Bool, u ≠ v →
        (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card = errors) := by
  have hNK : (2:ℕ) ^ m = 2 ^ s * 2 ^ (m - s) := by
    rw [← pow_add]
    congr 1
    omega
  have hNpos : 0 < (2:ℕ) ^ m := by positivity
  have hKpos : 0 < (2:ℕ) ^ (m - s) := by positivity
  -- the number of triples, counted by maps
  have hT1 : r * ((2:ℕ) ^ m) ^ 2 ≤ 2 ^ s * ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
      (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card := by
    have h1 : ∀ i : Fin r, ((2:ℕ) ^ m) ^ 2 ≤ 2 ^ s * ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
        (if f i u = f i v then 1 else 0) := by
      intro i
      have h := one_map_bound (f i)
      rw [card_X m, card_X s] at h
      exact h
    have h2 : (∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
        (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card) =
        ∑ i : Fin r, ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
          (if f i u = f i v then 1 else 0) := by
      calc (∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
            (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card)
          = ∑ u : Fin m → Bool, ∑ v : Fin m → Bool, ∑ i : Fin r,
              (if f i u = f i v then 1 else 0) := by
            simp only [Finset.card_filter]
        _ = ∑ u : Fin m → Bool, ∑ i : Fin r, ∑ v : Fin m → Bool,
              (if f i u = f i v then 1 else 0) :=
            Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ i : Fin r, ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
              (if f i u = f i v then 1 else 0) := Finset.sum_comm
    calc r * ((2:ℕ) ^ m) ^ 2 = ∑ _i : Fin r, ((2:ℕ) ^ m) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ i : Fin r, 2 ^ s * ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
            (if f i u = f i v then 1 else 0) := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 ^ s * ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
            (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card := by
          rw [h2, Finset.mul_sum]
  -- the same number, counted by pairs
  have hdiag : ∀ u : Fin m → Bool,
      (Finset.univ.filter (fun i : Fin r => f i u = f i u)).card ≤ r := by
    intro u
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have herase : ∀ u : Fin m → Bool,
      (Finset.univ.erase u : Finset (Fin m → Bool)).card = 2 ^ m - 1 := by
    intro u
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, card_X]
  have hrow : ∀ u : Fin m → Bool, (∑ v : Fin m → Bool,
      (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card) ≤
        r + (2 ^ m - 1) * errors := by
    intro u
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u)]
    have h2 : (∑ v ∈ Finset.univ.erase u,
        (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card) ≤
        (Finset.univ.erase u).card • errors :=
      Finset.sum_le_card_nsmul _ _ _ (fun v hv => hcoll u v (Finset.ne_of_mem_erase hv).symm)
    rw [herase u, smul_eq_mul] at h2
    have h1 := hdiag u
    omega
  have hT2 : (∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
      (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card) ≤
        2 ^ m * (r + (2 ^ m - 1) * errors) := by
    calc (∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
          (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card)
        ≤ ∑ _u : Fin m → Bool, (r + (2 ^ m - 1) * errors) :=
          Finset.sum_le_sum fun u _ => hrow u
      _ = 2 ^ m * (r + (2 ^ m - 1) * errors) := by
          rw [Finset.sum_const, Finset.card_univ, card_X, smul_eq_mul]
  have he : r * ((2:ℕ) ^ m) ^ 2 = (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) := by
    have h : (2:ℕ) ^ m * 2 ^ m = 2 ^ m * (2 ^ s * 2 ^ (m - s)) := congrArg (fun t => 2 ^ m * t) hNK
    calc r * ((2:ℕ) ^ m) ^ 2 = r * (2 ^ m * 2 ^ m) := by ring
      _ = r * (2 ^ m * (2 ^ s * 2 ^ (m - s))) := by rw [h]
      _ = (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) := by ring
  have hmain : r * 2 ^ (m - s) ≤ r + (2 ^ m - 1) * errors := by
    have h1 : (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) ≤
        (2 ^ s * 2 ^ m) * (r + (2 ^ m - 1) * errors) := by
      rw [← he]
      calc r * ((2:ℕ) ^ m) ^ 2 ≤ 2 ^ s * ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
            (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card := hT1
        _ ≤ 2 ^ s * (2 ^ m * (r + (2 ^ m - 1) * errors)) := Nat.mul_le_mul_left _ hT2
        _ = (2 ^ s * 2 ^ m) * (r + (2 ^ m - 1) * errors) := by ring
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have hsub : r * (2 ^ (m - s) - 1) = r * 2 ^ (m - s) - r := Nat.mul_sub_one r _
  refine ⟨?_, fun heq => ⟨?_, ?_⟩⟩
  · rw [hsub, mul_comm errors]
    omega
  · -- the divisibility
    have hg : 0 < Nat.gcd m s := Nat.gcd_pos_of_pos_left s hm
    have hdpos : 0 < 2 ^ Nat.gcd m s - 1 := by
      have h : (2:ℕ) ^ 1 ≤ 2 ^ Nat.gcd m s := Nat.pow_le_pow_right (by norm_num) hg
      omega
    have hgcd : Nat.gcd (2 ^ m - 1) (2 ^ (m - s) - 1) = 2 ^ Nat.gcd m s - 1 := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_self_sub_right hs]
    have hcop : Nat.Coprime ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1))
        ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) := by
      have h := Nat.coprime_div_gcd_div_gcd (m := 2 ^ m - 1) (n := 2 ^ (m - s) - 1)
        (by rw [hgcd]; exact hdpos)
      rw [hgcd] at h
      exact h
    have hdN : 2 ^ Nat.gcd m s - 1 ∣ 2 ^ m - 1 := hgcd ▸ Nat.gcd_dvd_left _ _
    have hdK : 2 ^ Nat.gcd m s - 1 ∣ 2 ^ (m - s) - 1 := hgcd ▸ Nat.gcd_dvd_right _ _
    have heq' : errors * ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) =
        r * ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) := by
      have h1 : errors * (2 ^ m - 1) =
          errors * ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) * (2 ^ Nat.gcd m s - 1) := by
        rw [mul_assoc, Nat.div_mul_cancel hdN]
      have h2 : r * (2 ^ (m - s) - 1) =
          r * ((2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1)) * (2 ^ Nat.gcd m s - 1) := by
        rw [mul_assoc, Nat.div_mul_cancel hdK]
      rw [h1, h2] at heq
      exact Nat.eq_of_mul_eq_mul_right hdpos heq
    exact hcop.dvd_of_dvd_mul_right (Dvd.intro_left errors heq')
  · -- every pair attains the bound
    intro u0 v0 hne
    by_contra hcne
    have hlt : (Finset.univ.filter (fun i : Fin r => f i u0 = f i v0)).card < errors :=
      lt_of_le_of_ne (hcoll u0 v0 hne) hcne
    have hrow0 : (∑ v : Fin m → Bool,
        (Finset.univ.filter (fun i : Fin r => f i u0 = f i v)).card) <
          r + (2 ^ m - 1) * errors := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u0)]
      have h2 : (∑ v ∈ Finset.univ.erase u0,
          (Finset.univ.filter (fun i : Fin r => f i u0 = f i v)).card) <
          ∑ _v ∈ Finset.univ.erase u0, errors :=
        Finset.sum_lt_sum (fun v hv => hcoll u0 v (Finset.ne_of_mem_erase hv).symm)
          ⟨v0, Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩, hlt⟩
      rw [Finset.sum_const, herase u0, smul_eq_mul] at h2
      have h1 := hdiag u0
      omega
    have hTlt : (∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
        (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card) <
          2 ^ m * (r + (2 ^ m - 1) * errors) := by
      calc (∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
            (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card)
          < ∑ _u : Fin m → Bool, (r + (2 ^ m - 1) * errors) :=
            Finset.sum_lt_sum (fun u _ => hrow u) ⟨u0, Finset.mem_univ _, hrow0⟩
        _ = 2 ^ m * (r + (2 ^ m - 1) * errors) := by
            rw [Finset.sum_const, Finset.card_univ, card_X, smul_eq_mul]
    have hrK : r + (2 ^ m - 1) * errors = r * 2 ^ (m - s) := by
      rw [mul_comm (2 ^ m - 1), heq, hsub]
      have h : r ≤ r * 2 ^ (m - s) := Nat.le_mul_of_pos_right r hKpos
      omega
    rw [hrK] at hTlt
    have hcontra : (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) < (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) := by
      calc (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) = r * ((2:ℕ) ^ m) ^ 2 := he.symm
        _ ≤ 2 ^ s * ∑ u : Fin m → Bool, ∑ v : Fin m → Bool,
            (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card := hT1
        _ < 2 ^ s * (2 ^ m * (r * 2 ^ (m - s))) := mul_lt_mul_of_pos_left hTlt (by positivity)
        _ = (2 ^ s * 2 ^ m) * (r * 2 ^ (m - s)) := by ring
    exact lt_irrefl _ hcontra

theorem bit_add (a b : Bool) :
    (if xor a b then (1 : ZMod 2) else 0) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem bit_inj (a b : Bool)
    (h : (if a then (1 : ZMod 2) else 0) = (if b then 1 else 0)) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem bit_surj : ∀ z : ZMod 2, (if decide (z = 1) then (1 : ZMod 2) else 0) = z := by
  decide

/-- A finite vector space over the two-element field with `2 ^ k` elements is a copy of the
bit strings of length `k`, with addition matching the bitwise exclusive or. -/
theorem exists_enc (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [Finite M] (k : ℕ)
    (hk : Nat.card M = 2 ^ k) :
    ∃ e : (Fin k → Bool) → M, Function.Bijective e ∧
      ∀ u v : Fin k → Bool, e (fun j => xor (u j) (v j)) = e u + e v := by
  have hfr : Module.finrank (ZMod 2) M = k := by
    have h := FiniteField.pow_finrank_eq_natCard 2 M
    rw [hk] at h
    exact Nat.pow_right_injective (le_refl 2) h
  refine ⟨fun u => (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm
    (fun j => if u j then (1 : ZMod 2) else 0), ⟨?_, ?_⟩, ?_⟩
  · intro u v h
    have h' := (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm.injective h
    funext j
    exact bit_inj _ _ (congrFun h' j)
  · intro x
    refine ⟨fun j => decide ((Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun x j = 1), ?_⟩
    have h1 : (fun j => if decide ((Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun x j = 1)
        then (1 : ZMod 2) else 0) = (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun x := by
      funext j
      exact bit_surj _
    show (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm
      (fun j => if decide ((Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun x j = 1)
        then (1 : ZMod 2) else 0) = x
    rw [h1]
    exact (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm_apply_apply x
  · intro u v
    show (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm
        (fun j => if xor (u j) (v j) then (1 : ZMod 2) else 0) =
      (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm
        (fun j => if u j then (1 : ZMod 2) else 0) +
      (Module.finBasisOfFinrankEq (ZMod 2) M hfr).equivFun.symm
        (fun j => if v j then (1 : ZMod 2) else 0)
    rw [← map_add]
    congr 1
    funext j
    exact bit_add _ _

/-- A set of group elements closed under right multiplication by a subgroup is a union of
cosets; the chosen coset representatives inside it count its cosets. -/
theorem coset_count {G : Type} [Group G] (H : Subgroup G) (T : Set G)
    (hT : ∀ a ∈ T, ∀ h ∈ H, a * h ∈ T) :
    Nat.card {c : G ⧸ H // Quotient.out c ∈ T} * Nat.card H = Nat.card T := by
  have hout : ∀ a : G, a ∈ T → Quotient.out (QuotientGroup.mk a : G ⧸ H) ∈ T := by
    intro a ha
    have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk a : G ⧸ H)) : G ⧸ H) =
        QuotientGroup.mk a := QuotientGroup.out_eq' _
    have h2 : a⁻¹ * Quotient.out (QuotientGroup.mk a : G ⧸ H) ∈ H := QuotientGroup.eq.mp h1.symm
    have h3 := hT a ha _ h2
    rwa [mul_inv_cancel_left] at h3
  have hmem : ∀ a : G, (Quotient.out (QuotientGroup.mk a : G ⧸ H))⁻¹ * a ∈ H := by
    intro a
    exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk a : G ⧸ H))
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun p => ⟨Quotient.out p.1.1 * p.2.1, hT _ p.1.2 _ p.2.2⟩
      invFun := fun a => (⟨QuotientGroup.mk a.1, hout a.1 a.2⟩,
        ⟨(Quotient.out (QuotientGroup.mk a.1 : G ⧸ H))⁻¹ * a.1, hmem a.1⟩)
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨c, hc⟩, ⟨h, hh⟩⟩
    have hc' : (QuotientGroup.mk (Quotient.out c * h) : G ⧸ H) = c :=
      (QuotientGroup.mk_mul_of_mem _ hh).trans (QuotientGroup.out_eq' c)
    refine Prod.ext (Subtype.ext hc') (Subtype.ext ?_)
    show (Quotient.out (QuotientGroup.mk (Quotient.out c * h) : G ⧸ H))⁻¹ * (Quotient.out c * h) = h
    rw [hc', inv_mul_cancel_left]
  · rintro ⟨a, ha⟩
    exact Subtype.ext (mul_inv_cancel_left _ _)

/-- The family of maps, for any finite fields `Kf ⊆ F` and a `Kf`-linear surjection of `F`. -/
theorem construct {F Kf V : Type} [Field F] [Finite F] [Field Kf] [Finite Kf] [Algebra Kf F]
    [AddCommGroup V] [Module Kf V] [Finite V]
    (m s g : ℕ) (hg : 0 < g) (hsm : s ≤ m)
    (hF : Nat.card F = 2 ^ m) (hK : Nat.card Kf = 2 ^ g) (hV : Nat.card V = 2 ^ s)
    (π : F →ₗ[Kf] V) (hπ : Function.Surjective π)
    (eX : (Fin m → Bool) → F) (heX : Function.Bijective eX)
    (haX : ∀ u v : Fin m → Bool, eX (fun j => xor (u j) (v j)) = eX u + eX v)
    (eY : (Fin s → Bool) → V) (heY : Function.Bijective eY)
    (haY : ∀ u v : Fin s → Bool, eY (fun j => xor (u j) (v j)) = eY u + eY v) :
    ∃ family : Fin ((2 ^ m - 1) / (2 ^ g - 1)) → (Fin m → Bool) → (Fin s → Bool),
      (∀ i, Function.Surjective (family i)) ∧
      (∀ i u v, family i (fun j => xor (u j) (v j)) =
        fun out => xor (family i u out) (family i v out)) ∧
      ∀ u v : Fin m → Bool, u ≠ v →
        (Finset.univ.filter (fun i => family i u = family i v)).card =
          (2 ^ (m - s) - 1) / (2 ^ g - 1) := by
  have hd : 0 < 2 ^ g - 1 := by
    have h : (2:ℕ) ^ 1 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega
  have hinj : Function.Injective (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)) :=
    Units.map_injective (algebraMap Kf F).injective
  have hHcard : Nat.card (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range =
      2 ^ g - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hK]
  have hFu : Nat.card Fˣ = 2 ^ m - 1 := by
    rw [Nat.card_units, hF]
  have hicard : Nat.card (Fˣ ⧸ (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range) =
      (2 ^ m - 1) / (2 ^ g - 1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range
    rw [hFu, hHcard] at h
    exact (Nat.div_eq_of_eq_mul_left hd h).symm
  -- the size of the kernel
  have hker : Nat.card {x : F // π x = 0} = 2 ^ (m - s) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (π.toAddMonoidHom.ker)
    have h2 : Nat.card (F ⧸ π.toAddMonoidHom.ker) = Nat.card V :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π.toAddMonoidHom hπ).toEquiv
    have h3 : Nat.card (π.toAddMonoidHom.ker) = Nat.card {x : F // π x = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [AddMonoidHom.mem_ker]
        rfl))
    rw [h2, hF, hV, h3] at h1
    have h4 : (2:ℕ) ^ m = 2 ^ s * 2 ^ (m - s) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h4] at h1
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
  -- the count of chosen representatives that send a nonzero element into the kernel
  have hcount : ∀ w : F, w ≠ 0 →
      Nat.card {c : Fˣ ⧸ (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range //
        π (((Quotient.out c : Fˣ) : F) * w) = 0} = (2 ^ (m - s) - 1) / (2 ^ g - 1) := by
    intro w hw
    have hstab : ∀ a ∈ {a : Fˣ | π ((a : F) * w) = 0},
        ∀ h ∈ (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range,
          a * h ∈ {a : Fˣ | π ((a : F) * w) = 0} := by
      rintro a ha h ⟨k, rfl⟩
      have ha' : π ((a : F) * w) = 0 := ha
      show π (((a * Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F) k : Fˣ) : F) * w) = 0
      have h1 : ((a * Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F) k : Fˣ) : F) * w =
          (k : Kf) • ((a : F) * w) := by
        rw [Algebra.smul_def]
        simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass]
        ring
      rw [h1, map_smul, ha', smul_zero]
    have h2 := coset_count (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range
      {a : Fˣ | π ((a : F) * w) = 0} hstab
    rw [hHcard] at h2
    -- the set has one element fewer than the kernel
    have h3 : Nat.card {a : Fˣ | π ((a : F) * w) = 0} + 1 = Nat.card {x : F // π x = 0} := by
      classical
      have : Fintype F := Fintype.ofFinite F
      have h4 : Nat.card {x : F // π x = 0} =
          (Finset.univ.filter (fun x : F => π x = 0)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hne : ∀ x : {x : F // x ∈ (Finset.univ.filter (fun x : F => π x = 0)).erase 0},
          x.1 * w⁻¹ ≠ 0 := by
        intro x
        have hx := x.2
        rw [Finset.mem_erase] at hx
        exact mul_ne_zero hx.1 (inv_ne_zero hw)
      have h5 : Nat.card {a : Fˣ | π ((a : F) * w) = 0} =
          ((Finset.univ.filter (fun x : F => π x = 0)).erase 0).card := by
        rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
        refine Nat.card_congr
          { toFun := fun a => ⟨(a.1 : F) * w, by
              rw [Finset.mem_erase, Finset.mem_filter]
              exact ⟨mul_ne_zero a.1.ne_zero hw, Finset.mem_univ _, a.2⟩⟩
            invFun := fun x => ⟨Units.mk0 (x.1 * w⁻¹) (hne x), by
              have hx := x.2
              rw [Finset.mem_erase, Finset.mem_filter] at hx
              show π (((Units.mk0 (x.1 * w⁻¹) (hne x) : Fˣ) : F) * w) = 0
              rw [Units.val_mk0, inv_mul_cancel_right₀ hw]
              exact hx.2.2⟩
            left_inv := ?_
            right_inv := ?_ }
        · intro a
          apply Subtype.ext
          apply Units.ext
          show (a.1 : F) * w * w⁻¹ = (a.1 : F)
          exact mul_inv_cancel_right₀ hw _
        · intro x
          apply Subtype.ext
          show ((Units.mk0 (x.1 * w⁻¹) (hne x) : Fˣ) : F) * w = x.1
          rw [Units.val_mk0, inv_mul_cancel_right₀ hw]
      have h6 : (0 : F) ∈ Finset.univ.filter (fun x : F => π x = 0) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, map_zero π⟩
      rw [h4, h5, Finset.card_erase_of_mem h6]
      have h7 : 0 < (Finset.univ.filter (fun x : F => π x = 0)).card :=
        Finset.card_pos.mpr ⟨0, h6⟩
      omega
    rw [hker] at h3
    have h8 : 2 ^ (m - s) - 1 = Nat.card {c : Fˣ ⧸
        (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range //
          π (((Quotient.out c : Fˣ) : F) * w) = 0} * (2 ^ g - 1) := by
      have h9 : Nat.card {c : Fˣ ⧸ (Units.map ((algebraMap Kf F : Kf →+* F) : Kf →* F)).range //
          Quotient.out c ∈ {a : Fˣ | π ((a : F) * w) = 0}} * (2 ^ g - 1) =
            Nat.card {a : Fˣ | π ((a : F) * w) = 0} := h2
      have h10 : Nat.card {a : Fˣ | π ((a : F) * w) = 0} = 2 ^ (m - s) - 1 := by omega
      rw [h10] at h9
      exact h9.symm
    exact (Nat.div_eq_of_eq_mul_left hd h8).symm
  -- the family
  refine ⟨fun i u => (Equiv.ofBijective eY heY).symm
    (π (((Quotient.out ((Finite.equivFinOfCardEq hicard).symm i) : Fˣ) : F) * eX u)), ?_, ?_, ?_⟩
  · intro i y
    obtain ⟨x, hx⟩ := hπ (eY y)
    obtain ⟨u, hu⟩ := heX.2
      ((((Quotient.out ((Finite.equivFinOfCardEq hicard).symm i) : Fˣ)⁻¹ : Fˣ) : F) * x)
    refine ⟨u, ?_⟩
    show (Equiv.ofBijective eY heY).symm
      (π (((Quotient.out ((Finite.equivFinOfCardEq hicard).symm i) : Fˣ) : F) * eX u)) = y
    rw [hu, Units.mul_inv_cancel_left, hx, Equiv.symm_apply_eq, Equiv.ofBijective_apply]
  · intro i u v
    apply (Equiv.ofBijective eY heY).injective
    rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, haY, ← Equiv.ofBijective_apply eY heY,
      ← Equiv.ofBijective_apply eY heY, Equiv.apply_symm_apply, Equiv.apply_symm_apply, haX,
      mul_add, map_add]
  · intro u v huv
    have hw : eX u - eX v ≠ 0 := sub_ne_zero.mpr (heX.1.ne huv)
    rw [← hcount (eX u - eX v) hw, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ((Finite.equivFinOfCardEq hicard).symm.subtypeEquiv (fun i => ?_))
    rw [Equiv.apply_eq_iff_eq, mul_sub, map_sub, sub_eq_zero]

/-- The construction half. -/
theorem partA (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    ∃ family : Fin ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) → (Fin m → Bool) → (Fin s → Bool),
      (∀ i, Function.Surjective (family i)) ∧
      (∀ i u v, family i (fun j => xor (u j) (v j)) =
        fun out => xor (family i u out) (family i v out)) ∧
      ∀ u v : Fin m → Bool, u ≠ v →
        (Finset.univ.filter (fun i => family i u = family i v)).card =
          (2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1) := by
  have hg : 0 < Nat.gcd m s := Nat.gcd_pos_of_pos_left s hm
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 (Nat.gcd m s)) (L := GaloisField 2 m)
    (by
      rw [GaloisField.finrank 2 hg.ne', GaloisField.finrank 2 hm.ne']
      exact Nat.gcd_dvd_left m s)
  let _ : Algebra (GaloisField 2 (Nat.gcd m s)) (GaloisField 2 m) := φ.toRingHom.toAlgebra
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm.ne'
  have hK : Nat.card (GaloisField 2 (Nat.gcd m s)) = 2 ^ Nat.gcd m s :=
    GaloisField.card 2 _ hg.ne'
  have hdim : Nat.gcd m s *
      Module.finrank (GaloisField 2 (Nat.gcd m s)) (GaloisField 2 m) = m := by
    have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 (Nat.gcd m s))
      (V := GaloisField 2 m)
    rw [hF, hK, ← pow_mul] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hle : s / Nat.gcd m s ≤
      Module.finrank (GaloisField 2 (Nat.gcd m s)) (GaloisField 2 m) := by
    apply Nat.div_le_of_le_mul
    rw [hdim]
    exact hs
  have hπ : Function.Surjective
      ((LinearMap.funLeft (GaloisField 2 (Nat.gcd m s)) (GaloisField 2 (Nat.gcd m s))
        (Fin.castLE hle)).comp
        (Module.finBasis (GaloisField 2 (Nat.gcd m s))
          (GaloisField 2 m)).equivFun.toLinearMap) := by
    intro y
    obtain ⟨z, hz⟩ := LinearMap.funLeft_surjective_of_injective
      (GaloisField 2 (Nat.gcd m s)) (GaloisField 2 (Nat.gcd m s)) _
      (Fin.castLE_injective hle) y
    refine ⟨(Module.finBasis (GaloisField 2 (Nat.gcd m s))
      (GaloisField 2 m)).equivFun.symm z, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hz]
  have hV : Nat.card (Fin (s / Nat.gcd m s) → GaloisField 2 (Nat.gcd m s)) = 2 ^ s := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hK, ← pow_mul,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right m s)]
  obtain ⟨eX, heX, haX⟩ := exists_enc (GaloisField 2 m) m hF
  obtain ⟨eY, heY, haY⟩ :=
    exists_enc (Fin (s / Nat.gcd m s) → GaloisField 2 (Nat.gcd m s)) s hV
  exact construct m s (Nat.gcd m s) hg hs hF hK hV _ hπ eX heX haX eY heY haY

end PEqualNP.Outside.L_lib_415

theorem PEqualNP.Outside.L_lib_415 : ∀ (m s : ℕ), 0 < m → s ≤ m →
  let N := 2 ^ m
  let K := 2 ^ (m - s)
  let divisor := 2 ^ Nat.gcd m s - 1
  let period := (N - 1) / divisor
  let hits := (K - 1) / divisor
  let X := Fin m → Bool
  let Y := Fin s → Bool
  let collisions := fun (r : ℕ) (f : Fin r → X → Y) (u v : X) =>
    (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card
  (∃ family : Fin period → X → Y,
    (∀ i, Function.Surjective (family i)) ∧
    (∀ i u v, family i (fun j => xor (u j) (v j)) =
      fun out => xor (family i u out) (family i v out)) ∧
    ∀ u v : X, u ≠ v → collisions period family u v = hits) ∧
  ∀ (r errors : ℕ) (f : Fin r → X → Y), 0 < r →
    (∀ u v : X, u ≠ v → collisions r f u v ≤ errors) →
    r * (K - 1) ≤ errors * (N - 1) ∧
    (errors * (N - 1) = r * (K - 1) →
      period ∣ r ∧ ∀ u v : X, u ≠ v → collisions r f u v = errors) := by
  intro m s hm hs N K divisor period hits X Y collisions
  exact ⟨PEqualNP.Outside.L_lib_415.partA m s hm hs,
    fun r errors f _ hcoll => PEqualNP.Outside.L_lib_415.partB m s hm hs r errors f hcoll⟩
