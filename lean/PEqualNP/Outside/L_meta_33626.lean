import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33626_aux

abbrev F2 := ZMod 2

lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma f2_add_self (a : F2) : a + a = 0 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma f2_add_eq_zero {a b : F2} : a + b = 0 ↔ a = b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> decide

def ix {k : Nat} (hk : 0 < k) (n : Nat) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rot {k : Nat} (hk : 0 < k) (n : Nat) (word : Fin k → F2) (i : Fin k) : F2 :=
  word (ix hk (i.val + k - n % k))

def rotLin {k : Nat} (hk : 0 < k) (n : Nat) : (Fin k → F2) →ₗ[F2] (Fin k → F2) where
  toFun := rot hk n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma rotLin_surjective {k : Nat} (hk : 0 < k) (n : Nat) :
    Function.Surjective (rotLin hk n) := by
  intro w
  refine ⟨fun j => w (ix hk (j.val + n % k)), ?_⟩
  funext i
  change w (ix hk ((ix hk (i.val + k - n % k)).val + n % k)) = w i
  congr 1
  ext
  simp only [ix]
  have h1 : n % k < k := Nat.mod_lt _ hk
  have h2 : i.val < k := i.isLt
  have h3 : ((i.val + k - n % k) % k + n % k) % k = (i.val + k - n % k + n % k) % k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h3]
  have h4 : i.val + k - n % k + n % k = i.val + k := by omega
  rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt h2]

def mix {k : Nat} (hk : 0 < k) : (Fin k → F2) →ₗ[F2] (Fin k → F2) where
  toFun z u := z u + z (ix hk (u.val + 2)) + z (ix hk (u.val + k - 2 % k))
  map_add' x y := by funext u; dsimp only [Pi.add_apply]; ring
  map_smul' r x := by funext u; dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma ix_step2_back {k : Nat} (hk : 0 < k) (u : Fin k) :
    ix hk ((ix hk (u.val + 2)).val + k - 2 % k) = u := by
  ext
  simp only [ix]
  have hu : u.val < k := u.isLt
  have h2 : 2 % k < k := Nat.mod_lt _ hk
  have h1 : ((u.val + 2) % k + k - 2 % k) % k = u.val := by
    by_cases hk1 : k = 1
    · subst hk1; omega
    · by_cases hk2 : k = 2
      · subst hk2; omega
      · have h2eq : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
        rw [h2eq]
        by_cases hlt : u.val + 2 < k
        · rw [Nat.mod_eq_of_lt hlt]
          have : u.val + 2 + k - 2 = u.val + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hu]
        · have hmod : (u.val + 2) % k = u.val + 2 - k := by
            have := Nat.mod_eq_sub_mod (by omega : k ≤ u.val + 2)
            rw [this, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have : u.val + 2 - k + k - 2 = u.val := by omega
          rw [this, Nat.mod_eq_of_lt hu]
  exact h1

lemma ix_back_step2 {k : Nat} (hk : 0 < k) (u : Fin k) :
    ix hk ((ix hk (u.val + k - 2 % k)).val + 2) = u := by
  ext
  simp only [ix]
  have hu : u.val < k := u.isLt
  by_cases hk1 : k = 1
  · subst hk1; omega
  · by_cases hk2 : k = 2
    · subst hk2; omega
    · have h2eq : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
      rw [h2eq]
      have h1 : ((u.val + k - 2) % k + 2) % k = (u.val + k - 2 + 2) % k := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1]
      have h2 : u.val + k - 2 + 2 = u.val + k := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hu]

lemma mix_self_adjoint {k : Nat} (hk : 0 < k) (c z : Fin k → F2) :
    (∑ u : Fin k, c u * mix hk z u) = ∑ u : Fin k, mix hk c u * z u := by
  simp only [mix, LinearMap.coe_mk, AddHom.coe_mk, mul_add, add_mul, Finset.sum_add_distrib]
  let e1 : Fin k ≃ Fin k := {
    toFun := fun u => ix hk (u.val + 2)
    invFun := fun u => ix hk (u.val + k - 2 % k)
    left_inv := ix_step2_back hk
    right_inv := ix_back_step2 hk
  }
  have h1 : (∑ u : Fin k, c u * z (ix hk (u.val + 2))) =
      ∑ u : Fin k, c (ix hk (u.val + k - 2 % k)) * z u := by
    rw [← Fintype.sum_equiv e1 _ (fun u => c (ix hk (u.val + k - 2 % k)) * z u)]
    intro u
    change c u * z (e1 u) = c (e1.symm (e1 u)) * z (e1 u)
    rw [e1.symm_apply_apply]
  have h2 : (∑ u : Fin k, c u * z (ix hk (u.val + k - 2 % k))) =
      ∑ u : Fin k, c (ix hk (u.val + 2)) * z u := by
    rw [← Fintype.sum_equiv e1.symm _ (fun u => c (ix hk (u.val + 2)) * z u)]
    intro u
    change c u * z (e1.symm u) = c (e1 (e1.symm u)) * z (e1.symm u)
    rw [e1.apply_symm_apply]
  rw [h1, h2]
  ring

lemma ker_mix_step2 {k : Nat} (hk : 0 < k) {c : Fin k → F2} (hc : mix hk c = 0) (n : Nat) :
    c (ix hk (n + 4)) = c (ix hk n) + c (ix hk (n + 2)) := by
  have h := congrFun hc (ix hk (n + 2))
  simp only [mix, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
  have h1 : ix hk ((ix hk (n + 2)).val + 2) = ix hk (n + 4) := by
    ext; simp only [ix]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : ix hk ((ix hk (n + 2)).val + k - 2 % k) = ix hk n := by
    have h0 := ix_step2_back hk (ix hk n)
    have h0' : ix hk ((ix hk n).val + 2) = ix hk (n + 2) := by
      ext; simp only [ix]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [← h0', h0]
  rw [h1, h2] at h

  apply f2_add_eq_zero.mp
  have : c (ix hk (n + 4)) + (c (ix hk n) + c (ix hk (n + 2))) =
      c (ix hk (n + 2)) + c (ix hk (n + 4)) + c (ix hk n) := by ring
  rw [this, h]

lemma ker_mix_period6 {k : Nat} (hk : 0 < k) {c : Fin k → F2} (hc : mix hk c = 0) (n : Nat) :
    c (ix hk (n + 6)) = c (ix hk n) := by
  have h1 := ker_mix_step2 hk hc (n + 2)
  have h2 := ker_mix_step2 hk hc n
  rw [h1, h2]
  have : c (ix hk (n + 2)) + (c (ix hk n) + c (ix hk (n + 2))) =
      c (ix hk n) + (c (ix hk (n + 2)) + c (ix hk (n + 2))) := by ring
  rw [this, f2_add_self, add_zero]

lemma ker_mix_mod6 {k : Nat} (hk : 0 < k) {c : Fin k → F2} (hc : mix hk c = 0) (n m : Nat) :
    c (ix hk (n + 6 * m)) = c (ix hk n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : n + 6 * (m + 1) = (n + 6 * m) + 6 := by omega
    rw [this, ker_mix_period6 hk hc, ih]

lemma ker_mix_eq_zero_of_not_dvd3 {k : Nat} (hk : 0 < k) (hnd : ¬ 3 ∣ k)
    {c : Fin k → F2} (hc : mix hk c = 0) : c = 0 := by
  funext u
  have hper : ∀ m : Nat, c (ix hk (u.val + 6 * m)) = c u := by
    intro m
    have := ker_mix_mod6 hk hc u.val m
    have hu : ix hk u.val = u := by ext; simp [ix, Nat.mod_eq_of_lt u.isLt]
    rwa [hu] at this
  have hmodk : ∀ a b : Nat, a % k = b % k → ix hk a = ix hk b := by
    intro a b hab; ext; simp [ix, hab]
  have h2k : c (ix hk (u.val + 2 * k)) = c u := by
    rw [hmodk (u.val + 2 * k) u.val (by rw [Nat.add_mul_mod_self_right]),
        show ix hk u.val = u from by ext; simp [ix, Nat.mod_eq_of_lt u.isLt]]
  have h4k : c (ix hk (u.val + 4 * k)) = c u := by
    rw [hmodk (u.val + 4 * k) u.val (by rw [Nat.add_mul_mod_self_right]),
        show ix hk u.val = u from by ext; simp [ix, Nat.mod_eq_of_lt u.isLt]]

  have hkm : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have h24 : c (ix hk (u.val + 2)) = c u ∧ c (ix hk (u.val + 4)) = c u := by
    rcases hkm with h1 | h2
    · have hq1 : 2 * k = 2 + 6 * (k / 3) := by omega
      have hq2 : 4 * k = 4 + 6 * (2 * (k / 3)) := by omega
      constructor
      · have := ker_mix_mod6 hk hc (u.val + 2) (k / 3)
        rw [show u.val + 2 + 6 * (k / 3) = u.val + 2 * k by omega, h2k] at this
        exact this.symm
      · have := ker_mix_mod6 hk hc (u.val + 4) (2 * (k / 3))
        rw [show u.val + 4 + 6 * (2 * (k / 3)) = u.val + 4 * k by omega, h4k] at this
        exact this.symm
    · have hq1 : 2 * k = 4 + 6 * (k / 3) := by omega
      have hq2 : 4 * k = 2 + 6 * (2 * (k / 3) + 1) := by omega
      constructor
      · have := ker_mix_mod6 hk hc (u.val + 2) (2 * (k / 3) + 1)
        rw [show u.val + 2 + 6 * (2 * (k / 3) + 1) = u.val + 4 * k by omega, h4k] at this
        exact this.symm
      · have := ker_mix_mod6 hk hc (u.val + 4) (k / 3)
        rw [show u.val + 4 + 6 * (k / 3) = u.val + 2 * k by omega, h2k] at this
        exact this.symm
  have hstep := ker_mix_step2 hk hc u.val
  have hu : ix hk u.val = u := by ext; simp [ix, Nat.mod_eq_of_lt u.isLt]
  rw [hu, h24.1, h24.2] at hstep
  rw [f2_add_self] at hstep
  exact hstep

lemma ker_mix_period3_odd {k : Nat} (hk : 0 < k) (hd3 : 3 ∣ k) (hodd : k % 2 = 1)
    {c : Fin k → F2} (hc : mix hk c = 0) (u : Fin k) :
    c u = c (ix hk (u.val % 3)) := by

  have h3 : ∀ n : Nat, c (ix hk (n + 3)) = c (ix hk n) := by
    intro n
    have hq : k = 3 + 6 * (k / 6) := by omega
    have h1 := ker_mix_mod6 hk hc (n + 3) (k / 6)
    have h2 : ix hk (n + 3 + 6 * (k / 6)) = ix hk n := by
      ext; simp only [ix]
      rw [show n + 3 + 6 * (k / 6) = n + k by omega, Nat.add_mod_right]
    rw [h2] at h1
    exact h1.symm
  have h3m : ∀ n m : Nat, c (ix hk (n + 3 * m)) = c (ix hk n) := by
    intro n m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show n + 3 * (m + 1) = (n + 3 * m) + 3 by omega, h3, ih]
  have h := h3m (u.val % 3) (u.val / 3)
  have hdiv : u.val % 3 + 3 * (u.val / 3) = u.val := by omega
  rw [hdiv, show ix hk u.val = u from by ext; simp [ix, Nat.mod_eq_of_lt u.isLt]] at h
  exact h

lemma ker_mix_sum3_odd {k : Nat} (hk : 0 < k) (hd3 : 3 ∣ k) (hodd : k % 2 = 1)
    {c : Fin k → F2} (hc : mix hk c = 0) :
    c (ix hk 0) + c (ix hk 1) + c (ix hk 2) = 0 := by
  have hstep := ker_mix_step2 hk hc 0
  have h4 : c (ix hk 4) = c (ix hk 1) := by
    have := ker_mix_period3_odd hk hd3 hodd hc (ix hk 4)
    have hk3 : 3 ≤ k := by omega
    have h4mod : (ix hk 4).val % 3 = 1 := by
      simp only [ix]
      have : (4 % k) % 3 = 4 % 3 := Nat.mod_mod_of_dvd 4 hd3
      omega
    rwa [h4mod] at this
  rw [h4] at hstep
  have : c (ix hk 0) + c (ix hk 1) + c (ix hk 2) =
      c (ix hk 1) + (c (ix hk 0) + c (ix hk 2)) := by ring
  rw [this, hstep, f2_add_self]

lemma ker_mix_mod6_val {k : Nat} (hk : 0 < k) {c : Fin k → F2} (hc : mix hk c = 0) (u : Fin k) :
    c u = c (ix hk (u.val % 6)) := by
  have h := ker_mix_mod6 hk hc (u.val % 6) (u.val / 6)
  have hdiv : u.val % 6 + 6 * (u.val / 6) = u.val := by omega
  rw [hdiv, show ix hk u.val = u from by ext; simp [ix, Nat.mod_eq_of_lt u.isLt]] at h
  exact h

lemma ker_mix_lane_sum {k : Nat} (hk : 0 < k) {c : Fin k → F2} (hc : mix hk c = 0) (v : Nat) :
    c (ix hk v) + c (ix hk (v + 2)) + c (ix hk (v + 4)) = 0 := by
  have hstep := ker_mix_step2 hk hc v
  rw [hstep]
  ring_nf
  have h1 : ∀ a : F2, a * 2 = 0 := fun a => by rcases f2_cases a with rfl | rfl <;> decide
  simp [h1]

lemma sum_prod_f2 {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    (∑ z : α → F2, ∏ a ∈ S, z a) = if S = Finset.univ then 1 else 0 := by
  by_cases hS : S = Finset.univ
  · subst hS
    rw [if_pos rfl]
    have huniq : ∀ z : α → F2, (∏ a : α, z a) = if z = fun _ => 1 then 1 else 0 := by
      intro z
      by_cases hz : z = fun _ => 1
      · subst hz; simp
      · rw [if_neg hz]
        have hex : ∃ a : α, z a ≠ 1 := by
          by_contra hall; push Not at hall; exact hz (funext hall)
        rcases hex with ⟨a, ha⟩
        have ha0 : z a = 0 := (f2_cases (z a)).resolve_right ha
        exact Finset.prod_eq_zero (Finset.mem_univ a) ha0
    simp_rw [huniq]
    simp
  · rw [if_neg hS]
    have hex : ∃ b : α, b ∉ S := by
      by_contra hall; push Not at hall
      apply hS; ext a; simp [hall a]
    rcases hex with ⟨b, hb⟩
    let eb : α → F2 := Pi.single b (1 : F2)
    let e : (α → F2) ≃ (α → F2) := Equiv.addRight eb
    have hinv : ∀ z : α → F2, (∏ a ∈ S, e z a) = ∏ a ∈ S, z a := by
      intro z
      apply Finset.prod_congr rfl
      intro a ha
      have hab : a ≠ b := fun h => hb (h ▸ ha)
      change z a + eb a = z a
      simp [eb, Pi.single_eq_of_ne hab]
    have hsplit : (∑ z : α → F2, ∏ a ∈ S, z a) =
        (∑ z ∈ (Finset.univ : Finset (α → F2)).filter (fun z => z b = 0), ∏ a ∈ S, z a) +
        (∑ z ∈ (Finset.univ : Finset (α → F2)).filter (fun z => z b ≠ 0), ∏ a ∈ S, z a) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : α → F2 => z b = 0) _).symm
    have hbij : (∑ z ∈ (Finset.univ : Finset (α → F2)).filter (fun z => z b ≠ 0), ∏ a ∈ S, z a) =
        (∑ z ∈ (Finset.univ : Finset (α → F2)).filter (fun z => z b = 0), ∏ a ∈ S, z a) := by
      symm
      apply Finset.sum_bij (fun z _ => e z)
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        change z b + eb b ≠ 0
        simp [eb, hz]
      · intro z1 _ z2 _ h; exact e.injective h
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have hz1 : z b = 1 := (f2_cases (z b)).resolve_left hz
        refine ⟨e z, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change z b + eb b = 0
          simp [eb, hz1, f2_add_self]
        · funext a
          change z a + eb a + eb a = z a
          rw [add_assoc, f2_add_self, add_zero]
      · intro z _; exact (hinv z).symm
    rw [hsplit, hbij, f2_add_self]

lemma sum_quad_factors_eq_one {J : Type*} [Fintype J] [DecidableEq J]
    (L : J → (J × Bool → F2) →ₗ[F2] F2) (c : J → F2) :
    (∑ z : J × Bool → F2, ∏ i : J, (z (i, false) * z (i, true) + L i z + c i)) = 1 := by

  let w : J → J × Bool → F2 := fun i p => L i (Pi.single p 1)
  have hL : ∀ i z, L i z = ∑ p : J × Bool, w i p * z p := by
    intro i z
    have hz : z = ∑ p : J × Bool, z p • Pi.single p (1 : F2) := by
      funext q; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hz]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, smul_eq_mul, mul_comm]

  let T := Option (Option (J × Bool))
  let coeff : J → T → F2 := fun i t =>
    match t with
    | none => 1
    | some none => c i
    | some (some p) => w i p
  let vars : J → T → Finset (J × Bool) := fun i t =>
    match t with
    | none => {(i, false), (i, true)}
    | some none => ∅
    | some (some p) => {p}
  have hfac : ∀ i z, z (i, false) * z (i, true) + L i z + c i =
      ∑ t : T, coeff i t * ∏ a ∈ vars i t, z a := by
    intro i z
    rw [hL i z]
    simp only [T, Fintype.sum_option, coeff, vars, one_mul, Finset.prod_empty, mul_one,
      Finset.prod_singleton]
    have hne : (i, false) ≠ (i, true) := by simp
    rw [Finset.prod_pair hne]
    ring
  simp_rw [hfac, Fintype.prod_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ f : J → T,
      (∑ z : J × Bool → F2, ∏ i : J, coeff i (f i) * ∏ a ∈ vars i (f i), z a) =
      (∏ i : J, coeff i (f i)) *
        if Finset.univ.biUnion (fun i => vars i (f i)) = Finset.univ then 1 else 0 := by
    intro f
    simp_rw [Finset.prod_mul_distrib, ← Finset.mul_sum]
    congr 1
    have hprod_eq : ∀ z : J × Bool → F2,
        (∏ i : J, ∏ a ∈ vars i (f i), z a) = ∏ a ∈ Finset.univ.biUnion (fun i => vars i (f i)), z a := by
      intro z

      have hsq : ∀ (a : F2), a * a = a := fun a => by rcases f2_cases a with rfl | rfl <;> decide
      have hsub : ∀ (A B : Finset (J × Bool)),
          (∏ a ∈ A, z a) * (∏ a ∈ B, z a) = ∏ a ∈ A ∪ B, z a := by
        intro A B
        have h1 := Finset.prod_union_inter (s₁ := A) (s₂ := B) (f := z)

        rw [← h1]
        have hsub' : A ∩ B ⊆ A ∪ B := Finset.Subset.trans Finset.inter_subset_left Finset.subset_union_left
        rw [← Finset.prod_sdiff hsub']
        have hmul : (∏ x ∈ (A ∪ B) \ (A ∩ B), z x) * (∏ x ∈ A ∩ B, z x) * (∏ x ∈ A ∩ B, z x) =
            (∏ x ∈ (A ∪ B) \ (A ∩ B), z x) * (∏ x ∈ A ∩ B, (z x * z x)) := by
          rw [mul_assoc, Finset.prod_mul_distrib]
        rw [hmul]
        simp_rw [hsq]

      have hgen : ∀ (S : Finset J),
          (∏ i ∈ S, ∏ a ∈ vars i (f i), z a) = ∏ a ∈ S.biUnion (fun i => vars i (f i)), z a := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | insert i S hi ih =>
          rw [Finset.prod_insert hi, Finset.biUnion_insert, ih, hsub]
      exact hgen Finset.univ
    simp_rw [hprod_eq]
    exact sum_prod_f2 _
  simp_rw [hterm]

  have honly : ∀ f : J → T,
      Finset.univ.biUnion (fun i => vars i (f i)) = Finset.univ ↔ f = fun _ => none := by
    intro f
    constructor
    · intro hfull
      have hcard : (Finset.univ : Finset (J × Bool)).card ≤ ∑ i : J, (vars i (f i)).card := by
        rw [← hfull]; exact Finset.card_biUnion_le
      have htot : (Finset.univ : Finset (J × Bool)).card = 2 * Fintype.card J := by
        simp [mul_comm]
      have hle2 : ∀ i : J, (vars i (f i)).card ≤ 2 := by
        intro i
        cases hf : f i with
        | none => simp [vars]
        | some o => cases o with
          | none => simp [vars]
          | some p => simp [vars]
      funext i
      by_contra hne
      have hlt2 : (vars i (f i)).card < 2 := by
        cases hf : f i with
        | none => exact absurd hf hne
        | some o => cases o with
          | none => simp [vars]
          | some p => simp [vars]
      have hstrict : (∑ j : J, (vars j (f j)).card) < ∑ _j : J, 2 :=
        Finset.sum_lt_sum (fun j _ => hle2 j) ⟨i, Finset.mem_univ i, hlt2⟩
      simp [Finset.sum_const, mul_comm] at hstrict
      omega
    · intro hf
      subst hf
      ext ⟨i, b⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
      refine ⟨i, ?_⟩
      cases b <;> simp [vars]
  simp_rw [honly]
  have h1 : ∀ f : J → T, (∏ i : J, coeff i (f i)) * (if f = fun _ => none then (1 : F2) else 0) =
      if f = fun _ => none then 1 else 0 := by
    intro f
    by_cases hf : f = fun _ => none
    · subst hf; simp [coeff]
    · simp [hf]
  simp_rw [h1]
  simp

lemma exists_all_fail_of_surj {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (J : Finset (Fin k))
    (x0 : Fin k → F2) (T : Submodule F2 (Fin k → F2))
    (aff : (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : Fin k → F2)
    (hsurj : Function.Surjective (fun (v : T) (p : J × Bool) =>
      mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1)))) :
    ∃ v : T, ∀ i ∈ J,
      (aff (x0 + v.1) + c) i ≠
        let old := rot hk s (x0 + v.1) + name
        let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
        y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t (x0 + v.1) i + constant i := by
  classical

  let proj : T →ₗ[F2] (J × Bool → F2) := {
    toFun := fun v p => mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1))
    map_add' := fun u v => by funext p; simp [map_add]
    map_smul' := fun r u => by funext p; simp [map_smul]
  }
  have hsurj' : Function.Surjective proj := hsurj
  choose pre hpre using fun p : J × Bool => hsurj' (Pi.single p (1 : F2))
  let sec : (J × Bool → F2) →ₗ[F2] T := {
    toFun := fun z => ∑ p : J × Bool, z p • pre p
    map_add' := fun z1 z2 => by simp [add_smul, Finset.sum_add_distrib]
    map_smul' := fun r z => by simp [mul_smul, Finset.smul_sum]
  }
  have hproj_sec : ∀ z : J × Bool → F2, proj (sec z) = z := by
    intro z
    simp only [sec, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, hpre]
    funext q; simp [Finset.sum_apply, Pi.single_apply]

  let y0 : Fin k → F2 := fun u => mix hk (rot hk s x0 + name) u
  let y_at : (J × Bool → F2) → Fin k → F2 := fun z u => y0 u + mix hk (rotLin hk s (sec z).1) u
  have hy_eq : ∀ z : J × Bool → F2,
      (fun u : Fin k =>
        let old := rot hk s (x0 + (sec z).1) + name
        old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))) = y_at z := by
    intro z
    funext u
    have hrot : rot hk s (x0 + (sec z).1) + name = (rot hk s x0 + name) + rotLin hk s (sec z).1 := by
      funext w
      change (x0 + (sec z).1) (ix hk (w.val + k - s % k)) + name w =
        (x0 (ix hk (w.val + k - s % k)) + name w) + (sec z).1 (ix hk (w.val + k - s % k))
      simp only [Pi.add_apply]; ring
    change mix hk (rot hk s (x0 + (sec z).1) + name) u = y0 u + mix hk (rotLin hk s (sec z).1) u
    rw [hrot, map_add]; rfl
  have hy1 : ∀ (z : J × Bool → F2) (i : J), y_at z (ix hk (i.1.val + 1)) = y0 (ix hk (i.1.val + 1)) + z (i, false) := by
    intro z i
    have h := congrFun (hproj_sec z) (i, false)
    simpa [proj, y_at] using congrArg (y0 (ix hk (i.1.val + 1)) + ·) h
  have hy2 : ∀ (z : J × Bool → F2) (i : J), y_at z (ix hk (i.1.val + 2)) = y0 (ix hk (i.1.val + 2)) + z (i, true) := by
    intro z i
    have h := congrFun (hproj_sec z) (i, true)
    simpa [proj, y_at] using congrArg (y0 (ix hk (i.1.val + 2)) + ·) h
  let L : J → (J × Bool → F2) →ₗ[F2] F2 := fun i => {
    toFun := fun z =>
      y0 (ix hk (i.1.val + 1)) * z (i, true) + y0 (ix hk (i.1.val + 2)) * z (i, false) +
      mix hk (rotLin hk s (sec z).1) i.1 +
      z (i, true) +
      rotLin hk t (sec z).1 i.1 +
      aff (sec z).1 i.1
    map_add' := fun z1 z2 => by simp [map_add, Submodule.coe_add, mul_add]; ring
    map_smul' := fun r z => by simp [map_smul, Submodule.coe_smul, smul_eq_mul]; ring
  }
  let c0 : J → F2 := fun i =>
    y0 (ix hk (i.1.val + 1)) * y0 (ix hk (i.1.val + 2)) +
    y0 i.1 + y0 (ix hk (i.1.val + 2)) + rot hk t x0 i.1 + constant i.1 + aff x0 i.1 + c i.1
  have hdiff : ∀ (z : J × Bool → F2) (i : J),
      (aff (x0 + (sec z).1) + c) i.1 +
        (let old := rot hk s (x0 + (sec z).1) + name
         let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
         y i.1 + (1 + y (ix hk (i.1.val + 1))) * y (ix hk (i.1.val + 2)) + rot hk t (x0 + (sec z).1) i.1 + constant i.1) =
      z (i, false) * z (i, true) + L i z + c0 i := by
    intro z i
    have hyu : ∀ u, (rot hk s (x0 + (sec z).1) + name) u +
        (rot hk s (x0 + (sec z).1) + name) (ix hk (u.val + 2)) +
        (rot hk s (x0 + (sec z).1) + name) (ix hk (u.val + k - 2 % k)) = y_at z u :=
      fun u => congrFun (hy_eq z) u
    change (aff (x0 + (sec z).1) + c) i.1 +
      (((rot hk s (x0 + (sec z).1) + name) i.1 + (rot hk s (x0 + (sec z).1) + name) (ix hk (i.1.val + 2)) +
        (rot hk s (x0 + (sec z).1) + name) (ix hk (i.1.val + k - 2 % k))) +
       (1 + ((rot hk s (x0 + (sec z).1) + name) (ix hk (i.1.val + 1)) +
         (rot hk s (x0 + (sec z).1) + name) (ix hk ((ix hk (i.1.val + 1)).val + 2)) +
         (rot hk s (x0 + (sec z).1) + name) (ix hk ((ix hk (i.1.val + 1)).val + k - 2 % k)))) *
        ((rot hk s (x0 + (sec z).1) + name) (ix hk (i.1.val + 2)) +
         (rot hk s (x0 + (sec z).1) + name) (ix hk ((ix hk (i.1.val + 2)).val + 2)) +
         (rot hk s (x0 + (sec z).1) + name) (ix hk ((ix hk (i.1.val + 2)).val + k - 2 % k))) +
       rot hk t (x0 + (sec z).1) i.1 + constant i.1) = _
    rw [hyu i.1, hyu (ix hk (i.1.val + 1)), hyu (ix hk (i.1.val + 2)), hy1 z i, hy2 z i]
    have haff : (aff (x0 + (sec z).1) + c) i.1 = aff x0 i.1 + aff (sec z).1 i.1 + c i.1 := by
      simp only [map_add, Pi.add_apply]
    have hrott : rot hk t (x0 + (sec z).1) i.1 = rot hk t x0 i.1 + rotLin hk t (sec z).1 i.1 := by
      change (x0 + (sec z).1) (ix hk (i.1.val + k - t % k)) =
        x0 (ix hk (i.1.val + k - t % k)) + (sec z).1 (ix hk (i.1.val + k - t % k))
      rfl
    rw [haff, hrott]
    simp only [L, c0, y_at, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hsum1 := sum_quad_factors_eq_one L c0
  have hex : ∃ z : J × Bool → F2, (∏ i : J, (z (i, false) * z (i, true) + L i z + c0 i)) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : (∑ z : J × Bool → F2, ∏ i : J, (z (i, false) * z (i, true) + L i z + c0 i)) = 0 :=
      Finset.sum_eq_zero (fun z _ => hall z)
    rw [hsum1] at h0
    exact one_ne_zero h0
  rcases hex with ⟨z, hz⟩
  refine ⟨sec z, fun i hi => ?_⟩
  have hfac_ne : z (⟨i, hi⟩, false) * z (⟨i, hi⟩, true) + L ⟨i, hi⟩ z + c0 ⟨i, hi⟩ ≠ 0 := by
    intro h0
    exact hz (Finset.prod_eq_zero (Finset.mem_univ ⟨i, hi⟩) h0)
  intro heq
  apply hfac_ne
  rw [← hdiff z ⟨i, hi⟩, heq, f2_add_self]

lemma surj_restrict_ker {k : Nat} (hk : 0 < k) (s : Nat)
    (T : Submodule F2 (Fin k → F2)) (f : (Fin k → F2) →ₗ[F2] F2)
    (J : Finset (Fin k))
    (hsurj : Function.Surjective (fun (v : T) (p : J × Bool) =>
      mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1)))) :
    ∃ J' ⊆ J, J.card - 1 ≤ J'.card ∧
      Function.Surjective (fun (v : (T ⊓ LinearMap.ker f : Submodule F2 (Fin k → F2))) (p : J' × Bool) =>
        mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1))) := by
  classical
  let proj : T →ₗ[F2] (J × Bool → F2) := {
    toFun := fun v p => mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1))
    map_add' := fun _ _ => by funext p; simp [map_add]
    map_smul' := fun _ _ => by funext p; simp [map_smul]
  }
  by_cases hker : ∃ v : T, proj v = 0 ∧ f v.1 ≠ 0
  ·
    rcases hker with ⟨v0, hv0p, hv0f⟩
    have hv0f1 : f v0.1 = 1 := (f2_cases (f v0.1)).resolve_left hv0f
    refine ⟨J, Finset.Subset.refl J, by omega, ?_⟩
    intro z
    obtain ⟨v, hv⟩ := hsurj z
    by_cases hfv : f v.1 = 0
    · exact ⟨⟨v.1, v.2, hfv⟩, hv⟩
    · have hfv1 : f v.1 = 1 := (f2_cases (f v.1)).resolve_left hfv
      refine ⟨⟨v.1 + v0.1, T.add_mem v.2 v0.2, ?_⟩, ?_⟩
      · simp [LinearMap.mem_ker, map_add, hfv1, hv0f1, f2_add_self]
      · funext p
        have h1 := congrFun hv p
        have h2 := congrFun hv0p p
        simp only [proj, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h2
        simp only [map_add, Pi.add_apply, h1, h2, add_zero]
  ·
    push Not at hker
    by_cases hfall : ∀ v : T, f v.1 = 0
    · refine ⟨J, Finset.Subset.refl J, by omega, ?_⟩
      intro z
      obtain ⟨v, hv⟩ := hsurj z
      exact ⟨⟨v.1, v.2, hfall v⟩, hv⟩
    · push Not at hfall

      choose pre hpre using fun p : J × Bool => hsurj (Pi.single p (1 : F2))
      have hexp0 : ∃ p0 : J × Bool, f (pre p0).1 ≠ 0 := by
        by_contra hall
        push Not at hall
        rcases hfall with ⟨v, hfv⟩
        let v' : T := ∑ p : J × Bool, proj v p • pre p
        have hp_eq : proj (v - v') = 0 := by
          rw [map_sub]
          have hv' : proj v' = proj v := by
            simp only [v', map_sum, map_smul]
            funext q
            have hq : ∀ p : J × Bool, proj (pre p) q = (Pi.single p (1 : F2) : J × Bool → F2) q := fun p =>
              congrFun (hpre p) q
            simp [Finset.sum_apply, hq, Pi.single_apply]
          rw [hv', sub_self]
        have hf0 := hker (v - v') hp_eq
        have hfv' : f v'.1 = 0 := by
          have hv'val : v'.1 = ∑ p : J × Bool, proj v p • (pre p).1 := by
            change Submodule.subtype T (∑ p : J × Bool, proj v p • pre p) = _
            rw [map_sum]
            rfl
          rw [hv'val, map_sum]
          exact Finset.sum_eq_zero (fun p _ => by rw [map_smul, hall p, smul_zero])
        have hsub : f (v - v').1 = f v.1 - f v'.1 := by
          change f (v.1 - v'.1) = _; rw [map_sub]
        rw [hsub, hfv', sub_zero] at hf0
        exact hfv hf0
      rcases hexp0 with ⟨⟨⟨i0, hi0⟩, b0⟩, hfp0⟩
      have hfp01 : f (pre (⟨i0, hi0⟩, b0)).1 = 1 := (f2_cases _).resolve_left hfp0
      let J' := J.erase i0
      refine ⟨J', Finset.erase_subset i0 J, by rw [Finset.card_erase_of_mem hi0], ?_⟩
      intro z
      let zfull : J × Bool → F2 := fun p =>
        if h : p.1.1 ∈ J' then z (⟨p.1.1, h⟩, p.2) else 0
      obtain ⟨v, hv⟩ := hsurj zfull
      let v0 := pre (⟨i0, hi0⟩, b0)
      by_cases hfv : f v.1 = 0
      · refine ⟨⟨v.1, ⟨v.2, hfv⟩⟩, ?_⟩
        funext ⟨⟨i, hi⟩, b⟩
        have hiJ : i ∈ J := Finset.mem_of_mem_erase hi
        have h1 := congrFun hv (⟨i, hiJ⟩, b)
        simpa [zfull, hi] using h1
      · have hfv1 : f v.1 = 1 := (f2_cases (f v.1)).resolve_left hfv
        refine ⟨⟨v.1 + v0.1, ⟨T.add_mem v.2 v0.2, ?_⟩⟩, ?_⟩
        · simp [LinearMap.mem_ker, map_add, hfv1, v0, hfp01, f2_add_self]
        · funext ⟨⟨i, hi⟩, b⟩
          have hiJ : i ∈ J := Finset.mem_of_mem_erase hi
          have hine : i ≠ i0 := Finset.ne_of_mem_erase hi
          have h1 := congrFun hv (⟨i, hiJ⟩, b)
          have h2 := congrFun (hpre (⟨i0, hi0⟩, b0)) (⟨i, hiJ⟩, b)
          have hpne : ((⟨i, hiJ⟩, b) : J × Bool) ≠ (⟨i0, hi0⟩, b0) :=
            fun h => hine (congrArg (fun x : J × Bool => x.1.1) h)
          rw [Pi.single_eq_of_ne hpne] at h2
          simp only [map_add, Pi.add_apply, h1, v0, h2, add_zero, zfull, hi, ↓reduceDIte]

def subOfList {k : Nat} : List ((Fin k → F2) →ₗ[F2] F2) → Submodule F2 (Fin k → F2)
  | [] => ⊤
  | f :: rest => subOfList rest ⊓ LinearMap.ker f

lemma mem_subOfList {k : Nat} (l : List ((Fin k → F2) →ₗ[F2] F2)) (x : Fin k → F2) :
    x ∈ subOfList l ↔ ∀ f ∈ l, f x = 0 := by
  induction l with
  | nil => simp [subOfList]
  | cons f rest ih => simp [subOfList, ih, LinearMap.mem_ker, and_comm]

lemma surj_restrict_list {k : Nat} (hk : 0 < k) (s : Nat)
    (fs : List ((Fin k → F2) →ₗ[F2] F2)) (J : Finset (Fin k))
    (hsurj : Function.Surjective (fun (v : Fin k → F2) (p : J × Bool) =>
      mix hk (rotLin hk s v) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1)))) :
    ∃ J' ⊆ J, J.card - fs.length ≤ J'.card ∧
      Function.Surjective (fun (v : ({x : Fin k → F2 | ∀ f ∈ fs, f x = 0} : Set (Fin k → F2))) (p : J' × Bool) =>
        mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1))) := by
  suffices h : ∃ J' ⊆ J, J.card - fs.length ≤ J'.card ∧
      Function.Surjective (fun (v : subOfList fs) (p : J' × Bool) =>
        mix hk (rotLin hk s v.1) (if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1))) by
    rcases h with ⟨J', hsub, hcard, hs⟩
    refine ⟨J', hsub, hcard, fun z => ?_⟩
    obtain ⟨⟨v, hv⟩, hzv⟩ := hs z
    exact ⟨⟨v, (mem_subOfList fs v).mp hv⟩, hzv⟩
  induction fs with
  | nil =>
    refine ⟨J, Finset.Subset.refl J, by simp, fun z => ?_⟩
    obtain ⟨v, hv⟩ := hsurj z
    exact ⟨⟨v, trivial⟩, hv⟩
  | cons f rest ih =>
    rcases ih with ⟨J1, hJ1sub, hJ1card, hJ1surj⟩
    obtain ⟨J2, hJ2sub, hJ2card, hJ2surj⟩ := surj_restrict_ker hk s (subOfList rest) f J1 hJ1surj
    refine ⟨J2, Finset.Subset.trans hJ2sub hJ1sub, ?_, hJ2surj⟩
    simp only [List.length_cons]
    omega

lemma surj_mix_iff_no_ker {k : Nat} (hk : 0 < k) (s : Nat) (E : Finset (Fin k))
    (hno : ∀ c : Fin k → F2, mix hk c = 0 → (∀ u, u ∉ E → c u = 0) → c = 0) :
    Function.Surjective (fun (v : Fin k → F2) (u : E) => mix hk (rotLin hk s v) u.1) := by
  let g : (Fin k → F2) →ₗ[F2] (E → F2) := {
    toFun := fun v u => mix hk (rotLin hk s v) u.1
    map_add' := fun _ _ => by funext u; simp [map_add]
    map_smul' := fun _ _ => by funext u; simp [map_smul]
  }
  change Function.Surjective g

  rw [← LinearMap.range_eq_top]
  by_contra hne

  have hlt : LinearMap.range g < ⊤ := lt_top_iff_ne_top.mpr hne

  have hex_lin : ∃ α : (E → F2) →ₗ[F2] F2, α ≠ 0 ∧ ∀ w ∈ LinearMap.range g, α w = 0 := by
    obtain ⟨w0, hw0⟩ : ∃ w0 : E → F2, w0 ∉ LinearMap.range g := by
      by_contra hall; push Not at hall; exact hne (eq_top_iff.mpr (fun w _ => hall w))
    let q0 : (E → F2) ⧸ LinearMap.range g := Submodule.Quotient.mk w0
    have hq0 : q0 ≠ 0 := by
      intro h; exact hw0 ((Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mp h)
    let b := Module.finBasis F2 ((E → F2) ⧸ LinearMap.range g)
    have hexj : ∃ j, b.coord j q0 ≠ 0 := by
      by_contra hall; push Not at hall
      apply hq0
      apply b.ext_elem
      intro j
      simpa [Module.Basis.coord_apply] using hall j
    rcases hexj with ⟨j, hj⟩
    refine ⟨(b.coord j).comp (Submodule.mkQ (LinearMap.range g)), ?_, ?_⟩
    · intro h
      have := LinearMap.congr_fun h w0
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
      exact hj this
    · intro w hw
      simp [LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).mpr hw]
  rcases hex_lin with ⟨α, hαne, hα0⟩
  let c : Fin k → F2 := fun u => if h : u ∈ E then α (Pi.single ⟨u, h⟩ (1 : F2)) else 0
  have hc_supp : ∀ u, u ∉ E → c u = 0 := fun u hu => by simp [c, hu]
  have hα_dot : ∀ w : E → F2, α w = ∑ u : E, c u.1 * w u := by
    intro w
    have hw : w = ∑ u : E, w u • Pi.single u (1 : F2) := by
      funext q; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [map_smul, smul_eq_mul, mul_comm]
    simp [c, u.2]
  have hmix_c : mix hk c = 0 := by
    funext u
    have hzero : ∀ z : Fin k → F2, (∑ w : Fin k, mix hk c w * z w) = 0 := by
      intro z
      rw [← mix_self_adjoint hk c z]
      obtain ⟨v, hv⟩ := rotLin_surjective hk s z
      have hgv := hα0 (g v) ⟨v, rfl⟩
      rw [hα_dot] at hgv
      have hsum_eq : (∑ w : Fin k, c w * mix hk z w) = ∑ w : E, c w.1 * g v w := by
        rw [← hv]
        have h1 : (∑ w : Fin k, c w * mix hk (rotLin hk s v) w) =
            ∑ w ∈ E, c w * mix hk (rotLin hk s v) w := by
          symm
          apply Finset.sum_subset (Finset.subset_univ E)
          intro w _ hwE; simp [hc_supp w hwE]
        rw [h1, ← Finset.sum_coe_sort E]
        rfl
      rw [hsum_eq, hgv]
    have h1 := hzero (Pi.single u 1)
    simpa [Pi.single_apply] using h1
  have hc0 : c = 0 := hno c hmix_c hc_supp
  apply hαne
  apply LinearMap.ext
  intro w
  rw [hα_dot w]
  simp [hc0]

def walkLeaf {k : Nat} (nodes : Finset (List Bool))
    (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
    (raw : Fin k → F2) : List Bool :=
  (List.range nodes.card).foldl (fun (p : List Bool) _ =>
    if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p) []

lemma walkLeaf_not_mem {k : Nat} (nodes : Finset (List Bool))
    (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
    (raw : Fin k → F2) :
    walkLeaf nodes ask bias raw ∉ nodes := by
  let step : List Bool → List Bool := fun p =>
    if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p
  have hfold : ∀ (m : Nat) (p : List Bool),
      ((List.range m).foldl (fun q _ => step q) p) = step^[m] p := by
    intro m
    induction m with
    | zero => intro p; rfl
    | succ m ih =>
      intro p
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
          Function.iterate_succ_apply']
  change ((List.range nodes.card).foldl (fun q _ => step q) []) ∉ nodes
  rw [hfold]
  by_contra hmem

  have hlen : ∀ j, j ≤ nodes.card → step^[j] [] ∈ nodes ∧ (step^[j] []).length = j := by
    have hfix : ∀ a b, a ≤ b → step^[a] [] ∉ nodes → step^[b] [] = step^[a] [] := by
      intro a b hab hna
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      induction d with
      | zero => simp
      | succ d ih =>
        rw [show a + (d + 1) = (a + d) + 1 by omega, Function.iterate_succ_apply', ih (by omega)]
        simp only [step, hna, ↓reduceIte]
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : step^[0] [] ∈ nodes := by
        by_contra hnj; exact hnj (hfix 0 nodes.card (Nat.zero_le _) hnj ▸ hmem)
      exact ⟨h0, rfl⟩
    | succ j ih =>
      intro hj
      have hj' : j ≤ nodes.card := by omega
      have hja : step^[j + 1] [] ∈ nodes := by
        by_contra hnj; exact hnj (hfix (j + 1) nodes.card hj hnj ▸ hmem)
      rcases ih hj' with ⟨hprev, hplen⟩
      refine ⟨hja, ?_⟩
      rw [Function.iterate_succ_apply']
      simp only [step, hprev, ↓reduceIte, List.length_append, List.length_singleton, hplen]
  have hinj : Function.Injective (fun j : Fin (nodes.card + 1) => step^[j.val] []) := by
    intro a b hab
    have ha := (hlen a.val (by omega)).2
    have hb := (hlen b.val (by omega)).2
    have hlen_eq : (step^[a.val] []).length = (step^[b.val] []).length := congrArg List.length hab
    exact Fin.ext (by omega)
  have hsub : (Finset.univ : Finset (Fin (nodes.card + 1))).image (fun j => step^[j.val] []) ⊆ nodes := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, _, rfl⟩
    exact (hlen j.val (by omega)).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  omega

lemma card_leaves_le_nodes_add_one (nodes : Finset (List Bool)) (leaves : Finset (List Bool))
    (hdisj : ∀ p ∈ leaves, p ∉ nodes)
    (hpref : ∀ p ∈ leaves, ∀ q, q <+: p → q ≠ p → q ∈ nodes)
    (hanti : ∀ p ∈ leaves, ∀ q ∈ leaves, p <+: q → p = q) :
    leaves.card ≤ nodes.card + 1 := by
  classical

  induction hn : nodes.card using Nat.strong_induction_on generalizing nodes leaves with
  | ind m ih =>
    by_cases hm0 : m = 0
    · have hne : nodes = ∅ := Finset.card_eq_zero.mp (hn.trans hm0)
      subst hne
      have hsub : leaves ⊆ {[]} := by
        intro p hp
        simp only [Finset.mem_singleton]
        by_contra hne
        have := hpref p hp [] (List.nil_prefix) (Ne.symm hne)
        simp at this
      exact (Finset.card_le_card hsub).trans (by simp)
    ·
      by_cases hnil : ([] : List Bool) ∈ nodes
      ·
        let n0 : Finset (List Bool) := (nodes.filter (fun l => l.head? = some false)).image List.tail
        let n1 : Finset (List Bool) := (nodes.filter (fun l => l.head? = some true)).image List.tail
        let l0 : Finset (List Bool) := (leaves.filter (fun l => l.head? = some false)).image List.tail
        let l1 : Finset (List Bool) := (leaves.filter (fun l => l.head? = some true)).image List.tail
        have hmem_b : ∀ (S : Finset (List Bool)) (b : Bool) (t : List Bool),
            t ∈ (S.filter (fun l => l.head? = some b)).image List.tail ↔ b :: t ∈ S := by
          intro S b t
          simp only [Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨a, ⟨ha, hhead⟩, rfl⟩
            cases a with | nil => simp at hhead | cons ba ta => simp at hhead; subst hhead; exact ha
          · intro h; exact ⟨b :: t, ⟨h, rfl⟩, rfl⟩
        have hncard : n0.card + n1.card + 1 ≤ nodes.card := by
          have h1 : n0.image (false :: ·) ⊆ nodes.erase [] := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
            exact Finset.mem_erase.mpr ⟨by simp, (hmem_b nodes false t).mp ht⟩
          have h2 : n1.image (true :: ·) ⊆ nodes.erase [] := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
            exact Finset.mem_erase.mpr ⟨by simp, (hmem_b nodes true t).mp ht⟩
          have hdisj_img : Disjoint (n0.image (false :: ·)) (n1.image (true :: ·)) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx1 with ⟨t1, _, rfl⟩
            rcases Finset.mem_image.mp hx2 with ⟨t2, _, h⟩
            simp at h
          have hle := Finset.card_le_card (Finset.union_subset h1 h2)
          rw [Finset.card_union_of_disjoint hdisj_img,
              Finset.card_image_of_injective _ List.cons_injective,
              Finset.card_image_of_injective _ List.cons_injective,
              Finset.card_erase_of_mem hnil] at hle
          omega
        have hlcard : leaves.card ≤ l0.card + l1.card := by
          have hsub : leaves ⊆ l0.image (false :: ·) ∪ l1.image (true :: ·) := by
            intro p hp
            cases p with
            | nil => exact absurd hnil (hdisj [] hp)
            | cons b t =>
              cases b
              · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, (hmem_b leaves false t).mpr hp, rfl⟩)
              · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, (hmem_b leaves true t).mpr hp, rfl⟩)
          have hle := Finset.card_le_card hsub
          calc leaves.card
              ≤ (l0.image (false :: ·) ∪ l1.image (true :: ·)).card := hle
            _ ≤ (l0.image (false :: ·)).card + (l1.image (true :: ·)).card := Finset.card_union_le _ _
            _ = l0.card + l1.card := by
                rw [Finset.card_image_of_injective _ List.cons_injective,
                    Finset.card_image_of_injective _ List.cons_injective]
        have hih0 : l0.card ≤ n0.card + 1 := by
          apply ih n0.card (by omega) n0 l0
          · intro t ht htn; exact hdisj (false :: t) ((hmem_b leaves false t).mp ht) ((hmem_b nodes false t).mp htn)
          · intro t ht q hqp hne
            exact (hmem_b nodes false q).mpr (hpref (false :: t) ((hmem_b leaves false t).mp ht) (false :: q) (List.cons_prefix_cons.mpr ⟨rfl, hqp⟩) (by simp [hne]))
          · intro p hp q hq hpq
            have := hanti (false :: p) ((hmem_b leaves false p).mp hp) (false :: q) ((hmem_b leaves false q).mp hq) (List.cons_prefix_cons.mpr ⟨rfl, hpq⟩)
            simpa using this
          · rfl
        have hih1 : l1.card ≤ n1.card + 1 := by
          apply ih n1.card (by omega) n1 l1
          · intro t ht htn; exact hdisj (true :: t) ((hmem_b leaves true t).mp ht) ((hmem_b nodes true t).mp htn)
          · intro t ht q hqp hne
            exact (hmem_b nodes true q).mpr (hpref (true :: t) ((hmem_b leaves true t).mp ht) (true :: q) (List.cons_prefix_cons.mpr ⟨rfl, hqp⟩) (by simp [hne]))
          · intro p hp q hq hpq
            have := hanti (true :: p) ((hmem_b leaves true p).mp hp) (true :: q) ((hmem_b leaves true q).mp hq) (List.cons_prefix_cons.mpr ⟨rfl, hpq⟩)
            simpa using this
          · rfl
        omega
      · have hsub : leaves ⊆ {[]} := by
          intro p hp
          simp only [Finset.mem_singleton]
          by_contra hne
          exact hnil (hpref p hp [] List.nil_prefix (Ne.symm hne))
        have hle := (Finset.card_le_card hsub).trans (by simp : ({[]} : Finset (List Bool)).card ≤ 1)
        omega

def endsOf {k : Nat} (hk : 0 < k) (S : Finset (Fin k)) : Finset (Fin k) :=
  S.biUnion (fun i => ({ix hk (i.val + 1), ix hk (i.val + 2)} : Finset (Fin k)))

lemma ix_add_one_inj {k : Nat} (hk : 0 < k) {i j : Fin k} (h : ix hk (i.val + 1) = ix hk (j.val + 1)) : i = j := by
  have hv := congrArg Fin.val h
  simp only [ix] at hv
  have hi : i.val < k := i.isLt
  have hj : j.val < k := j.isLt
  ext
  by_cases h1 : i.val + 1 < k <;> by_cases h2 : j.val + 1 < k
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv; omega
  · have : j.val + 1 = k := by omega
    rw [Nat.mod_eq_of_lt h1, this, Nat.mod_self] at hv; omega
  · have : i.val + 1 = k := by omega
    rw [this, Nat.mod_self, Nat.mod_eq_of_lt h2] at hv; omega
  · omega

lemma ix_add_two_inj {k : Nat} (hk : 0 < k) {i j : Fin k} (h : ix hk (i.val + 2) = ix hk (j.val + 2)) : i = j := by
  have h1 : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk ((ix hk (j.val + 1)).val + 1) := by
    have heq : ∀ u : Fin k, ix hk ((ix hk (u.val + 1)).val + 1) = ix hk (u.val + 2) := fun u => by
      ext; simp only [ix]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [heq i, heq j, h]
  exact ix_add_one_inj hk (ix_add_one_inj hk h1)

lemma ix_add_one_ne_add_two {k : Nat} (hk1 : 1 < k) (i : Fin k) :
    ix (by omega : 0 < k) (i.val + 1) ≠ ix (by omega : 0 < k) (i.val + 2) := by
  have hk : 0 < k := by omega
  intro h
  have hv := congrArg Fin.val h
  simp only [ix] at hv
  have h1 : (i.val + 1 + 1) % k = (i.val + 1) % k := by
    rw [show i.val + 1 + 1 = i.val + 2 by omega]
    exact hv.symm
  have h2 : ((i.val + 1) % k + 1) % k = (i.val + 1) % k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact h1
  set r := (i.val + 1) % k
  have hr : r < k := Nat.mod_lt _ hk
  by_cases hr1 : r + 1 < k
  · rw [Nat.mod_eq_of_lt hr1] at h2; omega
  · have : r + 1 = k := by omega
    rw [this, Nat.mod_self] at h2; omega

lemma pair_disjoint {k : Nat} (hk1 : 1 < k) {sites : Finset (Fin k)}
    (hsp : ∀ i ∈ sites, ix (by omega : 0 < k) (i.val + 1) ∉ sites)
    {i j : Fin k} (hi : i ∈ sites) (hj : j ∈ sites) (hij : i ≠ j) :
    Disjoint ({ix (by omega : 0 < k) (i.val + 1), ix (by omega : 0 < k) (i.val + 2)} : Finset (Fin k))
             ({ix (by omega : 0 < k) (j.val + 1), ix (by omega : 0 < k) (j.val + 2)} : Finset (Fin k)) := by
  have hk : 0 < k := by omega
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
  rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
  · exact hij (ix_add_one_inj hk h)
  · have h' : ix hk (j.val + 1) = i := by
      apply ix_add_one_inj hk
      have heq : ix hk ((ix hk (j.val + 1)).val + 1) = ix hk (j.val + 2) := by
        ext; simp only [ix]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [heq]; exact h.symm
    exact hsp j hj (h' ▸ hi)
  · have h' : ix hk (i.val + 1) = j := by
      apply ix_add_one_inj hk
      have heq : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by
        ext; simp only [ix]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [heq]; exact h
    exact hsp i hi (h' ▸ hj)
  · exact hij (ix_add_two_inj hk h)

lemma endsOf_card {k : Nat} (hk1 : 1 < k) {S : Finset (Fin k)}
    (hsp : ∀ i ∈ S, ix (by omega : 0 < k) (i.val + 1) ∉ S) :
    (endsOf (by omega : 0 < k) S).card = 2 * S.card := by
  have hk : 0 < k := by omega
  unfold endsOf
  rw [Finset.card_biUnion (fun i hi j hj hij => pair_disjoint hk1 hsp hi hj hij)]
  have h2 : ∀ i ∈ S, ({ix hk (i.val + 1), ix hk (i.val + 2)} : Finset (Fin k)).card = 2 :=
    fun i _ => Finset.card_pair (ix_add_one_ne_add_two hk1 i)
  rw [Finset.sum_congr rfl h2]
  simp [Finset.sum_const, mul_comm]

lemma surj_pairs_of_no_ker {k : Nat} (hk1 : 1 < k) (s : Nat) {J : Finset (Fin k)}
    (hsp : ∀ i ∈ J, ix (by omega : 0 < k) (i.val + 1) ∉ J)
    (hno : ∀ c : Fin k → F2, mix (by omega : 0 < k) c = 0 →
      (∀ u, u ∉ endsOf (by omega : 0 < k) J → c u = 0) → c = 0) :
    Function.Surjective (fun (v : Fin k → F2) (p : J × Bool) =>
      mix (by omega : 0 < k) (rotLin (by omega : 0 < k) s v)
        (if p.2 then ix (by omega : 0 < k) (p.1.1.val + 2) else ix (by omega : 0 < k) (p.1.1.val + 1))) := by
  have hk : 0 < k := by omega
  have hsurjE := surj_mix_iff_no_ker hk s (endsOf hk J) hno
  let emb : J × Bool → endsOf hk J := fun p =>
    ⟨if p.2 then ix hk (p.1.1.val + 2) else ix hk (p.1.1.val + 1), by
      apply Finset.mem_biUnion.mpr
      refine ⟨p.1.1, p.1.2, ?_⟩
      cases p.2 <;> simp⟩
  have hemb_inj : Function.Injective emb := by
    rintro ⟨⟨i1, hi1⟩, b1⟩ ⟨⟨i2, hi2⟩, b2⟩ h
    have hv : (if b1 then ix hk (i1.val + 2) else ix hk (i1.val + 1)) =
        (if b2 then ix hk (i2.val + 2) else ix hk (i2.val + 1)) := congrArg Subtype.val h
    have hi : i1 = i2 := by
      by_contra hne
      have hdisj := pair_disjoint hk1 hsp hi1 hi2 hne
      rw [Finset.disjoint_left] at hdisj
      apply hdisj (a := if b1 then ix hk (i1.val + 2) else ix hk (i1.val + 1))
      · cases b1 <;> simp
      · rw [hv]; cases b2 <;> simp
    subst hi
    congr 1
    cases b1 <;> cases b2 <;> simp at hv ⊢
    · exact absurd hv (ix_add_one_ne_add_two hk1 i1)
    · exact absurd hv.symm (ix_add_one_ne_add_two hk1 i1)
  intro z

  classical
  let zE : endsOf hk J → F2 := fun u =>
    if h : ∃ p : J × Bool, emb p = u then z h.choose else 0
  obtain ⟨v, hv⟩ := hsurjE zE
  refine ⟨v, ?_⟩
  funext p
  have h1 := congrFun hv (emb p)
  have hex : ∃ q : J × Bool, emb q = emb p := ⟨p, rfl⟩
  have hch : hex.choose = p := hemb_inj hex.choose_spec
  simp only [zE, hex, ↓reduceDIte, hch, emb] at h1
  exact h1

lemma exists_ker_list_of_submodule {k : Nat} (T : Submodule F2 (Fin k → F2)) :
    ∃ fs : List ((Fin k → F2) →ₗ[F2] F2),
      fs.length = k - Module.finrank F2 T ∧
      ∀ x : Fin k → F2, x ∈ T ↔ ∀ f ∈ fs, f x = 0 := by
  classical
  let d := Module.finrank F2 ((Fin k → F2) ⧸ T)
  have hd : d = k - Module.finrank F2 T := by
    have h := Submodule.finrank_quotient_add_finrank T
    have hk : Module.finrank F2 (Fin k → F2) = k := by simp
    omega
  let b := Module.finBasis F2 ((Fin k → F2) ⧸ T)
  let fs : List ((Fin k → F2) →ₗ[F2] F2) :=
    (List.finRange d).map (fun j => (b.coord j).comp (Submodule.mkQ T))
  refine ⟨fs, by simp [fs, hd], ?_⟩
  intro x
  constructor
  · intro hx f hf
    rcases List.mem_map.mp hf with ⟨j, _, rfl⟩
    simp [LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero T).mpr hx]
  · intro hall
    rw [← Submodule.Quotient.mk_eq_zero T]
    apply b.ext_elem
    intro j
    have hmem : (b.coord j).comp (Submodule.mkQ T) ∈ fs :=
      List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    have h0 := hall _ hmem
    simpa [LinearMap.comp_apply, Module.Basis.coord_apply] using h0

lemma walkLeaf_prefixes_and_fiber {k : Nat} (nodes : Finset (List Bool))
    (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
    (x0 : Fin k → F2) :
    let p := walkLeaf nodes ask bias x0
    (∀ q, q <+: p → q ≠ p → q ∈ nodes) ∧
    (∀ v : Fin k → F2, (∀ j (hj : j < p.length), ask (p.take j) v = 0) →
      walkLeaf nodes ask bias (x0 + v) = p) := by
  let step : (Fin k → F2) → List Bool → List Bool := fun raw q =>
    if q ∈ nodes then q ++ [decide (ask q raw + bias q ≠ 0)] else q
  have hfold : ∀ (raw : Fin k → F2) (m : Nat) (q : List Bool),
      ((List.range m).foldl (fun r _ => step raw r) q) = (step raw)^[m] q := by
    intro raw m
    induction m with
    | zero => intro q; rfl
    | succ m ih =>
      intro q
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
          Function.iterate_succ_apply']
  have hstep_pref : ∀ (m : Nat) (q : List Bool),
      q <+: (step x0)^[m] [] → q ≠ (step x0)^[m] [] → q ∈ nodes := by
    intro m
    induction m with
    | zero => intro q hq hne; simp at hq; exact absurd hq hne
    | succ m ih =>
      intro q hq hne
      rw [Function.iterate_succ_apply'] at hq hne
      by_cases hm : (step x0)^[m] [] ∈ nodes
      · change q <+: (if (step x0)^[m] [] ∈ nodes then (step x0)^[m] [] ++ [decide (ask ((step x0)^[m] []) x0 + bias ((step x0)^[m] []) ≠ 0)] else (step x0)^[m] []) at hq
        change q ≠ (if (step x0)^[m] [] ∈ nodes then (step x0)^[m] [] ++ [decide (ask ((step x0)^[m] []) x0 + bias ((step x0)^[m] []) ≠ 0)] else (step x0)^[m] []) at hne
        rw [if_pos hm] at hq hne
        have hlen : q.length ≤ ((step x0)^[m] []).length := by
          rcases hq with ⟨t, ht⟩
          have hlt := congrArg List.length ht
          simp only [List.length_append, List.length_cons, List.length_nil] at hlt
          by_cases ht0 : t = []
          · subst ht0; exact absurd (by simpa using ht) hne
          · have hpos : 0 < t.length := List.length_pos_of_ne_nil ht0
            omega
        have hq' : q <+: (step x0)^[m] [] := by
          rcases hq with ⟨t, ht⟩
          have htake := congrArg (List.take q.length) ht
          rw [List.take_left, List.take_append_of_le_length hlen] at htake
          refine ⟨((step x0)^[m] []).drop q.length, ?_⟩
          have h1 := List.take_append_drop q.length ((step x0)^[m] [])
          rwa [← htake] at h1
        by_cases hqe : q = (step x0)^[m] []
        · exact hqe ▸ hm
        · exact ih q hq' hqe
      · simp only [step, hm, ↓reduceIte] at hq hne
        exact ih q hq hne
  have hwalk_eq : walkLeaf nodes ask bias x0 = (step x0)^[nodes.card] [] := hfold x0 nodes.card []
  constructor
  · intro q hq hne
    rw [hwalk_eq] at hq hne
    exact hstep_pref nodes.card q hq hne
  · intro v hv
    change ((List.range nodes.card).foldl (fun r _ => step (x0 + v) r) []) = walkLeaf nodes ask bias x0
    rw [hfold (x0 + v) nodes.card [], hwalk_eq]
    have hiter : ∀ m ≤ nodes.card,
        (step (x0 + v))^[m] [] = (step x0)^[m] [] ∧
        ((step x0)^[m] [] <+: (step x0)^[nodes.card] []) := by
      intro m hm
      induction m with
      | zero => exact ⟨rfl, List.nil_prefix⟩
      | succ m ih =>
        rcases ih (by omega) with ⟨heq_m, hpref_m⟩
        have hpref_next : (step x0)^[m + 1] [] <+: (step x0)^[nodes.card] [] := by
          have hgen : ∀ a b, a ≤ b → (step x0)^[a] [] <+: (step x0)^[b] [] := by
            intro a b hab
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
            induction d with
            | zero => simp
            | succ d ihd =>
              rw [show a + (d + 1) = (a + d) + 1 by omega, Function.iterate_succ_apply']
              apply List.IsPrefix.trans (ihd (by omega))
              dsimp only [step]
              split_ifs
              · exact List.prefix_append _ _
              · exact List.prefix_refl _
          exact hgen (m + 1) nodes.card hm
        refine ⟨?_, hpref_next⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', heq_m]
        by_cases hmem : (step x0)^[m] [] ∈ nodes
        · change (if (step x0)^[m] [] ∈ nodes then (step x0)^[m] [] ++ [decide (ask ((step x0)^[m] []) (x0 + v) + bias ((step x0)^[m] []) ≠ 0)] else (step x0)^[m] []) =
              (if (step x0)^[m] [] ∈ nodes then (step x0)^[m] [] ++ [decide (ask ((step x0)^[m] []) x0 + bias ((step x0)^[m] []) ≠ 0)] else (step x0)^[m] [])
          rw [if_pos hmem, if_pos hmem]
          have hlt : ((step x0)^[m] []).length < ((step x0)^[nodes.card] []).length := by
            have hle := List.IsPrefix.length_le hpref_m
            have hne : (step x0)^[m] [] ≠ (step x0)^[nodes.card] [] := by
              intro h; rw [← hwalk_eq] at h; exact walkLeaf_not_mem nodes ask bias x0 (h ▸ hmem)
            have hne_len : ((step x0)^[m] []).length ≠ ((step x0)^[nodes.card] []).length :=
              fun hl => hne (List.IsPrefix.eq_of_length hpref_m hl)
            omega
          have htake : ((step x0)^[nodes.card] []).take ((step x0)^[m] []).length = (step x0)^[m] [] := by
            rcases hpref_m with ⟨t, ht⟩
            rw [← ht, List.take_left]
          have hv0 : ask ((step x0)^[m] []) v = 0 := by
            rw [← htake, ← hwalk_eq]
            exact hv ((step x0)^[m] []).length (by rwa [hwalk_eq])
          rw [map_add, hv0, add_zero]
        · change (if (step x0)^[m] [] ∈ nodes then _ else _) = (if (step x0)^[m] [] ∈ nodes then _ else _)
          rw [if_neg hmem, if_neg hmem]
    exact (hiter nodes.card (le_refl _)).1

lemma exists_indep_sites {k : Nat} (hk1 : 1 < k) (sites : Finset (Fin k))
    (hsp : ∀ i ∈ sites, ix (by omega : 0 < k) (i.val + 1) ∉ sites) :
    let hk : 0 < k := by omega
    let ends := endsOf hk sites
    let full := fun (p r : Nat) => ∀ j : Fin k, j.val % p = r → j ∈ ends
    let oddCase := 2 ≤ ((Finset.range 3).filter (fun r => full 3 r)).card
    let laneCase := ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => full 6 (2 * r + v))).card
    let save := if ¬ 3 ∣ k then 0 else if k % 2 = 1 then (if oddCase then 1 else 0)
      else if 2 * sites.card = k then 2 else if laneCase then 1 else 0
    ∃ sites0 ⊆ sites, sites.card - save ≤ sites0.card ∧
      ∀ c : Fin k → F2, mix hk c = 0 → (∀ u, u ∉ endsOf hk sites0 → c u = 0) → c = 0 := by
  have hk : 0 < k := by omega
  dsimp only
  by_cases hd3 : 3 ∣ k
  · simp only [hd3, not_true_eq_false, ↓reduceIte]
    by_cases hodd : k % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have hfull_of_c : ∀ {S : Finset (Fin k)} {c : Fin k → F2},
          mix hk c = 0 → (∀ u, u ∉ endsOf hk S → c u = 0) → c ≠ 0 →
          2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk S)).card := by
        intro S c hc hsupp hne
        have h012 := ker_mix_sum3_odd hk hd3 hodd hc
        have hper := ker_mix_period3_odd hk hd3 hodd hc
        have hex : ∃ r < 3, c (ix hk r) = 1 := by
          by_contra hall; push Not at hall
          apply hne; funext u
          rw [hper u]
          exact (f2_cases _).resolve_right (hall (u.val % 3) (Nat.mod_lt _ (by omega)))

        have htwo : 2 ≤ ((Finset.range 3).filter (fun r => c (ix hk r) = 1)).card := by
          have h0 := f2_cases (c (ix hk 0))
          have h1 := f2_cases (c (ix hk 1))
          have h2 := f2_cases (c (ix hk 2))
          rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · rcases hex with ⟨r, hr, hcr⟩
            interval_cases r
            · rw [h0] at hcr; exact absurd hcr (by decide)
            · rw [h1] at hcr; exact absurd hcr (by decide)
            · rw [h2] at hcr; exact absurd hcr (by decide)
          · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
          · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
          · have hsub : ({1, 2} : Finset Nat) ⊆ (Finset.range 3).filter (fun r => c (ix hk r) = 1) := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h1⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩
            exact (by decide : 2 ≤ ({1, 2} : Finset Nat).card).trans (Finset.card_le_card hsub)
          · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
          · have hsub : ({0, 2} : Finset Nat) ⊆ (Finset.range 3).filter (fun r => c (ix hk r) = 1) := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩
            exact (by decide : 2 ≤ ({0, 2} : Finset Nat).card).trans (Finset.card_le_card hsub)
          · have hsub : ({0, 1} : Finset Nat) ⊆ (Finset.range 3).filter (fun r => c (ix hk r) = 1) := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h1⟩
            exact (by decide : 2 ≤ ({0, 1} : Finset Nat).card).trans (Finset.card_le_card hsub)
          · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
        apply htwo.trans
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
        refine ⟨hr.1, fun j hj => ?_⟩
        by_contra hnot
        have hc0 := hsupp j hnot
        rw [hper j, hj, hr.2] at hc0
        exact one_ne_zero hc0
      by_cases hoddCase : 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites)).card
      · simp only [hoddCase, ↓reduceIte]

        have hnot3 : ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites)).card < 3 := by
          by_contra hge3
          have hall : ∀ j : Fin k, j ∈ endsOf hk sites := by
            have heq : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites) = Finset.range 3 :=
              Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simp; omega)
            intro j
            have hmem : j.val % 3 ∈ (Finset.range 3).filter (fun r => ∀ u : Fin k, u.val % 3 = r → u ∈ endsOf hk sites) := by
              rw [heq]; exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
            exact (Finset.mem_filter.mp hmem).2 j rfl
          have huniv : endsOf hk sites = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
          have hc := endsOf_card hk1 hsp
          rw [huniv, Finset.card_univ, Fintype.card_fin] at hc
          omega
        obtain ⟨r1, hr1⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites)).card)
        have hr1_lt : r1 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr1).1
        have hr1_full : ∀ j : Fin k, j.val % 3 = r1 → j ∈ endsOf hk sites := (Finset.mem_filter.mp hr1).2
        have hk3 : 3 ≤ k := by omega
        have hj1_mem : (⟨r1, by omega⟩ : Fin k) ∈ endsOf hk sites := hr1_full ⟨r1, by omega⟩ (Nat.mod_eq_of_lt hr1_lt)
        rcases Finset.mem_biUnion.mp hj1_mem with ⟨i0, hi0, hpair0⟩
        refine ⟨sites.erase i0, Finset.erase_subset i0 sites, by rw [Finset.card_erase_of_mem hi0], ?_⟩
        intro c hc hsupp
        by_contra hne
        have h2 := hfull_of_c hc hsupp hne

        have hr1_not : ¬ (∀ j : Fin k, j.val % 3 = r1 → j ∈ endsOf hk (sites.erase i0)) := by
          intro h
          have hmem := h ⟨r1, by omega⟩ (Nat.mod_eq_of_lt hr1_lt)
          rcases Finset.mem_biUnion.mp hmem with ⟨i1, hi1, hpair1⟩
          have hne_i : i1 ≠ i0 := Finset.ne_of_mem_erase hi1
          have hdisj := pair_disjoint hk1 hsp (Finset.mem_of_mem_erase hi1) hi0 hne_i
          exact Finset.disjoint_left.mp hdisj hpair1 hpair0
        have hsub : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk (sites.erase i0)) ⊆
            ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites)).erase r1 := by
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_erase] at hr ⊢
          refine ⟨fun h => hr1_not (h ▸ hr.2), hr.1, fun j hj => ?_⟩
          have hm := hr.2 j hj
          rcases Finset.mem_biUnion.mp hm with ⟨i, hi, hp⟩
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_of_mem_erase hi, hp⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hr1] at hle
        omega
      · simp only [hoddCase, ↓reduceIte]
        refine ⟨sites, Finset.Subset.refl _, by omega, ?_⟩
        intro c hc hsupp
        by_contra hne
        exact hoddCase (hfull_of_c hc hsupp hne)
    ·
      have heven : k % 2 = 0 := by omega
      have hd6 : 6 ∣ k := by omega
      have hk6 : 6 ≤ k := by omega
      simp only [hodd, ↓reduceIte]
      have hfull_lane_of_c : ∀ {S : Finset (Fin k)} {c : Fin k → F2},
          mix hk c = 0 → (∀ u, u ∉ endsOf hk S → c u = 0) → c ≠ 0 →
          ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk S)).card := by
        intro S c hc hsupp hne
        have hper := ker_mix_mod6_val hk hc
        have hex : ∃ u : Fin k, c u = 1 := by
          by_contra hall; push Not at hall
          apply hne; funext u
          exact (f2_cases _).resolve_right (hall u)
        rcases hex with ⟨u0, hu0⟩
        let v := u0.val % 2
        have hv : v ∈ Finset.range 2 := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
        refine ⟨v, hv, ?_⟩
        have hsum := ker_mix_lane_sum hk hc v
        have htwo : 2 ≤ ((Finset.range 3).filter (fun r => c (ix hk (2 * r + v)) = 1)).card := by
          have hv0 : c (ix hk (2 * 0 + v)) = c (ix hk v) := by simp
          have hv1 : c (ix hk (2 * 1 + v)) = c (ix hk (v + 2)) := by
            congr 1; apply Fin.ext; simp only [ix]; congr 1; omega
          have hv2 : c (ix hk (2 * 2 + v)) = c (ix hk (v + 4)) := by
            congr 1; apply Fin.ext; simp only [ix]; congr 1; omega
          have hu0' : c (ix hk (u0.val % 6)) = 1 := by rw [← hper u0]; exact hu0
          have h0 := f2_cases (c (ix hk v))
          have h1 := f2_cases (c (ix hk (v + 2)))
          have h2 := f2_cases (c (ix hk (v + 4)))
          rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · have hmod : u0.val % 6 = v ∨ u0.val % 6 = v + 2 ∨ u0.val % 6 = v + 4 := by omega
            rcases hmod with hm | hm | hm
            · rw [hm, h0] at hu0'; exact absurd hu0' (by decide)
            · rw [hm, h1] at hu0'; exact absurd hu0' (by decide)
            · rw [hm, h2] at hu0'; exact absurd hu0' (by decide)
          · rw [h0, h1, h2] at hsum; exact absurd hsum (by decide)
          · rw [h0, h1, h2] at hsum; exact absurd hsum (by decide)
          · have hsub : ({1, 2} : Finset Nat) ⊆ (Finset.range 3).filter (fun r => c (ix hk (2 * r + v)) = 1) := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv1.trans h1⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv2.trans h2⟩
            exact (by decide : 2 ≤ ({1, 2} : Finset Nat).card).trans (Finset.card_le_card hsub)
          · rw [h0, h1, h2] at hsum; exact absurd hsum (by decide)
          · have hsub : ({0, 2} : Finset Nat) ⊆ (Finset.range 3).filter (fun r => c (ix hk (2 * r + v)) = 1) := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv0.trans h0⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv2.trans h2⟩
            exact (by decide : 2 ≤ ({0, 2} : Finset Nat).card).trans (Finset.card_le_card hsub)
          · have hsub : ({0, 1} : Finset Nat) ⊆ (Finset.range 3).filter (fun r => c (ix hk (2 * r + v)) = 1) := by
              intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv0.trans h0⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hv1.trans h1⟩
            exact (by decide : 2 ≤ ({0, 1} : Finset Nat).card).trans (Finset.card_le_card hsub)
          · rw [h0, h1, h2] at hsum; exact absurd hsum (by decide)
        apply htwo.trans
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
        refine ⟨hr.1, fun j hj => ?_⟩
        by_contra hnot
        have hc0 := hsupp j hnot
        rw [hper j, hj, hr.2] at hc0
        exact one_ne_zero hc0
      by_cases hfull_match : 2 * sites.card = k
      · simp only [hfull_match, ↓reduceIte]
        have huniv : endsOf hk sites = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [endsOf_card hk1 hsp, hfull_match, Fintype.card_fin])
        have h0mem : (⟨0, hk⟩ : Fin k) ∈ endsOf hk sites := huniv ▸ Finset.mem_univ _
        have h2mem : (⟨2, by omega⟩ : Fin k) ∈ endsOf hk sites := huniv ▸ Finset.mem_univ _
        rcases Finset.mem_biUnion.mp h0mem with ⟨i1, hi1, hp1⟩
        rcases Finset.mem_biUnion.mp h2mem with ⟨i2, hi2, hp2⟩
        have hne12 : i1 ≠ i2 := by
          intro h; subst h
          have hi1lt := i1.isLt
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
          rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
          · have h1v := congrArg Fin.val h1; have h2v := congrArg Fin.val h2; simp only [ix] at h1v h2v; omega
          · have h1v := congrArg Fin.val h1; have h2v := congrArg Fin.val h2; simp only [ix] at h1v h2v
            have h1' : (i1.val + 1) % k = 0 := h1v.symm
            have h2' : (i1.val + 2) % k = 2 := h2v.symm
            have h1_eq : i1.val + 1 = k := by
              by_cases hlt : i1.val + 1 < k
              · rw [Nat.mod_eq_of_lt hlt] at h1'; omega
              · omega
            rw [show i1.val + 2 = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < k)] at h2'
            omega
          · have h1v := congrArg Fin.val h1; have h2v := congrArg Fin.val h2; simp only [ix] at h1v h2v
            have h1' : (i1.val + 2) % k = 0 := h1v.symm
            have h2' : (i1.val + 1) % k = 2 := h2v.symm
            have h1_eq : i1.val + 2 = k := by
              by_cases hlt : i1.val + 2 < k
              · rw [Nat.mod_eq_of_lt hlt] at h1'; omega
              · have : i1.val + 2 = k ∨ i1.val + 2 = k + 1 := by omega
                rcases this with heq | heq
                · exact heq
                · rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < k)] at h1'; omega
            rw [show i1.val + 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k)] at h2'
            omega
          · have h1v := congrArg Fin.val h1; have h2v := congrArg Fin.val h2; simp only [ix] at h1v h2v; omega

        let S0 := (sites.erase i1).erase i2
        refine ⟨S0, Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _), ?_, ?_⟩
        · have hi2' : i2 ∈ sites.erase i1 := Finset.mem_erase.mpr ⟨hne12.symm, hi2⟩
          rw [Finset.card_erase_of_mem hi2', Finset.card_erase_of_mem hi1]
          omega
        · intro c hc hsupp
          by_contra hne
          rcases hfull_lane_of_c hc hsupp hne with ⟨v, hv, h2⟩
          have hv01 : v = 0 ∨ v = 1 := by simp only [Finset.mem_range] at hv; omega
          rcases hv01 with rfl | rfl
          ·
            have hmiss0 : (⟨0, hk⟩ : Fin k) ∉ endsOf hk S0 := by
              intro hm; rcases Finset.mem_biUnion.mp hm with ⟨j, hj, hpj⟩
              have hjne : j ≠ i1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
              exact Finset.disjoint_left.mp (pair_disjoint hk1 hsp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)) hi1 hjne) hpj hp1
            have hmiss2 : (⟨2, by omega⟩ : Fin k) ∉ endsOf hk S0 := by
              intro hm; rcases Finset.mem_biUnion.mp hm with ⟨j, hj, hpj⟩
              have hjne : j ≠ i2 := Finset.ne_of_mem_erase hj
              exact Finset.disjoint_left.mp (pair_disjoint hk1 hsp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)) hi2 hjne) hpj hp2
            have hsub : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + 0 → j ∈ endsOf hk S0) ⊆ {2} := by
              intro r hr
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hr ⊢
              by_cases hr0 : r = 0
              · subst hr0; exact absurd (hr.2 ⟨0, hk⟩ (by simp)) hmiss0
              · by_cases hr1 : r = 1
                · subst hr1; exact absurd (hr.2 ⟨2, by omega⟩ (by simp)) hmiss2
                · omega
            have hle := (Finset.card_le_card hsub).trans (by simp : ({2} : Finset Nat).card ≤ 1)
            omega
          · have hi1_cases : (⟨1, by omega⟩ : Fin k) ∈ ({ix hk (i1.val + 1), ix hk (i1.val + 2)} : Finset (Fin k)) ∨
                (⟨k - 1, by omega⟩ : Fin k) ∈ ({ix hk (i1.val + 1), ix hk (i1.val + 2)} : Finset (Fin k)) := by
              have hi1lt := i1.isLt
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 ⊢
              rcases hp1 with h | h
              · left; right
                have hv := congrArg Fin.val h; simp only [ix] at hv
                have h1 : i1.val + 1 = k := by
                  by_cases hlt : i1.val + 1 < k
                  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
                  · omega
                apply Fin.ext; simp only [ix]
                rw [show i1.val + 2 = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < k)]
              · right; left
                have hv := congrArg Fin.val h; simp only [ix] at hv
                have h1 : i1.val + 2 = k := by
                  by_cases hlt : i1.val + 2 < k
                  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
                  · have : i1.val + 2 = k ∨ i1.val + 2 = k + 1 := by omega
                    rcases this with heq | heq
                    · exact heq
                    · rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < k)] at hv; omega
                apply Fin.ext; simp only [ix]
                rw [show i1.val + 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
            have hi2_cases : (⟨3, by omega⟩ : Fin k) ∈ ({ix hk (i2.val + 1), ix hk (i2.val + 2)} : Finset (Fin k)) ∨
                (⟨1, by omega⟩ : Fin k) ∈ ({ix hk (i2.val + 1), ix hk (i2.val + 2)} : Finset (Fin k)) := by
              have hi2lt := i2.isLt
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp2 ⊢
              rcases hp2 with h | h
              · left; right
                have hv := congrArg Fin.val h; simp only [ix] at hv
                have h1 : i2.val + 1 = 2 := by
                  by_cases hlt : i2.val + 1 < k
                  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
                  · have : i2.val + 1 = k := by omega
                    rw [this, Nat.mod_self] at hv; omega
                apply Fin.ext; simp only [ix]
                rw [show i2.val + 2 = 3 by omega, Nat.mod_eq_of_lt (by omega : 3 < k)]
              · right; left
                have hv := congrArg Fin.val h; simp only [ix] at hv
                have h1 : i2.val + 2 = 2 := by
                  by_cases hlt : i2.val + 2 < k
                  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
                  · have : i2.val + 2 = k ∨ i2.val + 2 = k + 1 := by omega
                    rcases this with heq | heq
                    · rw [heq, Nat.mod_self] at hv; omega
                    · rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < k)] at hv; omega
                apply Fin.ext; simp only [ix]
                rw [show i2.val + 1 = 1 by omega, Nat.mod_eq_of_lt (by omega : 1 < k)]
            have hmiss_of_i1 : ∀ u : Fin k, u ∈ ({ix hk (i1.val + 1), ix hk (i1.val + 2)} : Finset (Fin k)) → u ∉ endsOf hk S0 := by
              intro u hu hm; rcases Finset.mem_biUnion.mp hm with ⟨j, hj, hpj⟩
              have hjne : j ≠ i1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
              exact Finset.disjoint_left.mp (pair_disjoint hk1 hsp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)) hi1 hjne) hpj hu
            have hmiss_of_i2 : ∀ u : Fin k, u ∈ ({ix hk (i2.val + 1), ix hk (i2.val + 2)} : Finset (Fin k)) → u ∉ endsOf hk S0 := by
              intro u hu hm; rcases Finset.mem_biUnion.mp hm with ⟨j, hj, hpj⟩
              have hjne : j ≠ i2 := Finset.ne_of_mem_erase hj
              exact Finset.disjoint_left.mp (pair_disjoint hk1 hsp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)) hi2 hjne) hpj hu
            have hkm1_mod6 : (k - 1) % 6 = 5 := by rcases hd6 with ⟨q, rfl⟩; omega
            rcases hi1_cases with h1a | h1b <;> rcases hi2_cases with h2a | h2b
            · have hsub : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + 1 → j ∈ endsOf hk S0) ⊆ {2} := by
                intro r hr; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hr ⊢
                by_cases hr0 : r = 0
                · subst hr0; exact absurd (hr.2 ⟨1, by omega⟩ (by simp)) (hmiss_of_i1 _ h1a)
                · by_cases hr1 : r = 1
                  · subst hr1; exact absurd (hr.2 ⟨3, by omega⟩ (by simp)) (hmiss_of_i2 _ h2a)
                  · omega
              have hle := (Finset.card_le_card hsub).trans (by simp : ({2} : Finset Nat).card ≤ 1); omega
            · exact absurd h2b (Finset.disjoint_left.mp (pair_disjoint hk1 hsp hi1 hi2 hne12) h1a)
            · have hsub : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + 1 → j ∈ endsOf hk S0) ⊆ {0} := by
                intro r hr; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hr ⊢
                by_cases hr1 : r = 1
                · subst hr1; exact absurd (hr.2 ⟨3, by omega⟩ (by simp)) (hmiss_of_i2 _ h2a)
                · by_cases hr2 : r = 2
                  · subst hr2; exact absurd (hr.2 ⟨k - 1, by omega⟩ (by dsimp only; omega)) (hmiss_of_i1 _ h1b)
                  · omega
              have hle := (Finset.card_le_card hsub).trans (by simp : ({0} : Finset Nat).card ≤ 1); omega
            · have hsub : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + 1 → j ∈ endsOf hk S0) ⊆ {1} := by
                intro r hr; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hr ⊢
                by_cases hr0 : r = 0
                · subst hr0; exact absurd (hr.2 ⟨1, by omega⟩ (by simp)) (hmiss_of_i2 _ h2b)
                · by_cases hr2 : r = 2
                  · subst hr2; exact absurd (hr.2 ⟨k - 1, by omega⟩ (by dsimp only; omega)) (hmiss_of_i1 _ h1b)
                  · omega
              have hle := (Finset.card_le_card hsub).trans (by simp : ({1} : Finset Nat).card ≤ 1); omega
      · simp only [hfull_match, ↓reduceIte]
        have hlt_half : 2 * sites.card < k := by
          have hc := endsOf_card hk1 hsp
          have hle : (endsOf hk sites).card ≤ k := by simpa using Finset.card_le_univ (endsOf hk sites)
          omega
        have hd2 : 2 ∣ k := dvd_trans (by decide : 2 ∣ 6) hd6
        have hpar_ix : ∀ i : Fin k, (ix hk (i.val + 1)).val % 2 ≠ (ix hk (i.val + 2)).val % 2 := by
          intro i
          simp only [ix, Nat.mod_mod_of_dvd _ hd2]
          omega
        have hlane_card : ∀ v < 2, ((endsOf hk sites).filter (fun j => j.val % 2 = v)).card = sites.card := by
          intro v hv
          symm
          apply Finset.card_bij (fun i _ => if (ix hk (i.val + 1)).val % 2 = v then ix hk (i.val + 1) else ix hk (i.val + 2))
          · intro i hi
            have hpar := hpar_ix i
            simp only [Finset.mem_filter]
            split_ifs with h1
            · exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_insert_self _ _⟩, h1⟩
            · exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, by omega⟩
          · intro i1 hi1 i2 hi2 heq
            by_contra hne
            have hdisj := pair_disjoint hk1 hsp hi1 hi2 hne
            rw [Finset.disjoint_left] at hdisj
            apply hdisj (a := if (ix hk (i1.val + 1)).val % 2 = v then ix hk (i1.val + 1) else ix hk (i1.val + 2))
            · split_ifs <;> simp
            · rw [heq]; split_ifs <;> simp
          · intro u hu
            simp only [Finset.mem_filter] at hu
            rcases Finset.mem_biUnion.mp hu.1 with ⟨i, hi, hpu⟩
            refine ⟨i, hi, ?_⟩
            have hpar := hpar_ix i
            simp only [Finset.mem_insert, Finset.mem_singleton] at hpu
            rcases hpu with rfl | rfl
            · simp [hu.2]
            · have : (ix hk (i.val + 1)).val % 2 ≠ v := by omega
              simp [this]
        have hlane_lt3 : ∀ v < 2, ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk sites)).card < 3 := by
          intro v hv
          by_contra hge3
          have heq : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk sites) = Finset.range 3 :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simp; omega)
          have hall : ∀ j : Fin k, j.val % 2 = v → j ∈ endsOf hk sites := by
            intro j hj
            have hr : (j.val % 6) / 2 ∈ (Finset.range 3).filter (fun r => ∀ u : Fin k, u.val % 6 = 2 * r + v → u ∈ endsOf hk sites) := by
              rw [heq]; exact Finset.mem_range.mpr (by omega)
            exact (Finset.mem_filter.mp hr).2 j (by omega)
          have hsub : (Finset.univ : Finset (Fin k)).filter (fun j => j.val % 2 = v) ⊆
              (endsOf hk sites).filter (fun j => j.val % 2 = v) := by
            intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            exact ⟨hall j hj, hj⟩
          have hcard_half : ((Finset.univ : Finset (Fin k)).filter (fun j => j.val % 2 = v)).card = k / 2 := by
            rw [← Fintype.card_fin (k / 2), ← Finset.card_univ]
            symm
            apply Finset.card_bij (fun (m : Fin (k / 2)) _ => (⟨2 * m.val + v, by omega⟩ : Fin k))
            · intro m _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
            · intro m1 _ m2 _ h; ext; have := congrArg Fin.val h; dsimp only at this; omega
            · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine ⟨⟨j.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩; ext; dsimp only; omega
          have hle := Finset.card_le_card hsub
          rw [hcard_half, hlane_card v hv] at hle
          omega
        by_cases hlaneCase : ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk sites)).card
        · simp only [hlaneCase, ↓reduceIte]
          let fullPhases (v : Nat) := (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk sites)
          have hphase_card : ∀ v < 2, ∀ r < 3, ((Finset.univ : Finset (Fin k)).filter (fun j => j.val % 6 = 2 * r + v)).card = k / 6 := by
            intro v hv r hr
            rw [← Fintype.card_fin (k / 6), ← Finset.card_univ]
            symm
            apply Finset.card_bij (fun (m : Fin (k / 6)) _ => (⟨6 * m.val + (2 * r + v), by omega⟩ : Fin k))
            · intro m _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
            · intro m1 _ m2 _ h; ext; have := congrArg Fin.val h; dsimp only at this; omega
            · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine ⟨⟨j.val / 6, by omega⟩, Finset.mem_univ _, ?_⟩; ext; dsimp only; omega
          have hkill_lane : ∀ (i0 : Fin k) (v : Nat), i0 ∈ sites → v < 2 →
              (∃ u ∈ ({ix hk (i0.val + 1), ix hk (i0.val + 2)} : Finset (Fin k)),
                u.val % 2 = v ∧ (u.val % 6) / 2 ∈ fullPhases v) →
              ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk (sites.erase i0))).card < 2 := by
            intro i0 v hi0 hv ⟨u, hu_pair, hu_par, hu_full⟩
            let r0 := (u.val % 6) / 2
            have hr0_not : ¬ (∀ j : Fin k, j.val % 6 = 2 * r0 + v → j ∈ endsOf hk (sites.erase i0)) := by
              intro h
              have hm := h u (by omega)
              rcases Finset.mem_biUnion.mp hm with ⟨i1, hi1, hp1⟩
              exact Finset.disjoint_left.mp (pair_disjoint hk1 hsp (Finset.mem_of_mem_erase hi1) hi0 (Finset.ne_of_mem_erase hi1)) hp1 hu_pair
            have hsub : (Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk (sites.erase i0)) ⊆
                (fullPhases v).erase r0 := by
              intro r hr
              simp only [Finset.mem_filter, Finset.mem_erase, fullPhases] at hr ⊢
              refine ⟨fun h => hr0_not (h ▸ hr.2), hr.1, fun j hj => ?_⟩
              rcases Finset.mem_biUnion.mp (hr.2 j hj) with ⟨i, hi, hp⟩
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_of_mem_erase hi, hp⟩
            have hle := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hu_full] at hle
            have hlt : (fullPhases v).card < 3 := hlane_lt3 v hv
            omega
          by_cases hboth : 2 ≤ (fullPhases 0).card ∧ 2 ≤ (fullPhases 1).card
          · let hit (v : Nat) : Finset (Fin k) := sites.filter (fun i =>
              ∃ u ∈ ({ix hk (i.val + 1), ix hk (i.val + 2)} : Finset (Fin k)),
                u.val % 2 = v ∧ (u.val % 6) / 2 ∈ fullPhases v)
            have hhit_card : ∀ v < 2, 2 ≤ (fullPhases v).card → 2 * (k / 6) ≤ (hit v).card := by
              intro v hv h2v
              let U := (Finset.univ : Finset (Fin k)).filter (fun u => u.val % 2 = v ∧ (u.val % 6) / 2 ∈ fullPhases v)
              have hU_card : (fullPhases v).card * (k / 6) ≤ U.card := by
                have hbiU : (fullPhases v).biUnion (fun r => (Finset.univ : Finset (Fin k)).filter (fun j => j.val % 6 = 2 * r + v)) ⊆ U := by
                  intro u hu
                  rcases Finset.mem_biUnion.mp hu with ⟨r, hr, hu'⟩
                  simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hu' ⊢
                  have hr3 : r < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
                  exact ⟨by omega, by rwa [show (u.val % 6) / 2 = r by omega]⟩
                have hdisjU : ((fullPhases v) : Set Nat).PairwiseDisjoint
                    (fun r => (Finset.univ : Finset (Fin k)).filter (fun j => j.val % 6 = 2 * r + v)) := by
                  intro r1 hr1 r2 hr2 hne
                  rw [Function.onFun, Finset.disjoint_left]
                  intro u h1 h2
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
                  have hr1' : r1 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr1).1
                  have hr2' : r2 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr2).1
                  omega
                have h1 := Finset.card_le_card hbiU
                rw [Finset.card_biUnion hdisjU] at h1
                have hsum : ∑ r ∈ fullPhases v, ((Finset.univ : Finset (Fin k)).filter (fun j => j.val % 6 = 2 * r + v)).card =
                    (fullPhases v).card * (k / 6) := by
                  rw [Finset.sum_congr rfl (fun r hr => hphase_card v hv r (Finset.mem_range.mp (Finset.mem_filter.mp hr).1))]
                  rw [Finset.sum_const, smul_eq_mul]
                omega
              have hU_le : U.card ≤ (hit v).card := by
                have hex_i : ∀ u ∈ U, ∃ i ∈ hit v, u ∈ ({ix hk (i.val + 1), ix hk (i.val + 2)} : Finset (Fin k)) := by
                  intro u hu
                  simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hu
                  have hr_full := (Finset.mem_filter.mp hu.2).2
                  have hu_ends : u ∈ endsOf hk sites := hr_full u (by omega)
                  rcases Finset.mem_biUnion.mp hu_ends with ⟨i, hi, hp⟩
                  exact ⟨i, Finset.mem_filter.mpr ⟨hi, u, hp, hu.1, hu.2⟩, hp⟩
                let f : Fin k → Fin k := fun i =>
                  if (ix hk (i.val + 1)).val % 2 = v then ix hk (i.val + 1) else ix hk (i.val + 2)
                have hU_sub : U ⊆ (hit v).image f := by
                  intro u hu
                  rcases hex_i u hu with ⟨i, hi, hp⟩
                  have hu_par : u.val % 2 = v := (Finset.mem_filter.mp hu).2.1
                  have hpar := hpar_ix i
                  refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                  rcases hp with rfl | rfl
                  · simp [f, hu_par]
                  · have : (ix hk (i.val + 1)).val % 2 ≠ v := by omega
                    simp [f, this]
                exact (Finset.card_le_card hU_sub).trans Finset.card_image_le
              have hmul : 2 * (k / 6) ≤ (fullPhases v).card * (k / 6) := Nat.mul_le_mul_right _ h2v
              omega
            have h0c := hhit_card 0 (by omega) hboth.1
            have h1c := hhit_card 1 (by omega) hboth.2
            have hinter_pos : 0 < (hit 0 ∩ hit 1).card := by
              have hu := Finset.card_union_add_card_inter (hit 0) (hit 1)
              have hsub : hit 0 ∪ hit 1 ⊆ sites := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
              have hle := Finset.card_le_card hsub
              have hkdiv : 6 * (k / 6) = k := Nat.mul_div_cancel' hd6
              omega
            obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hinter_pos
            have hi0_0 : i0 ∈ hit 0 := (Finset.mem_inter.mp hi0).1
            have hi0_1 : i0 ∈ hit 1 := (Finset.mem_inter.mp hi0).2
            have hi0_s : i0 ∈ sites := (Finset.mem_filter.mp hi0_0).1
            refine ⟨sites.erase i0, Finset.erase_subset i0 sites, by rw [Finset.card_erase_of_mem hi0_s], ?_⟩
            intro c hc hsupp
            by_contra hne
            rcases hfull_lane_of_c hc hsupp hne with ⟨v, hv, h2⟩
            have hv01 : v = 0 ∨ v = 1 := by simp only [Finset.mem_range] at hv; omega
            rcases hv01 with rfl | rfl
            · have := hkill_lane i0 0 hi0_s (by omega) (Finset.mem_filter.mp hi0_0).2; omega
            · have := hkill_lane i0 1 hi0_s (by omega) (Finset.mem_filter.mp hi0_1).2; omega
          · rcases hlaneCase with ⟨v0, hv0, h2v0⟩
            have hv0_lt : v0 < 2 := Finset.mem_range.mp hv0
            change 2 ≤ (fullPhases v0).card at h2v0
            obtain ⟨r0, hr0⟩ := Finset.card_pos.mp (by omega : 0 < (fullPhases v0).card)
            have hr0_lt : r0 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr0).1
            have hr0_full := (Finset.mem_filter.mp hr0).2
            have hu_mem : (⟨2 * r0 + v0, by omega⟩ : Fin k) ∈ endsOf hk sites :=
              hr0_full ⟨2 * r0 + v0, by omega⟩ (by dsimp only; exact Nat.mod_eq_of_lt (by omega))
            rcases Finset.mem_biUnion.mp hu_mem with ⟨i0, hi0, hp0⟩
            refine ⟨sites.erase i0, Finset.erase_subset i0 sites, by rw [Finset.card_erase_of_mem hi0], ?_⟩
            intro c hc hsupp
            by_contra hne
            rcases hfull_lane_of_c hc hsupp hne with ⟨v, hv, h2⟩
            have hv_lt : v < 2 := Finset.mem_range.mp hv
            by_cases hvv0 : v = v0
            · subst hvv0
              have hkill := hkill_lane i0 v hi0 hv_lt
                ⟨⟨2 * r0 + v, by omega⟩, hp0, by dsimp only; omega, by
                  dsimp only; rwa [show ((2 * r0 + v) % 6) / 2 = r0 by omega]⟩
              omega
            ·
              have hle_sites : ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk (sites.erase i0))).card ≤
                  (fullPhases v).card := by
                apply Finset.card_le_card
                intro r hr; simp only [Finset.mem_filter, fullPhases] at hr ⊢
                refine ⟨hr.1, fun j hj => ?_⟩
                rcases Finset.mem_biUnion.mp (hr.2 j hj) with ⟨i, hi, hp⟩
                exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_of_mem_erase hi, hp⟩
              have hv_lt2 : (fullPhases v).card < 2 := by
                by_contra hge2
                have hv01 : v = 0 ∧ v0 = 1 ∨ v = 1 ∧ v0 = 0 := by omega
                rcases hv01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hboth ⟨by omega, by omega⟩
              omega
        · simp only [hlaneCase, ↓reduceIte]
          refine ⟨sites, Finset.Subset.refl _, by omega, ?_⟩
          intro c hc hsupp
          by_contra hne
          exact hlaneCase (hfull_lane_of_c hc hsupp hne)
  · simp only [hd3, not_false_eq_true, ↓reduceIte]
    refine ⟨sites, Finset.Subset.refl _, by omega, ?_⟩
    intro c hc _
    exact ker_mix_eq_zero_of_not_dvd3 hk hd3 hc

lemma walkLeaf_branch {k : Nat} (nodes : Finset (List Bool))
    (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
    (raw : Fin k → F2) (j : Nat) (hj : j < (walkLeaf nodes ask bias raw).length) :
    let p := walkLeaf nodes ask bias raw
    decide (ask (p.take j) raw + bias (p.take j) ≠ 0) = p[j] := by
  let p := walkLeaf nodes ask bias raw
  change j < p.length at hj
  let step : List Bool → List Bool := fun q =>
    if q ∈ nodes then q ++ [decide (ask q raw + bias q ≠ 0)] else q
  have hfold : ∀ (m : Nat) (q : List Bool),
      ((List.range m).foldl (fun r _ => step r) q) = step^[m] q := by
    intro m; induction m with
    | zero => intro q; rfl
    | succ m ih => intro q; rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, Function.iterate_succ_apply']
  have hp_eq : step^[nodes.card] [] = p := (hfold nodes.card []).symm
  have hplen : p.length ≤ nodes.card := by
    have hle : ∀ a, (step^[a] []).length ≤ a := by
      intro a; induction a with
      | zero => simp
      | succ a iha =>
        rw [Function.iterate_succ_apply']
        change (if step^[a] [] ∈ nodes then step^[a] [] ++ [decide (ask (step^[a] []) raw + bias (step^[a] []) ≠ 0)] else step^[a] []).length ≤ a + 1
        split_ifs
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · omega
    rw [← hp_eq]; exact hle nodes.card
  have hgen : ∀ a b, a ≤ b → step^[a] [] <+: step^[b] [] := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => simp
    | succ d ihd =>
      rw [show a + (d + 1) = (a + d) + 1 by omega, Function.iterate_succ_apply']
      apply List.IsPrefix.trans (ihd (by omega))
      dsimp only [step]; split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
  have hstep_len : ∀ m ≤ p.length, step^[m] [] = p.take m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hmem : p.take m ∈ nodes := by
        apply (walkLeaf_prefixes_and_fiber nodes ask bias raw).1 (p.take m) (List.take_prefix m p)
        intro h
        change p.take m = p at h
        have hlen := congrArg List.length h
        have hmle : m ≤ p.length := by omega
        rw [List.length_take_of_le hmle] at hlen
        omega
      have h1 : step^[m + 1] [] <+: p := hp_eq ▸ hgen (m + 1) nodes.card (by omega)
      rw [Function.iterate_succ_apply', ih (by omega)] at h1
      change (if p.take m ∈ nodes then p.take m ++ [decide (ask (p.take m) raw + bias (p.take m) ≠ 0)] else p.take m) <+: p at h1
      rw [if_pos hmem] at h1
      change (if p.take m ∈ nodes then p.take m ++ [decide (ask (p.take m) raw + bias (p.take m) ≠ 0)] else p.take m) = p.take (m + 1)
      rw [if_pos hmem]
      rcases h1 with ⟨t, ht⟩
      have hlen1 : (p.take m ++ [decide (ask (p.take m) raw + bias (p.take m) ≠ 0)]).length = m + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_take_of_le (by omega : m ≤ p.length)]
      have htake := congrArg (List.take (m + 1)) ht
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at htake
      exact htake
  have hj1 := hstep_len (j + 1) (by omega)
  have hj0 := hstep_len j (by omega)
  rw [Function.iterate_succ_apply', hj0] at hj1
  have hmem : p.take j ∈ nodes := by
    apply (walkLeaf_prefixes_and_fiber nodes ask bias raw).1 (p.take j) (List.take_prefix j p)
    intro h
    change p.take j = p at h
    have hlen := congrArg List.length h
    have hjle : j ≤ p.length := by omega
    rw [List.length_take_of_le hjle] at hlen
    omega
  change (if p.take j ∈ nodes then p.take j ++ [decide (ask (p.take j) raw + bias (p.take j) ≠ 0)] else p.take j) = p.take (j + 1) at hj1
  rw [if_pos hmem] at hj1
  have hget := congrArg (fun l => l[j]?) hj1
  have hjle : j ≤ p.length := by omega
  rw [List.getElem?_append_right (by rw [List.length_take_of_le hjle]),
      List.length_take_of_le hjle, Nat.sub_self,
      List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj] at hget
  simpa using hget

lemma lower_bound {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (sites : Finset (Fin k)) (e L : Nat)
    (hsp : 1 < k → ∀ i ∈ sites, ix hk (i.val + 1) ∉ sites)
    (nodes : Finset (List Bool))
    (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
    (aff : List Bool → (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : List Bool → Fin k → F2)
    (hL : nodes.card < L)
    (herr : ∀ x : Fin k → F2,
      (sites.filter (fun i =>
        (aff (walkLeaf nodes ask bias x) x + c (walkLeaf nodes ask bias x)) i ≠
          let old := rot hk s x + name
          let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
          y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t x i + constant i)).card ≤ e) :
    let ends := endsOf hk sites
    let full := fun (p r : Nat) => ∀ j : Fin k, j.val % p = r → j ∈ ends
    let oddCase := 2 ≤ ((Finset.range 3).filter (fun r => full 3 r)).card
    let laneCase := ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => full 6 (2 * r + v))).card
    let save := if ¬ 3 ∣ k then 0 else if k % 2 = 1 then (if oddCase then 1 else 0)
      else if 2 * sites.card = k then 2 else if laneCase then 1 else 0
    (if k = 1 then 1 else 2 ^ (sites.card - e - save)) ≤ L := by
  classical
  dsimp only
  by_cases hk1 : k = 1
  · simp only [hk1, ↓reduceIte]; omega
  · simp only [hk1, ↓reduceIte]
    have hgt1 : 1 < k := by omega
    have hsp' := hsp hgt1
    let ends := endsOf hk sites
    let full := fun (p r : Nat) => ∀ j : Fin k, j.val % p = r → j ∈ ends
    let oddCase := 2 ≤ ((Finset.range 3).filter (fun r => full 3 r)).card
    let laneCase := ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => full 6 (2 * r + v))).card
    let save := if ¬ 3 ∣ k then 0 else if k % 2 = 1 then (if oddCase then 1 else 0)
      else if 2 * sites.card = k then 2 else if laneCase then 1 else 0
    let D := sites.card - e - save
    change 2 ^ D ≤ L
    have hDk : D ≤ k := by
      have : sites.card ≤ k := by simpa using Finset.card_le_univ sites
      omega
    obtain ⟨sites0, hsites0_sub, hsites0_card, hsites0_noker⟩ := exists_indep_sites hgt1 sites hsp'
    have hsites0_sp : ∀ i ∈ sites0, ix hk (i.val + 1) ∉ sites0 :=
      fun i hi hm => hsp' i (hsites0_sub hi) (hsites0_sub hm)
    have hsites0_surj := surj_pairs_of_no_ker hgt1 s hsites0_sp hsites0_noker
    let leaves : Finset (List Bool) := (Finset.univ : Finset (Fin k → F2)).image (walkLeaf nodes ask bias)
    have hleaves_card : leaves.card ≤ nodes.card + 1 := by
      apply card_leaves_le_nodes_add_one nodes leaves
      · intro p hp
        rcases Finset.mem_image.mp hp with ⟨x, _, rfl⟩
        exact walkLeaf_not_mem nodes ask bias x
      · intro p hp q hqp hne
        rcases Finset.mem_image.mp hp with ⟨x, _, rfl⟩
        exact (walkLeaf_prefixes_and_fiber nodes ask bias x).1 q hqp hne
      · intro p hp q hq hpq
        by_contra hne
        rcases Finset.mem_image.mp hp with ⟨x, _, rfl⟩
        rcases Finset.mem_image.mp hq with ⟨y, _, rfl⟩
        exact walkLeaf_not_mem nodes ask bias x ((walkLeaf_prefixes_and_fiber nodes ask bias y).1 _ hpq hne)

    have hfiber_le : ∀ p ∈ leaves,
        ((Finset.univ : Finset (Fin k → F2)).filter (fun x => walkLeaf nodes ask bias x = p)).card ≤ 2 ^ (k - D) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨x0, _, rfl⟩
      let p := walkLeaf nodes ask bias x0
      let T : Submodule F2 (Fin k → F2) :=
        ⨅ j : Fin p.length, LinearMap.ker (ask (p.take j.val))

      have hfib_sub : (Finset.univ : Finset (Fin k → F2)).filter (fun x => walkLeaf nodes ask bias x = p) ⊆
          (Finset.univ : Finset T).image (fun v => x0 + v.1) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hvT : x - x0 ∈ T := by
          simp only [T, Submodule.mem_iInf, LinearMap.mem_ker, map_sub]
          intro j
          have hb1 : decide (ask (p.take j.val) x + bias (p.take j.val) ≠ 0) = p[j.val] := by
            have h := walkLeaf_branch nodes ask bias x j.val (by rw [hx]; exact j.isLt)
            simpa [hx] using h
          have hb0 : decide (ask (p.take j.val) x0 + bias (p.take j.val) ≠ 0) = p[j.val] :=
            walkLeaf_branch nodes ask bias x0 j.val j.isLt
          have heq_dec : decide (ask (p.take j.val) x + bias (p.take j.val) ≠ 0) =
              decide (ask (p.take j.val) x0 + bias (p.take j.val) ≠ 0) := hb1.trans hb0.symm
          have hiff : ask (p.take j.val) x + bias (p.take j.val) ≠ 0 ↔
              ask (p.take j.val) x0 + bias (p.take j.val) ≠ 0 :=
            decide_eq_decide.mp heq_dec
          rcases f2_cases (ask (p.take j.val) x) with h1 | h1 <;>
          rcases f2_cases (ask (p.take j.val) x0) with h2 | h2 <;>
          rcases f2_cases (bias (p.take j.val)) with hb | hb <;>
          rw [h1, h2, hb] at hiff <;>
          rw [h1, h2] <;>
          first | decide | (exfalso; revert hiff; decide)
        exact Finset.mem_image.mpr ⟨⟨x - x0, hvT⟩, Finset.mem_univ _, by dsimp only; abel⟩

      have hfin_bound : Module.finrank F2 T ≤ k := by
        simpa [Module.finrank_pi_fintype, Fintype.card_fin] using Submodule.finrank_le T
      have hfin_le : Module.finrank F2 T ≤ k - D := by
        by_contra hgt
        have hd_lt : k - Module.finrank F2 T < D := by omega
        obtain ⟨fs, hfs_len, hfs_mem⟩ := exists_ker_list_of_submodule T
        obtain ⟨J', hJ'sub, hJ'card, hJ'surj⟩ := surj_restrict_list hk s fs sites0 hsites0_surj
        have hJ'ge : e + 1 ≤ J'.card := by
          have hsc : sites.card - save ≤ sites0.card := hsites0_card
          dsimp only [D] at hd_lt
          omega

        have hTsurj : Function.Surjective (fun (v : T) (q : J' × Bool) =>
            mix hk (rotLin hk s v.1) (if q.2 then ix hk (q.1.1.val + 2) else ix hk (q.1.1.val + 1))) := by
          intro z
          obtain ⟨⟨v, hv⟩, hzv⟩ := hJ'surj z
          exact ⟨⟨v, (hfs_mem v).mpr hv⟩, hzv⟩
        obtain ⟨v, hv_fail⟩ := exists_all_fail_of_surj hk s t name constant J' x0 T (aff p) (c p) hTsurj
        have hwalk_v : walkLeaf nodes ask bias (x0 + v.1) = p := by
          apply (walkLeaf_prefixes_and_fiber nodes ask bias x0).2 v.1
          intro j hj
          have hvmem := v.2
          simp only [T, Submodule.mem_iInf, LinearMap.mem_ker] at hvmem
          exact hvmem ⟨j, hj⟩
        have herr_v := herr (x0 + v.1)
        rw [hwalk_v] at herr_v
        have hsub_err : J' ⊆ sites.filter (fun i =>
            (aff p (x0 + v.1) + c p) i ≠
              let old := rot hk s (x0 + v.1) + name
              let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
              y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t (x0 + v.1) i + constant i) := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨hsites0_sub (hJ'sub hi), hv_fail i hi⟩
        have hle := Finset.card_le_card hsub_err
        omega
      have hcard_T : Fintype.card T = 2 ^ Module.finrank F2 T := by
        simpa [ZMod.card] using Module.card_eq_pow_finrank (K := F2) (V := T)
      calc ((Finset.univ : Finset (Fin k → F2)).filter (fun x => walkLeaf nodes ask bias x = p)).card
          ≤ ((Finset.univ : Finset T).image (fun v => x0 + v.1)).card := Finset.card_le_card hfib_sub
        _ ≤ (Finset.univ : Finset T).card := Finset.card_image_le
        _ = 2 ^ Module.finrank F2 T := by simpa using hcard_T
        _ ≤ 2 ^ (k - D) := Nat.pow_le_pow_right (by omega) hfin_le

    have hsum_fib : 2 ^ k ≤ leaves.card * 2 ^ (k - D) := by
      have hpart : (Finset.univ : Finset (Fin k → F2)).card =
          ∑ p ∈ leaves, ((Finset.univ : Finset (Fin k → F2)).filter (fun x => walkLeaf nodes ask bias x = p)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext x; simp [leaves]
        · intro p1 _ p2 _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro x h1 h2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          exact hne (h1.symm.trans h2)
      have hcardW : (Finset.univ : Finset (Fin k → F2)).card = 2 ^ k := by simp
      rw [hcardW] at hpart
      rw [hpart]
      calc ∑ p ∈ leaves, ((Finset.univ : Finset (Fin k → F2)).filter (fun x => walkLeaf nodes ask bias x = p)).card
          ≤ ∑ _p ∈ leaves, 2 ^ (k - D) := Finset.sum_le_sum hfiber_le
        _ = leaves.card * 2 ^ (k - D) := by simp [Finset.sum_const]
    have hpow_split : 2 ^ k = 2 ^ D * 2 ^ (k - D) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hDk]
    rw [hpow_split] at hsum_fib
    have h2pos : 0 < 2 ^ (k - D) := Nat.pow_pos (by omega)
    have h2D_le : 2 ^ D ≤ leaves.card := Nat.le_of_mul_le_mul_right hsum_fib h2pos
    omega

def allListsOfLen : Nat → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (allListsOfLen n).image (false :: ·) ∪ (allListsOfLen n).image (true :: ·)

lemma mem_allListsOfLen (n : Nat) (l : List Bool) : l ∈ allListsOfLen n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allListsOfLen]
  | succ n ih =>
    simp only [allListsOfLen, Finset.mem_union, Finset.mem_image, ih]
    cases l with
    | nil => simp
    | cons b t =>
      cases b <;> simp

lemma card_allListsOfLen (n : Nat) : (allListsOfLen n).card = 2 ^ n := by
  induction n with
  | zero => simp [allListsOfLen]
  | succ n ih =>
    simp only [allListsOfLen]
    have hdisj : Disjoint ((allListsOfLen n).image (false :: ·)) ((allListsOfLen n).image (true :: ·)) := by
      rw [Finset.disjoint_left]; intro l h1 h2
      rcases Finset.mem_image.mp h1 with ⟨t1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨t2, _, h⟩
      simp at h
    rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ List.cons_injective,
        Finset.card_image_of_injective _ List.cons_injective, ih]
    ring

def allListsLt : Nat → Finset (List Bool)
  | 0 => ∅
  | n + 1 => allListsLt n ∪ allListsOfLen n

lemma mem_allListsLt (n : Nat) (l : List Bool) : l ∈ allListsLt n ↔ l.length < n := by
  induction n with
  | zero => simp [allListsLt]
  | succ n ih =>
    simp only [allListsLt, Finset.mem_union, ih, mem_allListsOfLen]
    omega

lemma card_allListsLt (n : Nat) : (allListsLt n).card = 2 ^ n - 1 := by
  induction n with
  | zero => simp [allListsLt]
  | succ n ih =>
    simp only [allListsLt]
    have hdisj : Disjoint (allListsLt n) (allListsOfLen n) := by
      rw [Finset.disjoint_left]; intro l h1 h2
      rw [mem_allListsLt] at h1; rw [mem_allListsOfLen] at h2; omega
    rw [Finset.card_union_of_disjoint hdisj, ih, card_allListsOfLen]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    rw [Nat.pow_succ]; omega

lemma walkLeaf_query_tree {k : Nat} (qs : List ((Fin k → F2) →ₗ[F2] F2)) (raw : Fin k → F2) :
    walkLeaf (allListsLt qs.length) (fun p => qs.getD p.length 0) (fun _ => 0) raw =
      qs.map (fun q => decide (q raw ≠ 0)) := by
  let nodes := allListsLt qs.length
  let ask : List Bool → (Fin k → F2) →ₗ[F2] F2 := fun p => qs.getD p.length 0
  let step : List Bool → List Bool := fun p =>
    if p ∈ nodes then p ++ [decide (ask p raw + 0 ≠ 0)] else p
  have hfold : ∀ (m : Nat) (p : List Bool),
      ((List.range m).foldl (fun q _ => step q) p) = step^[m] p := by
    intro m; induction m with
    | zero => intro p; rfl
    | succ m ih => intro p; rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, Function.iterate_succ_apply']
  change ((List.range nodes.card).foldl (fun q _ => step q) []) = _
  rw [hfold]
  have htake : ∀ m ≤ qs.length, step^[m] [] = (qs.take m).map (fun q => decide (q raw ≠ 0)) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hlen : ((qs.take m).map (fun q => decide (q raw ≠ 0))).length = m := by
        simp; omega
      have hmem : (qs.take m).map (fun q => decide (q raw ≠ 0)) ∈ nodes := by
        rw [mem_allListsLt, hlen]; omega
      simp only [step, hmem, ↓reduceIte, ask, hlen, add_zero]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega : m < qs.length), Option.toList_some,
          List.map_append, List.map_singleton, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : m < qs.length), Option.getD_some]
  have hfix : ∀ a, qs.length ≤ a → step^[a] [] = qs.map (fun q => decide (q raw ≠ 0)) := by
    intro a ha
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
    induction d with
    | zero => simpa using htake qs.length (le_refl _)
    | succ d ih =>
      rw [show qs.length + (d + 1) = (qs.length + d) + 1 by omega, Function.iterate_succ_apply', ih (by omega)]
      have hnot : qs.map (fun q => decide (q raw ≠ 0)) ∉ nodes := by
        rw [mem_allListsLt]; simp
      change (if qs.map (fun q => decide (q raw ≠ 0)) ∈ nodes then _ else qs.map (fun q => decide (q raw ≠ 0))) = _
      rw [if_neg hnot]
  have hcard_ge : qs.length ≤ nodes.card := by
    rw [card_allListsLt]
    have hpow : qs.length < 2 ^ qs.length := Nat.lt_two_pow_self (n := qs.length)
    omega
  exact hfix nodes.card hcard_ge

lemma approx_point_err (y1 y2 a b : F2) :
    ((b + 1) * y1 + a * y2 + (a + 1) * (b + 1) ≠ (1 + y1) * y2) ↔ (y1 = a ∧ y2 = b) := by
  rcases f2_cases y1 with rfl | rfl <;>
  rcases f2_cases y2 with rfl | rfl <;>
  rcases f2_cases a with rfl | rfl <;>
  rcases f2_cases b with rfl | rfl <;> decide

lemma approx_eq_of_y1 (y1 y2 a : F2) (h : y1 = a) : (1 + a) * y2 = (1 + y1) * y2 := by rw [h]
lemma approx_eq_of_y2 (y1 y2 b : F2) (h : y2 = b) : (1 + y1) * b = (1 + y1) * y2 := by rw [h]
lemma approx_eq_of_sum (y1 y2 c : F2) (h : y1 + y2 = c) : c * y2 = (1 + y1) * y2 := by
  rcases f2_cases y1 with rfl | rfl <;>
  rcases f2_cases y2 with rfl | rfl <;>
  rcases f2_cases c with rfl | rfl <;> simp_all <;> decide

def mkSiteAff {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (c1 c2 c0 : Fin k → F2) : ((Fin k → F2) →ₗ[F2] (Fin k → F2)) × (Fin k → F2) :=
  let yLin : (Fin k → F2) →ₗ[F2] (Fin k → F2) := (mix hk).comp (rotLin hk s)
  let yConst : Fin k → F2 := mix hk name
  let aff : (Fin k → F2) →ₗ[F2] (Fin k → F2) := {
    toFun := fun raw i =>
      yLin raw i + c1 i * yLin raw (ix hk (i.val + 1)) + c2 i * yLin raw (ix hk (i.val + 2)) + rotLin hk t raw i
    map_add' := fun x y => by funext i; simp [map_add, mul_add]; ring
    map_smul' := fun r x => by funext i; simp [map_smul, smul_eq_mul]; ring
  }
  let c : Fin k → F2 := fun i =>
    yConst i + c1 i * yConst (ix hk (i.val + 1)) + c2 i * yConst (ix hk (i.val + 2)) + c0 i + constant i
  (aff, c)

lemma mkSiteAff_eval_iff {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (c1 c2 c0 : Fin k → F2) (raw : Fin k → F2) (i : Fin k) :
    let ac := mkSiteAff hk s t name constant c1 c2 c0
    let old := rot hk s raw + name
    let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
    (ac.1 raw + ac.2) i ≠ y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t raw i + constant i ↔
      c1 i * y (ix hk (i.val + 1)) + c2 i * y (ix hk (i.val + 2)) + c0 i ≠
        (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) := by
  dsimp only [mkSiteAff, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, LinearMap.comp_apply]
  have hy : ∀ u : Fin k,
      mix hk (rotLin hk s raw) u + mix hk name u =
        rot hk s raw u + name u + (rot hk s raw (ix hk (u.val + 2)) + name (ix hk (u.val + 2))) +
        (rot hk s raw (ix hk (u.val + k - 2 % k)) + name (ix hk (u.val + k - 2 % k))) := by
    intro u
    have h1 : mix hk (rotLin hk s raw) u + mix hk name u = mix hk (rotLin hk s raw + name) u := by
      rw [map_add]; rfl
    rw [h1]; rfl
  change mix hk (rotLin hk s raw) i + c1 i * mix hk (rotLin hk s raw) (ix hk (i.val + 1)) +
      c2 i * mix hk (rotLin hk s raw) (ix hk (i.val + 2)) + rotLin hk t raw i +
      (mix hk name i + c1 i * mix hk name (ix hk (i.val + 1)) +
        c2 i * mix hk name (ix hk (i.val + 2)) + c0 i + constant i) ≠ _ ↔ _
  rw [← hy i, ← hy (ix hk (i.val + 1)), ← hy (ix hk (i.val + 2))]
  have hrot : rotLin hk t raw i = rot hk t raw i := rfl
  rw [hrot]
  constructor <;> intro h heq <;> apply h
  · have h1 : mix hk (rotLin hk s raw) i + c1 i * mix hk (rotLin hk s raw) (ix hk (i.val + 1)) +
        c2 i * mix hk (rotLin hk s raw) (ix hk (i.val + 2)) + rot hk t raw i +
        (mix hk name i + c1 i * mix hk name (ix hk (i.val + 1)) +
          c2 i * mix hk name (ix hk (i.val + 2)) + c0 i + constant i) =
        (mix hk (rotLin hk s raw) i + mix hk name i) +
        (c1 i * (mix hk (rotLin hk s raw) (ix hk (i.val + 1)) + mix hk name (ix hk (i.val + 1))) +
          c2 i * (mix hk (rotLin hk s raw) (ix hk (i.val + 2)) + mix hk name (ix hk (i.val + 2))) + c0 i) +
        rot hk t raw i + constant i := by ring
    rw [h1, heq]
  · have h1 : mix hk (rotLin hk s raw) i + c1 i * mix hk (rotLin hk s raw) (ix hk (i.val + 1)) +
        c2 i * mix hk (rotLin hk s raw) (ix hk (i.val + 2)) + rot hk t raw i +
        (mix hk name i + c1 i * mix hk name (ix hk (i.val + 1)) +
          c2 i * mix hk name (ix hk (i.val + 2)) + c0 i + constant i) =
        (mix hk (rotLin hk s raw) i + mix hk name i) +
        (c1 i * (mix hk (rotLin hk s raw) (ix hk (i.val + 1)) + mix hk name (ix hk (i.val + 1))) +
          c2 i * (mix hk (rotLin hk s raw) (ix hk (i.val + 2)) + mix hk name (ix hk (i.val + 2))) + c0 i) +
        rot hk t raw i + constant i := by ring
    rw [h1] at heq
    have := congrArg (· + (mix hk (rotLin hk s raw) i + mix hk name i) + rot hk t raw i + constant i) heq

    have hcancel : ∀ x y z : F2, x + z = y + z → x = y := fun x y z h => by
      have := congrArg (· + z) h; simpa [add_assoc, f2_add_self] using this
    apply hcancel _ _ ((mix hk (rotLin hk s raw) i + mix hk name i) + rot hk t raw i + constant i)
    linear_combination heq

lemma exists_tree_of_queries {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (sites : Finset (Fin k)) (e L : Nat)
    (qs : List ((Fin k → F2) →ₗ[F2] F2)) (hqsL : 2 ^ qs.length ≤ L)
    (c1 c2 c0 : List Bool → Fin k → F2)
    (herr : ∀ x : Fin k → F2,
      let p := qs.map (fun q => decide (q x ≠ 0))
      let old := rot hk s x + name
      let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
      (sites.filter (fun i =>
        c1 p i * y (ix hk (i.val + 1)) + c2 p i * y (ix hk (i.val + 2)) + c0 p i ≠
          (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)))).card ≤ e) :
    ∃ (nodes : Finset (List Bool))
      (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
      (aff : List Bool → (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : List Bool → Fin k → F2),
      nodes.card < L ∧ ∀ x : Fin k → F2,
        (sites.filter (fun i =>
          (aff (walkLeaf nodes ask bias x) x + c (walkLeaf nodes ask bias x)) i ≠
            let old := rot hk s x + name
            let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
            y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t x i + constant i)).card ≤ e := by
  refine ⟨allListsLt qs.length, fun p => qs.getD p.length 0, fun _ => 0,
          fun p => (mkSiteAff hk s t name constant (c1 p) (c2 p) (c0 p)).1,
          fun p => (mkSiteAff hk s t name constant (c1 p) (c2 p) (c0 p)).2, ?_, ?_⟩
  · rw [card_allListsLt]
    have hpos : 1 ≤ 2 ^ qs.length := Nat.one_le_pow _ 2 (by omega)
    omega
  · intro x
    rw [walkLeaf_query_tree]
    have h := herr x
    have hfilt : sites.filter (fun i =>
        ((mkSiteAff hk s t name constant (c1 (qs.map fun q => decide (q x ≠ 0)))
          (c2 (qs.map fun q => decide (q x ≠ 0))) (c0 (qs.map fun q => decide (q x ≠ 0)))).1 x +
         (mkSiteAff hk s t name constant (c1 (qs.map fun q => decide (q x ≠ 0)))
          (c2 (qs.map fun q => decide (q x ≠ 0))) (c0 (qs.map fun q => decide (q x ≠ 0)))).2) i ≠
          let old := rot hk s x + name
          let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
          y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t x i + constant i) =
        sites.filter (fun i =>
          c1 (qs.map fun q => decide (q x ≠ 0)) i *
            (let old := rot hk s x + name; fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))) (ix hk (i.val + 1)) +
          c2 (qs.map fun q => decide (q x ≠ 0)) i *
            (let old := rot hk s x + name; fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))) (ix hk (i.val + 2)) +
          c0 (qs.map fun q => decide (q x ≠ 0)) i ≠
            (1 + (let old := rot hk s x + name; fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))) (ix hk (i.val + 1))) *
            (let old := rot hk s x + name; fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))) (ix hk (i.val + 2))) := by
      apply Finset.filter_congr
      intro i _
      exact mkSiteAff_eval_iff hk s t name constant _ _ _ x i
    rw [hfilt]
    exact h

def yLinAt {k : Nat} (hk : 0 < k) (s : Nat) (u : Fin k) : (Fin k → F2) →ₗ[F2] F2 where
  toFun raw := mix hk (rotLin hk s raw) u
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp [map_smul]

lemma y_eq_yLinAt {k : Nat} (hk : 0 < k) (s : Nat) (name raw : Fin k → F2) (u : Fin k) :
    (let old := rot hk s raw + name
     old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))) =
      yLinAt hk s u raw + mix hk name u := by
  have : mix hk (rot hk s raw + name) u = mix hk (rotLin hk s raw) u + mix hk name u := by
    rw [map_add]; rfl
  exact this

def queryVal (b : Bool) : F2 := if b then 1 else 0

lemma queryVal_decide (a : F2) : queryVal (decide (a ≠ 0)) = a := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma upper_bound_save0 {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (sites : Finset (Fin k)) (e L : Nat) (hL : 2 ^ (sites.card - e) ≤ L) :
    ∃ (nodes : Finset (List Bool))
      (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
      (aff : List Bool → (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : List Bool → Fin k → F2),
      nodes.card < L ∧ ∀ x : Fin k → F2,
        (sites.filter (fun i =>
          (aff (walkLeaf nodes ask bias x) x + c (walkLeaf nodes ask bias x)) i ≠
            let old := rot hk s x + name
            let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
            y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t x i + constant i)).card ≤ e := by
  classical
  let D := sites.card - e
  let sl := sites.toList
  have hsl_len : sl.length = sites.card := Finset.length_toList sites
  let ql := sl.take D
  have hql_len : ql.length = D := by simp [ql, hsl_len, D]
  let qs : List ((Fin k → F2) →ₗ[F2] F2) := ql.map (fun i => yLinAt hk s (ix hk (i.val + 1)))
  have hqs_len : qs.length = D := by simp [qs, hql_len]

  let c1 : List Bool → Fin k → F2 := fun _ _ => 0
  let c2 : List Bool → Fin k → F2 := fun p i =>
    match ql.idxOf? i with
    | some idx => 1 + (queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 1)))
    | none => 0
  let c0 : List Bool → Fin k → F2 := fun _ _ => 0
  apply exists_tree_of_queries hk s t name constant sites e L qs (by rw [hqs_len]; exact hL) c1 c2 c0
  intro x

  have hsub : sites.filter (fun i =>
      let p := qs.map (fun q => decide (q x ≠ 0))
      let old := rot hk s x + name
      let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
      c1 p i * y (ix hk (i.val + 1)) + c2 p i * y (ix hk (i.val + 2)) + c0 p i ≠
        (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2))) ⊆ sites \ ql.toFinset := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    refine Finset.mem_sdiff.mpr ⟨hi.1, fun hiq => ?_⟩
    have hiq' : i ∈ ql := List.mem_toFinset.mp hiq
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp hiq'
    have hnd : ql.Nodup := (Finset.nodup_toList sites).take
    have hidxOf : ql.idxOf? i = some idx := by
      rw [List.idxOf?_eq_some_iff]
      exact ⟨hidx_lt, hidx_eq, fun j hj => by
        intro hji; exact absurd (hnd.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
    apply hi.2
    simp only [c1, c2, c0, hidxOf, zero_mul, zero_add, add_zero]
    have hget : (qs.map (fun q => decide (q x ≠ 0))).getD idx false =
        decide (yLinAt hk s (ix hk (i.val + 1)) x ≠ 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_getElem hidx_lt]
      simp [qs, hidx_eq]
    rw [hget, queryVal_decide, y_eq_yLinAt hk s name x (ix hk (i.val + 1))]
  have hql_sub : ql.toFinset ⊆ sites := by
    intro i hi; exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  have hql_card : ql.toFinset.card = D := by
    rw [List.toFinset_card_of_nodup ((Finset.nodup_toList sites).take), hql_len]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hql_sub, hql_card] at hle
  dsimp only [D] at hle
  exact hle.trans (by omega)

lemma upper_bound_save1_of_ker {k : Nat} (hk1 : 1 < k) (s t : Nat) (name constant : Fin k → F2)
    (sites : Finset (Fin k)) (e L : Nat)
    (hsp : ∀ i ∈ sites, ix (by omega : 0 < k) (i.val + 1) ∉ sites)
    (c_ker : Fin k → F2) (hker : mix (by omega : 0 < k) c_ker = 0)
    (hsupp : ∀ u, u ∉ endsOf (by omega : 0 < k) sites → c_ker u = 0) (hne : c_ker ≠ 0)
    (hL : 2 ^ (sites.card - e - 1) ≤ L) :
    ∃ (nodes : Finset (List Bool))
      (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
      (aff : List Bool → (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : List Bool → Fin k → F2),
      nodes.card < L ∧ ∀ x : Fin k → F2,
        (sites.filter (fun i =>
          (aff (walkLeaf nodes ask bias x) x + c (walkLeaf nodes ask bias x)) i ≠
            let old := rot (by omega : 0 < k) s x + name
            let y := fun u : Fin k => old u + old (ix (by omega : 0 < k) (u.val + 2)) + old (ix (by omega : 0 < k) (u.val + k - 2 % k))
            y i + (1 + y (ix (by omega : 0 < k) (i.val + 1))) * y (ix (by omega : 0 < k) (i.val + 2)) + rot (by omega : 0 < k) t x i + constant i)).card ≤ e := by
  classical
  have hk : 0 < k := by omega

  by_cases htriv : sites.card ≤ e
  · apply upper_bound_save0 hk s t name constant sites e L
    have : sites.card - e = 0 := by omega
    rw [this]; exact (Nat.one_le_pow _ 2 (by omega)).trans hL

  let act := sites.filter (fun i => c_ker (ix hk (i.val + 1)) = 1 ∨ c_ker (ix hk (i.val + 2)) = 1)
  have hact_ne : act.Nonempty := by
    have hex : ∃ u : Fin k, c_ker u = 1 := by
      by_contra hall; push Not at hall; apply hne; funext u; exact (f2_cases _).resolve_right (hall u)
    rcases hex with ⟨u, hu⟩
    have hu_ends : u ∈ endsOf hk sites := by
      by_contra hnot; have := hsupp u hnot; rw [hu] at this; exact one_ne_zero this
    rcases Finset.mem_biUnion.mp hu_ends with ⟨i, hi, hp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, by rcases hp with rfl | rfl; exact Or.inl hu; exact Or.inr hu⟩⟩

  let ell : Fin k → ((Fin k → F2) →ₗ[F2] F2) := fun i =>
    c_ker (ix hk (i.val + 1)) • yLinAt hk s (ix hk (i.val + 1)) +
    c_ker (ix hk (i.val + 2)) • yLinAt hk s (ix hk (i.val + 2))

  have hsum_ell : ∀ x : Fin k → F2, (∑ i ∈ act, ell i x) = 0 := by
    intro x
    have h1 : (∑ i ∈ act, ell i x) = ∑ i ∈ sites, ell i x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hna
      simp only [act, Finset.mem_filter, hi, true_and, not_or] at hna
      have ha : c_ker (ix hk (i.val + 1)) = 0 := (f2_cases _).resolve_right hna.1
      have hb : c_ker (ix hk (i.val + 2)) = 0 := (f2_cases _).resolve_right hna.2
      simp [ell, ha, hb]
    rw [h1]
    have h2 : (∑ i ∈ sites, ell i x) = ∑ u ∈ endsOf hk sites, c_ker u * mix hk (rotLin hk s x) u := by
      unfold endsOf
      rw [Finset.sum_biUnion (fun i hi j hj hij => pair_disjoint hk1 hsp hi hj hij)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_pair (ix_add_one_ne_add_two hk1 i)]
      simp [ell, yLinAt]
    rw [h2]
    have h3 : (∑ u ∈ endsOf hk sites, c_ker u * mix hk (rotLin hk s x) u) =
        ∑ u : Fin k, c_ker u * mix hk (rotLin hk s x) u := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u _ hu; simp [hsupp u hu]
    rw [h3, mix_self_adjoint hk c_ker (rotLin hk s x), hker]
    simp

  let D := sites.card - e - 1
  let inact := sites \ act
  have hinact_disj : Disjoint inact act := disjoint_sdiff_self_left
  let ord : List (Fin k) := inact.toList ++ act.toList
  have hord_nodup : ord.Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb hab => ?_⟩
    subst hab
    exact Finset.disjoint_left.mp hinact_disj (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb)
  have hord_toFinset : ord.toFinset = sites := by
    ext i; simp [ord, inact, act]
  have hord_len : ord.length = sites.card := by
    rw [← List.toFinset_card_of_nodup hord_nodup, hord_toFinset]
  let ql := ord.take D
  have hql_nodup : ql.Nodup := hord_nodup.take
  have hql_len : ql.length = D := by simp only [ql, List.length_take, hord_len]; dsimp only [D]; omega
  let qs : List ((Fin k → F2) →ₗ[F2] F2) :=
    ql.map (fun i => if i ∈ act then ell i else yLinAt hk s (ix hk (i.val + 1)))
  have hqs_len : qs.length = D := by simp [qs, hql_len]

  let R := sites \ ql.toFinset
  have hql_sub : ql.toFinset ⊆ sites := by
    intro i hi; rw [← hord_toFinset]; exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  have hR_card : R.card = e + 1 := by
    rw [Finset.card_sdiff_of_subset hql_sub, List.toFinset_card_of_nodup hord_nodup.take, hql_len]; omega
  let R_act := R ∩ act
  have hR_act_ne : R_act.Nonempty := by
    by_cases hD : D < inact.card
    ·
      obtain ⟨a, ha⟩ := hact_ne
      refine ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp ha).1, ?_⟩, ha⟩⟩
      intro hmem
      have hmem' : a ∈ ql := List.mem_toFinset.mp hmem
      have hin : a ∈ inact.toList := by
        have : ql = inact.toList.take D := by
          simp only [ql, ord]; rw [List.take_append_of_le_length (by simp; omega)]
        rw [this] at hmem'
        exact List.mem_of_mem_take hmem'
      exact Finset.disjoint_left.mp hinact_disj (Finset.mem_toList.mp hin) ha
    ·
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
      have ha_act : a ∈ act := by
        by_contra hna
        have ha_in : a ∈ inact := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hna⟩
        have ha_inL : a ∈ inact.toList := Finset.mem_toList.mpr ha_in
        have hsub_take : inact.toList ⊆ ql := by
          intro x hx
          have : ql = inact.toList ++ act.toList.take (D - inact.toList.length) := by
            simp only [ql, ord]; rw [List.take_append, List.take_of_length_le (by simp; omega)]
          rw [this]; exact List.mem_append_left _ hx
        exact (Finset.mem_sdiff.mp ha).2 (List.mem_toFinset.mpr (hsub_take ha_inL))
      exact ⟨a, Finset.mem_inter.mpr ⟨ha, ha_act⟩⟩
  let i_star := hR_act_ne.choose
  have hi_star_mem : i_star ∈ R_act := hR_act_ne.choose_spec

  let qSum : List Bool → F2 := fun p =>
    ∑ i ∈ ql.toFinset ∩ act,
      match ql.idxOf? i with
      | some idx => queryVal (p.getD idx false)
      | none => 0

  let pickAB : List Bool → Fin k → F2 × F2 := fun p i =>
    let tv : F2 := if i = i_star then qSum p + 1 else 0
    let m1 := mix hk name (ix hk (i.val + 1))
    let m2 := mix hk name (ix hk (i.val + 2))
    if c_ker (ix hk (i.val + 1)) = 1 then
      (tv + m1 + c_ker (ix hk (i.val + 2)) * m2, 0)
    else
      (0, tv + m2)

  let c1 : List Bool → Fin k → F2 := fun p i =>
    match ql.idxOf? i with
    | some idx =>
      if i ∈ act then
        if c_ker (ix hk (i.val + 1)) = 1 then 0
        else queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 2))
      else 0
    | none =>
      if i ∈ R_act then (pickAB p i).2 + 1 else 0
  let c2 : List Bool → Fin k → F2 := fun p i =>
    match ql.idxOf? i with
    | some idx =>
      if i ∈ act then
        if c_ker (ix hk (i.val + 1)) = 1 then
          if c_ker (ix hk (i.val + 2)) = 1 then
            queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 1)) + mix hk name (ix hk (i.val + 2))
          else
            1 + (queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 1)))
        else 0
      else
        1 + (queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 1)))
    | none =>
      if i ∈ R_act then (pickAB p i).1 else 0
  let c0 : List Bool → Fin k → F2 := fun p i =>
    match ql.idxOf? i with
    | some idx =>
      if i ∈ act then
        if c_ker (ix hk (i.val + 1)) = 1 then 0
        else queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 2))
      else 0
    | none =>
      if i ∈ R_act then ((pickAB p i).1 + 1) * ((pickAB p i).2 + 1) else 0
  apply exists_tree_of_queries hk s t name constant sites e L qs (by rw [hqs_len]; exact hL) c1 c2 c0
  intro x
  let p := qs.map (fun q => decide (q x ≠ 0))
  let old := rot hk s x + name
  let y : Fin k → F2 := fun u => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
  let bad := sites.filter (fun i =>
    c1 p i * y (ix hk (i.val + 1)) + c2 p i * y (ix hk (i.val + 2)) + c0 p i ≠
      (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)))
  change bad.card ≤ e

  have hbad_sub : bad ⊆ R := by
    intro i hi
    have hi_s : i ∈ sites := (Finset.mem_filter.mp hi).1
    have hi_err := (Finset.mem_filter.mp hi).2
    refine Finset.mem_sdiff.mpr ⟨hi_s, fun hiq => ?_⟩
    have hiq' : i ∈ ql := List.mem_toFinset.mp hiq
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp hiq'
    have hidxOf : ql.idxOf? i = some idx := by
      rw [List.idxOf?_eq_some_iff]
      exact ⟨hidx_lt, hidx_eq, fun j hj hji => absurd (hql_nodup.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
    have hget : p.getD idx false = decide ((if i ∈ act then ell i else yLinAt hk s (ix hk (i.val + 1))) x ≠ 0) := by
      simp only [p, List.getD_eq_getElem?_getD, List.getElem?_map, qs, List.getElem?_eq_getElem hidx_lt, hidx_eq, Option.map_some, Option.getD_some]
    apply hi_err
    simp only [c1, c2, c0, hidxOf, hget, queryVal_decide]
    by_cases hia : i ∈ act
    · simp only [hia, ↓reduceIte]
      have hact_or := (Finset.mem_filter.mp hia).2
      have hy1 : y (ix hk (i.val + 1)) = yLinAt hk s (ix hk (i.val + 1)) x + mix hk name (ix hk (i.val + 1)) :=
        y_eq_yLinAt hk s name x _
      have hy2 : y (ix hk (i.val + 2)) = yLinAt hk s (ix hk (i.val + 2)) x + mix hk name (ix hk (i.val + 2)) :=
        y_eq_yLinAt hk s name x _
      by_cases hc1 : c_ker (ix hk (i.val + 1)) = 1
      · by_cases hc2 : c_ker (ix hk (i.val + 2)) = 1
        · simp only [hc1, hc2, ↓reduceIte, zero_mul, zero_add, add_zero, ell, LinearMap.add_apply, LinearMap.smul_apply, one_smul]
          have hsum : y (ix hk (i.val + 1)) + y (ix hk (i.val + 2)) =
              yLinAt hk s (ix hk (i.val + 1)) x + yLinAt hk s (ix hk (i.val + 2)) x +
                mix hk name (ix hk (i.val + 1)) + mix hk name (ix hk (i.val + 2)) := by
            rw [hy1, hy2]; ring
          exact approx_eq_of_sum _ _ _ hsum
        · have hc20 : c_ker (ix hk (i.val + 2)) = 0 := (f2_cases _).resolve_right hc2
          simp only [hc1, hc2, hc20, ↓reduceIte, zero_mul, zero_add, add_zero, ell, LinearMap.add_apply, LinearMap.smul_apply, one_smul, zero_smul, LinearMap.zero_apply]
          exact approx_eq_of_y1 _ _ _ hy1
      · have hc2 : c_ker (ix hk (i.val + 2)) = 1 := hact_or.resolve_left hc1
        have hc10 : c_ker (ix hk (i.val + 1)) = 0 := (f2_cases _).resolve_right hc1
        simp only [hc1, hc2, hc10, zero_ne_one, ↓reduceIte, zero_mul, zero_add, add_zero, ell, LinearMap.add_apply, LinearMap.smul_apply, one_smul, zero_smul, LinearMap.zero_apply]
        rw [← hy2]; ring
    · simp only [hia, ↓reduceIte, zero_mul, zero_add, add_zero]
      exact approx_eq_of_y1 _ _ _ (y_eq_yLinAt hk s name x _)

  have hnot_all_Ract : ¬ (R_act ⊆ bad) := by
    intro hsub_act

    have hqSum_eq : qSum p = ∑ i ∈ ql.toFinset ∩ act, ell i x := by
      dsimp only [qSum]
      apply Finset.sum_congr rfl
      intro i hi
      have hiq : i ∈ ql := List.mem_toFinset.mp (Finset.mem_inter.mp hi).1
      have hia : i ∈ act := (Finset.mem_inter.mp hi).2
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp hiq
      have hidxOf : ql.idxOf? i = some idx := by
        rw [List.idxOf?_eq_some_iff]
        exact ⟨hidx_lt, hidx_eq, fun j hj hji => absurd (hql_nodup.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
      have hget : p.getD idx false = decide (ell i x ≠ 0) := by
        simp only [p, List.getD_eq_getElem?_getD, List.getElem?_map, qs, List.getElem?_eq_getElem hidx_lt, hidx_eq, hia, ↓reduceIte, Option.map_some, Option.getD_some]
      simp only [hidxOf]
      rw [hget, queryVal_decide]

    have hell_eq : ∀ i ∈ R_act, ell i x = if i = i_star then qSum p + 1 else 0 := by
      intro i hi
      have hi_bad : i ∈ bad := hsub_act hi
      have hi_not_q : i ∉ ql := fun h => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).1).2 (List.mem_toFinset.mpr h)
      have hidxOf : ql.idxOf? i = none := List.idxOf?_eq_none_iff.mpr hi_not_q
      have herr_i := (Finset.mem_filter.mp hi_bad).2
      simp only [c1, c2, c0, hidxOf, hi, ↓reduceIte] at herr_i
      have ⟨hy1eq, hy2eq⟩ := (approx_point_err (y (ix hk (i.val + 1))) (y (ix hk (i.val + 2))) (pickAB p i).1 (pickAB p i).2).mp herr_i
      have h2zero : ∀ a : F2, a * 2 = 0 := fun a => by rcases f2_cases a with rfl | rfl <;> decide
      have hyl1 : yLinAt hk s (ix hk (i.val + 1)) x = (pickAB p i).1 + mix hk name (ix hk (i.val + 1)) := by
        dsimp only [y] at hy1eq
        rw [← hy1eq, y_eq_yLinAt hk s name x]; ring_nf; simp [h2zero]
      have hyl2 : yLinAt hk s (ix hk (i.val + 2)) x = (pickAB p i).2 + mix hk name (ix hk (i.val + 2)) := by
        dsimp only [y] at hy2eq
        rw [← hy2eq, y_eq_yLinAt hk s name x]; ring_nf; simp [h2zero]
      have hact_or := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
      simp only [ell, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyl1, hyl2, pickAB]
      by_cases hc1 : c_ker (ix hk (i.val + 1)) = 1
      · simp only [hc1, ↓reduceIte, one_mul, zero_add]
        rcases f2_cases (c_ker (ix hk (i.val + 2))) with hc2 | hc2
        · simp [hc2]; ring_nf; simp [h2zero]
        · simp [hc2]; ring_nf; simp [h2zero]
      · have hc2 : c_ker (ix hk (i.val + 2)) = 1 := hact_or.resolve_left hc1
        have hc10 : c_ker (ix hk (i.val + 1)) = 0 := (f2_cases _).resolve_right hc1
        simp only [hc1, hc10, hc2, zero_ne_one, ↓reduceIte, zero_mul, one_mul, zero_add]
        split_ifs <;> (ring_nf; simp [h2zero])
    have hsum_Ract : (∑ i ∈ R_act, ell i x) = qSum p + 1 := by
      rw [Finset.sum_congr rfl hell_eq]
      simp [hi_star_mem]
    have hact_split : act = (ql.toFinset ∩ act) ∪ R_act := by
      ext i; simp only [R_act, R, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · intro hia
        by_cases hiq : i ∈ ql.toFinset
        · exact Or.inl ⟨hiq, hia⟩
        · exact Or.inr ⟨⟨(Finset.mem_filter.mp hia).1, hiq⟩, hia⟩
      · rintro (⟨_, hia⟩ | ⟨_, hia⟩) <;> exact hia
    have hdisj_act : Disjoint (ql.toFinset ∩ act) R_act := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).1).2 (Finset.mem_inter.mp h1).1
    have htot := hsum_ell x
    rw [hact_split, Finset.sum_union hdisj_act, ← hqSum_eq, hsum_Ract] at htot
    have : qSum p + (qSum p + 1) = 1 := by rw [← add_assoc, f2_add_self, zero_add]
    rw [this] at htot
    exact one_ne_zero htot

  have hlt : bad.card < R.card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hbad_sub, fun heq => hnot_all_Ract (heq ▸ Finset.inter_subset_left)⟩
  omega

lemma mix_mod6_ker {k : Nat} (hk : 0 < k) (hd6 : 6 ∣ k) (ra rb : Nat)
    (hra : ra < 6) (hrb : rb < 6) (hne : ra ≠ rb) (hpar : ra % 2 = rb % 2) :
    mix hk (fun u : Fin k => if u.val % 6 = ra ∨ u.val % 6 = rb then (1 : F2) else 0) = 0 := by
  have hk6 : 6 ≤ k := Nat.le_of_dvd hk hd6
  funext u
  simp only [mix, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  have h1 : (ix hk (u.val + 2)).val % 6 = (u.val + 2) % 6 := by
    simp only [ix]; exact Nat.mod_mod_of_dvd _ hd6
  have h2 : (ix hk (u.val + k - 2 % k)).val % 6 = (u.val + 4) % 6 := by
    simp only [ix]
    have h2k : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2k, Nat.mod_mod_of_dvd _ hd6]
    omega
  rw [h1, h2]
  have hmod : ∀ (r : Nat), r < 6 →
      (if r = ra ∨ r = rb then (1 : F2) else 0) +
      (if (r + 2) % 6 = ra ∨ (r + 2) % 6 = rb then 1 else 0) +
      (if (r + 4) % 6 = ra ∨ (r + 4) % 6 = rb then 1 else 0) = 0 := by
    intro r hr
    by_cases hp : r % 2 = ra % 2
    · by_cases h0 : r = ra ∨ r = rb
      · by_cases h1' : (r + 2) % 6 = ra ∨ (r + 2) % 6 = rb
        · have h2' : ¬ ((r + 4) % 6 = ra ∨ (r + 4) % 6 = rb) := by omega
          simp [h0, h1', h2', f2_add_self]
        · have h2' : (r + 4) % 6 = ra ∨ (r + 4) % 6 = rb := by omega
          simp [h0, h1', h2', f2_add_self]
      · have h1' : (r + 2) % 6 = ra ∨ (r + 2) % 6 = rb := by omega
        have h2' : (r + 4) % 6 = ra ∨ (r + 4) % 6 = rb := by omega
        simp [h0, h1', h2', f2_add_self]
    · have h0 : ¬ (r = ra ∨ r = rb) := by omega
      have h1' : ¬ ((r + 2) % 6 = ra ∨ (r + 2) % 6 = rb) := by omega
      have h2' : ¬ ((r + 4) % 6 = ra ∨ (r + 4) % 6 = rb) := by omega
      simp [h0, h1', h2']
  have hru := hmod (u.val % 6) (Nat.mod_lt _ (by decide))
  have ha2 : (u.val % 6 + 2) % 6 = (u.val + 2) % 6 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have ha4 : (u.val % 6 + 4) % 6 = (u.val + 4) % 6 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [ha2, ha4] at hru
  exact hru

lemma upper_bound_save2_complete {k : Nat} (hk1 : 1 < k) (hd6 : 6 ∣ k) (s t : Nat) (name constant : Fin k → F2)
    (sites : Finset (Fin k)) (e L : Nat)
    (hsp : ∀ i ∈ sites, ix (by omega : 0 < k) (i.val + 1) ∉ sites)
    (hfull : 2 * sites.card = k)
    (hL : 2 ^ (sites.card - e - 2) ≤ L) :
    ∃ (nodes : Finset (List Bool))
      (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
      (aff : List Bool → (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : List Bool → Fin k → F2),
      nodes.card < L ∧ ∀ x : Fin k → F2,
        (sites.filter (fun i =>
          (aff (walkLeaf nodes ask bias x) x + c (walkLeaf nodes ask bias x)) i ≠
            let old := rot (by omega : 0 < k) s x + name
            let y := fun u : Fin k => old u + old (ix (by omega : 0 < k) (u.val + 2)) + old (ix (by omega : 0 < k) (u.val + k - 2 % k))
            y i + (1 + y (ix (by omega : 0 < k) (i.val + 1))) * y (ix (by omega : 0 < k) (i.val + 2)) + rot (by omega : 0 < k) t x i + constant i)).card ≤ e := by
  classical
  have hk : 0 < k := by omega
  have hk6 : 6 ≤ k := by omega
  let m := k / 6
  have hm_pos : 0 < m := by omega
  have hsites_card : sites.card = 3 * m := by omega

  by_cases htriv : sites.card ≤ e
  · apply upper_bound_save0 hk s t name constant sites e L
    rw [show sites.card - e = 0 by omega]; exact (Nat.one_le_pow _ 2 (by omega)).trans hL

  have hsame_par : ∀ i ∈ sites, ∀ j ∈ sites, i.val % 2 = j.val % 2 := by
    have hiff : ∀ u : Fin k, u ∈ sites ↔ ix hk (u.val + 1) ∉ sites := by
      intro u
      constructor
      · exact hsp u
      · intro hnot

        have hdisj : Disjoint sites (sites.image (fun i => ix hk (i.val + 1))) := by
          rw [Finset.disjoint_left]; intro w hw1 hw2
          rcases Finset.mem_image.mp hw2 with ⟨i, hi, rfl⟩
          exact hsp i hi hw1
        have hunion : sites ∪ sites.image (fun i => ix hk (i.val + 1)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (fun _ _ h => ix_add_one_inj hk h),
              Fintype.card_fin]
          omega

        have hpre_mem : ix hk (u.val + 1) ∈ sites ∨ ix hk (u.val + 1) ∈ sites.image (fun i => ix hk (i.val + 1)) :=
          Finset.mem_union.mp (hunion ▸ Finset.mem_univ _)
        rcases hpre_mem with h1 | h2
        · exact absurd h1 hnot
        · rcases Finset.mem_image.mp h2 with ⟨i, hi, heq⟩
          exact (ix_add_one_inj hk heq) ▸ hi
    have hstep2 : ∀ u : Fin k, u ∈ sites ↔ ix hk (u.val + 2) ∈ sites := by
      intro u
      have h1 := hiff u
      have h2 := hiff (ix hk (u.val + 1))
      have heq : ix hk ((ix hk (u.val + 1)).val + 1) = ix hk (u.val + 2) := by
        ext; simp only [ix]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [heq] at h2
      tauto
    have h2m : ∀ (a d : Nat), ix hk a ∈ sites ↔ ix hk (a + 2 * d) ∈ sites := by
      intro a d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [ih, hstep2]
        have : ix hk ((ix hk (a + 2 * d)).val + 2) = ix hk (a + 2 * (d + 1)) := by
          ext; simp only [ix]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show a + 2 * d + 2 = a + 2 * (d + 1) by omega]
        rw [this]
    intro i hi j hj
    by_contra hne
    have hmod : (i.val % 2 = 0 ∧ j.val % 2 = 1) ∨ (i.val % 2 = 1 ∧ j.val % 2 = 0) := by omega
    have h0 : (⟨0, hk⟩ : Fin k) ∈ sites := by
      rcases hmod with ⟨hi0, _⟩ | ⟨_, hj0⟩
      · have h := (h2m 0 (i.val / 2)).mpr (by simpa [ix, show 0 + 2 * (i.val / 2) = i.val by omega, Nat.mod_eq_of_lt i.isLt] using hi)
        simpa [ix] using h
      · have h := (h2m 0 (j.val / 2)).mpr (by simpa [ix, show 0 + 2 * (j.val / 2) = j.val by omega, Nat.mod_eq_of_lt j.isLt] using hj)
        simpa [ix] using h
    have h1 : (⟨1, by omega⟩ : Fin k) ∈ sites := by
      rcases hmod with ⟨_, hj1⟩ | ⟨hi1, _⟩
      · have h := (h2m 1 (j.val / 2)).mpr (by simpa [ix, show 1 + 2 * (j.val / 2) = j.val by omega, Nat.mod_eq_of_lt j.isLt] using hj)
        simpa [ix, Nat.mod_eq_of_lt (by omega : 1 < k)] using h
      · have h := (h2m 1 (i.val / 2)).mpr (by simpa [ix, show 1 + 2 * (i.val / 2) = i.val by omega, Nat.mod_eq_of_lt i.isLt] using hi)
        simpa [ix, Nat.mod_eq_of_lt (by omega : 1 < k)] using h
    exact hsp ⟨0, hk⟩ h0 (by simpa [ix, Nat.mod_eq_of_lt (by omega : 1 < k)] using h1)

  let G : Fin 3 → Finset (Fin k) := fun a => sites.filter (fun i => (i.val / 2) % 3 = a.val)
  have hG_card : ∀ a : Fin 3, (G a).card = m := by
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < sites.card)
    let par := i0.val % 2
    have hsites_eq : sites = (Finset.univ : Finset (Fin k)).filter (fun i => i.val % 2 = par) := by
      apply Finset.eq_of_subset_of_card_le
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hsame_par i hi i0 hi0
      · have hhalf : ((Finset.univ : Finset (Fin k)).filter (fun i => i.val % 2 = par)).card = k / 2 := by
          symm
          rw [← Fintype.card_fin (k / 2), ← Finset.card_univ]
          apply Finset.card_bij (fun (q : Fin (k / 2)) _ => (⟨2 * q.val + par, by omega⟩ : Fin k))
          · intro q _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          · intro q1 _ q2 _ h; ext; have := congrArg Fin.val h; dsimp only at this; omega
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            refine ⟨⟨i.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩; ext; dsimp only; omega
        rw [hhalf]; omega
    intro a
    symm
    rw [← Fintype.card_fin m, ← Finset.card_univ]
    apply Finset.card_bij (fun (q : Fin m) _ => (⟨6 * q.val + 2 * a.val + par, by omega⟩ : Fin k))
    · intro q _
      simp only [G, hsites_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, by omega⟩
    · intro q1 _ q2 _ h; ext; have := congrArg Fin.val h; dsimp only at this; omega
    · intro i hi
      simp only [G, hsites_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨⟨i.val / 6, by omega⟩, Finset.mem_univ _, ?_⟩; ext; dsimp only; omega

  have hsum_G : ∀ (a b : Fin 3) (off : Nat), a ≠ b → (off = 1 ∨ off = 2) →
      ∀ x : Fin k → F2, (∑ i ∈ G a, yLinAt hk s (ix hk (i.val + off)) x) +
        (∑ i ∈ G b, yLinAt hk s (ix hk (i.val + off)) x) = 0 := by
    intro a b off hab hoff x
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < sites.card)
    let par := i0.val % 2

    let ra := (2 * a.val + par + off) % 6
    let rb := (2 * b.val + par + off) % 6
    have hra_ne_rb : ra ≠ rb := by
      have : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    let c_ker : Fin k → F2 := fun u => if u.val % 6 = ra ∨ u.val % 6 = rb then 1 else 0
    have hker : mix hk c_ker = 0 :=
      mix_mod6_ker hk hd6 ra rb (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hra_ne_rb (by omega)
    have h0 := congrArg (fun f => ∑ u : Fin k, f u * rotLin hk s x u) hker
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h0
    rw [← mix_self_adjoint hk c_ker (rotLin hk s x)] at h0

    have hdisj : Disjoint (G a) (G b) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [G, Finset.mem_filter] at h1 h2
      exact hab (Fin.ext (by omega))
    have hsum_eq : (∑ u : Fin k, c_ker u * mix hk (rotLin hk s x) u) =
        ∑ i ∈ G a ∪ G b, yLinAt hk s (ix hk (i.val + off)) x := by
      have hfilt : (∑ u : Fin k, c_ker u * mix hk (rotLin hk s x) u) =
          ∑ u ∈ (Finset.univ : Finset (Fin k)).filter (fun u => u.val % 6 = ra ∨ u.val % 6 = rb),
            mix hk (rotLin hk s x) u := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u _; simp [c_ker]
      rw [hfilt]
      symm
      apply Finset.sum_bij (fun i _ => ix hk (i.val + off))
      · intro i hi
        simp only [Finset.mem_union, G, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have hmod : (ix hk (i.val + off)).val % 6 = (i.val + off) % 6 := by
          simp only [ix]; exact Nat.mod_mod_of_dvd _ hd6
        rw [hmod]
        rcases hi with ⟨his, hia⟩ | ⟨his, hib⟩
        · have hip := hsame_par i his i0 hi0
          left; omega
        · have hip := hsame_par i his i0 hi0
          right; omega
      · intro i1 _ i2 _ h
        rcases hoff with rfl | rfl
        · exact ix_add_one_inj hk h
        · exact ix_add_two_inj hk h
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        let i : Fin k := ix hk (u.val + k - off)
        have hi_add : ix hk (i.val + off) = u := by
          ext; simp only [i, ix]
          have : ((u.val + k - off) % k + off) % k = (u.val + k - off + off) % k := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          rw [this, show u.val + k - off + off = u.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt u.isLt]
        have hi_mod6 : i.val % 6 = (u.val + 6 - off) % 6 := by
          simp only [i, ix]
          rw [Nat.mod_mod_of_dvd _ hd6]; omega
        have hi_par : i.val % 2 = par := by
          dsimp only [ra, rb] at hu
          omega

        have hi_sites : i ∈ sites := by
          have huniv : endsOf hk sites = Finset.univ :=
            Finset.eq_univ_of_card _ (by rw [endsOf_card hk1 hsp, hfull, Fintype.card_fin])
          have hdisj' : Disjoint sites (sites.image (fun j => ix hk (j.val + 1))) := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            rcases Finset.mem_image.mp hw2 with ⟨j, hj, rfl⟩; exact hsp j hj hw1
          have hunion : sites ∪ sites.image (fun j => ix hk (j.val + 1)) = Finset.univ := by
            apply Finset.eq_univ_of_card
            rw [Finset.card_union_of_disjoint hdisj', Finset.card_image_of_injective _ (fun _ _ h => ix_add_one_inj hk h), Fintype.card_fin]; omega
          rcases Finset.mem_union.mp (hunion ▸ Finset.mem_univ i) with h1 | h2
          · exact h1
          · rcases Finset.mem_image.mp h2 with ⟨j, hj, heq⟩
            have hjpar := hsame_par j hj i0 hi0
            have : i.val % 2 ≠ j.val % 2 := by
              rw [← heq]; simp only [ix]
              rw [Nat.mod_mod_of_dvd _ (dvd_trans (by decide : 2 ∣ 6) hd6)]
              omega
            omega
        refine ⟨i, ?_, hi_add⟩
        simp only [Finset.mem_union, G, Finset.mem_filter]
        rcases hu with hua | hub
        · left; exact ⟨hi_sites, by omega⟩
        · right; exact ⟨hi_sites, by omega⟩
      · intro i _; rfl
    rw [hsum_eq, Finset.sum_union hdisj] at h0
    exact h0

  by_cases hCaseA : e ≤ 2 * m - 2
  ·

    let e1 := min e (m - 1)
    let e2 := e - e1
    have he12 : e1 + e2 = e ∧ e1 ≤ m - 1 ∧ e2 ≤ m - 1 := by omega
    let q0 := (G 0).toList
    let q1 := (G 1).toList.take (m - 1 - e1)
    let q2 := (G 2).toList.take (m - 1 - e2)
    let ql := q0 ++ q1 ++ q2
    have hq0_len : q0.length = m := by simp [q0, hG_card 0]
    have hq1_len : q1.length = m - 1 - e1 := by simp [q1, hG_card 1]; omega
    have hq2_len : q2.length = m - 1 - e2 := by simp [q2, hG_card 2]; omega
    have hql_len : ql.length = sites.card - e - 2 := by
      simp only [ql, List.length_append, hq0_len, hq1_len, hq2_len, hsites_card]; omega
    have hG_disj : ∀ a b : Fin 3, a ≠ b → Disjoint (G a) (G b) := by
      intro a b hab; rw [Finset.disjoint_left]; intro i h1 h2
      simp only [G, Finset.mem_filter] at h1 h2; exact hab (Fin.ext (by omega))
    have hql_nodup : ql.Nodup := by
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨Finset.nodup_toList _, (Finset.nodup_toList _).take, fun a ha b hb h => by
        subst h; exact Finset.disjoint_left.mp (hG_disj 0 1 (by decide)) (Finset.mem_toList.mp ha) (Finset.mem_toList.mp (List.mem_of_mem_take hb))⟩,
        (Finset.nodup_toList _).take, fun a ha b hb h => by
          subst h; rcases List.mem_append.mp ha with ha0 | ha1
          · exact Finset.disjoint_left.mp (hG_disj 0 2 (by decide)) (Finset.mem_toList.mp ha0) (Finset.mem_toList.mp (List.mem_of_mem_take hb))
          · exact Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (Finset.mem_toList.mp (List.mem_of_mem_take ha1)) (Finset.mem_toList.mp (List.mem_of_mem_take hb))⟩
    let qs : List ((Fin k → F2) →ₗ[F2] F2) := ql.map (fun i => yLinAt hk s (ix hk (i.val + 1)))
    have hqs_len : qs.length = sites.card - e - 2 := by simp [qs, hql_len]
    let R1 := G 1 \ q1.toFinset
    let R2 := G 2 \ q2.toFinset
    have hR1_card : R1.card = e1 + 1 := by
      have hsub : q1.toFinset ⊆ G 1 := fun i hi => Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
      rw [Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup (Finset.nodup_toList _).take, hq1_len, hG_card 1]; omega
    have hR2_card : R2.card = e2 + 1 := by
      have hsub : q2.toFinset ⊆ G 2 := fun i hi => Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
      rw [Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup (Finset.nodup_toList _).take, hq2_len, hG_card 2]; omega
    have hR1_ne : R1.Nonempty := Finset.card_pos.mp (by omega)
    have hR2_ne : R2.Nonempty := Finset.card_pos.mp (by omega)
    let r1_star := hR1_ne.choose
    let r2_star := hR2_ne.choose
    have hr1_mem : r1_star ∈ R1 := hR1_ne.choose_spec
    have hr2_mem : r2_star ∈ R2 := hR2_ne.choose_spec
    let sumQ (S : Finset (Fin k)) (p : List Bool) : F2 :=
      ∑ i ∈ S, match ql.idxOf? i with | some idx => queryVal (p.getD idx false) | none => 0

    let pickA : List Bool → Fin k → F2 := fun p i =>
      let m1 := mix hk name (ix hk (i.val + 1))
      if i = r1_star then sumQ (G 0 ∪ q1.toFinset) p + 1 + m1
      else if i = r2_star then sumQ (G 0 ∪ q2.toFinset) p + 1 + m1
      else m1
    let c1 : List Bool → Fin k → F2 := fun p i =>
      match ql.idxOf? i with | some _ => 0 | none => 1
    let c2 : List Bool → Fin k → F2 := fun p i =>
      match ql.idxOf? i with
      | some idx => 1 + (queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 1)))
      | none => pickA p i
    let c0 : List Bool → Fin k → F2 := fun p i =>
      match ql.idxOf? i with | some _ => 0 | none => pickA p i + 1
    apply exists_tree_of_queries hk s t name constant sites e L qs (by rw [hqs_len]; exact hL) c1 c2 c0
    intro x
    let p := qs.map (fun q => decide (q x ≠ 0))
    let old := rot hk s x + name
    let y : Fin k → F2 := fun u => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
    let bad := sites.filter (fun i =>
      c1 p i * y (ix hk (i.val + 1)) + c2 p i * y (ix hk (i.val + 2)) + c0 p i ≠
        (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)))
    change bad.card ≤ e
    have hidx_val : ∀ i ∈ ql.toFinset,
        (match ql.idxOf? i with | some idx => queryVal (p.getD idx false) | none => 0) = yLinAt hk s (ix hk (i.val + 1)) x := by
      intro i hi
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hi)
      have hidxOf : ql.idxOf? i = some idx := by
        rw [List.idxOf?_eq_some_iff]
        exact ⟨hidx_lt, hidx_eq, fun j hj hji => absurd (hql_nodup.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
      have hget : p.getD idx false = decide (yLinAt hk s (ix hk (i.val + 1)) x ≠ 0) := by
        simp only [p, List.getD_eq_getElem?_getD, List.getElem?_map, qs, List.getElem?_eq_getElem hidx_lt, hidx_eq, Option.map_some, Option.getD_some]
      simp only [hidxOf]
      rw [hget, queryVal_decide]

    have hbad_sub : bad ⊆ R1 ∪ R2 := by
      intro i hi
      have his : i ∈ sites := (Finset.mem_filter.mp hi).1
      have hierr := (Finset.mem_filter.mp hi).2
      have hniq : i ∉ ql.toFinset := by
        intro hiq
        obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hiq)
        have hidxOf : ql.idxOf? i = some idx := by
          rw [List.idxOf?_eq_some_iff]
          exact ⟨hidx_lt, hidx_eq, fun j hj hji => absurd (hql_nodup.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
        have hv := hidx_val i hiq
        rw [hidxOf] at hv
        apply hierr
        simp only [c1, c2, c0, hidxOf, zero_mul, zero_add, add_zero, hv]
        exact approx_eq_of_y1 _ _ _ (y_eq_yLinAt hk s name x _)
      have hG012 : i ∈ G 0 ∨ i ∈ G 1 ∨ i ∈ G 2 := by
        simp only [G, Finset.mem_filter, his, true_and]; omega
      rcases hG012 with h0 | h1 | h2
      · exfalso; apply hniq; rw [List.mem_toFinset]; exact List.mem_append_left _ (List.mem_append_left _ (Finset.mem_toList.mpr h0))
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, fun hm => hniq (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_right _ (List.mem_toFinset.mp hm))))⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2, fun hm => hniq (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hm)))⟩)

    have hR1_not : ¬ (R1 ⊆ bad) := by
      intro hsub
      have hne_stars : r1_star ≠ r2_star := fun h =>
        Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (Finset.mem_sdiff.mp hr1_mem).1 (h ▸ (Finset.mem_sdiff.mp hr2_mem).1)
      have hyl_R1 : ∀ i ∈ R1, yLinAt hk s (ix hk (i.val + 1)) x = if i = r1_star then sumQ (G 0 ∪ q1.toFinset) p + 1 else 0 := by
        intro i hi
        have hniq : i ∉ ql := by
          intro hm; rcases List.mem_append.mp hm with hm01 | hm2
          · rcases List.mem_append.mp hm01 with hm0 | hm1
            · exact Finset.disjoint_left.mp (hG_disj 0 1 (by decide)) (Finset.mem_toList.mp hm0) (Finset.mem_sdiff.mp hi).1
            · exact (Finset.mem_sdiff.mp hi).2 (List.mem_toFinset.mpr hm1)
          · exact Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (Finset.mem_sdiff.mp hi).1 (Finset.mem_toList.mp (List.mem_of_mem_take hm2))
        have hidxOf : ql.idxOf? i = none := List.idxOf?_eq_none_iff.mpr hniq
        have herr := (Finset.mem_filter.mp (hsub hi)).2
        simp only [c1, c2, c0, hidxOf] at herr
        have hpt := (approx_point_err (y (ix hk (i.val + 1))) (y (ix hk (i.val + 2))) (pickA p i) 0).mp (by simpa using herr)
        have h2zero : ∀ a : F2, a * 2 = 0 := fun a => by rcases f2_cases a with rfl | rfl <;> decide
        have h1 : yLinAt hk s (ix hk (i.val + 1)) x = pickA p i + mix hk name (ix hk (i.val + 1)) := by
          dsimp only [y] at hpt
          rw [← hpt.1, y_eq_yLinAt hk s name x]; ring_nf; simp [h2zero]
        have hne2 : i ≠ r2_star := fun h =>
          Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (Finset.mem_sdiff.mp hi).1 (h ▸ (Finset.mem_sdiff.mp hr2_mem).1)
        rw [h1]; simp only [pickA, hne2, ↓reduceIte]
        split_ifs <;> (ring_nf; simp [h2zero])
      have hsumQ_eq : sumQ (G 0 ∪ q1.toFinset) p =
          (∑ i ∈ G 0, yLinAt hk s (ix hk (i.val + 1)) x) + (∑ i ∈ q1.toFinset, yLinAt hk s (ix hk (i.val + 1)) x) := by
        have hd01 : Disjoint (G 0) q1.toFinset := by
          rw [Finset.disjoint_left]; intro i h0 h1
          exact Finset.disjoint_left.mp (hG_disj 0 1 (by decide)) h0 (Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp h1)))
        dsimp only [sumQ]
        rw [Finset.sum_union hd01]
        congr 1
        · apply Finset.sum_congr rfl; intro i hi
          exact hidx_val i (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_left _ (Finset.mem_toList.mpr hi))))
        · apply Finset.sum_congr rfl; intro i hi
          exact hidx_val i (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_right _ (List.mem_toFinset.mp hi))))
      have hG1_split : G 1 = q1.toFinset ∪ R1 := by
        ext i; simp only [R1, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · intro h; by_cases hq : i ∈ q1.toFinset; exact Or.inl hq; exact Or.inr ⟨h, hq⟩
        · rintro (hq | ⟨h, _⟩); exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hq)); exact h
      have htot := hsum_G 0 1 1 (by decide) (Or.inl rfl) x
      rw [hG1_split, Finset.sum_union disjoint_sdiff_self_right, ← add_assoc, ← hsumQ_eq,
          Finset.sum_congr rfl hyl_R1] at htot
      simp [hr1_mem] at htot
      have : sumQ (G 0 ∪ q1.toFinset) p + (sumQ (G 0 ∪ q1.toFinset) p + 1) = 1 := by
        rw [← add_assoc, f2_add_self, zero_add]
      rw [this] at htot; exact one_ne_zero htot
    have hR2_not : ¬ (R2 ⊆ bad) := by
      intro hsub
      have hyl_R2 : ∀ i ∈ R2, yLinAt hk s (ix hk (i.val + 1)) x = if i = r2_star then sumQ (G 0 ∪ q2.toFinset) p + 1 else 0 := by
        intro i hi
        have hniq : i ∉ ql := by
          intro hm; rcases List.mem_append.mp hm with hm01 | hm2
          · rcases List.mem_append.mp hm01 with hm0 | hm1
            · exact Finset.disjoint_left.mp (hG_disj 0 2 (by decide)) (Finset.mem_toList.mp hm0) (Finset.mem_sdiff.mp hi).1
            · exact Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (Finset.mem_toList.mp (List.mem_of_mem_take hm1)) (Finset.mem_sdiff.mp hi).1
          · exact (Finset.mem_sdiff.mp hi).2 (List.mem_toFinset.mpr hm2)
        have hidxOf : ql.idxOf? i = none := List.idxOf?_eq_none_iff.mpr hniq
        have herr := (Finset.mem_filter.mp (hsub hi)).2
        simp only [c1, c2, c0, hidxOf] at herr
        have hpt := (approx_point_err (y (ix hk (i.val + 1))) (y (ix hk (i.val + 2))) (pickA p i) 0).mp (by simpa using herr)
        have h2zero : ∀ a : F2, a * 2 = 0 := fun a => by rcases f2_cases a with rfl | rfl <;> decide
        have h1 : yLinAt hk s (ix hk (i.val + 1)) x = pickA p i + mix hk name (ix hk (i.val + 1)) := by
          dsimp only [y] at hpt
          rw [← hpt.1, y_eq_yLinAt hk s name x]; ring_nf; simp [h2zero]
        have hne1 : i ≠ r1_star := fun h =>
          Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (h ▸ (Finset.mem_sdiff.mp hr1_mem).1) (Finset.mem_sdiff.mp hi).1
        rw [h1]; simp only [pickA, hne1, ↓reduceIte]
        split_ifs <;> (ring_nf; simp [h2zero])
      have hsumQ_eq : sumQ (G 0 ∪ q2.toFinset) p =
          (∑ i ∈ G 0, yLinAt hk s (ix hk (i.val + 1)) x) + (∑ i ∈ q2.toFinset, yLinAt hk s (ix hk (i.val + 1)) x) := by
        have hd02 : Disjoint (G 0) q2.toFinset := by
          rw [Finset.disjoint_left]; intro i h0 h2
          exact Finset.disjoint_left.mp (hG_disj 0 2 (by decide)) h0 (Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp h2)))
        dsimp only [sumQ]
        rw [Finset.sum_union hd02]
        congr 1
        · apply Finset.sum_congr rfl; intro i hi
          exact hidx_val i (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_left _ (Finset.mem_toList.mpr hi))))
        · apply Finset.sum_congr rfl; intro i hi
          exact hidx_val i (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hi)))
      have hG2_split : G 2 = q2.toFinset ∪ R2 := by
        ext i; simp only [R2, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · intro h; by_cases hq : i ∈ q2.toFinset; exact Or.inl hq; exact Or.inr ⟨h, hq⟩
        · rintro (hq | ⟨h, _⟩); exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hq)); exact h
      have htot := hsum_G 0 2 1 (by decide) (Or.inl rfl) x
      rw [hG2_split, Finset.sum_union disjoint_sdiff_self_right, ← add_assoc, ← hsumQ_eq,
          Finset.sum_congr rfl hyl_R2] at htot
      simp [hr2_mem] at htot
      have : sumQ (G 0 ∪ q2.toFinset) p + (sumQ (G 0 ∪ q2.toFinset) p + 1) = 1 := by
        rw [← add_assoc, f2_add_self, zero_add]
      rw [this] at htot; exact one_ne_zero htot

    have h1 : (bad ∩ R1).card < R1.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_right, fun h => hR1_not (h ▸ Finset.inter_subset_left)⟩)
    have h2 : (bad ∩ R2).card < R2.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_right, fun h => hR2_not (h ▸ Finset.inter_subset_left)⟩)
    have hbad_eq : bad = (bad ∩ R1) ∪ (bad ∩ R2) := by
      ext i; simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hi; rcases Finset.mem_union.mp (hbad_sub hi) with h1' | h2'; exact Or.inl ⟨hi, h1'⟩; exact Or.inr ⟨hi, h2'⟩
      · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    have hle := Finset.card_union_le (bad ∩ R1) (bad ∩ R2)
    rw [← hbad_eq] at hle
    omega
  ·

    let D := sites.card - e - 2
    have hD_lt : D < m := by omega
    let ql := (G 1).toList.take D
    have hql_nodup : ql.Nodup := (Finset.nodup_toList _).take
    have hql_len : ql.length = D := by simp only [ql, List.length_take, Finset.length_toList, hG_card 1]; omega
    let qs : List ((Fin k → F2) →ₗ[F2] F2) := ql.map (fun i => yLinAt hk s (ix hk (i.val + 1)))
    have hqs_len : qs.length = D := by simp [qs, hql_len]
    let J0 := G 0
    let J1 := G 1 \ ql.toFinset
    let J2 := G 2
    have hql_sub : ql.toFinset ⊆ G 1 := fun i hi => Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
    have hJ0_ne : J0.Nonempty := Finset.card_pos.mp (by rw [hG_card 0]; omega)
    have hJ1_card : J1.card = m - D := by
      rw [Finset.card_sdiff_of_subset hql_sub, List.toFinset_card_of_nodup (Finset.nodup_toList _).take, hql_len, hG_card 1]
    have hJ1_ne : J1.Nonempty := Finset.card_pos.mp (by omega)
    have hJ2_ne : J2.Nonempty := Finset.card_pos.mp (by rw [hG_card 2]; omega)
    let j0 := hJ0_ne.choose; have hj0 : j0 ∈ J0 := hJ0_ne.choose_spec
    let j1 := hJ1_ne.choose; have hj1 : j1 ∈ J1 := hJ1_ne.choose_spec
    let j2 := hJ2_ne.choose; have hj2 : j2 ∈ J2 := hJ2_ne.choose_spec
    have hG_disj : ∀ a b : Fin 3, a ≠ b → Disjoint (G a) (G b) := by
      intro a b hab; rw [Finset.disjoint_left]; intro i h1 h2
      simp only [G, Finset.mem_filter] at h1 h2; exact hab (Fin.ext (by omega))
    let qSum : List Bool → F2 := fun p =>
      ∑ i ∈ ql.toFinset, match ql.idxOf? i with | some idx => queryVal (p.getD idx false) | none => 0

    let pickA : List Bool → Fin k → F2 := fun p i =>
      (if i = j1 then qSum p + 1 else 0) + mix hk name (ix hk (i.val + 1))
    let pickB : Fin k → F2 := fun i =>
      (if i = j0 then 1 else 0) + mix hk name (ix hk (i.val + 2))
    let c1 : List Bool → Fin k → F2 := fun _ i =>
      match ql.idxOf? i with | some _ => 0 | none => pickB i + 1
    let c2 : List Bool → Fin k → F2 := fun p i =>
      match ql.idxOf? i with
      | some idx => 1 + (queryVal (p.getD idx false) + mix hk name (ix hk (i.val + 1)))
      | none => pickA p i
    let c0 : List Bool → Fin k → F2 := fun p i =>
      match ql.idxOf? i with | some _ => 0 | none => (pickA p i + 1) * (pickB i + 1)
    apply exists_tree_of_queries hk s t name constant sites e L qs (by rw [hqs_len]; exact hL) c1 c2 c0
    intro x
    let p := qs.map (fun q => decide (q x ≠ 0))
    let old := rot hk s x + name
    let y : Fin k → F2 := fun u => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
    let bad := sites.filter (fun i =>
      c1 p i * y (ix hk (i.val + 1)) + c2 p i * y (ix hk (i.val + 2)) + c0 p i ≠
        (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)))
    change bad.card ≤ e
    have hidx_val : ∀ i ∈ ql.toFinset,
        (match ql.idxOf? i with | some idx => queryVal (p.getD idx false) | none => 0) = yLinAt hk s (ix hk (i.val + 1)) x := by
      intro i hi
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hi)
      have hidxOf : ql.idxOf? i = some idx := by
        rw [List.idxOf?_eq_some_iff]
        exact ⟨hidx_lt, hidx_eq, fun j hj hji => absurd (hql_nodup.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
      have hget : p.getD idx false = decide (yLinAt hk s (ix hk (i.val + 1)) x ≠ 0) := by
        simp only [p, List.getD_eq_getElem?_getD, List.getElem?_map, qs, List.getElem?_eq_getElem hidx_lt, hidx_eq, Option.map_some, Option.getD_some]
      simp only [hidxOf]
      rw [hget, queryVal_decide]
    have hqSum_eq : qSum p = ∑ i ∈ ql.toFinset, yLinAt hk s (ix hk (i.val + 1)) x :=
      Finset.sum_congr rfl hidx_val
    have hbad_sub : bad ⊆ J0 ∪ J1 ∪ J2 := by
      intro i hi
      have his : i ∈ sites := (Finset.mem_filter.mp hi).1
      have hierr := (Finset.mem_filter.mp hi).2
      have hniq : i ∉ ql.toFinset := by
        intro hiq
        obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hiq)
        have hidxOf : ql.idxOf? i = some idx := by
          rw [List.idxOf?_eq_some_iff]
          exact ⟨hidx_lt, hidx_eq, fun j hj hji => absurd (hql_nodup.getElem_inj_iff.mp (hji.trans hidx_eq.symm)) (by omega)⟩
        have hv := hidx_val i hiq; rw [hidxOf] at hv
        apply hierr; simp only [c1, c2, c0, hidxOf, zero_mul, zero_add, add_zero, hv]
        exact approx_eq_of_y1 _ _ _ (y_eq_yLinAt hk s name x _)
      have hG012 : i ∈ G 0 ∨ i ∈ G 1 ∨ i ∈ G 2 := by
        simp only [G, Finset.mem_filter, his, true_and]; omega
      rcases hG012 with h0 | h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h0)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, hniq⟩))
      · exact Finset.mem_union_right _ h2
    have hbad_val : ∀ i ∈ bad,
        yLinAt hk s (ix hk (i.val + 1)) x = (if i = j1 then qSum p + 1 else 0) ∧
        yLinAt hk s (ix hk (i.val + 2)) x = (if i = j0 then 1 else 0) := by
      intro i hi
      have hniq : i ∉ ql := by
        intro hm
        have h1 := hbad_sub hi
        have hiq : i ∈ ql.toFinset := List.mem_toFinset.mpr hm
        have hiG1 : i ∈ G 1 := hql_sub hiq
        simp only [Finset.mem_union, J0, J1, J2, Finset.mem_sdiff] at h1
        rcases h1 with (h0 | ⟨_, hnot⟩) | h2
        · exact Finset.disjoint_left.mp (hG_disj 0 1 (by decide)) h0 hiG1
        · exact hnot hiq
        · exact Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) hiG1 h2
      have hidxOf : ql.idxOf? i = none := List.idxOf?_eq_none_iff.mpr hniq
      have herr := (Finset.mem_filter.mp hi).2
      simp only [c1, c2, c0, hidxOf] at herr
      have ⟨h1, h2⟩ := (approx_point_err (y (ix hk (i.val + 1))) (y (ix hk (i.val + 2))) (pickA p i) (pickB i)).mp herr
      dsimp only [y] at h1 h2
      constructor
      · rw [y_eq_yLinAt hk s name x] at h1
        have := congrArg (· + mix hk name (ix hk (i.val + 1))) h1
        simpa [pickA, add_assoc, f2_add_self] using this
      · rw [y_eq_yLinAt hk s name x] at h2
        have := congrArg (· + mix hk name (ix hk (i.val + 2))) h2
        simpa [pickB, add_assoc, f2_add_self] using this
    have hG1_split : G 1 = ql.toFinset ∪ J1 := by
      ext i; simp only [J1, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro h; by_cases hq : i ∈ ql.toFinset; exact Or.inl hq; exact Or.inr ⟨h, hq⟩
      · rintro (hq | ⟨h, _⟩); exact hql_sub hq; exact h
    have hno01 : ¬ (J0 ⊆ bad ∧ J1 ⊆ bad) := by
      rintro ⟨h0, h1⟩
      have htot := hsum_G 0 1 1 (by decide) (Or.inl rfl) x
      rw [hG1_split, Finset.sum_union disjoint_sdiff_self_right, ← hqSum_eq] at htot
      have hs0 : (∑ i ∈ J0, yLinAt hk s (ix hk (i.val + 1)) x) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        have hv := (hbad_val i (h0 hi)).1
        have hne : i ≠ j1 := fun h => Finset.disjoint_left.mp (hG_disj 0 1 (by decide)) hi (h ▸ (Finset.mem_sdiff.mp hj1).1)
        simpa [hne] using hv
      have hs1 : (∑ i ∈ J1, yLinAt hk s (ix hk (i.val + 1)) x) = qSum p + 1 := by
        rw [Finset.sum_congr rfl (fun i hi => (hbad_val i (h1 hi)).1)]
        simp [hj1]
      rw [hs0, zero_add, hs1] at htot
      have : qSum p + (qSum p + 1) = 1 := by rw [← add_assoc, f2_add_self, zero_add]
      rw [this] at htot; exact one_ne_zero htot
    have hno12 : ¬ (J1 ⊆ bad ∧ J2 ⊆ bad) := by
      rintro ⟨h1, h2⟩
      have htot := hsum_G 1 2 1 (by decide) (Or.inl rfl) x
      rw [hG1_split, Finset.sum_union disjoint_sdiff_self_right, ← hqSum_eq] at htot
      have hs2 : (∑ i ∈ J2, yLinAt hk s (ix hk (i.val + 1)) x) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        have hv := (hbad_val i (h2 hi)).1
        have hne : i ≠ j1 := fun h => Finset.disjoint_left.mp (hG_disj 1 2 (by decide)) (h ▸ (Finset.mem_sdiff.mp hj1).1) hi
        simpa [hne] using hv
      have hs1 : (∑ i ∈ J1, yLinAt hk s (ix hk (i.val + 1)) x) = qSum p + 1 := by
        rw [Finset.sum_congr rfl (fun i hi => (hbad_val i (h1 hi)).1)]
        simp [hj1]
      rw [hs2, add_zero, hs1] at htot
      have : qSum p + (qSum p + 1) = 1 := by rw [← add_assoc, f2_add_self, zero_add]
      rw [this] at htot; exact one_ne_zero htot
    have hno20 : ¬ (J2 ⊆ bad ∧ J0 ⊆ bad) := by
      rintro ⟨h2, h0⟩
      have htot := hsum_G 2 0 2 (by decide) (Or.inr rfl) x
      have hs2 : (∑ i ∈ J2, yLinAt hk s (ix hk (i.val + 2)) x) = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        have hv := (hbad_val i (h2 hi)).2
        have hne : i ≠ j0 := fun h => Finset.disjoint_left.mp (hG_disj 0 2 (by decide)) (h ▸ hj0) hi
        simpa [hne] using hv
      have hs0 : (∑ i ∈ J0, yLinAt hk s (ix hk (i.val + 2)) x) = 1 := by
        rw [Finset.sum_congr rfl (fun i hi => (hbad_val i (h0 hi)).2)]
        simp [hj0]
      rw [hs2, zero_add, hs0] at htot; exact one_ne_zero htot

    have hmiss : (bad ∩ J0).card + (bad ∩ J1).card + (bad ∩ J2).card + 2 ≤ J0.card + J1.card + J2.card := by
      have hle0 : (bad ∩ J0).card ≤ J0.card := Finset.card_le_card Finset.inter_subset_right
      have hle1 : (bad ∩ J1).card ≤ J1.card := Finset.card_le_card Finset.inter_subset_right
      have hle2 : (bad ∩ J2).card ≤ J2.card := Finset.card_le_card Finset.inter_subset_right
      have hlt_of_not : ∀ S : Finset (Fin k), ¬ (S ⊆ bad) → (bad ∩ S).card < S.card := fun S hns =>
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun h => hns (h ▸ Finset.inter_subset_left)⟩)
      by_cases h0 : J0 ⊆ bad
      · have h1 : ¬ (J1 ⊆ bad) := fun h => hno01 ⟨h0, h⟩
        have h2 : ¬ (J2 ⊆ bad) := fun h => hno20 ⟨h, h0⟩
        have := hlt_of_not J1 h1; have := hlt_of_not J2 h2; omega
      · by_cases h1 : J1 ⊆ bad
        · have h2 : ¬ (J2 ⊆ bad) := fun h => hno12 ⟨h1, h⟩
          have := hlt_of_not J0 h0; have := hlt_of_not J2 h2; omega
        · have := hlt_of_not J0 h0; have := hlt_of_not J1 h1; omega
    have hbad_eq : bad = (bad ∩ J0) ∪ (bad ∩ J1) ∪ (bad ∩ J2) := by
      ext i; simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hi; rcases Finset.mem_union.mp (hbad_sub hi) with h01 | h2
        · rcases Finset.mem_union.mp h01 with h0 | h1; exact Or.inl (Or.inl ⟨hi, h0⟩); exact Or.inl (Or.inr ⟨hi, h1⟩)
        · exact Or.inr ⟨hi, h2⟩
      · rintro ((⟨hi, _⟩ | ⟨hi, _⟩) | ⟨hi, _⟩) <;> exact hi
    have hle1 := (Finset.card_union_le ((bad ∩ J0) ∪ (bad ∩ J1)) (bad ∩ J2)).trans
      (Nat.add_le_add_right (Finset.card_union_le (bad ∩ J0) (bad ∩ J1)) _)
    rw [← hbad_eq] at hle1
    have hJ0c : J0.card = m := hG_card 0
    have hJ2c : J2.card = m := hG_card 2
    omega

lemma upper_bound {k : Nat} (hk : 0 < k) (s t : Nat) (name constant : Fin k → F2)
    (sites : Finset (Fin k)) (e L : Nat)
    (hsp : 1 < k → ∀ i ∈ sites, ix hk (i.val + 1) ∉ sites)
    (hL : let ends := endsOf hk sites
          let full := fun (p r : Nat) => ∀ j : Fin k, j.val % p = r → j ∈ ends
          let oddCase := 2 ≤ ((Finset.range 3).filter (fun r => full 3 r)).card
          let laneCase := ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => full 6 (2 * r + v))).card
          let save := if ¬ 3 ∣ k then 0 else if k % 2 = 1 then (if oddCase then 1 else 0)
            else if 2 * sites.card = k then 2 else if laneCase then 1 else 0
          (if k = 1 then 1 else 2 ^ (sites.card - e - save)) ≤ L) :
    ∃ (nodes : Finset (List Bool))
      (ask : List Bool → (Fin k → F2) →ₗ[F2] F2) (bias : List Bool → F2)
      (aff : List Bool → (Fin k → F2) →ₗ[F2] (Fin k → F2)) (c : List Bool → Fin k → F2),
      nodes.card < L ∧ ∀ x : Fin k → F2,
        (sites.filter (fun i =>
          (aff (walkLeaf nodes ask bias x) x + c (walkLeaf nodes ask bias x)) i ≠
            let old := rot hk s x + name
            let y := fun u : Fin k => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
            y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rot hk t x i + constant i)).card ≤ e := by
  dsimp only at hL
  by_cases hk1 : k = 1
  · simp only [hk1, ↓reduceIte] at hL

    apply exists_tree_of_queries hk s t name constant sites e L [] (by simpa using hL)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    intro x
    let old := rot hk s x + name
    let y : Fin k → F2 := fun u => old u + old (ix hk (u.val + 2)) + old (ix hk (u.val + k - 2 % k))
    have h0 : (sites.filter (fun i =>
        (0 : F2) * y (ix hk (i.val + 1)) + (0 : F2) * y (ix hk (i.val + 2)) + (0 : F2) ≠
          (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)))) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      have heq : ix hk (i.val + 1) = ix hk (i.val + 2) := by ext; simp [ix, hk1, Nat.mod_one]
      rw [heq]
      simp only [zero_mul, zero_add, not_not]
      rcases f2_cases (y (ix hk (i.val + 2))) with hv | hv <;> (simp [hv]; try decide)
    change (sites.filter (fun i =>
        (0 : F2) * y (ix hk (i.val + 1)) + (0 : F2) * y (ix hk (i.val + 2)) + (0 : F2) ≠
          (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)))).card ≤ e
    rw [h0]; simp
  · have hgt1 : 1 < k := by omega
    have hsp' := hsp hgt1
    simp only [hk1, ↓reduceIte] at hL
    by_cases hd3 : 3 ∣ k
    · simp only [hd3, not_true_eq_false, ↓reduceIte] at hL
      by_cases hodd : k % 2 = 1
      · simp only [hodd, ↓reduceIte] at hL
        by_cases hoddCase : 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites)).card
        · simp only [hoddCase, ↓reduceIte] at hL

          obtain ⟨r1, hr1, r2, hr2, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 3 = r → j ∈ endsOf hk sites)).card)
          let c_ker : Fin k → F2 := fun u => if u.val % 3 = r1 ∨ u.val % 3 = r2 then 1 else 0
          have hr1_lt : r1 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr1).1
          have hr2_lt : r2 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr2).1
          have hker : mix hk c_ker = 0 := by
            funext u
            simp only [mix, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, c_ker]
            have h1 : (ix hk (u.val + 2)).val % 3 = (u.val + 2) % 3 := by simp only [ix]; exact Nat.mod_mod_of_dvd _ hd3
            have h2 : (ix hk (u.val + k - 2 % k)).val % 3 = (u.val + 1) % 3 := by
              simp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_mod_of_dvd _ hd3]; omega
            rw [h1, h2]
            by_cases ha : u.val % 3 = r1 ∨ u.val % 3 = r2
            · by_cases hb : (u.val + 2) % 3 = r1 ∨ (u.val + 2) % 3 = r2
              · have hc : ¬ ((u.val + 1) % 3 = r1 ∨ (u.val + 1) % 3 = r2) := by omega
                simp [ha, hb, hc, f2_add_self]
              · have hc : (u.val + 1) % 3 = r1 ∨ (u.val + 1) % 3 = r2 := by omega
                simp [ha, hb, hc, f2_add_self]
            · have hb : (u.val + 2) % 3 = r1 ∨ (u.val + 2) % 3 = r2 := by omega
              have hc : (u.val + 1) % 3 = r1 ∨ (u.val + 1) % 3 = r2 := by omega
              simp [ha, hb, hc, f2_add_self]
          have hsupp : ∀ u, u ∉ endsOf hk sites → c_ker u = 0 := by
            intro u hu; simp only [c_ker]; split_ifs with h
            · rcases h with h | h
              · exact absurd ((Finset.mem_filter.mp hr1).2 u h) hu
              · exact absurd ((Finset.mem_filter.mp hr2).2 u h) hu
            · rfl
          have hne : c_ker ≠ 0 := by
            intro h
            have := congrFun h ⟨r1, by omega⟩
            simp [c_ker, Nat.mod_eq_of_lt hr1_lt] at this
          exact upper_bound_save1_of_ker hgt1 s t name constant sites e L hsp' c_ker hker hsupp hne hL
        · simp only [hoddCase, ↓reduceIte, Nat.sub_zero] at hL
          exact upper_bound_save0 hk s t name constant sites e L hL
      · have hd6 : 6 ∣ k := by omega
        simp only [hodd, ↓reduceIte] at hL
        by_cases hfull : 2 * sites.card = k
        · simp only [hfull, ↓reduceIte] at hL
          exact upper_bound_save2_complete hgt1 hd6 s t name constant sites e L hsp' hfull hL
        · simp only [hfull, ↓reduceIte] at hL
          by_cases hlane : ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk sites)).card
          · simp only [hlane, ↓reduceIte] at hL
            rcases hlane with ⟨v, hv, h2v⟩
            have hv_lt : v < 2 := Finset.mem_range.mp hv
            obtain ⟨r1, hr1, r2, hr2, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < ((Finset.range 3).filter (fun r => ∀ j : Fin k, j.val % 6 = 2 * r + v → j ∈ endsOf hk sites)).card)
            have hr1_lt : r1 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr1).1
            have hr2_lt : r2 < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr2).1
            let c_ker : Fin k → F2 := fun u => if u.val % 6 = 2 * r1 + v ∨ u.val % 6 = 2 * r2 + v then 1 else 0
            have hker : mix hk c_ker = 0 := by
              funext u
              simp only [mix, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, c_ker]
              have h1 : (ix hk (u.val + 2)).val % 6 = (u.val + 2) % 6 := by simp only [ix]; exact Nat.mod_mod_of_dvd _ hd6
              have h2 : (ix hk (u.val + k - 2 % k)).val % 6 = (u.val + 4) % 6 := by
                simp only [ix]; rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_mod_of_dvd _ hd6]; omega
              rw [h1, h2]
              by_cases hp : u.val % 2 = v
              · by_cases ha : u.val % 6 = 2 * r1 + v ∨ u.val % 6 = 2 * r2 + v
                · by_cases hb : (u.val + 2) % 6 = 2 * r1 + v ∨ (u.val + 2) % 6 = 2 * r2 + v
                  · have hc : ¬ ((u.val + 4) % 6 = 2 * r1 + v ∨ (u.val + 4) % 6 = 2 * r2 + v) := by omega
                    simp [ha, hb, hc, f2_add_self]
                  · have hc : (u.val + 4) % 6 = 2 * r1 + v ∨ (u.val + 4) % 6 = 2 * r2 + v := by omega
                    simp [ha, hb, hc, f2_add_self]
                · have hb : (u.val + 2) % 6 = 2 * r1 + v ∨ (u.val + 2) % 6 = 2 * r2 + v := by omega
                  have hc : (u.val + 4) % 6 = 2 * r1 + v ∨ (u.val + 4) % 6 = 2 * r2 + v := by omega
                  simp [ha, hb, hc, f2_add_self]
              · have ha : ¬ (u.val % 6 = 2 * r1 + v ∨ u.val % 6 = 2 * r2 + v) := by omega
                have hb : ¬ ((u.val + 2) % 6 = 2 * r1 + v ∨ (u.val + 2) % 6 = 2 * r2 + v) := by omega
                have hc : ¬ ((u.val + 4) % 6 = 2 * r1 + v ∨ (u.val + 4) % 6 = 2 * r2 + v) := by omega
                simp [ha, hb, hc]
            have hsupp : ∀ u, u ∉ endsOf hk sites → c_ker u = 0 := by
              intro u hu; simp only [c_ker]; split_ifs with h
              · rcases h with h | h
                · exact absurd ((Finset.mem_filter.mp hr1).2 u h) hu
                · exact absurd ((Finset.mem_filter.mp hr2).2 u h) hu
              · rfl
            have hne : c_ker ≠ 0 := by
              intro h
              have := congrFun h ⟨2 * r1 + v, by omega⟩
              simp [c_ker, Nat.mod_eq_of_lt (by omega : 2 * r1 + v < 6)] at this
            exact upper_bound_save1_of_ker hgt1 s t name constant sites e L hsp' c_ker hker hsupp hne hL
          · simp only [hlane, ↓reduceIte, Nat.sub_zero] at hL
            exact upper_bound_save0 hk s t name constant sites e L hL
    · simp only [hd3, not_false_eq_true, ↓reduceIte, Nat.sub_zero] at hL
      exact upper_bound_save0 hk s t name constant sites e L hL

end PEqualNP.Outside.L_meta_33626_aux

theorem PEqualNP.Outside.L_meta_33626 : (∀ (k : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  ∀ (s t : Nat) (name constant : W),
    let out := fun (raw : W) (site : Fin k) =>
      let old := rot s raw + name
      let y := fun u : Fin k =>
        old u + old (ix (u.val+2)) + old (ix (u.val+k-2 % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) + rot t raw site + constant site
    let H := List Bool
    let Tree := Finset H × (H → W →ₗ[F] F) × (H → F) × (H → W →ₗ[F] W) × (H → W)
    let predict : Tree → W → W := fun tree raw =>
      let nodes := tree.1
      let ask := tree.2.1
      let bias := tree.2.2.1
      let aff := tree.2.2.2.1
      let c := tree.2.2.2.2
      let leaf := (List.range nodes.card).foldl (fun (p : H) _ =>
        if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p) []
      aff leaf raw + c leaf
    ∀ (sites : Finset (Fin k)) (e L : Nat),
      (1 < k → ∀ i ∈ sites, ix (i.val+1) ∉ sites) →
      let ends := sites.biUnion (fun i => ({ix (i.val+1), ix (i.val+2)} : Finset (Fin k)))
      let full := fun (p r : Nat) => ∀ j : Fin k, j.val % p = r → j ∈ ends
      let oddCase := 2 ≤ ((Finset.range 3).filter (fun r => full 3 r)).card
      let laneCase := ∃ v ∈ Finset.range 2, 2 ≤ ((Finset.range 3).filter (fun r => full 6 (2*r+v))).card
      let save := if ¬ 3 ∣ k then 0 else if k % 2 = 1 then (if oddCase then 1 else 0)
        else if 2*sites.card = k then 2 else if laneCase then 1 else 0
      let price := if k = 1 then 1 else 2^(sites.card-e-save)
      (∃ tree : Tree, tree.1.card < L ∧ ∀ x : W,
        (sites.filter (fun i => predict tree x i ≠ out x i)).card ≤ e) ↔ price ≤ L) := by
  intro k hk F W ix rot s t name constant out H Tree predict sites e L hsp ends full oddCase laneCase save price
  constructor
  · rintro ⟨⟨nodes, ask, bias, aff, c⟩, hL, herr⟩
    exact L_meta_33626_aux.lower_bound hk s t name constant sites e L hsp nodes ask bias aff c hL herr
  · intro hL
    obtain ⟨nodes, ask, bias, aff, c, hcard, herr⟩ :=
      L_meta_33626_aux.upper_bound hk s t name constant sites e L hsp hL
    exact ⟨⟨nodes, ask, bias, aff, c⟩, hcard, herr⟩
