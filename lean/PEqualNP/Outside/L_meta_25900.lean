import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25900

def sgn (x : ZMod 2) : ℚ := if x = 0 then 1 else -1

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> simp [sgn, h11]

lemma sgn_sub (x y : ZMod 2) : sgn (x - y) = sgn x * sgn y := by
  have h01 : (0 : ZMod 2) - 1 = 1 := by decide
  have h11 : (1 : ZMod 2) - 1 = 0 := by decide
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> simp [sgn, h01, h11]

lemma sgn_sq (x : ZMod 2) : sgn x * sgn x = 1 := by
  rcases z2_cases x with rfl | rfl <;> norm_num [sgn]

lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sgn_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

lemma sum_sgn_subgroup {α : Type*} [AddCommGroup α] [DecidableEq α]
    (H : Finset α) (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) (hneg : ∀ x ∈ H, -x ∈ H)
    (φ : α → ZMod 2) (hφ : ∀ x ∈ H, ∀ y ∈ H, φ (x + y) = φ x + φ y) :
    (∑ x ∈ H, sgn (φ x)) = if ∀ x ∈ H, φ x = 0 then (H.card : ℚ) else 0 := by
  by_cases hall : ∀ x ∈ H, φ x = 0
  · rw [if_pos hall]
    have h1 : ∀ x ∈ H, sgn (φ x) = 1 := fun x hx => by rw [hall x hx, sgn_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [if_neg hall]
    have hex : ∃ y ∈ H, φ y ≠ 0 := by
      by_contra hno
      apply hall; intro x hx
      by_contra hne; exact hno ⟨x, hx, hne⟩
    obtain ⟨y, hy, hφy⟩ := hex
    have hsgny : sgn (φ y) = -1 := by unfold sgn; rw [if_neg hφy]
    have hshift : ∑ x ∈ H, sgn (φ (x + y)) = ∑ x ∈ H, sgn (φ x) := by
      refine Finset.sum_bij (fun x _ => x + y) (fun x hx => hadd x hx y hy) ?_ ?_ (fun _ _ => rfl)
      · intro x1 _ x2 _ h; exact add_right_cancel h
      · intro z hz
        exact ⟨z + (-y), hadd z hz (-y) (hneg y hy), by abel⟩
    have hneg_sum : ∑ x ∈ H, sgn (φ (x + y)) = -(∑ x ∈ H, sgn (φ x)) := by
      have hterm : ∀ x ∈ H, sgn (φ (x + y)) = -(sgn (φ x)) := fun x hx => by
        rw [hφ x hx y hy, sgn_add, hsgny, mul_neg_one]
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    linarith

def rotF {k : ℕ} (hk : 0 < k) (amount : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  x ⟨(j.val + k - amount % k) % k, Nat.mod_lt _ hk⟩

def mixF {k : ℕ} (hk : 0 < k) (gap : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  x j + x ⟨(j.val + gap) % k, Nat.mod_lt _ hk⟩ + x ⟨(j.val + k - gap % k) % k, Nat.mod_lt _ hk⟩

def layerF {k : ℕ} (hk : 0 < k) (gap : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  let m := mixF hk gap x
  m j + (1 + m ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) * m ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩

def polarF {k : ℕ} (hk : 0 < k) (gap : ℕ) (u v : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  layerF hk gap (u + v) - layerF hk gap u - layerF hk gap v

lemma rotF_add {k : ℕ} (hk : 0 < k) (a : ℕ) (x y : Fin k → ZMod 2) :
    rotF hk a (x + y) = rotF hk a x + rotF hk a y := rfl

lemma mixF_add {k : ℕ} (hk : 0 < k) (g : ℕ) (x y : Fin k → ZMod 2) :
    mixF hk g (x + y) = mixF hk g x + mixF hk g y := by
  funext j; simp only [mixF, Pi.add_apply]; ring

lemma mixF_zero {k : ℕ} (hk : 0 < k) (g : ℕ) :
    mixF hk g (0 : Fin k → ZMod 2) = 0 := by
  funext j; simp [mixF]

lemma layerF_zero {k : ℕ} (hk : 0 < k) (g : ℕ) :
    layerF hk g (0 : Fin k → ZMod 2) = 0 := by
  funext j; simp [layerF, mixF]

lemma polarF_apply {k : ℕ} (hk : 0 < k) (g : ℕ) (u v : Fin k → ZMod 2) (j : Fin k) :
    polarF hk g u v j =
      mixF hk g u ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ * mixF hk g v ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ +
      mixF hk g v ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ * mixF hk g u ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ := by
  simp only [polarF, layerF, Pi.sub_apply, mixF_add, Pi.add_apply]
  have : ∀ a1 a2 b1 b2 c1 c2 : ZMod 2,
      a1 + a2 + (1 + (b1 + b2)) * (c1 + c2) - (a1 + (1 + b1) * c1) - (a2 + (1 + b2) * c2) =
        b1 * c2 + b2 * c1 := by decide
  exact this _ _ _ _ _ _

lemma polarF_comm {k : ℕ} (hk : 0 < k) (g : ℕ) (u v : Fin k → ZMod 2) :
    polarF hk g u v = polarF hk g v u := by
  funext j; simp only [polarF_apply]; ring

lemma polarF_zero_left {k : ℕ} (hk : 0 < k) (g : ℕ) (v : Fin k → ZMod 2) :
    polarF hk g 0 v = 0 := by
  funext j; simp [polarF_apply, mixF_zero]

lemma polarF_add_left {k : ℕ} (hk : 0 < k) (g : ℕ) (u1 u2 v : Fin k → ZMod 2) :
    polarF hk g (u1 + u2) v = polarF hk g u1 v + polarF hk g u2 v := by
  funext j; simp only [polarF_apply, mixF_add, Pi.add_apply]; ring

lemma polarF_add_right {k : ℕ} (hk : 0 < k) (g : ℕ) (u v1 v2 : Fin k → ZMod 2) :
    polarF hk g u (v1 + v2) = polarF hk g u v1 + polarF hk g u v2 := by
  rw [polarF_comm hk g u (v1 + v2), polarF_add_left, polarF_comm hk g v1 u, polarF_comm hk g v2 u]

lemma layerF_diff_eq {k : ℕ} (hk : 0 < k) (g : ℕ) (v d : Fin k → ZMod 2) :
    layerF hk g (v + d) - layerF hk g v = polarF hk g v d + layerF hk g d := by
  funext j
  simp only [polarF, Pi.sub_apply, Pi.add_apply]
  have : ∀ a b c : ZMod 2, a - b = (a - b - c) + c := by decide
  exact this _ _ _

lemma layerF_add_eq {k : ℕ} (hk : 0 < k) (g : ℕ) (v d : Fin k → ZMod 2) :
    layerF hk g (v + d) = layerF hk g v + polarF hk g v d + layerF hk g d := by
  have h := layerF_diff_eq hk g v d
  have h2 := congrArg (fun x => x + layerF hk g v) h
  rw [sub_add_cancel] at h2
  rw [h2]; abel

lemma z2_neg_eq {α : Type*} (x : α → ZMod 2) : -x = x := by
  funext i; change -(x i) = x i; generalize x i = a; revert a; decide

lemma z2_add_self_fun {α : Type*} (x : α → ZMod 2) : x + x = 0 := by
  funext i; change x i + x i = 0; generalize x i = a; revert a; decide

lemma z2_add_self_S {k r : ℕ} (x : Fin r → Fin k → ZMod 2) : x + x = 0 :=
  funext fun t => z2_add_self_fun (x t)

lemma z2_sub_eq_add_fun {α : Type*} (x y : α → ZMod 2) : x - y = x + y := by
  funext i; change x i - y i = x i + y i; generalize x i = a; generalize y i = b; revert a b; decide

lemma take_succ_finRange {r : ℕ} (t : Fin r) :
    (List.finRange r).take (t.val + 1) = (List.finRange r).take t.val ++ [t] := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_take, List.length_finRange] at hi1
    have hilt : i < t.val + 1 := by omega
    by_cases hit : i < t.val
    · rw [List.getElem_take, List.getElem_append_left (by simp; omega), List.getElem_take]
    · have hieq : i = t.val := by omega
      subst hieq
      rw [List.getElem_take, List.getElem_append_right (by simp)]
      have hlen : ((List.finRange r).take t.val).length = t.val := by simp
      simp [hlen]

def pairingF {k r : ℕ} (b c : Fin r → Fin k → ZMod 2) : ZMod 2 :=
  ∑ t : Fin r, dotProduct (b t) (c t)

lemma pairingF_add_left {k r : ℕ} (b1 b2 c : Fin r → Fin k → ZMod 2) :
    pairingF (b1 + b2) c = pairingF b1 c + pairingF b2 c := by
  simp only [pairingF, Pi.add_apply, add_dotProduct, Finset.sum_add_distrib]

lemma pairingF_add_right {k r : ℕ} (b c1 c2 : Fin r → Fin k → ZMod 2) :
    pairingF b (c1 + c2) = pairingF b c1 + pairingF b c2 := by
  simp only [pairingF, Pi.add_apply, dotProduct_add, Finset.sum_add_distrib]

lemma pairingF_smul_left {k r : ℕ} (a : ZMod 2) (b c : Fin r → Fin k → ZMod 2) :
    pairingF (a • b) c = a * pairingF b c := by
  simp only [pairingF, Pi.smul_apply, smul_dotProduct, smul_eq_mul, Finset.mul_sum]

lemma pairingF_smul_right {k r : ℕ} (a : ZMod 2) (b c : Fin r → Fin k → ZMod 2) :
    pairingF b (a • c) = a * pairingF b c := by
  simp only [pairingF, Pi.smul_apply, dotProduct_smul, smul_eq_mul, Finset.mul_sum]

lemma pairingF_zero_left {k r : ℕ} (c : Fin r → Fin k → ZMod 2) :
    pairingF (0 : Fin r → Fin k → ZMod 2) c = 0 := by
  simp [pairingF]

lemma pairingF_zero_right {k r : ℕ} (b : Fin r → Fin k → ZMod 2) :
    pairingF b (0 : Fin r → Fin k → ZMod 2) = 0 := by
  simp [pairingF]

lemma pairingF_eq_zero_forall {k r : ℕ} (u : Fin r → Fin k → ZMod 2) :
    (∀ b : Fin r → Fin k → ZMod 2, pairingF b u = 0) ↔ u = 0 := by
  constructor
  · intro hall
    funext t j
    let e : Fin r → Fin k → ZMod 2 := fun t' j' => if t' = t ∧ j' = j then 1 else 0
    have he := hall e
    have hcalc : pairingF e u = u t j := by
      simp only [pairingF, dotProduct, e]
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'; simp [hj']
        · intro h; exact False.elim (h (Finset.mem_univ j))
      · intro t' _ ht'
        refine Finset.sum_eq_zero fun j' _ => by simp [ht']
      · intro h; exact False.elim (h (Finset.mem_univ t))
    rw [hcalc] at he; exact he
  · rintro rfl b; exact pairingF_zero_right b

lemma card_S_eq (k r : ℕ) :
    (Finset.univ : Finset (Fin r → Fin k → ZMod 2)).card = 2 ^ (k * r) := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, Fintype.card_fin, ← pow_mul]

lemma parseval_S {k r : ℕ} (f : (Fin r → Fin k → ZMod 2) → ℚ) :
    (2 : ℚ) ^ (k * r) * (∑ z : Fin r → Fin k → ZMod 2, (f z) ^ 2) =
      ∑ b : Fin r → Fin k → ZMod 2,
        (∑ z : Fin r → Fin k → ZMod 2, f z * sgn (pairingF b z)) ^ 2 := by
  have hexpand : ∀ b : Fin r → Fin k → ZMod 2,
      (∑ z : Fin r → Fin k → ZMod 2, f z * sgn (pairingF b z)) ^ 2 =
      ∑ z1 : Fin r → Fin k → ZMod 2, ∑ z2 : Fin r → Fin k → ZMod 2,
        f z1 * f z2 * sgn (pairingF b (z1 + z2)) := by
    intro b
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    rw [pairingF_add_right, sgn_add]; ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hswap : (∑ z1 : Fin r → Fin k → ZMod 2, ∑ b : Fin r → Fin k → ZMod 2,
      ∑ z2 : Fin r → Fin k → ZMod 2, f z1 * f z2 * sgn (pairingF b (z1 + z2))) =
      ∑ z1 : Fin r → Fin k → ZMod 2, ∑ z2 : Fin r → Fin k → ZMod 2,
        f z1 * f z2 * (∑ b : Fin r → Fin k → ZMod 2, sgn (pairingF b (z1 + z2))) := by
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    rw [Finset.mul_sum]
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  have horth : ∀ z2 : Fin r → Fin k → ZMod 2,
      (∑ b : Fin r → Fin k → ZMod 2, sgn (pairingF b (z1 + z2))) =
      if z2 = z1 then (2 : ℚ) ^ (k * r) else 0 := by
    intro z2
    have hsub := sum_sgn_subgroup (Finset.univ : Finset (Fin r → Fin k → ZMod 2))
      (fun _ _ _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
      (fun b => pairingF b (z1 + z2))
      (fun b1 _ b2 _ => pairingF_add_left b1 b2 (z1 + z2))
    rw [hsub]
    have hiff : (∀ b ∈ (Finset.univ : Finset (Fin r → Fin k → ZMod 2)),
        pairingF b (z1 + z2) = 0) ↔ z2 = z1 := by
      simp only [Finset.mem_univ, true_implies, pairingF_eq_zero_forall]
      constructor
      · intro h
        have h' := congrArg (fun x => z1 + x) h
        have hself : z1 + z1 = 0 := z2_add_self_S z1
        simpa [← add_assoc, hself] using h'
      · rintro rfl; exact z2_add_self_S _
    have hcard : ((Finset.univ : Finset (Fin r → Fin k → ZMod 2)).card : ℚ) = (2 : ℚ) ^ (k * r) := by
      rw [card_S_eq]; push_cast; rfl
    by_cases h : z2 = z1
    · rw [if_pos (hiff.mpr h), if_pos h, hcard]
    · rw [if_neg (fun hall => h (hiff.mp hall)), if_neg h]
  simp_rw [horth]
  rw [Finset.sum_eq_single z1]
  · simp [sq]; ring
  · intro z2 _ hz2; simp [hz2]
  · intro h; exact False.elim (h (Finset.mem_univ z1))

lemma finrank_dualKer_le {k r q : ℕ}
    (Q : (Fin r → Fin k → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2)) :
    let S := Fin r → Fin k → ZMod 2
    let dualK : Submodule (ZMod 2) S :=
      { carrier := {b : S | ∀ z : S, Q z = 0 → pairingF b z = 0}, add_mem' := fun {b1 b2} h1 h2 z hz => by
          rw [pairingF_add_left, h1 z hz, h2 z hz, add_zero]
        zero_mem' := fun z _ => pairingF_zero_left z
        smul_mem' := fun c {b} hb z hz => by
          rw [pairingF_smul_left, hb z hz, mul_zero] }
    Module.finrank (ZMod 2) dualK ≤ q := by
  classical
  intro S dualK
  let K : Finset S := Finset.univ.filter (fun z : S => Q z = 0)
  let D : Finset S := Finset.univ.filter (fun b : S => ∀ z : S, Q z = 0 → pairingF b z = 0)
  have hsum1 : ∑ z ∈ K, ∑ b : S, sgn (pairingF b z) = (2 : ℚ) ^ (k * r) := by
    have hinner : ∀ z : S, (∑ b : S, sgn (pairingF b z)) = if z = 0 then (2 : ℚ) ^ (k * r) else 0 := by
      intro z
      rw [sum_sgn_subgroup Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
          (fun _ _ => Finset.mem_univ _) (fun b => pairingF b z)
          (fun b1 _ b2 _ => pairingF_add_left b1 b2 z)]
      have hiff : (∀ b ∈ (Finset.univ : Finset S), pairingF b z = 0) ↔ z = 0 := by
        simpa using pairingF_eq_zero_forall z
      have hcard : ((Finset.univ : Finset S).card : ℚ) = (2 : ℚ) ^ (k * r) := by
        rw [card_S_eq]; push_cast; rfl
      by_cases hz : z = 0
      · rw [if_pos (hiff.mpr hz), if_pos hz, hcard]
      · rw [if_neg (fun h => hz (hiff.mp h)), if_neg hz]
    simp_rw [hinner]
    rw [Finset.sum_eq_single (0 : S)]
    · simp
    · intro z _ hz; simp [hz]
    · intro h0; exfalso; apply h0; simp [K]
  have hsum2 : ∑ b : S, ∑ z ∈ K, sgn (pairingF b z) = (D.card : ℚ) * (K.card : ℚ) := by
    have hinner : ∀ b : S, (∑ z ∈ K, sgn (pairingF b z)) =
        if b ∈ D then (K.card : ℚ) else 0 := by
      intro b
      have hKadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
        intro x hx y hy
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
        rw [map_add, hx, hy, add_zero]
      have hKneg : ∀ x ∈ K, -x ∈ K := by
        intro x hx
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [map_neg, hx, neg_zero]
      rw [sum_sgn_subgroup K hKadd hKneg (fun z => pairingF b z)
          (fun x _ y _ => pairingF_add_right b x y)]
      have hiff : (∀ z ∈ K, pairingF b z = 0) ↔ b ∈ D := by simp [K, D]
      by_cases hb : b ∈ D
      · rw [if_pos (hiff.mpr hb), if_pos hb]
      · rw [if_neg (fun h => hb (hiff.mp h)), if_neg hb]
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hprod_rat : (D.card : ℚ) * (K.card : ℚ) = (2 : ℚ) ^ (k * r) := by
    rw [← hsum2, Finset.sum_comm, hsum1]
  have hprod_nat : D.card * K.card = 2 ^ (k * r) := by exact_mod_cast hprod_rat
  have hD_card : D.card = 2 ^ Module.finrank (ZMod 2) dualK := by
    have hbij : D.card = Fintype.card dualK := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun b hb => (⟨b, (Finset.mem_filter.mp hb).2⟩ : dualK))
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h) ?_
      intro ⟨b, hb⟩ _
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩
    rw [hbij]
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := dualK)
    rw [ZMod.card] at h; exact h
  have hK_card : K.card = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker Q) := by
    have hbij : K.card = Fintype.card (LinearMap.ker Q) := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun z hz => (⟨z, (Finset.mem_filter.mp hz).2⟩ : LinearMap.ker Q))
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h) ?_
      intro ⟨z, hz⟩ _
      exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩, rfl⟩
    rw [hbij]
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker Q)
    rw [ZMod.card] at h; exact h
  rw [hD_card, hK_card, ← pow_add] at hprod_nat
  have hsum_fin : Module.finrank (ZMod 2) dualK + Module.finrank (ZMod 2) (LinearMap.ker Q) = k * r :=
    Nat.pow_right_injective (by decide : 1 < 2) hprod_nat
  have hrn : Module.finrank (ZMod 2) (LinearMap.range Q) +
      Module.finrank (ZMod 2) (LinearMap.ker Q) = Module.finrank (ZMod 2) S :=
    LinearMap.finrank_range_add_finrank_ker Q
  have hfinS : Module.finrank (ZMod 2) S = k * r := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
    rw [ZMod.card] at h
    have hc : Fintype.card S = 2 ^ (k * r) := by rw [← Finset.card_univ, card_S_eq]
    rw [hc] at h
    exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm
  rw [hfinS] at hrn
  have hr_le : Module.finrank (ZMod 2) (LinearMap.range Q) ≤ q := by
    calc Module.finrank (ZMod 2) (LinearMap.range Q)
        ≤ Module.finrank (ZMod 2) (Fin q → ZMod 2) := Submodule.finrank_le _
      _ = q := Module.finrank_fin_fun (ZMod 2)
  omega

lemma card_zero_on_test {k : ℕ} (test : Finset (Fin k)) :
    (Finset.univ.filter (fun u : Fin k → ZMod 2 => ∀ j ∈ test, u j = 0)).card =
      2 ^ (k - test.card) := by
  let U := Finset.univ.filter (fun u : Fin k → ZMod 2 => ∀ j ∈ test, u j = 0)
  let Rest := {j : Fin k // j ∉ test}
  have hbij : U.card = Fintype.card (Rest → ZMod 2) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun u _ => fun j : Rest => u j.val)
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro u1 hu1 u2 hu2 h
      funext j
      by_cases hj : j ∈ test
      · rw [(Finset.mem_filter.mp hu1).2 j hj, (Finset.mem_filter.mp hu2).2 j hj]
      · exact congrFun h ⟨j, hj⟩
    · intro f _
      refine ⟨fun j => if hj : j ∈ test then 0 else f ⟨j, hj⟩, ?_, ?_⟩
      · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j hj; simp [hj]
      · funext ⟨j, hj⟩; simp [hj]
  rw [hbij, Fintype.card_fun, ZMod.card]
  congr 1
  rw [Fintype.card_subtype]
  have hset : Finset.univ.filter (fun j : Fin k => j ∉ test) = Finset.univ \ test := by
    ext j; simp
  rw [hset, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]

-- Modular lemma 1: terminal factor square
lemma term_sq_lemma {k : ℕ} (test : Finset (Fin k)) (target p : Fin k → ZMod 2) :
    (∑ vr : Fin k → ZMod 2, if ∀ j ∈ test, vr j = target j then sgn (dotProduct p vr) else 0) ^ 2 =
    if ∀ j : Fin k, j ∉ test → p j = 0 then ((2 : ℕ) ^ (2 * (k - test.card)) : ℚ) else 0 := by
  let vt : Fin k → ZMod 2 := fun j => if j ∈ test then target j else 0
  let U : Finset (Fin k → ZMod 2) := Finset.univ.filter (fun u => ∀ j ∈ test, u j = 0)
  have hshift : (∑ vr : Fin k → ZMod 2, if ∀ j ∈ test, vr j = target j then sgn (dotProduct p vr) else 0) =
      sgn (dotProduct p vt) * ∑ u ∈ U, sgn (dotProduct p u) := by
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun vr _ => vr + vt) ?_ ?_ ?_ ?_
    · intro vr hvr
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hvr ⊢
      intro j hj
      simp only [Pi.add_apply, vt, if_pos hj, hvr j hj]
      exact congrFun (z2_add_self_fun target) j
    · intro v1 _ v2 _ h; exact add_right_cancel h
    · intro u hu
      refine ⟨u + vt, ?_, ?_⟩
      · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        intro j hj
        simp only [Pi.add_apply, vt, if_pos hj, hu j hj, zero_add]
      · rw [add_assoc, z2_add_self_fun vt, add_zero]
    · intro vr _
      rw [dotProduct_add, sgn_add, mul_comm (sgn (dotProduct p vt)), mul_assoc, sgn_sq, mul_one]
  have hUadd : ∀ x ∈ U, ∀ y ∈ U, x + y ∈ U := by
    intro x hx y hy
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
    intro j hj
    simp only [Pi.add_apply, hx j hj, hy j hj, add_zero]
  have hUneg : ∀ x ∈ U, -x ∈ U := fun x hx => by rw [z2_neg_eq]; exact hx
  have hUsgn := sum_sgn_subgroup U hUadd hUneg (fun u => dotProduct p u)
    (fun x _ y _ => dotProduct_add p x y)
  have hiff : (∀ u ∈ U, dotProduct p u = 0) ↔ (∀ j : Fin k, j ∉ test → p j = 0) := by
    constructor
    · intro hall j hj
      let ej : Fin k → ZMod 2 := fun i => if i = j then 1 else 0
      have hej : ej ∈ U := by
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, ej]
        intro i hi
        have hne : i ≠ j := fun h => hj (h ▸ hi)
        rw [if_neg hne]
      have h0 := hall ej hej
      have hcalc : dotProduct p ej = p j := by
        simp only [dotProduct, ej]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hi; simp [hi]
        · intro h; exact False.elim (h (Finset.mem_univ j))
      rw [hcalc] at h0; exact h0
    · intro hall u hu
      simp only [dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j ∈ test
      · rw [(Finset.mem_filter.mp hu).2 j hj, mul_zero]
      · rw [hall j hj, zero_mul]
  rw [hshift, mul_pow, sq (sgn _), sgn_sq, one_mul, hUsgn]
  by_cases hc : ∀ j : Fin k, j ∉ test → p j = 0
  · rw [if_pos (hiff.mpr hc), if_pos hc]
    have hcard : U.card = 2 ^ (k - test.card) := card_zero_on_test test
    rw [hcard]; push_cast; rw [← pow_mul, mul_comm 2]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]; simp

-- Modular lemma 2: round factor square R_t(b)^2 = weight b t
lemma round_sq_lemma {k s : ℕ} (hk : 0 < k) (gap : ℕ)
    (pin : Fin s → (Fin k → ZMod 2)) (pout : Fin s → (Fin k → ZMod 2))
    (inj_d : Fin s → (Fin k → ZMod 2)) (inj_r : Fin k → ZMod 2)
    (pb bt : Fin k → ZMod 2) :
    let loc : Finset (Fin k → ZMod 2) := Finset.univ.filter (fun v => ∀ p : Fin s,
      layerF hk gap (v + pin p) - layerF hk gap v + inj_d p = pout p)
    let dirs : Finset (Fin k → ZMod 2) := Finset.univ.filter (fun z => ∀ p : Fin s,
      polarF hk gap z (pin p) = 0)
    let rad : Finset (Fin k → ZMod 2) := dirs.filter (fun z => ∀ u ∈ dirs,
      dotProduct bt (polarF hk gap z u) = 0)
    let ph : (Fin k → ZMod 2) → ZMod 2 := fun v =>
      dotProduct pb v + dotProduct bt (layerF hk gap v + inj_r)
    (∑ v ∈ loc, sgn (ph v)) ^ 2 =
      if ∃ v ∈ loc, ∀ z ∈ rad, ph (v + z) = ph v then ((dirs.card * rad.card : ℕ) : ℚ) else 0 := by
  classical
  intro loc dirs rad ph
  have hphase_diff : ∀ v z : Fin k → ZMod 2,
      ph (v + z) - ph v =
        dotProduct pb z + dotProduct bt (polarF hk gap v z + layerF hk gap z) := by
    intro v z
    dsimp only [ph]
    rw [dotProduct_add, layerF_add_eq hk gap v z]
    have hre : layerF hk gap v + polarF hk gap v z + layerF hk gap z + inj_r =
        (layerF hk gap v + inj_r) + (polarF hk gap v z + layerF hk gap z) := by abel
    rw [hre, dotProduct_add]; abel
  have hdirs_add : ∀ x ∈ dirs, ∀ y ∈ dirs, x + y ∈ dirs := by
    intro x hx y hy
    simp only [dirs, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
    intro p; rw [polarF_add_left, hx p, hy p, add_zero]
  have hdirs_neg : ∀ x ∈ dirs, -x ∈ dirs := fun x hx => by rw [z2_neg_eq]; exact hx
  have hrad_add : ∀ x ∈ rad, ∀ y ∈ rad, x + y ∈ rad := by
    intro x hx y hy
    simp only [rad, Finset.mem_filter] at hx hy ⊢
    refine ⟨hdirs_add x hx.1 y hy.1, fun u hu => ?_⟩
    rw [polarF_add_left, dotProduct_add, hx.2 u hu, hy.2 u hu, add_zero]
  have hrad_neg : ∀ x ∈ rad, -x ∈ rad := fun x hx => by rw [z2_neg_eq]; exact hx
  by_cases hne : loc.Nonempty
  · obtain ⟨v0, hv0⟩ := hne
    have hmem_loc : ∀ u : Fin k → ZMod 2, v0 + u ∈ loc ↔ u ∈ dirs := by
      intro u
      simp only [loc, dirs, Finset.mem_filter, Finset.mem_univ, true_and]
      have hv0' := (Finset.mem_filter.mp hv0).2
      constructor
      · intro hu p
        have h1 := hu p
        have h2 := hv0' p
        rw [layerF_diff_eq, polarF_add_left] at h1
        rw [layerF_diff_eq] at h2
        have hsub : polarF hk gap v0 (pin p) + polarF hk gap u (pin p) +
            layerF hk gap (pin p) + inj_d p =
            polarF hk gap v0 (pin p) + layerF hk gap (pin p) + inj_d p := h1.trans h2.symm
        have hdiff := congrArg (fun x => x - (polarF hk gap v0 (pin p) +
            layerF hk gap (pin p) + inj_d p)) hsub
        simp only [sub_self] at hdiff
        rw [← hdiff]; abel
      · intro hu p
        have h2 := hv0' p
        rw [layerF_diff_eq, polarF_add_left, hu p, add_zero]
        rw [layerF_diff_eq] at h2
        exact h2
    have hR_shift : ∑ v ∈ loc, sgn (ph v) = ∑ u ∈ dirs, sgn (ph (v0 + u)) := by
      refine Finset.sum_bij (fun v _ => v + v0) ?_ ?_ ?_ ?_
      · intro v hv
        rw [← hmem_loc]
        have : v0 + (v + v0) = v := by
          rw [add_comm v v0, ← add_assoc, z2_add_self_fun v0, zero_add]
        rw [this]; exact hv
      · intro v1 _ v2 _ h; exact add_right_cancel h
      · intro u hu
        refine ⟨v0 + u, (hmem_loc u).mpr hu, ?_⟩
        rw [add_comm v0 u, add_assoc, z2_add_self_fun v0, add_zero]
      · intro v _
        have : v0 + (v + v0) = v := by
          rw [add_comm v v0, ← add_assoc, z2_add_self_fun v0, zero_add]
        rw [this]
    rw [hR_shift, sq, Finset.sum_mul]
    have hsq_reindex : (∑ u ∈ dirs, sgn (ph (v0 + u)) * ∑ u' ∈ dirs, sgn (ph (v0 + u'))) =
        ∑ z ∈ dirs, sgn (ph (v0 + z) - ph v0) *
          ∑ u ∈ dirs, sgn (dotProduct bt (polarF hk gap z u)) := by
      have hstep1 : ∀ u ∈ dirs, sgn (ph (v0 + u)) * ∑ u' ∈ dirs, sgn (ph (v0 + u')) =
          ∑ z ∈ dirs, sgn (ph (v0 + z) - ph v0) * sgn (dotProduct bt (polarF hk gap z u)) := by
        intro u hu
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun u' _ => u + u') (fun u' hu' => hdirs_add u hu u' hu') ?_ ?_ ?_
        · intro u1 _ u2 _ h; exact add_left_cancel h
        · intro z hz
          exact ⟨u + z, hdirs_add u hu z hz, by rw [← add_assoc, z2_add_self_fun u, zero_add]⟩
        · intro u' _
          set z := u + u'
          have hu'eq : u' = u + z := by simp only [z, ← add_assoc, z2_add_self_fun u, zero_add]
          rw [hu'eq, ← add_assoc, ← sgn_add, ← sgn_add]
          congr 1
          have h1 := hphase_diff (v0 + u) z
          have h2 := hphase_diff v0 z
          have h12 : ph (v0 + u) + ph (v0 + u + z) = ph (v0 + u + z) - ph (v0 + u) := by
            generalize ph (v0 + u) = a; generalize ph (v0 + u + z) = c; revert a c; decide
          have hre : polarF hk gap v0 z + polarF hk gap u z + layerF hk gap z =
              (polarF hk gap v0 z + layerF hk gap z) + polarF hk gap z u := by
            rw [polarF_comm hk gap u z]; abel
          rw [h12, h1, h2, polarF_add_left, hre, dotProduct_add, dotProduct_add, dotProduct_add]
          abel
      rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm
    rw [hsq_reindex]
    have hinner : ∀ z ∈ dirs,
        (∑ u ∈ dirs, sgn (dotProduct bt (polarF hk gap z u))) =
        if z ∈ rad then (dirs.card : ℚ) else 0 := by
      intro z hz
      rw [sum_sgn_subgroup dirs hdirs_add hdirs_neg
          (fun u => dotProduct bt (polarF hk gap z u))
          (fun u1 _ u2 _ => by rw [polarF_add_right, dotProduct_add])]
      have hiff : (∀ u ∈ dirs, dotProduct bt (polarF hk gap z u) = 0) ↔ z ∈ rad := by
        simp only [rad, Finset.mem_filter, hz, true_and]
      by_cases hzr : z ∈ rad
      · rw [if_pos (hiff.mpr hzr), if_pos hzr]
      · rw [if_neg (fun h => hzr (hiff.mp h)), if_neg hzr]
    have hrad_sum : (∑ z ∈ dirs, sgn (ph (v0 + z) - ph v0) *
        ∑ u ∈ dirs, sgn (dotProduct bt (polarF hk gap z u))) =
        (dirs.card : ℚ) * ∑ z ∈ rad, sgn (ph (v0 + z) - ph v0) := by
      have hcongr : ∀ z ∈ dirs,
          sgn (ph (v0 + z) - ph v0) * (∑ u ∈ dirs, sgn (dotProduct bt (polarF hk gap z u))) =
          if z ∈ rad then (dirs.card : ℚ) * sgn (ph (v0 + z) - ph v0) else 0 := by
        intro z hz; rw [hinner z hz]; split_ifs <;> ring
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr (Finset.filter_subset _ _), Finset.mul_sum]
    rw [hrad_sum]
    have hφ_add : ∀ z1 ∈ rad, ∀ z2 ∈ rad,
        (ph (v0 + (z1 + z2)) - ph v0) = (ph (v0 + z1) - ph v0) + (ph (v0 + z2) - ph v0) := by
      intro z1 hz1 z2 hz2
      have hz2_dir : z2 ∈ dirs := (Finset.mem_filter.mp hz2).1
      have hrad0 : dotProduct bt (polarF hk gap z1 z2) = 0 :=
        (Finset.mem_filter.mp hz1).2 z2 hz2_dir
      rw [hphase_diff, hphase_diff, hphase_diff, dotProduct_add, polarF_add_right,
          layerF_add_eq hk gap z1 z2]
      have hre : polarF hk gap v0 z1 + polarF hk gap v0 z2 +
          (layerF hk gap z1 + polarF hk gap z1 z2 + layerF hk gap z2) =
          (polarF hk gap v0 z1 + layerF hk gap z1) +
          (polarF hk gap v0 z2 + layerF hk gap z2) + polarF hk gap z1 z2 := by abel
      rw [hre, dotProduct_add, dotProduct_add, hrad0, add_zero]
      abel
    rw [sum_sgn_subgroup rad hrad_add hrad_neg (fun z => ph (v0 + z) - ph v0) hφ_add]
    have hcond_iff : (∀ z ∈ rad, ph (v0 + z) - ph v0 = 0) ↔
        (∃ v ∈ loc, ∀ z ∈ rad, ph (v + z) = ph v) := by
      constructor
      · intro h; exact ⟨v0, hv0, fun z hz => sub_eq_zero.mp (h z hz)⟩
      · rintro ⟨v, hv, hconst⟩ z hz
        have hu : v + v0 ∈ dirs := by
          rw [← hmem_loc]
          have : v0 + (v + v0) = v := by
            rw [add_comm v v0, ← add_assoc, z2_add_self_fun v0, zero_add]
          rw [this]; exact hv
        have hv_eq : v = v0 + (v + v0) := by
          rw [add_comm v v0, ← add_assoc, z2_add_self_fun v0, zero_add]
        have h0 : ph (v + z) - ph v = 0 := sub_eq_zero.mpr (hconst z hz)
        rw [hv_eq, hphase_diff, polarF_add_left] at h0
        rw [hphase_diff]
        have hrad0 : dotProduct bt (polarF hk gap (v + v0) z) = 0 := by
          rw [polarF_comm]; exact (Finset.mem_filter.mp hz).2 (v + v0) hu
        have hre : polarF hk gap v0 z + polarF hk gap (v + v0) z + layerF hk gap z =
            (polarF hk gap v0 z + layerF hk gap z) + polarF hk gap (v + v0) z := by abel
        rw [hre, dotProduct_add, hrad0, add_zero] at h0
        exact h0
    by_cases hc : ∃ v ∈ loc, ∀ z ∈ rad, ph (v + z) = ph v
    · rw [if_pos (hcond_iff.mpr hc), if_pos hc]; push_cast; rfl
    · rw [if_neg (fun h => hc (hcond_iff.mp h)), if_neg hc]; simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty, zero_pow (by decide : 2 ≠ 0)]
    have hno : ¬ ∃ v ∈ (∅ : Finset (Fin k → ZMod 2)), ∀ z ∈ rad, ph (v + z) = ph v := by
      rintro ⟨v, hv, _⟩; exact Finset.notMem_empty v hv
    rw [if_neg hno]

-- Modular lemma 3: Part 1 least-squares & fiber mean
lemma least_squares_lemma {k r q : ℕ}
    (hits : (Fin r → Fin k → ZMod 2) → ℕ)
    (energy : (Fin r → Fin k → ZMod 2) → ℕ)
    (hH_sq : ∀ b : Fin r → Fin k → ZMod 2,
      (∑ c : Fin r → Fin k → ZMod 2, (hits c : ℚ) * sgn (pairingF b c)) ^ 2 = (energy b : ℚ))
    (Q : (Fin r → Fin k → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2)) :
    let S := Fin r → Fin k → ZMod 2
    let visible := fun b : S => ∀ z : S, Q z = 0 → pairingF b z = 0
    let lost : ℚ := ∑ b ∈ (Finset.univ : Finset S).filter (fun m => ¬visible m), (energy b : ℚ)
    let err := fun (dec : (Fin q → ZMod 2) → ℚ) =>
      (2 : ℚ)^(k*r) * (∑ z : S, ((hits z : ℚ) - dec (Q z))^2)
    (∀ dec, lost ≤ err dec) ∧ (∃ dec, err dec = lost) := by
  classical
  intro S visible lost err
  let H : S → ℚ := fun b => ∑ c : S, (hits c : ℚ) * sgn (pairingF b c)
  let K : Finset S := Finset.univ.filter (fun z : S => Q z = 0)
  have hKpos : (0 : ℚ) < (K.card : ℚ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨0, by simp [K]⟩)
  have hhat_zero_invis : ∀ (dec : (Fin q → ZMod 2) → ℚ) (b : S), ¬ visible b →
      ∑ z : S, dec (Q z) * sgn (pairingF b z) = 0 := by
    intro dec b hinvis
    have hex : ∃ u : S, Q u = 0 ∧ pairingF b u ≠ 0 := by
      by_contra hno
      apply hinvis; intro u hu
      by_contra hne; exact hno ⟨u, hu, hne⟩
    obtain ⟨u, huQ, hub⟩ := hex
    have hsgnu : sgn (pairingF b u) = -1 := by unfold sgn; rw [if_neg hub]
    have hshift : ∑ z : S, dec (Q (z + u)) * sgn (pairingF b (z + u)) =
        ∑ z : S, dec (Q z) * sgn (pairingF b z) := by
      refine Finset.sum_bij (fun z _ => z + u) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => add_right_cancel h)
        (fun z _ => ⟨z + u, Finset.mem_univ _, by rw [add_assoc, z2_add_self_S u, add_zero]⟩)
        (fun _ _ => rfl)
    have hneg : ∑ z : S, dec (Q (z + u)) * sgn (pairingF b (z + u)) =
        -(∑ z : S, dec (Q z) * sgn (pairingF b z)) := by
      have hterm : ∀ z : S, dec (Q (z + u)) * sgn (pairingF b (z + u)) =
          -(dec (Q z) * sgn (pairingF b z)) := by
        intro z
        rw [map_add, huQ, add_zero, pairingF_add_right, sgn_add, hsgnu]
        ring
      simp_rw [hterm, Finset.sum_neg_distrib]
    linarith
  have herr_parseval : ∀ dec : (Fin q → ZMod 2) → ℚ,
      err dec =
        (∑ b ∈ (Finset.univ : Finset S).filter (fun m => visible m),
          (H b - ∑ z : S, dec (Q z) * sgn (pairingF b z)) ^ 2) + lost := by
    intro dec
    dsimp only [err, lost]
    rw [parseval_S (fun z => (hits z : ℚ) - dec (Q z))]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m : S => visible m)]
    have hdiff : ∀ b : Fin r → Fin k → ZMod 2,
        (∑ z : Fin r → Fin k → ZMod 2, ((hits z : ℚ) - dec (Q z)) * sgn (pairingF b z)) =
        H b - ∑ z : S, dec (Q z) * sgn (pairingF b z) := by
      intro b; dsimp only [H]; simp_rw [sub_mul, Finset.sum_sub_distrib]; rfl
    simp_rw [hdiff]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    have hinvis : ¬ visible b := (Finset.mem_filter.mp hb).2
    rw [hhat_zero_invis dec b hinvis, sub_zero, hH_sq b]
  constructor
  · intro dec
    rw [herr_parseval dec]
    have hnonneg : 0 ≤ ∑ b ∈ (Finset.univ : Finset S).filter (fun m => visible m),
        (H b - ∑ z : S, dec (Q z) * sgn (pairingF b z)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  · let decOpt : (Fin q → ZMod 2) → ℚ := fun y =>
      (∑ z ∈ Finset.univ.filter (fun z : S => Q z = y), (hits z : ℚ)) / (K.card : ℚ)
    refine ⟨decOpt, ?_⟩
    rw [herr_parseval decOpt]
    have hzero_vis : ∀ b ∈ (Finset.univ : Finset S).filter (fun m => visible m),
        (H b - ∑ z : S, decOpt (Q z) * sgn (pairingF b z)) ^ 2 = 0 := by
      intro b hb
      have hvis : visible b := (Finset.mem_filter.mp hb).2
      have heq : ∑ z : S, decOpt (Q z) * sgn (pairingF b z) = H b := by
        have hfiber : ∀ z : S, decOpt (Q z) = (∑ u ∈ K, (hits (z + u) : ℚ)) / (K.card : ℚ) := by
          intro z
          dsimp only [decOpt]
          congr 1
          refine Finset.sum_bij (fun z' _ => z' + z) ?_ ?_ ?_ ?_
          · intro z' hz'
            simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hz' ⊢
            rw [map_add, hz']; exact z2_add_self_fun (Q z)
          · intro z1 _ z2 _ h; exact add_right_cancel h
          · intro u hu
            refine ⟨z + u, ?_, ?_⟩
            · simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
              rw [map_add, hu, add_zero]
            · rw [add_comm z u, add_assoc, z2_add_self_S z, add_zero]
          · intro z' _
            have : z + (z' + z) = z' := by
              rw [add_comm z' z, ← add_assoc, z2_add_self_S z, zero_add]
            rw [this]
        have hstep_sum : ∑ z : S, decOpt (Q z) * sgn (pairingF b z) =
            (∑ u ∈ K, ∑ z : S, (hits (z + u) : ℚ) * sgn (pairingF b z)) * (K.card : ℚ)⁻¹ := by
          have hterm : ∀ z : S, decOpt (Q z) * sgn (pairingF b z) =
              (∑ u ∈ K, (hits (z + u) : ℚ) * sgn (pairingF b z)) * (K.card : ℚ)⁻¹ := by
            intro z
            rw [hfiber z, div_eq_mul_inv, mul_right_comm, Finset.sum_mul]
          simp_rw [hterm]
          rw [← Finset.sum_mul, Finset.sum_comm]
        rw [hstep_sum]
        have hinner : ∀ u ∈ K, (∑ z : S, (hits (z + u) : ℚ) * sgn (pairingF b z)) = H b := by
          intro u hu
          have hub : pairingF b u = 0 := hvis u (Finset.mem_filter.mp hu).2
          dsimp only [H]
          refine Finset.sum_bij (fun z _ => z + u) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => add_right_cancel h)
            (fun z _ => ⟨z + u, Finset.mem_univ _, by rw [add_assoc, z2_add_self_S u, add_zero]⟩) ?_
          intro z _
          rw [pairingF_add_right, hub, add_zero]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
        have hne : (K.card : ℚ) ≠ 0 := ne_of_gt hKpos
        field_simp [hne]
      rw [heq, sub_self, zero_pow (by decide : 2 ≠ 0)]
    rw [Finset.sum_eq_zero hzero_vis, zero_add]

end PEqualNP.Outside.L_meta_25900

open PEqualNP.Outside.L_meta_25900 in
theorem PEqualNP.Outside.L_meta_25900 : ∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ (col : Bool) (raw : W) (delta : Fin s → W)
    (path : Fin (r+1) → Fin s → W) (test : Finset (Fin k)) (target : W),
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let S := Fin r → W
    let valid := ∀ p, path 0 p = rot initial (delta p)
    let localSet := fun (t : Fin r) => (Finset.univ : Finset W).filter (fun v => ∀ p : Fin s,
      layer gap (v+path t.castSucc p) - layer gap v + rot (inject t.val) (delta p) = path t.succ p)
    let hits := fun (c : S) => ((Finset.univ : Finset W).filter (fun name =>
      (∀ t p, state (name,c) (raw+delta p) t - state (name,c) raw t = path t p) ∧
      (∀ j ∈ test, state (name,c) raw (Fin.last r) j = target j))).card
    let prev := fun (b : S) (j : Nat) => ∑ t : Fin r, (if t.val+1 = j then b t else 0)
    let pairing := fun (b c : S) => ∑ t : Fin r, dotProduct (b t) (c t)
    let phase := fun (b : S) (t : Fin r) (v : W) => dotProduct (prev b t.val) v +
      dotProduct (b t) (layer gap v + rot (inject t.val) raw)
    let polar := fun (u v : W) => layer gap (u+v) - layer gap u - layer gap v + layer gap 0
    let dirs := fun (t : Fin r) => (Finset.univ : Finset W).filter
      (fun z => ∀ p, polar z (path t.castSucc p) = 0)
    let rad := fun (b : S) (t : Fin r) => (dirs t).filter
      (fun z => ∀ u ∈ dirs t, dotProduct (b t) (polar z u) = 0)
    let weight := fun (b : S) (t : Fin r) =>
      if ∃ v ∈ localSet t, ∀ z ∈ rad b t, phase b t (v+z) = phase b t v
      then (dirs t).card * (rad b t).card else 0
    let energy := fun b : S =>
      if valid ∧ (∀ j : Fin k, j ∉ test → prev b r j = 0) then
        (2 : Nat)^(2*(k-test.card)) * (∏ t : Fin r, weight b t)
      else 0
    let supp := (Finset.univ : Finset S).filter (fun b => 0 < energy b)
    ∀ q : Nat,
      (∀ Q : S →ₗ[F] (Fin q → F),
        let visible := fun b : S => ∀ z : S, Q z = 0 → pairing b z = 0
        let lost : ℚ := ∑ b ∈ (Finset.univ : Finset S).filter (fun m => ¬visible m), (energy b : ℚ)
        let err := fun (dec : (Fin q → F) → ℚ) =>
          (2 : ℚ)^(k*r) * (∑ z : S, ((hits z : ℚ) - dec (Q z))^2)
        (∀ dec, lost ≤ err dec) ∧ (∃ dec, err dec = lost)) ∧
      ((∃ (Q : S →ₗ[F] (Fin q → F)) (dec : (Fin q → F) → Nat), ∀ z, dec (Q z) = hits z) ↔
        Module.finrank F (Submodule.span F (supp : Set S)) ≤ q) := by
  classical
  intro k r s hk F W ix rot layer col raw delta path test target
    initial gap inject state S valid localSet hits prev pairing phase polar dirs rad weight energy supp
  have hrot_eq : ∀ a x, rot a x = rotF hk a x := fun _ _ => rfl
  have hlayer_eq : ∀ g x, layer g x = layerF hk g x := fun _ _ => rfl
  have hpair_eq : ∀ b c, pairing b c = pairingF b c := fun _ _ => rfl
  have hpolar_eq : ∀ u v, polar u v = polarF hk gap u v := fun u v => by
    dsimp only [polar]
    simp_rw [hlayer_eq]
    rw [layerF_zero, add_zero]
    rfl
  have hstate0 : ∀ data key, state data key 0 = rot initial key + data.1 := fun _ _ => rfl
  have hstate_succ : ∀ data key (t : Fin r),
      state data key t.succ = layer gap (state data key t.castSucc) + rot (inject t.val) key + data.2 t := by
    intro data key t
    dsimp only [state]
    rw [Fin.val_succ, take_succ_finRange t, List.foldl_append]
    rfl
  have hdiff0 : ∀ data p,
      state data (raw + delta p) 0 - state data raw 0 = rot initial (delta p) := by
    intro data p
    rw [hstate0, hstate0, hrot_eq, rotF_add, ← hrot_eq, ← hrot_eq]
    abel
  have hdiff_succ : ∀ data (t : Fin r) p,
      state data (raw + delta p) t.castSucc - state data raw t.castSucc = path t.castSucc p →
      state data (raw + delta p) t.succ - state data raw t.succ =
        layer gap (state data raw t.castSucc + path t.castSucc p) -
          layer gap (state data raw t.castSucc) + rot (inject t.val) (delta p) := by
    intro data t p hprev
    have hadd : state data (raw + delta p) t.castSucc =
        state data raw t.castSucc + path t.castSucc p := by
      have := congrArg (fun x => x + state data raw t.castSucc) hprev
      simpa [sub_add_cancel, add_comm] using this
    rw [hstate_succ, hstate_succ, hadd, hrot_eq, rotF_add, ← hrot_eq, ← hrot_eq]
    abel
  -- Bijection between (name, c) : W × S and trajectory v : Fin (r+1) → W
  let traj : W × S → (Fin (r + 1) → W) := fun data t => state data raw t
  let fromTraj : (Fin (r + 1) → W) → W × S := fun v =>
    (v 0 - rot initial raw, fun t => v t.succ - layer gap (v t.castSucc) - rot (inject t.val) raw)
  have htraj_inv : ∀ v : Fin (r + 1) → W, traj (fromTraj v) = v := by
    intro v
    suffices ∀ (n : ℕ) (hn : n ≤ r),
        traj (fromTraj v) ⟨n, Nat.lt_succ_of_le hn⟩ = v ⟨n, Nat.lt_succ_of_le hn⟩ by
      funext t; exact this t.val (Nat.le_of_lt_succ t.isLt)
    intro n
    induction n with
    | zero =>
      intro _; change state (fromTraj v) raw 0 = v 0; rw [hstate0]; dsimp only [fromTraj]; abel
    | succ n ih =>
      intro hn
      let tn : Fin r := ⟨n, by omega⟩
      change state (fromTraj v) raw tn.succ = v tn.succ
      have ih' : state (fromTraj v) raw tn.castSucc = v tn.castSucc := ih (by omega)
      rw [hstate_succ, ih']; dsimp only [fromTraj]; abel
  have hfrom_inv : ∀ data : W × S, fromTraj (traj data) = data := by
    rintro ⟨name, c⟩
    apply Prod.ext
    · dsimp only [fromTraj, traj]; rw [hstate0]; abel
    · funext t; dsimp only [fromTraj, traj]; rw [hstate_succ]; abel
  let trajEquiv : (Fin (r + 1) → W) ≃ W × S :=
    { toFun := fromTraj, invFun := traj, left_inv := htraj_inv, right_inv := hfrom_inv }
  have hgood_iff : ∀ v : Fin (r + 1) → W,
      ((∀ t p, state (fromTraj v) (raw + delta p) t - state (fromTraj v) raw t = path t p) ∧
        (∀ j ∈ test, state (fromTraj v) raw (Fin.last r) j = target j)) ↔
      (valid ∧ (∀ t : Fin r, v t.castSucc ∈ localSet t) ∧
        (∀ j ∈ test, v (Fin.last r) j = target j)) := by
    intro v
    have hv : ∀ t : Fin (r + 1), state (fromTraj v) raw t = v t := fun t =>
      congrFun (htraj_inv v) t
    simp_rw [hv]
    constructor
    · rintro ⟨hdiff, hterm⟩
      refine ⟨fun p => ?_, fun t => ?_, hterm⟩
      · have h0 := hdiff 0 p; rw [← hv 0, hdiff0] at h0; exact h0.symm
      · simp only [localSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro p
        have hprev := hdiff t.castSucc p
        have hnext := hdiff t.succ p
        rw [← hv t.castSucc] at hprev
        rw [← hv t.succ, hdiff_succ (fromTraj v) t p hprev, hv t.castSucc] at hnext
        exact hnext
    · rintro ⟨hval, hloc, hterm⟩
      refine ⟨?_, hterm⟩
      suffices ∀ (n : ℕ) (hn : n ≤ r) (p : Fin s),
          state (fromTraj v) (raw + delta p) ⟨n, Nat.lt_succ_of_le hn⟩ -
            v ⟨n, Nat.lt_succ_of_le hn⟩ = path ⟨n, Nat.lt_succ_of_le hn⟩ p by
        intro t p; exact this t.val (Nat.le_of_lt_succ t.isLt) p
      intro n
      induction n with
      | zero =>
        intro _ p
        change state (fromTraj v) (raw + delta p) 0 - v 0 = path 0 p
        rw [← hv 0, hdiff0]; exact (hval p).symm
      | succ n ih =>
        intro hn p
        let tn : Fin r := ⟨n, by omega⟩
        change state (fromTraj v) (raw + delta p) tn.succ - v tn.succ = path tn.succ p
        have hprev : state (fromTraj v) (raw + delta p) tn.castSucc -
            state (fromTraj v) raw tn.castSucc = path tn.castSucc p := by
          rw [hv tn.castSucc]; exact ih (by omega) p
        rw [← hv tn.succ, hdiff_succ (fromTraj v) tn p hprev, hv tn.castSucc]
        exact (Finset.mem_filter.mp (hloc tn)).2 p
  have hexp_regroup : ∀ (b : S) (v : Fin (r + 1) → W),
      pairing b (fromTraj v).2 =
        dotProduct (prev b r) (v (Fin.last r)) + ∑ t : Fin r, phase b t (v t.castSucc) := by
    intro b v
    have hsplit : pairing b (fromTraj v).2 =
        (∑ t : Fin r, dotProduct (b t) (v t.succ)) +
        ∑ t : Fin r, dotProduct (b t) (layer gap (v t.castSucc) + rot (inject t.val) raw) := by
      dsimp only [pairing, fromTraj]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have heq : v t.succ - layer gap (v t.castSucc) - rot (inject t.val) raw =
          v t.succ + (layer gap (v t.castSucc) + rot (inject t.val) raw) := by
        rw [z2_sub_eq_add_fun, z2_sub_eq_add_fun, add_assoc]
      rw [heq, dotProduct_add]
    have hprev_sum : ∑ t : Fin r, dotProduct (b t) (v t.succ) =
        dotProduct (prev b r) (v (Fin.last r)) +
        ∑ t : Fin r, dotProduct (prev b t.val) (v t.castSucc) := by
      have h1 : ∑ j : Fin (r + 1), dotProduct (prev b j.val) (v j) =
          ∑ t : Fin r, dotProduct (b t) (v t.succ) := by
        have hterm : ∀ j : Fin (r + 1), dotProduct (prev b j.val) (v j) =
            ∑ t : Fin r, if t.val + 1 = j.val then dotProduct (b t) (v j) else 0 := by
          intro j; dsimp only [prev]; rw [sum_dotProduct]
          refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
        simp_rw [hterm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_eq_single t.succ]
        · simp
        · intro j _ hj
          have hne : t.val + 1 ≠ j.val := fun h => hj (Fin.ext (by simp [h]))
          rw [if_neg hne]
        · intro h; exact False.elim (h (Finset.mem_univ t.succ))
      rw [← h1, Fin.sum_univ_castSucc]
      simp [Fin.val_last, Fin.val_castSucc, add_comm]
    rw [hsplit, hprev_sum, add_assoc, ← Finset.sum_add_distrib]
  -- Walsh transform H b
  let H : S → ℚ := fun b => ∑ c : S, (hits c : ℚ) * sgn (pairingF b c)
  have hH_factor : ∀ b : S,
      H b = if valid then
        (∑ vr : W, if ∀ j ∈ test, vr j = target j then sgn (dotProduct (prev b r) vr) else 0) *
        ∏ t : Fin r, ∑ v ∈ localSet t, sgn (phase b t v)
      else 0 := by
    intro b
    let goodData : W × S → Prop := fun data =>
      (∀ t p, state data (raw + delta p) t - state data raw t = path t p) ∧
      (∀ j ∈ test, state data raw (Fin.last r) j = target j)
    have hsum_prod : H b = ∑ data : W × S, if goodData data then sgn (pairing b data.2) else 0 := by
      dsimp only [H]
      have hhits : ∀ c : S, (hits c : ℚ) * sgn (pairingF b c) =
          ∑ name : W, if goodData (name, c) then sgn (pairing b c) else 0 := by
        intro c
        dsimp only [hits, goodData]
        rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun name _ => by split_ifs <;> simp [hpair_eq]
      simp_rw [hhits]
      rw [Finset.sum_comm]
      exact (Fintype.sum_prod_type (fun data : W × S =>
        if goodData data then sgn (pairing b data.2) else 0)).symm
    rw [hsum_prod, ← Equiv.sum_comp trajEquiv]
    dsimp only [trajEquiv, Equiv.coe_fn_mk, goodData]
    have hrew : ∀ v : Fin (r + 1) → W,
        (if (∀ t p, state (fromTraj v) (raw + delta p) t - state (fromTraj v) raw t = path t p) ∧
          (∀ j ∈ test, state (fromTraj v) raw (Fin.last r) j = target j)
        then sgn (pairing b (fromTraj v).2) else 0) =
        if valid ∧ (∀ t : Fin r, v t.castSucc ∈ localSet t) ∧
          (∀ j ∈ test, v (Fin.last r) j = target j)
        then sgn (dotProduct (prev b r) (v (Fin.last r))) *
          ∏ t : Fin r, sgn (phase b t (v t.castSucc))
        else 0 := by
      intro v
      by_cases hP : (∀ t p, state (fromTraj v) (raw + delta p) t - state (fromTraj v) raw t = path t p) ∧
          (∀ j ∈ test, state (fromTraj v) raw (Fin.last r) j = target j)
      · rw [if_pos hP, if_pos ((hgood_iff v).mp hP), hexp_regroup b v, sgn_add, sgn_sum]
      · rw [if_neg hP, if_neg (fun h => hP ((hgood_iff v).mpr h))]
    simp_rw [hrew]
    by_cases hval : valid
    · rw [if_pos hval]
      let splitEquiv : (Fin r → W) × W ≃ (Fin (r + 1) → W) :=
        { toFun := fun p => Fin.snoc p.1 p.2
          invFun := fun v => (fun t => v t.castSucc, v (Fin.last r))
          left_inv := fun ⟨vi, vr⟩ => by
            apply Prod.ext
            · funext t; simp [Fin.snoc_castSucc]
            · simp [Fin.snoc_last]
          right_inv := fun v => by
            funext t
            refine Fin.lastCases ?_ (fun i => ?_) t
            · simp [Fin.snoc_last]
            · simp [Fin.snoc_castSucc] }
      rw [← Equiv.sum_comp splitEquiv, Fintype.sum_prod_type]
      simp only [splitEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]
      have hterm : ∀ (vi : Fin r → W) (vr : W),
          (if valid ∧ (∀ t : Fin r, vi t ∈ localSet t) ∧ (∀ j ∈ test, vr j = target j)
          then sgn (dotProduct (prev b r) vr) * ∏ t : Fin r, sgn (phase b t (vi t))
          else 0) =
          (if ∀ j ∈ test, vr j = target j then sgn (dotProduct (prev b r) vr) else 0) *
          ∏ t : Fin r, if vi t ∈ localSet t then sgn (phase b t (vi t)) else 0 := by
        intro vi vr
        by_cases hvi : ∀ t : Fin r, vi t ∈ localSet t
        · have hprod : (∏ t : Fin r, if vi t ∈ localSet t then sgn (phase b t (vi t)) else 0) =
              ∏ t : Fin r, sgn (phase b t (vi t)) :=
            Finset.prod_congr rfl fun t _ => if_pos (hvi t)
          rw [hprod]
          by_cases hvr : ∀ j ∈ test, vr j = target j
          · simp [hval, hvi, hvr]
          · simp [hval, hvi, hvr]
        · have hex : ∃ t : Fin r, vi t ∉ localSet t := by
            by_contra h; exact hvi (fun t => by by_contra ht; exact h ⟨t, ht⟩)
          obtain ⟨t0, ht0⟩ := hex
          have hprod0 : (∏ t : Fin r, if vi t ∈ localSet t then sgn (phase b t (vi t)) else 0) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ t0) (if_neg ht0)
          rw [hprod0, mul_zero, if_neg (fun h => hvi h.2.1)]
      simp_rw [hterm]
      rw [Finset.sum_comm]
      have hfact : (∑ vr : W, ∑ vi : Fin r → W,
          (if ∀ j ∈ test, vr j = target j then sgn (dotProduct (prev b r) vr) else 0) *
          ∏ t : Fin r, if vi t ∈ localSet t then sgn (phase b t (vi t)) else 0) =
          (∑ vr : W, if ∀ j ∈ test, vr j = target j then sgn (dotProduct (prev b r) vr) else 0) *
          (∑ vi : Fin r → W, ∏ t : Fin r, if vi t ∈ localSet t then sgn (phase b t (vi t)) else 0) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun vr _ => (Finset.mul_sum _ _ _).symm
      rw [hfact]
      congr 1
      have hps := (Fintype.prod_sum (fun (t : Fin r) (v : W) =>
        if v ∈ localSet t then sgn (phase b t v) else 0)).symm
      rw [hps]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [← Finset.sum_filter]
      congr 1; ext v; simp
    · rw [if_neg hval]
      refine Finset.sum_eq_zero fun v _ => by simp [hval]
  have hH_sq : ∀ b : S, (H b) ^ 2 = (energy b : ℚ) := by
    intro b
    rw [hH_factor b]
    dsimp only [energy]
    by_cases hval : valid
    · rw [if_pos hval, mul_pow, term_sq_lemma test target (prev b r), ← Finset.prod_pow]
      have hr_eq : ∀ t : Fin r, (∑ v ∈ localSet t, sgn (phase b t v)) ^ 2 = (weight b t : ℚ) := by
        intro t
        have hlem := round_sq_lemma hk gap (fun p => path t.castSucc p) (fun p => path t.succ p)
          (fun p => rot (inject t.val) (delta p)) (rot (inject t.val) raw) (prev b t.val) (b t)
        have hdirs_eq : dirs t = Finset.univ.filter (fun z => ∀ p : Fin s,
            polarF hk gap z (path t.castSucc p) = 0) := by
          ext z; simp only [dirs, Finset.mem_filter, Finset.mem_univ, true_and, hpolar_eq]
        have hrad_eq : rad b t = (dirs t).filter (fun z => ∀ u ∈ dirs t,
            dotProduct (b t) (polarF hk gap z u) = 0) := by
          ext z; simp only [rad, Finset.mem_filter, hpolar_eq]
        simpa only [weight, localSet, phase, hlayer_eq, hdirs_eq, hrad_eq,
          Nat.cast_ite, Nat.cast_zero] using hlem
      simp_rw [hr_eq]
      by_cases htest : ∀ j : Fin k, j ∉ test → prev b r j = 0
      · rw [if_pos htest, if_pos ⟨hval, htest⟩]; push_cast; rfl
      · rw [if_neg htest, if_neg (fun h => htest h.2)]; simp
    · rw [if_neg hval, if_neg (fun h => hval h.1)]; simp
  intro q
  have hpart1 : ∀ Q : S →ₗ[F] (Fin q → F),
      let visible := fun b : S => ∀ z : S, Q z = 0 → pairing b z = 0
      let lost : ℚ := ∑ b ∈ (Finset.univ : Finset S).filter (fun m => ¬visible m), (energy b : ℚ)
      let err := fun (dec : (Fin q → F) → ℚ) =>
        (2 : ℚ)^(k*r) * (∑ z : S, ((hits z : ℚ) - dec (Q z))^2)
      (∀ dec, lost ≤ err dec) ∧ (∃ dec, err dec = lost) := fun Q =>
    least_squares_lemma hits energy hH_sq Q
  refine ⟨hpart1, ?_⟩
  constructor
  · rintro ⟨Q, dec, hrec⟩
    have hp := (hpart1 Q).1 (fun y => (dec y : ℚ))
    have herr0 : (2 : ℚ) ^ (k * r) * (∑ z : S, ((hits z : ℚ) - (dec (Q z) : ℚ)) ^ 2) = 0 := by
      have h0 : ∀ z : S, ((hits z : ℚ) - (dec (Q z) : ℚ)) ^ 2 = 0 := fun z => by
        rw [hrec z, sub_self, zero_pow (by decide : 2 ≠ 0)]
      simp [h0]
    dsimp only at hp
    rw [herr0] at hp
    let dualK : Submodule F S :=
      { carrier := {b : S | ∀ z : S, Q z = 0 → pairingF b z = 0}, add_mem' := fun {b1 b2} h1 h2 z hz => by rw [pairingF_add_left, h1 z hz, h2 z hz, add_zero]
        zero_mem' := fun z _ => pairingF_zero_left z
        smul_mem' := fun c {b} hb z hz => by rw [pairingF_smul_left, hb z hz, mul_zero] }
    have hsub : (supp : Set S) ⊆ (dualK : Set S) := by
      intro b hb
      have hb_pos : 0 < energy b := (Finset.mem_filter.mp hb).2
      change ∀ z : S, Q z = 0 → pairingF b z = 0
      by_contra hnot
      have hmem : b ∈ (Finset.univ : Finset S).filter (fun m => ¬ (∀ z : S, Q z = 0 → pairing m z = 0)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpair_eq]
        exact hnot
      have hge : (energy b : ℚ) ≤ ∑ m ∈ (Finset.univ : Finset S).filter
          (fun m => ¬ (∀ z : S, Q z = 0 → pairing m z = 0)), (energy m : ℚ) :=
        Finset.single_le_sum (fun m _ => Nat.cast_nonneg (energy m)) hmem
      have hpos : (0 : ℚ) < (energy b : ℚ) := Nat.cast_pos.mpr hb_pos
      linarith
    have hspan_le : Submodule.span F (supp : Set S) ≤ dualK := Submodule.span_le.mpr hsub
    exact le_trans (Submodule.finrank_mono hspan_le) (finrank_dualKer_le Q)
  · intro hle
    let U := Submodule.span F (supp : Set S)
    let d := Module.finrank F U
    let bas := Module.finBasis F U
    let Q : S →ₗ[F] (Fin q → F) :=
      { toFun := fun z i => if hi : i.val < d then pairingF (bas ⟨i.val, hi⟩).val z else 0
        map_add' := fun z1 z2 => by
          funext i; simp only [Pi.add_apply]; split_ifs
          · exact pairingF_add_right _ z1 z2
          · simp
        map_smul' := fun c z => by
          funext i; simp only [Pi.smul_apply, smul_eq_mul]; split_ifs
          · exact pairingF_smul_right c _ z
          · simp }
    have hlost0 : ∑ b ∈ (Finset.univ : Finset S).filter
        (fun m => ¬ (∀ z : S, Q z = 0 → pairing m z = 0)), (energy b : ℚ) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hinvis : ¬ (∀ z : S, Q z = 0 → pairing b z = 0) := (Finset.mem_filter.mp hb).2
      have hb_not_supp : b ∉ supp := by
        intro hbs
        apply hinvis
        intro z hz
        have hbas0 : ∀ j : Fin d, pairingF (bas j).val z = 0 := by
          intro j
          have hjq : j.val < q := lt_of_lt_of_le j.isLt hle
          have hzi := congrFun hz ⟨j.val, hjq⟩
          simp only [Q, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.isLt, Pi.zero_apply] at hzi
          exact hzi
        have hmemU : b ∈ U := Submodule.subset_span hbs
        let linz : U →ₗ[F] F :=
          { toFun := fun u => pairingF u.val z
            map_add' := fun u1 u2 => pairingF_add_left u1.val u2.val z
            map_smul' := fun c u => pairingF_smul_left c u.val z }
        have hlin0 : linz = 0 := bas.ext fun j => hbas0 j
        have := LinearMap.congr_fun hlin0 ⟨b, hmemU⟩
        simpa [linz, hpair_eq] using this
      have he0 : energy b = 0 := by
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hb_not_supp
        omega
      simp [he0]
    obtain ⟨decQ, hdecQ⟩ := (hpart1 Q).2
    rw [hlost0] at hdecQ
    have hpow_pos : (0 : ℚ) < (2 : ℚ) ^ (k * r) := by positivity
    have hsum0 : ∑ z : S, ((hits z : ℚ) - decQ (Q z)) ^ 2 = 0 := by
      have := mul_eq_zero.mp hdecQ
      rcases this with h0 | h0
      · exact False.elim ((ne_of_gt hpow_pos) h0)
      · exact h0
    have hmatch : ∀ z : S, (hits z : ℚ) = decQ (Q z) := by
      intro z
      have hterm0 : ((hits z : ℚ) - decQ (Q z)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum0 z (Finset.mem_univ z)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm0)
    let dec : (Fin q → F) → ℕ := fun y =>
      if hy : ∃ z : S, Q z = y then hits hy.choose else 0
    refine ⟨Q, dec, fun z => ?_⟩
    have hex : ∃ z' : S, Q z' = Q z := ⟨z, rfl⟩
    dsimp only [dec]
    rw [dif_pos hex]
    have hq : Q hex.choose = Q z := hex.choose_spec
    have hrat : (hits hex.choose : ℚ) = (hits z : ℚ) := by
      rw [hmatch hex.choose, hq, ← hmatch z]
    exact_mod_cast hrat
