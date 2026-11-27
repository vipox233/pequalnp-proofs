import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25748_aux

open scoped BigOperators

def scope {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) : Finset (Fin n) :=
  (Finset.range k).image (fun t => (⟨(i.val + t) % n, Nat.mod_lt _ hn⟩ : Fin n))

def full {n : ℕ} (hn : 0 < n) (k : ℕ) : Finset (Fin n × Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n × Finset (Fin n))).filter (fun c => c.2 ⊆ scope hn k c.1)

def passSet {n : ℕ} (hn : 0 < n) (k : ℕ) (A : Finset (Fin n × Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun x => ∀ i : Fin n, (i, x ∩ scope hn k i) ∈ A)

def total {n : ℕ} (hn : 0 < n) (k : ℕ) (A : Finset (Fin n × Finset (Fin n))) : ℕ :=
  (passSet hn k A).card

noncomputable def price {n : ℕ} (hn : 0 < n) (k : ℕ) (t : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ A ∈ (full hn k).powerset, t ≤ total hn k A ∧ A.card = c}

def box {n : ℕ} (hn : 0 < n) (k : ℕ) (base free : Finset (Fin n)) : Finset (Fin n × Finset (Fin n)) :=
  (full hn k).filter (fun entry => entry.2 \ free = (base ∩ scope hn k entry.1) \ free)

def rowSlice {n : ℕ} (A : Finset (Fin n × Finset (Fin n))) (i : Fin n) : Finset (Finset (Fin n)) :=
  (A.filter (fun e => e.1 = i)).image Prod.snd

lemma mem_rowSlice {n : ℕ} (A : Finset (Fin n × Finset (Fin n))) (i : Fin n) (S : Finset (Fin n)) :
    S ∈ rowSlice A i ↔ (i, S) ∈ A := by
  unfold rowSlice
  simp only [Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩; exact hab
  · intro h; exact ⟨i, S, ⟨h, rfl⟩, rfl⟩

lemma card_eq_sum_rowSlice {n : ℕ} (A : Finset (Fin n × Finset (Fin n))) :
    A.card = ∑ i : Fin n, (rowSlice A i).card := by
  classical
  have h1 : ∀ i : Fin n, (rowSlice A i).card = (A.filter (fun e => e.1 = i)).card := by
    intro i
    unfold rowSlice
    apply Finset.card_image_of_injOn
    intro e₁ he₁ e₂ he₂ hsnd
    have h1 := (Finset.mem_filter.mp he₁).2
    have h2 := (Finset.mem_filter.mp he₂).2
    exact Prod.ext (h1.trans h2.symm) hsnd
  simp_rw [h1]
  have hfib := Finset.sum_card_fiberwise_eq_card_filter (s := A) (t := (Finset.univ : Finset (Fin n)))
    (g := Prod.fst)
  simpa using hfib.symm

lemma self_mem_scope {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 1 ≤ k) (i : Fin n) :
    i ∈ scope hn k i := by
  unfold scope
  rw [Finset.mem_image]
  refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

lemma scope_card {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) (i : Fin n) :
    (scope hn k i).card = k := by
  unfold scope
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range k
  · intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at ht₁ ht₂
    have hval : (i.val + t₁) % n = (i.val + t₂) % n := congr_arg Fin.val heq
    have hmod : t₁ % n = t₂ % n := by
      have h1 : ((i.val + t₁) + (n - i.val % n)) % n = ((i.val + t₂) + (n - i.val % n)) % n := by
        rw [Nat.add_mod, hval, ← Nat.add_mod]
      have hi : i.val % n = i.val := Nat.mod_eq_of_lt i.isLt
      rw [hi] at h1
      have hL : (i.val + t₁ + (n - i.val)) % n = t₁ % n := by
        rw [show i.val + t₁ + (n - i.val) = t₁ + n by omega, Nat.add_mod_right]
      have hR : (i.val + t₂ + (n - i.val)) % n = t₂ % n := by
        rw [show i.val + t₂ + (n - i.val) = t₂ + n by omega, Nat.add_mod_right]
      omega
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    exact hmod

lemma scope_eq_univ {n : ℕ} (hn : 0 < n) (i : Fin n) :
    scope hn n i = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [scope_card hn le_rfl i, Fintype.card_fin]

lemma incident_windows_card {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) (s : Fin n) :
    (Finset.univ.filter (fun i : Fin n => s ∈ scope hn k i)).card = k := by
  have heq : Finset.univ.filter (fun i : Fin n => s ∈ scope hn k i) =
      (Finset.range k).image (fun t => (⟨(s.val + n - t) % n, Nat.mod_lt _ hn⟩ : Fin n)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range, scope]
    constructor
    · rintro ⟨t, ht, hst⟩
      refine ⟨t, ht, ?_⟩
      apply Fin.ext
      have hval : (i.val + t) % n = s.val := congr_arg Fin.val hst
      have h1 : (s.val + n - t) % n = i.val := by
        by_cases hle : i.val + t < n
        · rw [Nat.mod_eq_of_lt hle] at hval
          rw [show s.val + n - t = i.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
        · have hlt2 : i.val + t < 2 * n := by omega
          have hsub : (i.val + t) % n = i.val + t - n := by
            rw [Nat.mod_eq_sub_mod (by omega : n ≤ i.val + t), Nat.mod_eq_of_lt (by omega)]
          rw [hsub] at hval
          rw [show s.val + n - t = i.val by omega, Nat.mod_eq_of_lt i.isLt]
      exact h1
    · rintro ⟨t, ht, his⟩
      refine ⟨t, ht, ?_⟩
      apply Fin.ext
      dsimp only
      have hval : (s.val + n - t) % n = i.val := congr_arg Fin.val his
      rw [← hval]
      have h1 : ((s.val + n - t) % n + t) % n = (s.val + n - t + t) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1, show s.val + n - t + t = s.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]
  rw [heq, Finset.card_image_of_injOn]
  · exact Finset.card_range k
  · intro t₁ ht₁ t₂ ht₂ h12
    rw [Finset.mem_coe, Finset.mem_range] at ht₁ ht₂
    have hval : (s.val + n - t₁) % n = (s.val + n - t₂) % n := congr_arg Fin.val h12
    by_cases h1 : t₁ ≤ s.val
    · by_cases h2 : t₂ ≤ s.val
      · have a1 : (s.val + n - t₁) % n = s.val - t₁ := by
          rw [show s.val + n - t₁ = (s.val - t₁) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have a2 : (s.val + n - t₂) % n = s.val - t₂ := by
          rw [show s.val + n - t₂ = (s.val - t₂) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have a1 : (s.val + n - t₁) % n = s.val - t₁ := by
          rw [show s.val + n - t₁ = (s.val - t₁) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have a2 : (s.val + n - t₂) % n = s.val + n - t₂ := Nat.mod_eq_of_lt (by omega)
        omega
    · by_cases h2 : t₂ ≤ s.val
      · have a1 : (s.val + n - t₁) % n = s.val + n - t₁ := Nat.mod_eq_of_lt (by omega)
        have a2 : (s.val + n - t₂) % n = s.val - t₂ := by
          rw [show s.val + n - t₂ = (s.val - t₂) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have a1 : (s.val + n - t₁) % n = s.val + n - t₁ := Nat.mod_eq_of_lt (by omega)
        have a2 : (s.val + n - t₂) % n = s.val + n - t₂ := Nat.mod_eq_of_lt (by omega)
        omega

lemma sum_inter_scope_card {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) (S : Finset (Fin n)) :
    ∑ i : Fin n, (S ∩ scope hn k i).card = k * S.card := by
  have h1 : ∀ i : Fin n, (S ∩ scope hn k i).card = ∑ s ∈ S, if s ∈ scope hn k i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter]
    congr 1
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ s ∈ S, ∑ i : Fin n, (if s ∈ scope hn k i then 1 else 0) = k := by
    intro s _
    rw [← Finset.card_filter]
    exact incident_windows_card hn hk s
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

lemma proper_windows_distinguish {n : ℕ} (hn : 0 < n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n)
    {s₁ s₂ : Fin n} (hsub : ∀ i : Fin n, s₁ ∈ scope hn k i → s₂ ∈ scope hn k i) :
    s₁ = s₂ := by
  have hset_sub : Finset.univ.filter (fun i : Fin n => s₁ ∈ scope hn k i) ⊆
      Finset.univ.filter (fun i : Fin n => s₂ ∈ scope hn k i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hsub i hi
  have hset_eq : Finset.univ.filter (fun i : Fin n => s₁ ∈ scope hn k i) =
      Finset.univ.filter (fun i : Fin n => s₂ ∈ scope hn k i) := by
    apply Finset.eq_of_subset_of_card_le hset_sub
    rw [incident_windows_card hn (by omega), incident_windows_card hn (by omega)]
  have hiff : ∀ i : Fin n, s₁ ∈ scope hn k i ↔ s₂ ∈ scope hn k i := by
    intro i
    have := Finset.ext_iff.mp hset_eq i
    simpa using this
  have hs1_in : s₂ ∈ scope hn k s₁ := (hiff s₁).mp (self_mem_scope hn hk1 s₁)
  unfold scope at hs1_in
  rw [Finset.mem_image] at hs1_in
  rcases hs1_in with ⟨t, ht, hst⟩
  rw [Finset.mem_range] at ht
  have hval : (s₁.val + t) % n = s₂.val := congr_arg Fin.val hst
  by_cases ht0 : t = 0
  · subst ht0
    apply Fin.ext
    simpa [Nat.mod_eq_of_lt s₁.isLt] using hval
  · let i' : Fin n := ⟨(s₁.val + 1) % n, Nat.mod_lt _ hn⟩
    have hs2_in : s₂ ∈ scope hn k i' := by
      unfold scope
      rw [Finset.mem_image]
      refine ⟨t - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply Fin.ext
      dsimp only
      have h1 : ((s₁.val + 1) % n + (t - 1)) % n = (s₁.val + 1 + (t - 1)) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1, show s₁.val + 1 + (t - 1) = s₁.val + t by omega]
      exact hval
    have hs1_in' : s₁ ∈ scope hn k i' := (hiff i').mpr hs2_in
    unfold scope at hs1_in'
    rw [Finset.mem_image] at hs1_in'
    rcases hs1_in' with ⟨t', ht', hst'⟩
    rw [Finset.mem_range] at ht'
    have hval' : ((s₁.val + 1) % n + t') % n = s₁.val := congr_arg Fin.val hst'
    have h1 : ((s₁.val + 1) % n + t') % n = (s₁.val + (1 + t')) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    rw [h1] at hval'
    have h2 : (1 + t') % n = 0 := by
      have hmod1 : (s₁.val + (1 + t') + (n - s₁.val)) % n = (s₁.val + (n - s₁.val)) % n :=
        calc (s₁.val + (1 + t') + (n - s₁.val)) % n
            = ((s₁.val + (1 + t')) % n + (n - s₁.val) % n) % n := Nat.add_mod _ _ _
          _ = (s₁.val % n + (n - s₁.val) % n) % n := by rw [hval', Nat.mod_eq_of_lt s₁.isLt]
          _ = (s₁.val + (n - s₁.val)) % n := (Nat.add_mod _ _ _).symm
      rw [show s₁.val + (1 + t') + (n - s₁.val) = (1 + t') + n by omega, Nat.add_mod_right,
          show s₁.val + (n - s₁.val) = n by omega, Nat.mod_self] at hmod1
      exact hmod1
    rw [Nat.mod_eq_of_lt (by omega)] at h2
    omega

lemma box_subset_full {n : ℕ} (hn : 0 < n) (k : ℕ) (base free : Finset (Fin n)) :
    box hn k base free ∈ (full hn k).powerset := by
  rw [Finset.mem_powerset]
  exact Finset.filter_subset _ _

lemma rowSlice_box_card {n : ℕ} (hn : 0 < n) (k : ℕ) (base free : Finset (Fin n)) (i : Fin n) :
    (rowSlice (box hn k base free) i).card = 2 ^ (free ∩ scope hn k i).card := by
  classical
  let R := free ∩ scope hn k i
  let fix := (base ∩ scope hn k i) \ free
  have heq : rowSlice (box hn k base free) i = R.powerset.image (fun sub => fix ∪ sub) := by
    ext S
    rw [mem_rowSlice]
    simp only [box, full, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · rintro ⟨hSsub, hSdiff⟩
      refine ⟨S ∩ free, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_inter] at hx
        simp only [R, Finset.mem_inter]
        exact ⟨hx.2, hSsub hx.1⟩
      · ext x
        simp only [fix, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        by_cases hxf : x ∈ free
        · simp [hxf]
        · have hx := Finset.ext_iff.mp hSdiff x
          simp only [Finset.mem_sdiff, Finset.mem_inter, hxf, not_false_eq_true, and_true] at hx
          simp [hxf, hx]
    · rintro ⟨sub, hsub, rfl⟩
      constructor
      · intro x hx
        simp only [Finset.mem_union, fix, Finset.mem_sdiff, Finset.mem_inter] at hx
        rcases hx with ⟨⟨_, hxs⟩, _⟩ | hx
        · exact hxs
        · exact (Finset.mem_inter.mp (hsub hx)).2
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union, fix, Finset.mem_inter]
        by_cases hxf : x ∈ free
        · simp [hxf]
        · have hxsub : x ∉ sub := fun h => hxf (Finset.mem_inter.mp (hsub h)).1
          simp [hxf, hxsub]
  rw [heq, Finset.card_image_of_injOn, Finset.card_powerset]
  intro s₁ hs₁ s₂ hs₂ h12
  rw [Finset.mem_coe, Finset.mem_powerset] at hs₁ hs₂
  ext x
  have hx := Finset.ext_iff.mp h12 x
  simp only [Finset.mem_union, fix, Finset.mem_sdiff, Finset.mem_inter] at hx
  by_cases hxf : x ∈ free
  · simpa [hxf] using hx
  · have h1 : x ∉ s₁ := fun h => hxf (Finset.mem_inter.mp (hs₁ h)).1
    have h2 : x ∉ s₂ := fun h => hxf (Finset.mem_inter.mp (hs₂ h)).1
    simp [h1, h2]

lemma box_card_spaced {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) (base free : Finset (Fin n))
    (hsp : ∀ i : Fin n, (free ∩ scope hn k i).card ≤ 1) :
    (box hn k base free).card = n + k * free.card := by
  rw [card_eq_sum_rowSlice]
  have h1 : ∀ i : Fin n, (rowSlice (box hn k base free) i).card = 1 + (free ∩ scope hn k i).card := by
    intro i
    rw [rowSlice_box_card]
    have hle := hsp i
    interval_cases (free ∩ scope hn k i).card <;> decide
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, sum_inter_scope_card hn hk free]

lemma total_box {n : ℕ} (hn : 0 < n) {k : ℕ} (hk1 : 1 ≤ k) (base free : Finset (Fin n)) :
    total hn k (box hn k base free) = 2 ^ free.card := by
  classical
  have hpass : passSet hn k (box hn k base free) =
      free.powerset.image (fun sub => (base \ free) ∪ sub) := by
    ext x
    simp only [passSet, box, full, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · intro hx
      refine ⟨x ∩ free, Finset.inter_subset_right, ?_⟩
      ext s
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      by_cases hsf : s ∈ free
      · simp [hsf]
      · have hs := Finset.ext_iff.mp (hx s).2 s
        have hself := self_mem_scope hn hk1 s
        simp only [Finset.mem_sdiff, Finset.mem_inter, hsf, hself, not_false_eq_true, and_true] at hs
        simp [hsf, hs]
    · rintro ⟨sub, hsub, rfl⟩ i
      refine ⟨Finset.inter_subset_right, ?_⟩
      ext s
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
      by_cases hsf : s ∈ free
      · simp [hsf]
      · have hssub : s ∉ sub := fun h => hsf (hsub h)
        simp [hsf, hssub]
  unfold total
  rw [hpass, Finset.card_image_of_injOn, Finset.card_powerset]
  intro s₁ hs₁ s₂ hs₂ h12
  rw [Finset.mem_coe, Finset.mem_powerset] at hs₁ hs₂
  ext x
  have hx := Finset.ext_iff.mp h12 x
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx
  by_cases hxf : x ∈ free
  · simpa [hxf] using hx
  · simp [show x ∉ s₁ from fun h => hxf (hs₁ h), show x ∉ s₂ from fun h => hxf (hs₂ h)]

lemma spaced_free_exists {n : ℕ} (hn : 0 < n) {k h : ℕ} (hk1 : 1 ≤ k) (hkh : k * h ≤ n) :
    ∃ free : Finset (Fin n), free.card = h ∧ ∀ i : Fin n, (free ∩ scope hn k i).card ≤ 1 := by
  let free : Finset (Fin n) := (Finset.range h).image (fun m => (⟨(k * m) % n, Nat.mod_lt _ hn⟩ : Fin n))
  have hcard : free.card = h := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro m₁ hm₁ m₂ hm₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hm₁ hm₂
    have hval : (k * m₁) % n = (k * m₂) % n := congr_arg Fin.val heq
    have hlt1 : k * m₁ < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hm₁ (by omega)) hkh
    have hlt2 : k * m₂ < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hm₂ (by omega)) hkh
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hval
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) hval
  refine ⟨free, hcard, fun i => ?_⟩
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_inter, free, scope, Finset.mem_image, Finset.mem_range] at ha hb
  rcases ha with ⟨⟨m₁, hm₁, rfl⟩, ⟨t₁, ht₁, hta⟩⟩
  rcases hb with ⟨⟨m₂, hm₂, rfl⟩, ⟨t₂, ht₂, htb⟩⟩
  have hlt1 : k * m₁ < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hm₁ (by omega)) hkh
  have hlt2 : k * m₂ < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hm₂ (by omega)) hkh
  have hva : (i.val + t₁) % n = k * m₁ := by
    have := congr_arg Fin.val hta
    simpa [Nat.mod_eq_of_lt hlt1] using this
  have hvb : (i.val + t₂) % n = k * m₂ := by
    have := congr_arg Fin.val htb
    simpa [Nat.mod_eq_of_lt hlt2] using this
  have hdiff : ∀ (u v s₁ s₂ : ℕ), u < v → v < h → s₁ < k → s₂ < k →
      (i.val + s₁) % n = k * u → (i.val + s₂) % n = k * v → False := by
    intro u v s₁ s₂ huv hv hs₁ hs₂ hu hv'
    have hku : k * u < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (lt_trans huv hv) (by omega)) hkh
    have hkv : k * v < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hv (by omega)) hkh
    have hgap1 : k ≤ k * v - k * u := by
      have : k * (u + 1) ≤ k * v := Nat.mul_le_mul_left k huv
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    have hgap2 : k * v - k * u + k ≤ n := by
      have h1 : k * (v + 1) ≤ k * h := Nat.mul_le_mul_left k hv
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    have hcase : ((i.val + s₁) < n ∨ n ≤ i.val + s₁) ∧ ((i.val + s₂) < n ∨ n ≤ i.val + s₂) :=
      ⟨lt_or_ge _ _, lt_or_ge _ _⟩
    have hmod_cases : ∀ a b : ℕ, a < n → b < k → (a + b) % n = a + b ∨ (a + b) % n + n = a + b := by
      intro a b ha hb
      by_cases hlt : a + b < n
      · left; exact Nat.mod_eq_of_lt hlt
      · right
        have : (a + b) % n = a + b - n := by
          rw [Nat.mod_eq_sub_mod (by omega : n ≤ a + b), Nat.mod_eq_of_lt (by omega)]
        omega
    rcases hmod_cases i.val s₁ i.isLt hs₁ with h1 | h1 <;>
    rcases hmod_cases i.val s₂ i.isLt hs₂ with h2 | h2 <;> omega
  by_cases h12 : m₁ = m₂
  · subst h12; rfl
  · rcases lt_or_gt_of_ne h12 with hlt | hgt
    · exact absurd (hdiff m₁ m₂ t₁ t₂ hlt hm₂ ht₁ ht₂ hva hvb) id
    · exact absurd (hdiff m₂ m₁ t₂ t₁ hgt hm₁ ht₂ ht₁ hvb hva) id

def vec {n : ℕ} (x : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun s => if s ∈ x then 1 else 0

lemma vec_injective {n : ℕ} : Function.Injective (@vec n) := by
  intro x y hxy
  ext s
  have hs := congr_fun hxy s
  simp only [vec] at hs
  by_cases hx : s ∈ x <;> by_cases hy : s ∈ y <;> simp_all

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

lemma exists_pivots {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    ∃ Piv : Finset (Fin n),
      Function.Bijective (fun v : W => (fun p : Piv => v.1 p.1)) := by
  classical
  have hstep : ∀ (m : ℕ) (P : Finset (Fin n)),
      Function.Surjective (fun v : W => (fun p : P => v.1 p.1)) →
      n - P.card ≤ m →
      ∃ Piv : Finset (Fin n), Function.Bijective (fun v : W => (fun p : Piv => v.1 p.1)) := by
    intro m
    induction m with
    | zero =>
        intro P hsurj hm
        have hPcard : P.card = n := by
          have := Finset.card_le_univ P
          simp only [Fintype.card_fin] at this
          omega
        have hPun : P = Finset.univ := Finset.eq_univ_of_card P (by simpa using hPcard)
        refine ⟨P, ?_, hsurj⟩
        intro v₁ v₂ heq
        apply Subtype.ext
        funext s
        have hs : s ∈ P := by rw [hPun]; exact Finset.mem_univ s
        exact congr_fun heq ⟨s, hs⟩
    | succ m ih =>
        intro P hsurj hm
        by_cases hinj : Function.Injective (fun v : W => (fun p : P => v.1 p.1))
        · exact ⟨P, hinj, hsurj⟩
        · have hex : ∃ v : W, (∀ p ∈ P, v.1 p = 0) ∧ ∃ s : Fin n, v.1 s = 1 := by
            simp only [Function.Injective, not_forall] at hinj
            rcases hinj with ⟨v₁, v₂, heq, hne⟩
            let v : W := v₁ - v₂
            have hv0 : ∀ p ∈ P, v.1 p = 0 := by
              intro p hp
              have := congr_fun heq ⟨p, hp⟩
              simp [v, this]
            have hvne : v ≠ 0 := sub_ne_zero.mpr hne
            have hxs : ∃ s : Fin n, v.1 s ≠ 0 := by
              by_contra h
              push Not at h
              apply hvne
              apply Subtype.ext
              funext s
              exact h s
            rcases hxs with ⟨s, hs⟩
            exact ⟨v, hv0, s, zmod2_ne_zero hs⟩
          rcases hex with ⟨v, hvP, s, hvs⟩
          have hs_not : s ∉ P := by
            intro hmem
            have := hvP s hmem
            rw [hvs] at this
            exact one_ne_zero this
          let P' : Finset (Fin n) := insert s P
          have hcard' : P'.card = P.card + 1 := Finset.card_insert_of_notMem hs_not
          have hsurj' : Function.Surjective (fun w : W => (fun p : P' => w.1 p.1)) := by
            intro g
            rcases hsurj (fun p : P => g ⟨p.1, Finset.mem_insert_of_mem p.2⟩) with ⟨u, hu⟩
            by_cases hmatch : u.1 s = g ⟨s, Finset.mem_insert_self s P⟩
            · refine ⟨u, ?_⟩
              funext ⟨p, hp⟩
              rcases Finset.mem_insert.mp hp with rfl | hpP
              · exact hmatch
              · exact congr_fun hu ⟨p, hpP⟩
            · refine ⟨u + v, ?_⟩
              funext ⟨p, hp⟩
              rcases Finset.mem_insert.mp hp with hps | hpP
              · subst hps
                change u.1 p + v.1 p = g ⟨p, Finset.mem_insert_self p P⟩
                rw [hvs]
                generalize u.1 p = a at hmatch ⊢
                generalize g ⟨p, Finset.mem_insert_self p P⟩ = b at hmatch ⊢
                fin_cases a <;> fin_cases b <;> first | exact absurd rfl hmatch | rfl
              · change u.1 p + v.1 p = g ⟨p, hp⟩
                rw [hvP p hpP, add_zero]
                exact congr_fun hu ⟨p, hpP⟩
          exact ih P' hsurj' (by omega)
  have hsurj0 : Function.Surjective (fun _v : W => (fun p : (∅ : Finset (Fin n)) => _v.1 p.1)) := by
    intro g
    refine ⟨0, ?_⟩
    funext ⟨p, hp⟩
    exact absurd hp (Finset.notMem_empty p)
  exact hstep n ∅ hsurj0 (by simp)

lemma card_W_eq_pow {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype W]
    (Piv : Finset (Fin n)) (hbij : Function.Bijective (fun v : W => (fun p : Piv => v.1 p.1))) :
    Fintype.card W = 2 ^ Piv.card := by
  classical
  let e : W ≃ (Piv → ZMod 2) := Equiv.ofBijective _ hbij
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_coe]

lemma row_lower_bound {n : ℕ} (hn : 0 < n) (k : ℕ)
    (A : Finset (Fin n × Finset (Fin n))) (x₀ : Finset (Fin n)) (hx₀ : x₀ ∈ passSet hn k A)
    (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hW : W = Submodule.span (ZMod 2) ((passSet hn k A).image (fun x => vec x - vec x₀) : Set (Fin n → ZMod 2)))
    (Piv : Finset (Fin n)) (hbij : Function.Bijective (fun v : W => (fun p : Piv => v.1 p.1)))
    (i : Fin n) :
    let R := scope hn k i
    let proj : W →ₗ[ZMod 2] (R → ZMod 2) :=
      { toFun := fun v r => v.1 r.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    (Piv ∩ R).card ≤ Module.finrank (ZMod 2) (LinearMap.range proj) ∧
    Module.finrank (ZMod 2) (LinearMap.range proj) + 1 ≤
      ((passSet hn k A).image (fun x => x ∩ R)).card ∧
    ((passSet hn k A).image (fun x => x ∩ R)).card ≤ (rowSlice A i).card := by
  classical
  intro R proj
  let projPiv : W →ₗ[ZMod 2] ((Piv ∩ R : Finset (Fin n)) → ZMod 2) :=
    { toFun := fun v r => v.1 r.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurjP : Function.Surjective projPiv := by
    intro g
    let gfull : Piv → ZMod 2 := fun p =>
      if hp : p.1 ∈ R then g ⟨p.1, Finset.mem_inter.mpr ⟨p.2, hp⟩⟩ else 0
    rcases hbij.2 gfull with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    funext ⟨p, hp⟩
    have hp1 : p ∈ Piv := (Finset.mem_inter.mp hp).1
    have hp2 : p ∈ R := (Finset.mem_inter.mp hp).2
    have := congr_fun hv ⟨p, hp1⟩
    simpa [projPiv, gfull, hp2] using this
  let drop : (LinearMap.range proj) →ₗ[ZMod 2] ((Piv ∩ R : Finset (Fin n)) → ZMod 2) :=
    { toFun := fun y p => y.1 ⟨p.1, (Finset.mem_inter.mp p.2).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj_drop : Function.Surjective drop := by
    intro g
    rcases hsurjP g with ⟨v, hv⟩
    refine ⟨⟨proj v, v, rfl⟩, ?_⟩
    funext p
    exact congr_fun hv p
  have hrank_ge : (Piv ∩ R).card ≤ Module.finrank (ZMod 2) (LinearMap.range proj) := by
    have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj_drop
    have h2 : Module.finrank (ZMod 2) ((Piv ∩ R : Finset (Fin n)) → ZMod 2) = (Piv ∩ R).card := by
      rw [Module.finrank_pi, Fintype.card_coe]
    omega
  let Q := (passSet hn k A).image (fun x => x ∩ R)
  let Qvec : Finset (LinearMap.range proj) :=
    Q.attach.image (fun S => ⟨fun r => vec S.1 r.1 - vec x₀ r.1, by
      rcases Finset.mem_image.mp S.2 with ⟨x, hxP, hxS⟩
      have hvW : vec x - vec x₀ ∈ W := by
        rw [hW]
        apply Submodule.subset_span
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hxP, rfl⟩)
      refine ⟨⟨vec x - vec x₀, hvW⟩, ?_⟩
      funext ⟨r, hr⟩
      simp [proj, ← hxS, vec, Finset.mem_inter, hr]⟩)
  have hQcard : Qvec.card ≤ Q.card := by
    calc Qvec.card ≤ Q.attach.card := Finset.card_image_le
      _ = Q.card := Finset.card_attach
  have hzero_mem : (0 : LinearMap.range proj) ∈ Qvec := by
    unfold Qvec
    rw [Finset.mem_image]
    refine ⟨⟨x₀ ∩ R, Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    funext ⟨r, hr⟩
    simp [vec, Finset.mem_inter, hr]
  have hspan_Q : Submodule.span (ZMod 2) ((Qvec.erase 0 : Finset (LinearMap.range proj)) : Set (LinearMap.range proj)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, v, rfl⟩ _
    have hv : v.1 ∈ Submodule.span (ZMod 2) ((passSet hn k A).image (fun x => vec x - vec x₀) : Set (Fin n → ZMod 2)) := by
      rw [← hW]; exact v.2
    have hgen : ∀ (u : Fin n → ZMod 2)
        (hu : u ∈ Submodule.span (ZMod 2) ((passSet hn k A).image (fun x => vec x - vec x₀) : Set (Fin n → ZMod 2))),
        (⟨fun r : R => u r.1, ⟨⟨u, hW ▸ hu⟩, rfl⟩⟩ : LinearMap.range proj) ∈
          Submodule.span (ZMod 2) ((Qvec.erase 0 : Finset (LinearMap.range proj)) : Set (LinearMap.range proj)) := by
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · intro w hw
        rw [Finset.mem_coe, Finset.mem_image] at hw
        rcases hw with ⟨x, hxP, rfl⟩
        set z : LinearMap.range proj := ⟨fun r : R => (vec x - vec x₀) r.1, ⟨⟨vec x - vec x₀, by
          rw [hW]; apply Submodule.subset_span; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hxP, rfl⟩)⟩, rfl⟩⟩
        by_cases hz : z = 0
        · rw [hz]; exact Submodule.zero_mem _
        · apply Submodule.subset_span
          rw [Finset.mem_coe, Finset.mem_erase]
          refine ⟨hz, ?_⟩
          unfold Qvec
          rw [Finset.mem_image]
          refine ⟨⟨x ∩ R, Finset.mem_image.mpr ⟨x, hxP, rfl⟩⟩, Finset.mem_attach _ _, ?_⟩
          apply Subtype.ext
          funext ⟨r, hr⟩
          simp [z, vec, Finset.mem_inter, hr]
      · exact Submodule.zero_mem _
      · intro u₁ u₂ hu₁ hu₂ ih₁ ih₂
        exact Submodule.add_mem _ ih₁ ih₂
      · intro c u₁ hu₁ ih₁
        exact Submodule.smul_mem _ c ih₁
    exact hgen v.1 hv
  have hrank_le : Module.finrank (ZMod 2) (LinearMap.range proj) ≤ (Qvec.erase 0).card := by
    have h1 := finrank_span_le_card (R := ZMod 2) ((Qvec.erase 0 : Finset (LinearMap.range proj)) : Set (LinearMap.range proj))
    rw [hspan_Q, finrank_top] at h1
    have h2 : ((Qvec.erase 0 : Finset (LinearMap.range proj)) : Set (LinearMap.range proj)).toFinset = Qvec.erase 0 := by
      ext x; simp only [Set.mem_toFinset, Finset.mem_coe]
    rwa [h2] at h1
  have hQ_ge : Module.finrank (ZMod 2) (LinearMap.range proj) + 1 ≤ Q.card := by
    have h2 : (Qvec.erase 0).card + 1 = Qvec.card := by
      have := Finset.card_erase_add_one hzero_mem
      omega
    omega
  have hQ_sub : Q ⊆ rowSlice A i := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, hxP, rfl⟩
    rw [mem_rowSlice]
    exact (Finset.mem_filter.mp hxP).2 i
  exact ⟨hrank_ge, hQ_ge, Finset.card_le_card hQ_sub⟩

lemma card_lower_bound {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n)
    (A : Finset (Fin n × Finset (Fin n))) {t : ℕ} (ht0 : 0 < t) (ht : t ≤ total hn k A) :
    n + k * Nat.clog 2 t ≤ A.card := by
  classical
  have hne : (passSet hn k A).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le ht0 ht)
  rcases hne with ⟨x₀, hx₀⟩
  let W : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    Submodule.span (ZMod 2) ((passSet hn k A).image (fun x => vec x - vec x₀) : Set (Fin n → ZMod 2))
  rcases exists_pivots W with ⟨Piv, hbij⟩
  have hP_le : total hn k A ≤ 2 ^ Piv.card := by
    unfold total
    rw [← card_W_eq_pow W Piv hbij]
    let f : {x // x ∈ passSet hn k A} → W := fun x =>
      ⟨vec x.1 - vec x₀, Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩))⟩
    have hf_inj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have h1 : vec x.1 - vec x₀ = vec y.1 - vec x₀ := congr_arg Subtype.val hxy
      exact vec_injective (sub_left_inj.mp h1)
    have hcard := Fintype.card_le_of_injective f hf_inj
    simpa using hcard
  have hclog : Nat.clog 2 t ≤ Piv.card := Nat.clog_le_of_le_pow (le_trans ht hP_le)
  have hrow : ∀ i : Fin n, (Piv ∩ scope hn k i).card + 1 ≤ (rowSlice A i).card := by
    intro i
    obtain ⟨h1, h2, h3⟩ := row_lower_bound hn k A x₀ hx₀ W rfl Piv hbij i
    omega
  have hsum : ∑ i : Fin n, ((Piv ∩ scope hn k i).card + 1) ≤ A.card := by
    rw [card_eq_sum_rowSlice]
    exact Finset.sum_le_sum (fun i _ => hrow i)
  rw [Finset.sum_add_distrib, sum_inter_scope_card hn hk Piv, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  have hmul : k * Nat.clog 2 t ≤ k * Piv.card := Nat.mul_le_mul_left k hclog
  omega

lemma price_nonempty {n : ℕ} (hn : 0 < n) {k t : ℕ} (ht : t ≤ 2 ^ n) :
    {c : ℕ | ∃ A ∈ (full hn k).powerset, t ≤ total hn k A ∧ A.card = c}.Nonempty := by
  refine ⟨(full hn k).card, full hn k, Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_, rfl⟩
  have hpass : passSet hn k (full hn k) = Finset.univ := by
    ext x
    simp only [passSet, full, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro i
    exact Finset.inter_subset_right
  unfold total
  rw [hpass, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  exact ht

lemma price_lower_bound {n : ℕ} (hn : 0 < n) {k t : ℕ} (hk : k ≤ n) (ht0 : 0 < t) (ht : t ≤ 2 ^ n) :
    n + k * Nat.clog 2 t ≤ price hn k t := by
  unfold price
  apply le_csInf (price_nonempty hn ht)
  rintro c ⟨A, _, htot, rfl⟩
  exact card_lower_bound hn hk A ht0 htot

lemma price_eq_spaced {n : ℕ} (hn : 0 < n) {k t : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (ht0 : 0 < t) (ht : t ≤ 2 ^ n) (hkh : k * Nat.clog 2 t ≤ n) :
    price hn k t = n + k * Nat.clog 2 t := by
  apply le_antisymm
  · rcases spaced_free_exists hn hk1 hkh with ⟨free, hcard, hsp⟩
    unfold price
    apply Nat.sInf_le
    refine ⟨box hn k ∅ free, box_subset_full hn k ∅ free, ?_, ?_⟩
    · rw [total_box hn hk1 ∅ free, hcard]
      exact Nat.le_pow_clog (by omega : 1 < 2) t
    · rw [box_card_spaced hn hk ∅ free hsp, hcard]
  · exact price_lower_bound hn hk ht0 ht

lemma price_full_window {n : ℕ} (hn : 0 < n) {t : ℕ} (ht : t ≤ 2 ^ n) :
    price hn n t = n * t := by
  apply le_antisymm
  · have hle : t ≤ (Finset.univ : Finset (Finset (Fin n))).card := by
      simpa using ht
    rcases Finset.exists_subset_card_eq hle with ⟨S, _, hScard⟩
    let A : Finset (Fin n × Finset (Fin n)) := (Finset.univ : Finset (Fin n)) ×ˢ S
    unfold price
    apply Nat.sInf_le
    refine ⟨A, ?_, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro e _
      simp [full, scope_eq_univ hn e.1]
    · have hpass : passSet hn n A = S := by
        ext x
        simp only [passSet, A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          scope_eq_univ, Finset.inter_univ]
        exact ⟨fun h => h ⟨0, hn⟩, fun hx _ => hx⟩
      unfold total
      rw [hpass, hScard]
    · simp [A, hScard]
  · unfold price
    apply le_csInf (price_nonempty hn ht)
    rintro c ⟨A, _, htot, rfl⟩
    rw [card_eq_sum_rowSlice]
    have hrow : ∀ i : Fin n, t ≤ (rowSlice A i).card := by
      intro i
      have hsub : passSet hn n A ⊆ rowSlice A i := by
        intro x hx
        rw [mem_rowSlice]
        have := (Finset.mem_filter.mp hx).2 i
        simpa [scope_eq_univ hn i] using this
      exact le_trans htot (Finset.card_le_card hsub)
    calc n * t = ∑ _i : Fin n, t := by simp
      _ ≤ ∑ i : Fin n, (rowSlice A i).card := Finset.sum_le_sum (fun i _ => hrow i)

lemma two_pow_ge_add_one (r : ℕ) : r + 1 ≤ 2 ^ r := by
  induction r with
  | zero => decide
  | succ m ih =>
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      omega

lemma two_pow_eq_add_one_imp {r : ℕ} (h : 2 ^ r = r + 1) : r ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hge : ∀ m : ℕ, 2 ≤ m → m + 2 ≤ 2 ^ m := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
        by_cases hk : k < 2
        · have : k = 1 := by omega
          subst this; decide
        · have := ih (by omega)
          have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
  have := hge r hgt
  omega

lemma equality_structure {n : ℕ} (hn : 0 < n) {k d : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (T : Finset (Fin n × Finset (Fin n))) (hTfull : T ∈ (full hn k).powerset)
    (htot : 2 ^ d ≤ total hn k T) (hcard : T.card = n + k * d) :
    k * d ≤ n ∧
    (k < n → ∃ base free : Finset (Fin n), free.card = d ∧
      (∀ i : Fin n, (free ∩ scope hn k i).card ≤ 1) ∧ T = box hn k base free) := by
  classical
  have hne : (passSet hn k T).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by positivity) htot)
  rcases hne with ⟨x₀, hx₀⟩
  let W : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    Submodule.span (ZMod 2) ((passSet hn k T).image (fun x => vec x - vec x₀) : Set (Fin n → ZMod 2))
  rcases exists_pivots W with ⟨Piv, hbij⟩
  let fW : {x // x ∈ passSet hn k T} → W := fun x =>
    ⟨vec x.1 - vec x₀, Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩))⟩
  have hfW_inj : Function.Injective fW := by
    intro x y hxy
    apply Subtype.ext
    exact vec_injective (sub_left_inj.mp (congr_arg Subtype.val hxy))
  have hP_le : total hn k T ≤ 2 ^ Piv.card := by
    unfold total
    rw [← card_W_eq_pow W Piv hbij]
    simpa using Fintype.card_le_of_injective fW hfW_inj
  have hd_le_Piv : d ≤ Piv.card := by
    by_contra hlt
    push Not at hlt
    have hpow : 2 ^ Piv.card < 2 ^ d := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    omega
  have hPiv_le_d : Piv.card ≤ d := by
    have hrow : ∀ i : Fin n, (Piv ∩ scope hn k i).card + 1 ≤ (rowSlice T i).card := by
      intro i
      obtain ⟨h1, h2, h3⟩ := row_lower_bound hn k T x₀ hx₀ W rfl Piv hbij i
      omega
    have hsum : ∑ i : Fin n, ((Piv ∩ scope hn k i).card + 1) ≤ T.card := by
      rw [card_eq_sum_rowSlice]
      exact Finset.sum_le_sum (fun i _ => hrow i)
    rw [Finset.sum_add_distrib, sum_inter_scope_card hn hk Piv, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, hcard] at hsum
    exact Nat.le_of_mul_le_mul_left (by omega : k * Piv.card ≤ k * d) (by omega : 0 < k)
  have hPiv_eq_d : Piv.card = d := le_antisymm hPiv_le_d hd_le_Piv
  have hcard_eq : Fintype.card {x // x ∈ passSet hn k T} = Fintype.card W := by
    rw [card_W_eq_pow W Piv hbij, hPiv_eq_d]
    rw [hPiv_eq_d] at hP_le
    have h1 : Fintype.card {x // x ∈ passSet hn k T} = total hn k T := by simp [total]
    omega
  have hfW_bij : Function.Bijective fW := (Fintype.bijective_iff_injective_and_card fW).mpr ⟨hfW_inj, hcard_eq⟩
  have hP_full : ∀ v : W, ∃ x ∈ passSet hn k T, vec x = vec x₀ + v.1 := by
    intro v
    rcases hfW_bij.2 v with ⟨⟨x, hxP⟩, hx⟩
    refine ⟨x, hxP, ?_⟩
    have h1 : vec x - vec x₀ = v.1 := congr_arg Subtype.val hx
    funext s
    have hs := congr_fun h1 s
    simp only [Pi.sub_apply, Pi.add_apply] at hs ⊢
    rw [zmod2_sub_eq_add] at hs
    have := congr_arg (vec x₀ s + ·) hs
    rw [add_comm (vec x s) (vec x₀ s), ← add_assoc, zmod2_add_self, zero_add] at this
    exact this
  let projOf : ∀ i : Fin n, W →ₗ[ZMod 2] (scope hn k i → ZMod 2) := fun i =>
    { toFun := fun v r => v.1 r.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hQi_pow : ∀ i : Fin n,
      ((passSet hn k T).image (fun x => x ∩ scope hn k i)).card =
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (projOf i)) := by
    intro i
    let R := scope hn k i
    let Q := (passSet hn k T).image (fun x => x ∩ R)
    let g : {S // S ∈ Q} → LinearMap.range (projOf i) := fun S =>
      ⟨fun r => vec S.1 r.1 - vec x₀ r.1, by
        rcases Finset.mem_image.mp S.2 with ⟨x, hxP, hxeq⟩
        refine ⟨fW ⟨x, hxP⟩, ?_⟩
        funext ⟨r, hr⟩
        simp [projOf, fW, ← hxeq, vec, Finset.mem_inter, R, hr]⟩
    have hg_inj : Function.Injective g := by
      intro S₁ S₂ h12
      apply Subtype.ext
      rcases Finset.mem_image.mp S₁.2 with ⟨x₁, _, hx₁⟩
      rcases Finset.mem_image.mp S₂.2 with ⟨x₂, _, hx₂⟩
      ext s
      by_cases hs : s ∈ R
      · have hval := congr_fun (congr_arg Subtype.val h12) ⟨s, hs⟩
        have hv : vec S₁.1 s = vec S₂.1 s := sub_left_inj.mp hval
        simp only [vec] at hv
        by_cases h1 : s ∈ S₁.1 <;> by_cases h2 : s ∈ S₂.1 <;> simp_all
      · have h1 : s ∉ S₁.1 := by rw [← hx₁]; simp [hs]
        have h2 : s ∉ S₂.1 := by rw [← hx₂]; simp [hs]
        simp [h1, h2]
    have hg_surj : Function.Surjective g := by
      rintro ⟨y, v, rfl⟩
      rcases hP_full v with ⟨x, hxP, hxv⟩
      refine ⟨⟨x ∩ R, Finset.mem_image.mpr ⟨x, hxP, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      funext ⟨r, hr⟩
      simp only [g, projOf, LinearMap.coe_mk, AddHom.coe_mk]
      have hvr : vec (x ∩ R) r = vec x r := by simp [vec, Finset.mem_inter, R, hr]
      rw [hvr, hxv]
      simp [Pi.add_apply, zmod2_sub_eq_add, add_comm, add_assoc, zmod2_add_self]
    let eQ : {S // S ∈ Q} ≃ LinearMap.range (projOf i) := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
    have hcardQ : Q.card = Fintype.card (LinearMap.range (projOf i)) := by
      rw [← Fintype.card_coe, Fintype.card_congr eQ]
    rw [hcardQ, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hrow_chain : ∀ i : Fin n,
      (Piv ∩ scope hn k i).card + 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (projOf i)) + 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (projOf i)) + 1 ≤
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (projOf i)) ∧
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (projOf i)) ≤ (rowSlice T i).card := by
    intro i
    obtain ⟨h1, _, h3⟩ := row_lower_bound hn k T x₀ hx₀ W rfl Piv hbij i
    rw [hQi_pow i] at h3
    exact ⟨Nat.add_le_add_right h1 1, two_pow_ge_add_one _, h3⟩
  have hsum_eq : ∑ i : Fin n, ((Piv ∩ scope hn k i).card + 1) = ∑ i : Fin n, (rowSlice T i).card := by
    rw [← card_eq_sum_rowSlice, hcard, Finset.sum_add_distrib, sum_inter_scope_card hn hk Piv,
      hPiv_eq_d, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, add_comm]
  have heach_eq : ∀ i : Fin n,
      (Piv ∩ scope hn k i).card + 1 = (rowSlice T i).card := by
    intro i
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), (Piv ∩ scope hn k j).card + 1 ≤ (rowSlice T j).card := by
      intro j _
      obtain ⟨a, b, c⟩ := hrow_chain j
      omega
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq i (Finset.mem_univ i)
  have hri_eq : ∀ i : Fin n,
      (Piv ∩ scope hn k i).card = Module.finrank (ZMod 2) (LinearMap.range (projOf i)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (projOf i)) ≤ 1 ∧
      (passSet hn k T).image (fun x => x ∩ scope hn k i) = rowSlice T i := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hrow_chain i
    have he := heach_eq i
    have hpow_eq : 2 ^ Module.finrank (ZMod 2) (LinearMap.range (projOf i)) =
        Module.finrank (ZMod 2) (LinearMap.range (projOf i)) + 1 := by omega
    have hrle1 : Module.finrank (ZMod 2) (LinearMap.range (projOf i)) ≤ 1 := two_pow_eq_add_one_imp hpow_eq
    have hQeq : (passSet hn k T).image (fun x => x ∩ scope hn k i) = rowSlice T i := by
      apply Finset.eq_of_subset_of_card_le
      · intro S hS
        rcases Finset.mem_image.mp hS with ⟨x, hxP, rfl⟩
        rw [mem_rowSlice]
        exact (Finset.mem_filter.mp hxP).2 i
      · rw [hQi_pow i]; omega
    exact ⟨by omega, hrle1, hQeq⟩
  have hsp : ∀ i : Fin n, (Piv ∩ scope hn k i).card ≤ 1 := fun i => by
    have := hri_eq i; omega
  have hkd_le_n : k * d ≤ n := by
    have h1 : k * d = ∑ i : Fin n, (Piv ∩ scope hn k i).card := by
      rw [sum_inter_scope_card hn hk Piv, hPiv_eq_d]
    have h2 : ∑ i : Fin n, (Piv ∩ scope hn k i).card ≤ ∑ _i : Fin n, 1 :=
      Finset.sum_le_sum (fun i _ => hsp i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
    omega
  refine ⟨hkd_le_n, fun hkn => ?_⟩
  let ePiv : Piv → W := fun p =>
    (Equiv.ofBijective (fun v : W => (fun q : Piv => v.1 q.1)) hbij).symm
      (fun q => if q = p then 1 else 0)
  have hePiv_apply : ∀ p q : Piv, (ePiv p).1 q.1 = if q = p then 1 else 0 := by
    intro p q
    have h := (Equiv.ofBijective (fun v : W => (fun q : Piv => v.1 q.1)) hbij).apply_symm_apply
      (fun q : Piv => if q = p then 1 else 0)
    exact congr_fun h q
  have hePiv_coord : ∀ (p : Piv) (s : Fin n), (ePiv p).1 s = if s = p.1 then 1 else 0 := by
    intro p s
    by_cases hsp_eq : s = p.1
    · subst hsp_eq
      simpa using hePiv_apply p p
    · rw [if_neg hsp_eq]
      by_contra hne
      have h1 : (ePiv p).1 s = 1 := zmod2_ne_zero hne
      have hsub : ∀ i : Fin n, s ∈ scope hn k i → p.1 ∈ scope hn k i := by
        intro i hsi
        have hnz : projOf i (ePiv p) ≠ 0 := by
          intro hz
          have := congr_fun hz ⟨s, hsi⟩
          simp [projOf, h1] at this
        have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range (projOf i)) := by
          by_contra h0
          have hfin0 : Module.finrank (ZMod 2) (LinearMap.range (projOf i)) = 0 := by omega
          have hsub0 : (LinearMap.range (projOf i)) = ⊥ := Submodule.finrank_eq_zero.mp hfin0
          have hmem : projOf i (ePiv p) ∈ (⊥ : Submodule (ZMod 2) (scope hn k i → ZMod 2)) := by
            rw [← hsub0]; exact ⟨ePiv p, rfl⟩
          simp only [Submodule.mem_bot] at hmem
          exact hnz hmem
        have hpi1 : (Piv ∩ scope hn k i).card = 1 := by
          have := hri_eq i; omega
        rcases Finset.card_eq_one.mp hpi1 with ⟨q, hqeq⟩
        have hqmem : q ∈ Piv ∩ scope hn k i := by rw [hqeq]; exact Finset.mem_singleton_self q
        have hqP : q ∈ Piv := (Finset.mem_inter.mp hqmem).1
        have hqS : q ∈ scope hn k i := (Finset.mem_inter.mp hqmem).2
        by_cases hqp : q = p.1
        · rwa [← hqp]
        · have hnz_q : projOf i (ePiv ⟨q, hqP⟩) ≠ 0 := by
            intro hz
            have := congr_fun hz ⟨q, hqS⟩
            have hqq := hePiv_apply ⟨q, hqP⟩ ⟨q, hqP⟩
            simp [projOf] at this hqq
            rw [hqq] at this
            exact one_ne_zero this
          have hcard2 : Fintype.card (LinearMap.range (projOf i)) = 2 := by
            rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
            have := hri_eq i
            have : Module.finrank (ZMod 2) (LinearMap.range (projOf i)) = 1 := by omega
            rw [this]; norm_num
          have huniq : ∀ a b : LinearMap.range (projOf i), a ≠ 0 → b ≠ 0 → a = b := by
            intro a b ha hb
            by_contra hab
            have h3 : ({0, a, b} : Finset (LinearMap.range (projOf i))).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [ha.symm, hb.symm]),
                  Finset.card_pair hab]
            have hle : ({0, a, b} : Finset (LinearMap.range (projOf i))).card ≤
                Fintype.card (LinearMap.range (projOf i)) := Finset.card_le_univ _
            omega
          have hpeq : (⟨projOf i (ePiv p), ePiv p, rfl⟩ : LinearMap.range (projOf i)) =
              ⟨projOf i (ePiv ⟨q, hqP⟩), ePiv ⟨q, hqP⟩, rfl⟩ := by
            apply huniq
            · intro h; exact hnz (congr_arg Subtype.val h)
            · intro h; exact hnz_q (congr_arg Subtype.val h)
          have hqval := congr_fun (congr_arg Subtype.val hpeq) ⟨q, hqS⟩
          have hL : (ePiv p).1 q = 0 := by
            have := hePiv_apply p ⟨q, hqP⟩
            have hne' : (⟨q, hqP⟩ : Piv) ≠ p := fun h => hqp (congr_arg Subtype.val h)
            simpa [hne'] using this
          have hR : (ePiv ⟨q, hqP⟩).1 q = 1 := by
            simpa using hePiv_apply ⟨q, hqP⟩ ⟨q, hqP⟩
          simp only [projOf, LinearMap.coe_mk, AddHom.coe_mk] at hqval
          rw [hL, hR] at hqval
          exact absurd hqval zero_ne_one
      exact hsp_eq (proper_windows_distinguish hn hk1 hkn hsub)
  have hW_supp : ∀ v : W, ∀ s : Fin n, s ∉ Piv → v.1 s = 0 := by
    intro v s hs
    let w : W := ∑ p : Piv, v.1 p.1 • ePiv p
    have hvw : v = w := by
      apply hbij.1
      funext q
      change v.1 q.1 = (∑ p : Piv, v.1 p.1 • ePiv p).1 q.1
      have hsum : (∑ p : Piv, v.1 p.1 • ePiv p).1 q.1 = ∑ p : Piv, v.1 p.1 * (ePiv p).1 q.1 := by
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum]
      have hterm : ∀ p : Piv, v.1 p.1 * (ePiv p).1 q.1 = if p = q then v.1 q.1 else 0 := by
        intro p
        rw [hePiv_apply p q]
        by_cases hpq : p = q
        · subst hpq; simp
        · simp [hpq, Ne.symm hpq]
      simp_rw [hterm]
      simp
    rw [hvw]
    have hsum : (∑ p : Piv, v.1 p.1 • ePiv p).1 s = ∑ p : Piv, v.1 p.1 * (ePiv p).1 s := by
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    apply Finset.sum_eq_zero
    intro p _
    have hne : s ≠ p.1 := fun h => hs (h ▸ p.2)
    rw [hePiv_coord p s, if_neg hne, mul_zero]
  have hP_eq : ∀ x : Finset (Fin n), x ∈ passSet hn k T ↔ x \ Piv = x₀ \ Piv := by
    intro x
    constructor
    · intro hxP
      let v : W := fW ⟨x, hxP⟩
      ext s
      simp only [Finset.mem_sdiff]
      by_cases hsP : s ∈ Piv
      · simp [hsP]
      · have hv0 : v.1 s = 0 := hW_supp v s hsP
        have hsub : vec x s - vec x₀ s = 0 := hv0
        have hveq : vec x s = vec x₀ s := sub_eq_zero.mp hsub
        simp only [vec] at hveq
        by_cases h1 : s ∈ x <;> by_cases h2 : s ∈ x₀ <;> simp_all
    · intro hdiff
      let v : W := ∑ p : Piv, (vec x p.1 - vec x₀ p.1) • ePiv p
      rcases hP_full v with ⟨x', hx'P, hx'v⟩
      have hxx' : x = x' := by
        apply vec_injective
        funext s
        rw [hx'v]
        simp only [Pi.add_apply]
        have hsum : v.1 s = ∑ p : Piv, (vec x p.1 - vec x₀ p.1) * (ePiv p).1 s := by
          simp [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [hsum]
        by_cases hsP : s ∈ Piv
        · have hterm : ∀ p : Piv, (vec x p.1 - vec x₀ p.1) * (ePiv p).1 s =
              if p = ⟨s, hsP⟩ then vec x s - vec x₀ s else 0 := by
            intro p
            rw [hePiv_coord p s]
            by_cases hp : p = ⟨s, hsP⟩
            · subst hp; simp
            · have hne : s ≠ p.1 := fun h => hp (Subtype.ext h.symm)
              simp [hp, hne]
          simp_rw [hterm]
          rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), zmod2_sub_eq_add, add_comm (vec x s) (vec x₀ s), ← add_assoc, zmod2_add_self, zero_add]
        · have hz : ∑ p : Piv, (vec x p.1 - vec x₀ p.1) * (ePiv p).1 s = 0 := by
            apply Finset.sum_eq_zero
            intro p _
            have hne : s ≠ p.1 := fun h => hsP (h ▸ p.2)
            rw [hePiv_coord p s, if_neg hne, mul_zero]
          rw [hz, add_zero]
          have hs := Finset.ext_iff.mp hdiff s
          simp only [Finset.mem_sdiff, hsP, not_false_eq_true, and_true] at hs
          simp [vec, hs]
      rwa [hxx']
  refine ⟨x₀, Piv, hPiv_eq_d, hsp, ?_⟩
  ext ⟨i, S⟩
  rw [← mem_rowSlice, ← (hri_eq i).2.2]
  simp only [Finset.mem_image, box, full, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hxP, rfl⟩
    refine ⟨Finset.inter_subset_right, ?_⟩
    have hdiff := (hP_eq x).mp hxP
    ext s
    have hs := Finset.ext_iff.mp hdiff s
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hs ⊢
    tauto
  · rintro ⟨hSsub, hSdiff⟩
    let x : Finset (Fin n) := (x₀ \ scope hn k i) ∪ S
    have hxP : x ∈ passSet hn k T := by
      rw [hP_eq]
      ext s
      simp only [x, Finset.mem_sdiff, Finset.mem_union]
      by_cases hsi : s ∈ scope hn k i
      · have hs := Finset.ext_iff.mp hSdiff s
        simp only [Finset.mem_sdiff, Finset.mem_inter, hsi, and_true] at hs
        simp [hsi, hs]
      · have hsS : s ∉ S := fun h => hsi (hSsub h)
        simp [hsi, hsS]
    refine ⟨x, hxP, ?_⟩
    ext s
    simp only [x, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨_, hns⟩ | hS, hsi⟩
      · exact absurd hsi hns
      · exact hS
    · intro hS
      exact ⟨Or.inr hS, hSsub hS⟩

end PEqualNP.Outside.L_meta_25748_aux

theorem PEqualNP.Outside.L_meta_25748 : (∀ (n w : Nat) (hn : 0 < n),
  let Site := Fin n
  let Slot := Site × Finset Site
  let k := min n (w+1)
  let scope := fun i : Site => (Finset.range k).image
    (fun t => (⟨(i.val+t)%n, Nat.mod_lt _ hn⟩ : Site))
  let full := (Finset.univ : Finset Slot).filter (fun candidate => candidate.2 ⊆ scope candidate.1)
  let total := fun table : Finset Slot =>
    ((Finset.univ : Finset (Finset Site)).filter
      (fun x => ∀ i : Site, (i, x ∩ scope i) ∈ table)).card
  let price := fun t : Nat => sInf {c : Nat | ∃ A ∈ full.powerset,
    t ≤ total A ∧ A.card = c}
  let box := fun (base free : Finset Site) => full.filter (fun entry =>
    entry.2 \ free = (base ∩ scope entry.1) \ free)
  (∀ t : Nat, 0 < t → t ≤ 2^n →
    let h := Nat.clog 2 t
    n+k*h ≤ price t ∧ (k*h ≤ n → price t = n+k*h) ∧
      (k = n → price t = n*t)) ∧
  ∀ d : Nat, d ≤ n →
    (price (2^d) = n+k*d ↔ k*d ≤ n) ∧
    (k < n → ∀ T ∈ full.powerset, 2^d ≤ total T →
      (T.card = n+k*d ↔
        ∃ base free : Finset Site, free.card = d ∧
          (∀ i : Site, (free ∩ scope i).card ≤ 1) ∧ T = box base free))) := by
  intro n w hn Site Slot k scope full total price box
  have hk1 : 1 ≤ k := le_min hn (Nat.succ_le_succ (Nat.zero_le w))
  have hk : k ≤ n := min_le_left n (w + 1)
  constructor
  · intro t ht0 ht h
    refine ⟨PEqualNP.Outside.L_meta_25748_aux.price_lower_bound hn hk ht0 ht,
      fun hkh => PEqualNP.Outside.L_meta_25748_aux.price_eq_spaced hn hk1 hk ht0 ht hkh,
      fun hkn => ?_⟩
    change PEqualNP.Outside.L_meta_25748_aux.price hn k t = n * t
    rw [hkn]
    exact PEqualNP.Outside.L_meta_25748_aux.price_full_window hn ht
  · intro d hd
    have hpow_pos : 0 < 2 ^ d := by positivity
    have hpow_le : 2 ^ d ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    have hclog : Nat.clog 2 (2 ^ d) = d := Nat.clog_pow 2 d (by decide : 1 < 2)
    constructor
    · constructor
      · intro hpeq
        have hne := PEqualNP.Outside.L_meta_25748_aux.price_nonempty (k := k) hn hpow_le
        have hmem := Nat.sInf_mem hne
        change ∃ A ∈ (PEqualNP.Outside.L_meta_25748_aux.full hn k).powerset,
          2 ^ d ≤ PEqualNP.Outside.L_meta_25748_aux.total hn k A ∧
          A.card = PEqualNP.Outside.L_meta_25748_aux.price hn k (2 ^ d) at hmem
        rcases hmem with ⟨A, hAfull, hAtot, hAcard⟩
        change A.card = price (2 ^ d) at hAcard
        rw [hpeq] at hAcard
        exact (PEqualNP.Outside.L_meta_25748_aux.equality_structure hn hk1 hk A hAfull hAtot hAcard).1
      · intro hkd
        have := PEqualNP.Outside.L_meta_25748_aux.price_eq_spaced hn hk1 hk hpow_pos hpow_le
          (by rwa [hclog])
        rwa [hclog] at this
    · intro hkn T hTfull hTtot
      constructor
      · intro hTcard
        exact (PEqualNP.Outside.L_meta_25748_aux.equality_structure hn hk1 hk T hTfull hTtot hTcard).2 hkn
      · rintro ⟨base, free, hfree_card, hsp, rfl⟩
        have := PEqualNP.Outside.L_meta_25748_aux.box_card_spaced hn hk base free hsp
        rwa [hfree_card] at this
