import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25888

lemma z2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by revert x y; decide
lemma z2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma w_sub_eq_add {k : ℕ} (x y : Fin k → ZMod 2) : x - y = x + y :=
  funext fun j => z2_sub_eq_add (x j) (y j)

lemma w_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 :=
  funext fun j => z2_add_self (x j)

lemma log2_two_pow : ∀ n : ℕ, Nat.log2 (2 ^ n) = n
  | 0 => by decide
  | n + 1 => by
    rw [Nat.log2_def]
    have hge : 2 ≤ 2 ^ (n + 1) := by
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      rw [pow_succ]; omega
    rw [if_pos hge]
    have hdiv : 2 ^ (n + 1) / 2 = 2 ^ n := by rw [pow_succ]; omega
    rw [hdiv, log2_two_pow n]

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

lemma rotF_zero {k : ℕ} (hk : 0 < k) (a : ℕ) :
    rotF hk a (0 : Fin k → ZMod 2) = 0 := rfl

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

lemma polarF_zero_left {k : ℕ} (hk : 0 < k) (g : ℕ) (v : Fin k → ZMod 2) :
    polarF hk g 0 v = 0 := by
  funext j; simp [polarF_apply, mixF_zero]

lemma polarF_add_left {k : ℕ} (hk : 0 < k) (g : ℕ) (u1 u2 v : Fin k → ZMod 2) :
    polarF hk g (u1 + u2) v = polarF hk g u1 v + polarF hk g u2 v := by
  funext j; simp only [polarF_apply, mixF_add, Pi.add_apply]; ring

lemma polarF_smul_left {k : ℕ} (hk : 0 < k) (g : ℕ) (c : ZMod 2) (u v : Fin k → ZMod 2) :
    polarF hk g (c • u) v = c • polarF hk g u v := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp [polarF_zero_left]
  · simp

def polarLin {k : ℕ} (hk : 0 < k) (g : ℕ) (d : Fin k → ZMod 2) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun := fun v => polarF hk g v d
  map_add' := fun u1 u2 => polarF_add_left hk g u1 u2 d
  map_smul' := fun c u => polarF_smul_left hk g c u d

lemma layerF_diff_eq {k : ℕ} (hk : 0 < k) (g : ℕ) (v d : Fin k → ZMod 2) :
    layerF hk g (v + d) - layerF hk g v = polarF hk g v d + layerF hk g d := by
  funext j
  simp only [polarF, Pi.sub_apply, Pi.add_apply]
  have : ∀ a b c : ZMod 2, a - b = (a - b - c) + c := by decide
  exact this _ _ _

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

-- General affine linear system over Fin k → ZMod 2
def kerSet {k s : ℕ} (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (A : Finset (Fin s)) : Submodule (ZMod 2) (Fin k → ZMod 2) :=
  ⨅ p ∈ A, LinearMap.ker (L p)

def solSet {k s : ℕ} (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (b : Fin s → (Fin k → ZMod 2)) (A : Finset (Fin s)) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter (fun v => ∀ p ∈ A, L p v = b p)

lemma kerSet_empty {k s : ℕ} (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    kerSet L ∅ = ⊤ := by
  simp [kerSet]

lemma kerSet_insert {k s : ℕ} (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (p : Fin s) (A : Finset (Fin s)) :
    kerSet L (insert p A) = LinearMap.ker (L p) ⊓ kerSet L A := by
  ext v
  simp [kerSet, Submodule.mem_iInf, LinearMap.mem_ker]

lemma kerSet_antitone {k s : ℕ} (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    {A B : Finset (Fin s)} (hAB : A ⊆ B) :
    kerSet L B ≤ kerSet L A := by
  intro v hv
  simp only [kerSet, Submodule.mem_iInf] at hv ⊢
  intro p hp
  exact hv p (hAB hp)

lemma mem_kerSet_iff {k s : ℕ} (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (A : Finset (Fin s)) (v : Fin k → ZMod 2) :
    v ∈ kerSet L A ↔ ∀ p ∈ A, L p v = 0 := by
  simp [kerSet, Submodule.mem_iInf, LinearMap.mem_ker]

lemma card_solSet_of_mem {k s : ℕ}
    (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (b : Fin s → (Fin k → ZMod 2)) (A : Finset (Fin s))
    {v0 : Fin k → ZMod 2} (hv0 : v0 ∈ solSet L b A) :
    (solSet L b A).card = 2 ^ (Module.finrank (ZMod 2) (kerSet L A)) := by
  classical
  have hv0' : ∀ p ∈ A, L p v0 = b p := (Finset.mem_filter.mp hv0).2
  have hbij : (solSet L b A).card = Fintype.card (kerSet L A) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun v hv => (⟨v - v0, by
        rw [mem_kerSet_iff]
        intro p hp
        rw [map_sub, (Finset.mem_filter.mp hv).2 p hp, hv0' p hp, sub_self]⟩ : kerSet L A))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro v1 _ v2 _ h
      have h' : v1 - v0 = v2 - v0 := congrArg Subtype.val h
      exact sub_left_inj.mp h'
    · intro ⟨z, hz⟩ _
      refine ⟨v0 + z, ?_, ?_⟩
      · simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro p hp
        rw [map_add, hv0' p hp, (mem_kerSet_iff L A z).mp hz p hp, add_zero]
      · apply Subtype.ext; simp
  rw [hbij]
  have hcard : Fintype.card (kerSet L A) =
      Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (kerSet L A) :=
    Module.card_eq_pow_finrank (K := ZMod 2) (V := kerSet L A)
  rw [ZMod.card] at hcard
  exact hcard

lemma exists_basis_subset_aux {k s : ℕ}
    (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    ∀ (d : ℕ) (A : Finset (Fin s)),
      Module.finrank (ZMod 2) (kerSet L A) - Module.finrank (ZMod 2) (kerSet L Finset.univ) ≤ d →
      ∃ B : Finset (Fin s), A ⊆ B ∧ B.card ≤ A.card + d ∧ kerSet L B = kerSet L Finset.univ := by
  intro d
  induction d with
  | zero =>
    intro A hd
    have hle : kerSet L Finset.univ ≤ kerSet L A := kerSet_antitone L (Finset.subset_univ A)
    have hfin_le : Module.finrank (ZMod 2) (kerSet L A) ≤
        Module.finrank (ZMod 2) (kerSet L Finset.univ) := by omega
    have heq : kerSet L A = kerSet L Finset.univ :=
      (Submodule.eq_of_le_of_finrank_le hle hfin_le).symm
    exact ⟨A, Finset.Subset.rfl, by omega, heq⟩
  | succ d ih =>
    intro A hd
    by_cases heq : kerSet L A = kerSet L Finset.univ
    · exact ⟨A, Finset.Subset.rfl, by omega, heq⟩
    · have hex : ∃ p : Fin s, ¬ (kerSet L A ≤ LinearMap.ker (L p)) := by
        by_contra hall
        push_neg at hall
        apply heq
        refine le_antisymm ?_ (kerSet_antitone L (Finset.subset_univ A))
        intro v hv
        rw [mem_kerSet_iff]
        intro p _
        exact hall p hv
      obtain ⟨p, hp⟩ := hex
      let A' := insert p A
      have hlt : kerSet L A' < kerSet L A := by
        rw [kerSet_insert]
        refine lt_of_le_of_ne inf_le_right ?_
        intro hinf
        apply hp
        intro v hv
        rw [← hinf] at hv
        exact hv.1
      have hflt : Module.finrank (ZMod 2) (kerSet L A') < Module.finrank (ZMod 2) (kerSet L A) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨B, hA'B, hcardB, hkerB⟩ := ih A' (by omega)
      have hcardA' : A'.card ≤ A.card + 1 := Finset.card_insert_le p A
      exact ⟨B, Finset.Subset.trans (Finset.subset_insert p A) hA'B, by omega, hkerB⟩

lemma exists_basis_subset {k s : ℕ}
    (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    ∃ B : Finset (Fin s),
      B.card ≤ k - Module.finrank (ZMod 2) (kerSet L Finset.univ) ∧
      kerSet L B = kerSet L Finset.univ := by
  have htop : Module.finrank (ZMod 2) (kerSet L ∅) = k := by
    rw [kerSet_empty, finrank_top, Module.finrank_fin_fun]
  obtain ⟨B, _, hcard, hker⟩ :=
    exists_basis_subset_aux L (k - Module.finrank (ZMod 2) (kerSet L Finset.univ)) ∅ (by omega)
  exact ⟨B, by simpa using hcard, hker⟩

lemma exists_infeasible_subset_aux {k s : ℕ}
    (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (b : Fin s → (Fin k → ZMod 2))
    (hempty : solSet L b Finset.univ = ∅) :
    ∀ (d : ℕ) (A : Finset (Fin s)),
      Module.finrank (ZMod 2) (kerSet L A) ≤ d →
      (solSet L b A).Nonempty →
      ∃ small : Finset (Fin s), small.card ≤ A.card + d + 1 ∧ solSet L b small = ∅ := by
  intro d
  induction d with
  | zero =>
    intro A hd ⟨v0, hv0⟩
    have hv0_not : v0 ∉ solSet L b Finset.univ := by rw [hempty]; exact Finset.notMem_empty v0
    simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv0_not
    push_neg at hv0_not
    obtain ⟨p, _, hp⟩ := hv0_not
    refine ⟨insert p A, by have := Finset.card_insert_le p A; omega, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v1 hv1
    have hv1A : v1 ∈ solSet L b A := by
      simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 ⊢
      intro q hq; exact hv1 q (Finset.mem_insert_of_mem hq)
    have hdiff : v1 - v0 ∈ kerSet L A := by
      rw [mem_kerSet_iff]
      intro q hq
      rw [map_sub, (Finset.mem_filter.mp hv1A).2 q hq, (Finset.mem_filter.mp hv0).2 q hq, sub_self]
    classical
    have hcard : Fintype.card (kerSet L A) = 1 := by
      have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := kerSet L A)
      rw [ZMod.card, Nat.le_zero.mp hd, pow_zero] at hc
      exact hc
    have hsub0 : (⟨v1 - v0, hdiff⟩ : kerSet L A) = ⟨0, Submodule.zero_mem _⟩ :=
      Fintype.card_le_one_iff.mp (by omega) _ _
    have heq : v1 = v0 := sub_eq_zero.mp (congrArg Subtype.val hsub0)
    subst heq
    exact hp ((Finset.mem_filter.mp hv1).2 p (Finset.mem_insert_self p A))
  | succ d ih =>
    intro A hd ⟨v0, hv0⟩
    have hv0_not : v0 ∉ solSet L b Finset.univ := by rw [hempty]; exact Finset.notMem_empty v0
    simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv0_not
    push_neg at hv0_not
    obtain ⟨p, _, hp⟩ := hv0_not
    let A' := insert p A
    by_cases hne' : (solSet L b A').Nonempty
    · obtain ⟨v1, hv1⟩ := hne'
      have hv1A : v1 ∈ solSet L b A := by
        simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 ⊢
        intro q hq; exact hv1 q (Finset.mem_insert_of_mem hq)
      have hdiff_mem : v1 - v0 ∈ kerSet L A := by
        rw [mem_kerSet_iff]
        intro q hq
        rw [map_sub, (Finset.mem_filter.mp hv1A).2 q hq, (Finset.mem_filter.mp hv0).2 q hq, sub_self]
      have hdiff_not : v1 - v0 ∉ LinearMap.ker (L p) := by
        rw [LinearMap.mem_ker, map_sub]
        have hv1p : L p v1 = b p := (Finset.mem_filter.mp hv1).2 p (Finset.mem_insert_self p A)
        rw [hv1p]
        intro h0
        exact hp (sub_eq_zero.mp h0).symm
      have hlt : kerSet L A' < kerSet L A := by
        rw [kerSet_insert]
        refine lt_of_le_of_ne inf_le_right ?_
        intro hinf
        apply hdiff_not
        rw [← hinf] at hdiff_mem
        exact hdiff_mem.1
      have hflt : Module.finrank (ZMod 2) (kerSet L A') < Module.finrank (ZMod 2) (kerSet L A) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨small, hcard, hsmall_empty⟩ := ih A' (by omega) ⟨v1, hv1⟩
      have hcardA' : A'.card ≤ A.card + 1 := Finset.card_insert_le p A
      exact ⟨small, by omega, hsmall_empty⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne'
      have hcardA' : A'.card ≤ A.card + 1 := Finset.card_insert_le p A
      exact ⟨A', by omega, hne'⟩

lemma exists_infeasible_subset {k s : ℕ}
    (L : Fin s → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (b : Fin s → (Fin k → ZMod 2))
    (hempty : solSet L b Finset.univ = ∅) :
    ∃ small : Finset (Fin s), small.card ≤ k + 1 ∧ solSet L b small = ∅ := by
  have htop : Module.finrank (ZMod 2) (kerSet L ∅) = k := by
    rw [kerSet_empty, finrank_top, Module.finrank_fin_fun]
  have hne0 : (solSet L b ∅).Nonempty := ⟨0, by simp [solSet]⟩
  obtain ⟨small, hcard, hsmall⟩ := exists_infeasible_subset_aux L b hempty k ∅ (by omega) hne0
  exact ⟨small, by simpa using hcard, hsmall⟩

def keepRec {r s : ℕ} (step : Fin r → Finset (Fin s)) : ∀ n : ℕ, n ≤ r → Finset (Fin s)
  | 0, _ => ∅
  | n + 1, hn => keepRec step n (by omega) ∪ step ⟨n, hn⟩

end PEqualNP.Outside.L_meta_25888

open PEqualNP.Outside.L_meta_25888 in
theorem PEqualNP.Outside.L_meta_25888 : ∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ (col : Bool) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W),
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let S := Fin r → W
    let ok := fun (raw : W) (data : W × S) (h : Fin (r+1)) (keep : Finset (Fin s)) =>
      ∀ t : Fin (r+1), t ≤ h → ∀ p ∈ keep,
        state data (raw+delta p) t - state data raw t = path t p
    let localSet := fun (t : Fin r) => (Finset.univ : Finset W).filter (fun v =>
      ∀ p : Fin s, layer gap (v+path t.castSucc p) - layer gap v +
        rot (inject t.val) (delta p) = path t.succ p)
    let feasible := ∃ data : W × S, ok 0 data (Fin.last r) Finset.univ
    (feasible → ∃ keep : Fin (r+1) → Finset (Fin s),
      keep 0 = ∅ ∧
      (∀ t : Fin r, keep t.castSucc ⊆ keep t.succ ∧
        (keep t.succ \ keep t.castSucc).card ≤ k - Nat.log2 (localSet t).card) ∧
      (∀ (raw : W) (data : W × S) (h : Fin (r+1)),
        (ok raw data h (keep h) ↔ ok raw data h Finset.univ))) ∧
    (¬feasible → ∃ small : Finset (Fin s), small.card ≤ k+1 ∧
      ∀ (raw : W) (data : W × S), ¬ok raw data (Fin.last r) small) := by
  intro k r s hk F W ix rot layer col delta path initial gap inject state S ok localSet feasible
  have hrot_eq : ∀ a x, rot a x = rotF hk a x := fun _ _ => rfl
  have hlayer_eq : ∀ g x, layer g x = layerF hk g x := fun _ _ => rfl
  have hstate0 : ∀ data key, state data key 0 = rot initial key + data.1 := fun _ _ => rfl
  have hstate_succ : ∀ data key (t : Fin r),
      state data key t.succ = layer gap (state data key t.castSucc) + rot (inject t.val) key + data.2 t := by
    intro data key t
    dsimp only [state]
    rw [Fin.val_succ, take_succ_finRange t, List.foldl_append]
    rfl
  have hdiff0 : ∀ raw data p,
      state data (raw + delta p) 0 - state data raw 0 = rot initial (delta p) := by
    intro raw data p
    rw [hstate0, hstate0, hrot_eq, rotF_add, ← hrot_eq, ← hrot_eq]
    abel
  have hdiff_succ : ∀ raw data (t : Fin r) p,
      state data (raw + delta p) t.castSucc - state data raw t.castSucc = path t.castSucc p →
      state data (raw + delta p) t.succ - state data raw t.succ =
        layer gap (state data raw t.castSucc + path t.castSucc p) -
          layer gap (state data raw t.castSucc) + rot (inject t.val) (delta p) := by
    intro raw data t p hprev
    have hadd : state data (raw + delta p) t.castSucc =
        state data raw t.castSucc + path t.castSucc p := by
      have := congrArg (fun x => x + state data raw t.castSucc) hprev
      simpa [sub_add_cancel, add_comm] using this
    rw [hstate_succ, hstate_succ, hadd, hrot_eq, rotF_add, ← hrot_eq, ← hrot_eq]
    abel
  -- Express round-t local equations as linear system L_t p v = rhs_t p
  let Lt : Fin r → Fin s → W →ₗ[F] W := fun t p => polarLin hk gap (path t.castSucc p)
  let rhst : Fin r → Fin s → W := fun t p =>
    path t.succ p - layer gap (path t.castSucc p) - rot (inject t.val) (delta p)
  have heq_iff : ∀ (t : Fin r) (p : Fin s) (v : W),
      (layer gap (v + path t.castSucc p) - layer gap v + rot (inject t.val) (delta p) = path t.succ p) ↔
      Lt t p v = rhst t p := by
    intro t p v
    dsimp only [Lt, rhst, polarLin, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [hlayer_eq]
    rw [layerF_diff_eq]
    constructor
    · intro h; rw [← h]; abel
    · intro h; rw [h]; abel
  have hlocal_eq : ∀ t : Fin r, localSet t = solSet (Lt t) (rhst t) Finset.univ := by
    intro t
    ext v
    simp only [localSet, solSet, Finset.mem_filter, Finset.mem_univ, true_and, true_implies, heq_iff]
  have hfeas_iff : feasible ↔
      (∀ p : Fin s, path 0 p = rot initial (delta p)) ∧ ∀ t : Fin r, (localSet t).Nonempty := by
    constructor
    · rintro ⟨data, hok⟩
      refine ⟨fun p => ?_, fun t => ?_⟩
      · have h0 := hok 0 (Fin.zero_le _) p (Finset.mem_univ p)
        rw [hdiff0] at h0; exact h0.symm
      · refine ⟨state data 0 t.castSucc, ?_⟩
        simp only [localSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro p
        have hprev := hok t.castSucc (Fin.le_last _) p (Finset.mem_univ p)
        have hnext := hok t.succ (Fin.le_last _) p (Finset.mem_univ p)
        rw [hdiff_succ 0 data t p hprev] at hnext
        exact hnext
    · rintro ⟨hinit, hloc⟩
      by_cases hr : r = 0
      · subst hr
        refine ⟨(0, Fin.elim0), fun t _ p _ => ?_⟩
        have ht0 : t = 0 := Fin.ext (by simp)
        subst ht0
        rw [hdiff0]; exact (hinit p).symm
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        have hv_ex : ∀ t : Fin r, ∃ v : W, v ∈ localSet t := hloc
        choose v hv using hv_ex
        let name : W := v ⟨0, hrpos⟩
        let c : S := fun t =>
          if ht : t.val + 1 < r then v ⟨t.val + 1, ht⟩ - layer gap (v t) else 0
        have hbase : ∀ (n : ℕ) (hn : n < r), state (name, c) 0 ⟨n, by omega⟩ = v ⟨n, hn⟩ := by
          intro n
          induction n with
          | zero =>
            intro hn
            change state (name, c) 0 0 = v ⟨0, hn⟩
            rw [hstate0, hrot_eq, rotF_zero, zero_add]
          | succ n ih =>
            intro hn
            let tn : Fin r := ⟨n, by omega⟩
            change state (name, c) 0 tn.succ = v ⟨n + 1, hn⟩
            have ih' : state (name, c) 0 tn.castSucc = v tn := ih (by omega)
            rw [hstate_succ, ih']
            dsimp only [c]
            rw [dif_pos hn, hrot_eq, rotF_zero, add_zero]
            abel
        have hdiff_all : ∀ (n : ℕ) (hn : n ≤ r) (p : Fin s),
            state (name, c) (0 + delta p) ⟨n, Nat.lt_succ_of_le hn⟩ -
              state (name, c) 0 ⟨n, Nat.lt_succ_of_le hn⟩ = path ⟨n, Nat.lt_succ_of_le hn⟩ p := by
          intro n
          induction n with
          | zero =>
            intro _ p
            change state (name, c) (0 + delta p) 0 - state (name, c) 0 0 = path 0 p
            rw [hdiff0]; exact (hinit p).symm
          | succ n ih =>
            intro hn p
            let tn : Fin r := ⟨n, by omega⟩
            change state (name, c) (0 + delta p) tn.succ - state (name, c) 0 tn.succ = path tn.succ p
            rw [hdiff_succ 0 (name, c) tn p (ih (by omega) p)]
            have hb := hbase n (by omega)
            change state (name, c) 0 tn.castSucc = v tn at hb
            rw [hb]
            exact (Finset.mem_filter.mp (hv tn)).2 p
        refine ⟨(name, c), fun t _ p _ => ?_⟩
        exact hdiff_all t.val (Nat.le_of_lt_succ t.isLt) p
  constructor
  · -- Part 1: feasible → keep
    intro hfeas
    obtain ⟨hinit, hloc⟩ := hfeas_iff.mp hfeas
    have hstep_ex : ∀ t : Fin r, ∃ B : Finset (Fin s),
        B.card ≤ k - Nat.log2 (localSet t).card ∧ kerSet (Lt t) B = kerSet (Lt t) Finset.univ := by
      intro t
      obtain ⟨v0, hv0⟩ := hloc t
      rw [hlocal_eq t] at hv0
      have hcard := card_solSet_of_mem (Lt t) (rhst t) Finset.univ hv0
      rw [← hlocal_eq t] at hcard
      have hlog : Nat.log2 (localSet t).card = Module.finrank F (kerSet (Lt t) Finset.univ) := by
        rw [hcard, log2_two_pow]
      rw [hlog]
      exact exists_basis_subset (Lt t)
    choose step hstep_card hstep_ker using hstep_ex
    let keep : Fin (r + 1) → Finset (Fin s) := fun h =>
      keepRec step h.val (Nat.le_of_lt_succ h.isLt)
    have hkeep0 : keep 0 = ∅ := rfl
    have hkeep_succ : ∀ t : Fin r, keep t.succ = keep t.castSucc ∪ step t := fun _ => rfl
    refine ⟨keep, hkeep0, fun t => ?_, ?_⟩
    · refine ⟨by rw [hkeep_succ]; exact Finset.subset_union_left, ?_⟩
      rw [hkeep_succ]
      have hsub : (keep t.castSucc ∪ step t) \ keep t.castSucc ⊆ step t := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_union] at hx
        rcases hx.1 with h1 | h2
        · exact False.elim (hx.2 h1)
        · exact h2
      exact le_trans (Finset.card_le_card hsub) (hstep_card t)
    · intro raw data h
      constructor
      · -- Induction on h.val
        suffices ∀ (n : ℕ) (hn : n ≤ r),
            ok raw data ⟨n, Nat.lt_succ_of_le hn⟩ (keep ⟨n, Nat.lt_succ_of_le hn⟩) →
            ok raw data ⟨n, Nat.lt_succ_of_le hn⟩ Finset.univ by
          exact this h.val (Nat.le_of_lt_succ h.isLt)
        intro n
        induction n with
        | zero =>
          intro _ _ t ht p _
          have ht0 : t = 0 := Fin.ext (by simp only [Fin.val_zero]; have : t.val ≤ 0 := ht; omega)
          subst ht0
          rw [hdiff0]; exact (hinit p).symm
        | succ n ih =>
          intro hn hok_succ
          let tn : Fin r := ⟨n, by omega⟩
          have hok_prev : ok raw data tn.castSucc (keep tn.castSucc) := by
            intro t ht p hp
            have hle : t ≤ tn.succ := le_trans ht (Fin.castSucc_le_succ tn)
            have hmem : p ∈ keep tn.succ := by rw [hkeep_succ]; exact Finset.mem_union_left _ hp
            exact hok_succ t hle p hmem
          have hall_prev : ok raw data tn.castSucc Finset.univ := ih (by omega) hok_prev
          -- Show state data raw tn.castSucc ∈ localSet tn
          have hv_mem : state data raw tn.castSucc ∈ localSet tn := by
            obtain ⟨v0, hv0⟩ := hloc tn
            rw [hlocal_eq tn] at hv0 ⊢
            have hv_step : ∀ p ∈ step tn, Lt tn p (state data raw tn.castSucc) = rhst tn p := by
              intro p hp
              rw [← heq_iff]
              have hprev := hall_prev tn.castSucc le_rfl p (Finset.mem_univ p)
              have hmem : p ∈ keep tn.succ := by rw [hkeep_succ]; exact Finset.mem_union_right _ hp
              have hnext := hok_succ tn.succ le_rfl p hmem
              rw [hdiff_succ raw data tn p hprev] at hnext
              exact hnext
            have hdiff_ker : state data raw tn.castSucc - v0 ∈ kerSet (Lt tn) (step tn) := by
              rw [mem_kerSet_iff]
              intro p hp
              rw [map_sub, hv_step p hp, (Finset.mem_filter.mp hv0).2 p (Finset.mem_univ p), sub_self]
            rw [hstep_ker tn, mem_kerSet_iff] at hdiff_ker
            simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and]
            intro p _
            have h0 := hdiff_ker p (Finset.mem_univ p)
            rw [map_sub] at h0
            rw [sub_eq_zero.mp h0]
            exact (Finset.mem_filter.mp hv0).2 p (Finset.mem_univ p)
          intro t ht p _
          by_cases hlt : t ≤ tn.castSucc
          · exact hall_prev t hlt p (Finset.mem_univ p)
          · have hteq : t = tn.succ := Fin.ext (by
              simp only [Fin.val_succ, tn]
              have h1 : t.val ≤ n + 1 := ht
              have h2 : ¬ t.val ≤ n := hlt
              omega)
            subst hteq
            have hprev := hall_prev tn.castSucc le_rfl p (Finset.mem_univ p)
            rw [hdiff_succ raw data tn p hprev]
            exact (Finset.mem_filter.mp hv_mem).2 p
      · intro hall t ht p _
        exact hall t ht p (Finset.mem_univ p)
  · -- Part 2: ¬feasible → small
    intro hnotfeas
    by_cases hinit : ∀ p : Fin s, path 0 p = rot initial (delta p)
    · have hex_empty : ∃ t : Fin r, localSet t = ∅ := by
        by_contra hall
        push_neg at hall
        apply hnotfeas
        rw [hfeas_iff]
        exact ⟨hinit, hall⟩
      obtain ⟨t0, ht0⟩ := hex_empty
      rw [hlocal_eq t0] at ht0
      obtain ⟨small, hcard, hsmall_empty⟩ := exists_infeasible_subset (Lt t0) (rhst t0) ht0
      refine ⟨small, hcard, fun raw data hok => ?_⟩
      have hv_in : state data raw t0.castSucc ∈ solSet (Lt t0) (rhst t0) small := by
        simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro p hp
        rw [← heq_iff]
        have hprev := hok t0.castSucc (Fin.le_last _) p hp
        have hnext := hok t0.succ (Fin.le_last _) p hp
        rw [hdiff_succ raw data t0 p hprev] at hnext
        exact hnext
      rw [hsmall_empty] at hv_in
      exact Finset.notMem_empty _ hv_in
    · push_neg at hinit
      obtain ⟨p0, hp0⟩ := hinit
      refine ⟨{p0}, by simp, fun raw data hok => ?_⟩
      have h0 := hok 0 (Fin.zero_le _) p0 (Finset.mem_singleton_self p0)
      rw [hdiff0] at h0
      exact hp0 h0.symm
