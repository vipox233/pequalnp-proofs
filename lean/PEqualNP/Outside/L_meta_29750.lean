import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29750

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open scoped BigOperators

private def entire (C : Circuit) : Finset ℕ := Finset.range C.size
private def useOld (C : Circuit) (S : Finset ℕ) (o w : ℕ) : ℕ :=
  readsIn C S w + (if o = w then 1 else 0)
private structure ConeData (N : ℕ) (C : Circuit) (S : Finset ℕ) (r : ℕ) : Prop where
  subset : S ⊆ entire C
  root : r ∈ S
  order : ∀ j ∈ S, j ≤ r
  closed : ∀ j ∈ S, ∀ i, N+i ∈ (gateAt C j).inputs → i ∈ S
  used : ∀ j ∈ S, j ≠ r → 0 < readsIn C S (N+j)
private theorem reads_le (C : Circuit) {S T : Finset ℕ} (hst : S ⊆ T) (w : ℕ) :
    readsIn C S w ≤ readsIn C T w := Finset.sum_le_sum_of_subset hst
private theorem reads_sdiff (C : Circuit) {S T : Finset ℕ} (hst : S ⊆ T) (w : ℕ) :
    readsIn C (T \ S) w + readsIn C S w = readsIn C T w := Finset.sum_sdiff hst
private theorem reads_pos_has_reader (C : Circuit) (S : Finset ℕ) (w : ℕ)
    (h : 0 < readsIn C S w) : ∃ j ∈ S, w ∈ (gateAt C j).inputs := by
  by_contra hn
  push Not at hn
  have h0 : readsIn C S w = 0 :=
    Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hn j hj))
  omega
private theorem reads_zero_when (C : Circuit) (S : Finset ℕ) (w : ℕ)
    (hn : ∀ j ∈ S, w ∉ (gateAt C j).inputs) : readsIn C S w = 0 :=
  Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hn j hj))
private theorem exclusive_reads {N : ℕ} {C : Circuit} {S : Finset ℕ} {r j : ℕ}
    (h : ConeData N C S r) (hj : j ∉ S) : readsIn C S (N+j) = 0 := by
  apply reads_zero_when
  intro g hg hread
  exact hj (h.closed g hg j hread)
private structure SplitCounts (N : ℕ) (C : Circuit) (f t h : ℕ) (F H D : Finset ℕ) : Prop where
  size : F.card + H.card + D.card + 1 = C.size
  last_mem : C.size-1 ∈ D
  raw : ∀ i < N, useOld C F (N+f) i + useOld C H h i + useOld C D C.output i =
    readsIn C (entire C) i
  intF : ∀ j ∈ F, useOld C F (N+f) (N+j) = 1
  intH : ∀ j ∈ H, useOld C H h (N+j) = 1
  intD : ∀ j ∈ D, useOld C D C.output (N+j) = 1
  forkH : useOld C H h (N+f) = 1
  forkD : useOld C D C.output (N+f) = 1
  notD : useOld C D C.output (N+t) = 1
private theorem splitCounts (N : ℕ) (C : Circuit) (f t h : ℕ) (F T : Finset ℕ)
    (hF : ConeData N C F f) (hT : ConeData N C T t) (hst : F ⊆ T) (hft : f < t)
    (hback : ReadsBack N C) (hout : C.output+1 = N+C.size)
    (hread : ∀ j ∈ entire C, readsIn C (entire C) (N+j) =
      if j = f then 2 else if j+1 = C.size then 0 else 1)
    (hfork : readsIn C T (N+f) = 1) (hhead : (gateAt C t).inputs = [h])
    (hraw : N ≤ h) :
    SplitCounts N C f t h F (T \ insert t F) (entire C \ T) := by
  let H := T \ insert t F
  let D := entire C \ T
  have htF : t ∉ F := fun ht => (Nat.not_le_of_lt hft) (hF.order t ht)
  have htf : insert t F ⊆ T := Finset.insert_subset hT.root hst
  have htlt : t < C.size := Finset.mem_range.mp (hT.subset hT.root)
  have hflt : f < C.size := by omega
  have hsep (w : ℕ) : readsIn C H w + readsIn C F w + (if h=w then 1 else 0) =
      readsIn C T w := by
    have hv := reads_sdiff C htf w
    have hs : readsIn C (insert t F) w =
        (if h=w then 1 else 0) + readsIn C F w := by
      unfold readsIn
      rw [Finset.sum_insert htF, hhead]
      simp [List.count_cons]
    change readsIn C H w + readsIn C (insert t F) w = _ at hv
    omega
  have houter (w : ℕ) : readsIn C D w + readsIn C T w =
      readsIn C (entire C) w := reads_sdiff C hT.subset w
  have hreadFork : readsIn C D (N+f) = 1 := by
    have hr := houter (N+f)
    rw [hfork, hread f (Finset.mem_range.mpr hflt), ite_eq_left rfl] at hr
    omega
  have hlast : C.size-1 ∈ D := by
    obtain ⟨j, hj, -⟩ := reads_pos_has_reader C D (N+f) (by omega)
    let k := D.max' (show D.Nonempty from ⟨j,hj⟩)
    have hk : k ∈ D := Finset.max'_mem ..
    have hkall := (Finset.mem_sdiff.mp hk).1
    have hklt : k < C.size := Finset.mem_range.mp hkall
    by_cases heq : k = C.size-1
    · simpa [heq] using hk
    · have hkf : k ≠ f := fun e => (Finset.mem_sdiff.mp hk).2 (e ▸ hst hF.root)
      have hk0 := exclusive_reads hT (Finset.mem_sdiff.mp hk).2
      have hr := houter (N+k)
      rw [hk0, hread k hkall, ite_eq_right hkf, ite_eq_right (by omega)] at hr
      obtain ⟨g, hg, hguse⟩ := reads_pos_has_reader C D (N+k) (by omega)
      have hgle : g ≤ k := Finset.le_max' D g hg
      have hglt : g < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hg).1
      have hlt := hback g hglt (N+k) hguse
      omega
  have htlast : t+1 < C.size := by
    have hnt := (Finset.mem_sdiff.mp hlast).2
    have hne : t ≠ C.size-1 := fun h => hnt (h ▸ hT.root)
    omega
  have horderF : readsIn C F (N+f) = 0 := by
    apply reads_zero_when
    intro j hj hr
    have hlt := hback j (Finset.mem_range.mp (hF.subset hj)) (N+f) hr
    have hjle := hF.order j hj
    omega
  dsimp [H, D] at *
  refine ⟨?_, hlast, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcardH := Finset.card_sdiff (s := insert t F) (t := T)
    have hcardD := Finset.card_sdiff (s := T) (t := entire C)
    rw [Finset.inter_eq_left.mpr htf, Finset.card_insert_of_notMem htF] at hcardH
    rw [Finset.inter_eq_left.mpr hT.subset] at hcardD
    have hs := Finset.card_le_card htf
    rw [Finset.card_insert_of_notMem htF] at hs
    have hs' := Finset.card_le_card hT.subset
    simp only [entire, Finset.card_range] at hcardD hs'
    change (entire C \ T).card = C.size - T.card at hcardD
    rw [hcardH, hcardD]
    omega
  · intro i hi
    have h1 := hsep i
    have h2 := houter i
    simp only [useOld, ite_eq_right (show ¬ N+f=i by omega), ite_eq_right (show ¬ h=i by omega),
      ite_eq_right (show ¬ C.output=i by omega), Nat.add_zero] at h1 ⊢
    omega
  · intro j hj
    by_cases hjf : j = f
    · subst j
      simp [useOld, horderF]
    · have hjle := hF.order j hj
      have hr := hread j (hF.subset hj)
      rw [ite_eq_right hjf, ite_eq_right (by omega)] at hr
      have hl := reads_le C hF.subset (N+j)
      have hp := hF.used j hj hjf
      simp only [useOld, ite_eq_right (show ¬ N+f=N+j by omega), Nat.add_zero]
      omega
  · intro j hj
    have hj' := Finset.mem_sdiff.mp hj
    have hjt : j ≠ t := fun e => hj'.2 (e ▸ Finset.mem_insert_self ..)
    have hjF : j ∉ F := fun hm => hj'.2 (Finset.mem_insert_of_mem hm)
    have hjf : j ≠ f := fun e => hjF (e ▸ hF.root)
    have hjle := hT.order j hj'.1
    have hp := hT.used j hj'.1 hjt
    have hl := reads_le C hT.subset (N+j)
    have hz := exclusive_reads hF hjF
    have hr := hread j (hT.subset hj'.1)
    have he := hsep (N+j)
    rw [ite_eq_right hjf, ite_eq_right (by omega)] at hr
    unfold useOld
    omega
  · intro j hj
    have hj' := Finset.mem_sdiff.mp hj
    have hjf : j ≠ f := fun e => hj'.2 (e ▸ hst hF.root)
    have hr := hread j hj'.1
    have hz := exclusive_reads hT hj'.2
    have he := houter (N+j)
    simp only [hz, Nat.add_zero] at he
    unfold useOld
    rw [he, hr, ite_eq_right hjf]
    by_cases heq : j+1 = C.size <;> simp [heq, show C.output=N+j ↔ j+1=C.size by omega]
  · have he := hsep (N+f)
    unfold useOld
    omega
  · simp [useOld, hreadFork, show C.output ≠ N+f by omega]
  · have hr := hread t (hT.subset hT.root)
    have he := houter (N+t)
    have hz := reads_zero_when C T (N+t) (by
      intro j hj hm
      have hlt := hback j (Finset.mem_range.mp (hT.subset hj)) (N+t) hm
      have hle := hT.order j hj
      omega)
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hr
    simp [useOld, show C.output ≠ N+t by omega]
    omega

private theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega
private theorem cones_length (n : ℕ) (C : Circuit) :
    (PEqualNP.EdgeOwnership.cones n C).length = C.gates.length := by
  unfold PEqualNP.EdgeOwnership.cones
  rw [cones_len]; simp
private theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
private theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3
private theorem inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩
private theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩
private theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3
private theorem inCone_irrefl (n : ℕ) (C : Circuit) (j : ℕ) : ¬ PEqualNP.EdgeOwnership.InCone n C j j := by
  intro h
  have := (inCone_lt n C j j h).1
  omega

private def inFork (N : ℕ) (C : Circuit) (f j : ℕ) : Prop :=
  j = f ∨ InCone N C j f
private def inInner (N : ℕ) (C : Circuit) (f t j : ℕ) : Prop :=
  InCone N C j t ∧ ¬ inFork N C f j
private def inOuter (N : ℕ) (C : Circuit) (t j : ℕ) : Prop :=
  j ≠ t ∧ ¬ InCone N C j t
private abbrev UniqueReaders (N : ℕ) (C : Circuit) (f : ℕ) : Prop :=
  ∀ {i a b : ℕ}, i ≠ f → a < C.size → b < C.size →
    N+i ∈ (gateAt C a).inputs → N+i ∈ (gateAt C b).inputs → a = b
private theorem inCone_first (N : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone N C i j → ∃ k < C.size,
      N+i ∈ (gateAt C k).inputs ∧ (k = j ∨ InCone N C k j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    obtain ⟨hj, a, ha, hread, hi | hi⟩ := (inCone_iff N C i j).mp h
    · exact ⟨j, hj, by simpa [hi] using hread, Or.inl rfl⟩
    · obtain ⟨k,hk,hr,hnext | hnext⟩ := ih a ha hi
      · exact ⟨k,hk,hr,Or.inr (by simpa [hnext] using inCone_of_read N C a j hj ha hread)⟩
      · exact ⟨k,hk,hr,Or.inr (inCone_trans N C k a hnext j
          (inCone_of_read N C a j hj ha hread))⟩
private theorem inFork_inCone {N : ℕ} {C : Circuit} {f t j : ℕ}
    (ft : InCone N C f t) (hj : inFork N C f j) : InCone N C j t := by
  rcases hj with h | h
  · simpa [h] using ft
  · exact inCone_trans N C j f h t ft
private theorem inFork_le {N : ℕ} {C : Circuit} {f j : ℕ} (hj : inFork N C f j) :
    j ≤ f := by
  rcases hj with h | h
  · exact h.le
  · exact (inCone_lt N C j f h).1.le
private theorem pred_fork {N : ℕ} {C : Circuit} {f k j : ℕ}
    (rb : ReadsBack N C) (hj : j < C.size) (hf : inFork N C f j)
    (hr : N+k ∈ (gateAt C j).inputs) : inFork N C f k := by
  have hlt := rb j hj (N+k) hr
  have c := inCone_of_read N C k j hj (by omega) hr
  right
  rcases hf with h | h
  · simpa [h] using c
  · exact inCone_trans N C k j c f h
private theorem reader_of_fork_strict {N : ℕ} {C : Circuit} {f k j : ℕ}
    (unique : UniqueReaders N C f) (hj : j < C.size) (hc : InCone N C k f)
    (hr : N+k ∈ (gateAt C j).inputs) : inFork N C f j := by
  obtain ⟨a,ha,hr',qin⟩ := inCone_first N C k f hc
  have kn := (inCone_lt N C k f hc).1.ne
  have eq := unique kn hj ha hr hr'
  simpa [inFork, eq] using qin
private theorem reader_of_inner {N : ℕ} {C : Circuit} {f t k j : ℕ}
    (unique : UniqueReaders N C f) (hj : j < C.size) (hc : inInner N C f t k)
    (hr : N+k ∈ (gateAt C j).inputs) : j = t ∨ InCone N C j t := by
  obtain ⟨a,ha,hr',qin⟩ := inCone_first N C k t hc.1
  have kn : k ≠ f := fun h => hc.2 (Or.inl h)
  have eq := unique kn hj ha hr hr'
  simpa [eq] using qin
private theorem pred_inner {N : ℕ} {C : Circuit} {f t k j : ℕ}
    (rb : ReadsBack N C) (unique : UniqueReaders N C f)
    (hj : j < C.size) (hc : inInner N C f t j)
    (hr : N+k ∈ (gateAt C j).inputs) : k = f ∨ inInner N C f t k := by
  have hlt := rb j hj (N+k) hr
  have c := inCone_of_read N C k j hj (by omega) hr
  by_cases h : k = f
  · exact Or.inl h
  · right
    refine ⟨inCone_trans N C k j c t hc.1,?_⟩
    intro hFork
    rcases hFork with h' | h'
    · exact h h'
    · exact hc.2 (reader_of_fork_strict unique hj h' hr)
private theorem pred_outer {N : ℕ} {C : Circuit} {f t k j : ℕ}
    (unique : UniqueReaders N C f) (ft : InCone N C f t)
    (hj : j < C.size) (hc : inOuter N C t j)
    (hr : N+k ∈ (gateAt C j).inputs) : k = f ∨ k = t ∨ inOuter N C t k := by
  by_cases hf : k = f
  · exact Or.inl hf
  right
  by_cases ht : k = t
  · exact Or.inl ht
  refine Or.inr ⟨ht,?_⟩
  intro hcone
  by_cases hk : InCone N C k f
  · have fj := reader_of_fork_strict unique hj hk hr
    exact hc.2 (inFork_inCone ft fj)
  · have hin : inInner N C f t k := ⟨hcone, fun h => h.elim hf hk⟩
    exact (reader_of_inner unique hj hin hr).elim hc.1 hc.2
private theorem not_operand {N : ℕ} {C : Circuit} {f t : ℕ} (ft : InCone N C f t)
    (ht : (gateAt C t).inputs.length = 1) :
    ∃ k < t, (gateAt C t).inputs = [N+k] ∧
      (∀ j, InCone N C j t ↔ j = k ∨ InCone N C j k) ∧
      (k = f ∨ inInner N C f t k) := by
  obtain ⟨htC,k,hk,hr,fc⟩ := (inCone_iff N C f t).mp ft
  obtain ⟨w,hw⟩ := List.length_eq_one_iff.mp ht
  have he : w = N+k := (show N+k = w from by simpa [hw] using hr).symm
  have heq : (gateAt C t).inputs = [N+k] := hw.trans (congrArg (fun w => [w]) he)
  have char (j : ℕ) : InCone N C j t ↔ j = k ∨ InCone N C j k := by
    rw [inCone_iff]
    constructor
    · rintro ⟨_,a,_,ha,h⟩
      have h' : a = k := by simpa [heq] using ha
      simpa [h'] using h
    · intro h
      exact ⟨htC,k,hk,hr,h⟩
  refine ⟨k,hk,heq,char,?_⟩
  by_cases eq : k = f
  · exact Or.inl eq
  right
  refine ⟨(char k).2 (Or.inl rfl),?_⟩
  intro hf
  have hi := inFork_le hf
  have hfi : f ≤ k := fc.elim (fun h => h.le) (fun h => (inCone_lt N C f k h).1.le)
  exact eq (Nat.le_antisymm hi hfi)
private theorem mem_insert_cone {N : ℕ} {C : Circuit} {j k : ℕ} :
    k ∈ insert j ((cones N C).getD j []).toFinset ↔ k = j ∨ InCone N C k j := by
  simp [InCone]

private theorem coneData_of_root {N : ℕ} {C : Circuit} {r : ℕ}
    (rb : ReadsBack N C) (hr : r < C.size) :
    ConeData N C (insert r ((cones N C).getD r []).toFinset) r := by
  let S := insert r ((cones N C).getD r []).toFinset
  have sub : S ⊆ entire C := by
    intro j hj
    apply Finset.mem_range.mpr
    exact ((mem_insert_cone.mp hj).elim (fun e => e.le)
      (fun h => (inCone_lt N C j r h).1.le)).trans_lt hr
  refine ⟨sub,Finset.mem_insert_self _ _,?_,?_,?_⟩
  · intro j hj
    exact inFork_le (mem_insert_cone.mp hj)
  · intro j hj i hread
    exact mem_insert_cone.mpr (pred_fork rb (Finset.mem_range.mp (sub hj))
      (mem_insert_cone.mp hj) hread)
  · intro j hj hne
    have hc := (mem_insert_cone.mp hj).resolve_left hne
    obtain ⟨k,hk,hread,hin⟩ := inCone_first N C j r hc
    have hsub : ({k} : Finset ℕ) ⊆ S := Finset.singleton_subset_iff.mpr (mem_insert_cone.mpr hin)
    have hle := reads_le C hsub (N+j)
    simp only [readsIn, Finset.sum_singleton] at hle
    exact (List.count_pos_iff.mpr hread).trans_le hle
private theorem cone_subset_of_inCone {N : ℕ} {C : Circuit} {f t : ℕ}
    (ft : InCone N C f t) :
    insert f ((cones N C).getD f []).toFinset ⊆ insert t ((cones N C).getD t []).toFinset := by
  intro j hj
  exact mem_insert_cone.mpr (Or.inr (inFork_inCone ft (mem_insert_cone.mp hj)))

private theorem unique_readers_of_bound {N : ℕ} {C : Circuit} {f : ℕ}
    (rb : ReadsBack N C)
    (bound : ∀ i < C.size, i ≠ f → readsIn C (entire C) (N+i) ≤ 1) :
    UniqueReaders N C f := by
  intro i a b hif ha hb har hbr
  have hi' := rb a ha (N+i) har
  have hi : i < C.size := by omega
  by_contra E
  have hsub : ({a,b} : Finset ℕ) ⊆ entire C := by
    exact Finset.insert_subset (Finset.mem_range.mpr ha)
      (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hb))
  have h := (reads_le C hsub (N+i)).trans (bound i hi hif)
  unfold readsIn at h
  rw [Finset.sum_insert (by simpa using E), Finset.sum_singleton] at h
  have ap := List.count_pos_iff.mpr har
  have bp := List.count_pos_iff.mpr hbr
  omega
private theorem mem_inner {N : ℕ} {C : Circuit} {f t j : ℕ} :
    j ∈ insert t ((cones N C).getD t []).toFinset \
        insert t (insert f ((cones N C).getD f []).toFinset) ↔ inInner N C f t j := by
  rw [Finset.mem_sdiff, mem_insert_cone, Finset.mem_insert, mem_insert_cone]
  constructor
  · rintro ⟨h, no⟩
    exact ⟨h.resolve_left (fun h => no (Or.inl h)), fun h => no (Or.inr h)⟩
  · rintro ⟨h, no⟩
    refine ⟨Or.inr h, ?_⟩
    rintro (e | h')
    · exact inCone_irrefl N C t (e ▸ h)
    · exact no h'
private theorem mem_outer {N : ℕ} {C : Circuit} {t j : ℕ} :
    j ∈ entire C \ insert t ((cones N C).getD t []).toFinset ↔
      j < C.size ∧ inOuter N C t j := by
  rw [Finset.mem_sdiff, mem_insert_cone, entire, Finset.mem_range, not_or]
  rfl

private def rank (S : Finset ℕ) (j : ℕ) : ℕ := S.sort.idxOf j
private def loc (N : ℕ) (P : List ℕ) (S : Finset ℕ) (w : ℕ) : ℕ :=
  if w < N then w else if w ∈ P then N + P.idxOf w else N + P.length + rank S (w-N)
private def build (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ) : Circuit :=
  ⟨S.sort.map (fun j => ⟨(gateAt C j).op, (gateAt C j).inputs.map (loc N P S)⟩), loc N P S o⟩
private def Ports (N : ℕ) (P : List ℕ) (S : Finset ℕ) : Prop :=
  ∀ w ∈ P, N ≤ w ∧ w-N ∉ S
private def Available (N : ℕ) (P : List ℕ) (S : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ w ∈ P ∨ ∃ j ∈ S, w = N+j
private def Closed (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) : Prop :=
  ∀ j ∈ S, ∀ w ∈ (gateAt C j).inputs, Available N P S w
private theorem loc_raw (N : ℕ) (P : List ℕ) (S : Finset ℕ) {w : ℕ} (hw : w < N) :
    loc N P S w = w := by
  simp [loc, hw]
private theorem loc_port (N : ℕ) (P : List ℕ) (S : Finset ℕ) {w : ℕ}
    (hp : Ports N P S) (hw : w ∈ P) :
    loc N P S w = N + P.idxOf w := by
  simp [loc, hw, Nat.not_lt.mpr (hp w hw).1]
private theorem loc_gate (N : ℕ) (P : List ℕ) (S : Finset ℕ)
    (hp : Ports N P S) {j : ℕ} (hj : j ∈ S) :
    loc N P S (N+j) = N + P.length + rank S j := by
  have hnot : N+j ∉ P := fun h => (hp (N+j) h).2 (by simpa using hj)
  simp [loc, hnot, show ¬ N+j < N by omega]
private theorem rank_bound (S : Finset ℕ) {j : ℕ} (hj : j ∈ S) : rank S j < S.card := by
  unfold rank
  rw [← Finset.length_sort (s := S) (· ≤ ·)]
  exact List.idxOf_lt_length_of_mem (by simpa using hj)
private theorem rank_lt_iff (S : Finset ℕ) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) :
    rank S i < rank S j ↔ i < j := by
  let e := S.orderIsoOfFin rfl
  have ei : (e.symm ⟨i, hi⟩).val = rank S i := Finset.orderIsoOfFin_symm_apply S rfl ⟨i, hi⟩
  have ej : (e.symm ⟨j, hj⟩).val = rank S j := Finset.orderIsoOfFin_symm_apply S rfl ⟨j, hj⟩
  rw [← ei, ← ej]
  exact e.symm.lt_iff_lt
private theorem rank_inj (S : Finset ℕ) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S)
    (h : rank S i = rank S j) : i = j := by
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt (fun hlt => (Nat.ne_of_lt ((rank_lt_iff S hj hi).mpr hlt)) h.symm)
  · exact Nat.le_of_not_gt (fun hlt => (Nat.ne_of_lt ((rank_lt_iff S hi hj).mpr hlt)) h)
private theorem rank_surj (S : Finset ℕ) {i : ℕ} (hi : i < S.card) :
    ∃ j ∈ S, rank S j = i := by
  let e := S.orderIsoOfFin rfl
  let j := e ⟨i, hi⟩
  refine ⟨j.val, j.property, ?_⟩
  rw [rank, ← Finset.orderIsoOfFin_symm_apply S rfl j]
  exact congrArg Fin.val (e.symm_apply_apply ⟨i, hi⟩)

@[simp] theorem build_size (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ) :
    (build N C S P o).size = S.card := by
  simp [build, Circuit.size]
private theorem gateAt_build (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    {j : ℕ} (hj : j ∈ S) :
    gateAt (build N C S P o) (rank S j) =
      ⟨(gateAt C j).op, (gateAt C j).inputs.map (loc N P S)⟩ := by
  have hlt : rank S j < S.sort.length := by simpa using rank_bound S hj
  have hget : S.sort[rank S j] = j := List.getElem_idxOf hlt
  simp only [gateAt, build, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, hget]
  rfl
private theorem build_readsBack (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (hs : S ⊆ Finset.range C.size) (hp : Ports N P S) (hc : Closed N C S P)
    (hb : ReadsBack N C) :
    ReadsBack (N+P.length) (build N C S P o) := by
  intro j hj w hw
  change j < (build N C S P o).size at hj
  have hj' : j < S.card := by simpa using hj
  obtain ⟨g, hg, rfl⟩ := rank_surj S hj'
  rw [gateAt_build N C S P o hg] at hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rcases hc g hg v hv with hraw | hport | ⟨i, hi, rfl⟩
  · rw [loc_raw N P S hraw]
    omega
  · rw [loc_port N P S hp hport]
    have := List.idxOf_lt_length_of_mem hport
    omega
  · rw [loc_gate N P S hp hi]
    have hvlt := hb g (Finset.mem_range.mp (hs hg)) (N+i) hv
    exact Nat.add_lt_add_left ((rank_lt_iff S hi hg).mpr (by omega)) _
private theorem loc_valid (N : ℕ) (P : List ℕ) (S : Finset ℕ) {w : ℕ}
    (hp : Ports N P S) (hw : Available N P S w) :
    loc N P S w < N + P.length + S.card := by
  obtain hraw | hport | ⟨i, hi, rfl⟩ := hw
  · rw [loc_raw N P S hraw]
    omega
  · rw [loc_port N P S hp hport]
    have := List.idxOf_lt_length_of_mem hport
    omega
  · rw [loc_gate N P S hp hi]
    have := rank_bound S hi
    omega
private theorem build_ops (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (h : ∀ j ∈ S, ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      (gateAt C j).inputs.length = 2) :
    ∀ g ∈ (build N C S P o).gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  simpa using h j (by simpa using hj)
private theorem port_index_inj {P : List ℕ} {u v : ℕ} (hu : u ∈ P) (hv : v ∈ P)
    (h : P.idxOf u = P.idxOf v) : u = v := by
  have hu' : P[P.idxOf u]? = some u := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hu), List.getElem_idxOf]
  have hv' : P[P.idxOf v]? = some v := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hv), List.getElem_idxOf]
  rw [h] at hu'
  exact Option.some.inj (hu'.symm.trans hv')
private theorem loc_inj (N : ℕ) (P : List ℕ) (S : Finset ℕ) (hp : Ports N P S)
    {u v : ℕ} (hu : Available N P S u) (hv : Available N P S v)
    (he : loc N P S u = loc N P S v) : u = v := by
  rcases hu with hu | hu | ⟨i, hi, rfl⟩ <;>
    rcases hv with hv | hv | ⟨j, hj, rfl⟩
  · simpa only [loc_raw N P S hu, loc_raw N P S hv] using he
  · rw [loc_raw N P S hu, loc_port N P S hp hv] at he
    omega
  · rw [loc_raw N P S hu, loc_gate N P S hp hj] at he
    omega
  · rw [loc_port N P S hp hu, loc_raw N P S hv] at he
    omega
  · rw [loc_port N P S hp hu, loc_port N P S hp hv] at he
    exact port_index_inj hu hv (Nat.add_left_cancel he)
  · rw [loc_port N P S hp hu, loc_gate N P S hp hj] at he
    have := List.idxOf_lt_length_of_mem hu
    omega
  · rw [loc_gate N P S hp hi, loc_raw N P S hv] at he
    omega
  · rw [loc_gate N P S hp hi, loc_port N P S hp hv] at he
    have := List.idxOf_lt_length_of_mem hv
    omega
  · rw [loc_gate N P S hp hi, loc_gate N P S hp hj] at he
    exact congrArg (fun q : ℕ => N+q) (rank_inj S hi hj (Nat.add_left_cancel he))
private theorem readsIn_build (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (hp : Ports N P S) (hc : Closed N C S P) {w : ℕ} (hw : Available N P S w) :
    readsIn (build N C S P o) (Finset.range (build N C S P o).size) (loc N P S w) =
      readsIn C S w := by
  simp only [readsIn, build_size]
  symm
  refine Finset.sum_bij (fun j _ => rank S j) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr (rank_bound S hj)
  · intro i hi j hj eq
    exact rank_inj S hi hj eq
  · intro i hi
    obtain ⟨j, hj, he⟩ := rank_surj S (Finset.mem_range.mp hi)
    exact ⟨j, hj, he⟩
  · intro j hj
    rw [gateAt_build N C S P o hj]
    simp only [List.count, List.countP_map]
    symm
    apply List.countP_congr
    intro v hv
    simp only [Function.comp_apply, beq_iff_eq]
    exact ⟨loc_inj N P S hp (hc j hj v hv) hw, congrArg (loc N P S)⟩

private theorem closed_fork {N : ℕ} {C : Circuit} {F : Finset ℕ} {f : ℕ}
    (dataF : ConeData N C F f) : Closed N C F [] := by
  intro j hj w hw
  by_cases ws : w < N
  · exact Or.inl ws
  have eq : w = N+(w-N) := by omega
  exact Or.inr (Or.inr ⟨w-N,dataF.closed j hj (w-N) (eq ▸ hw),eq⟩)
private theorem closed_inner {N : ℕ} {C : Circuit} {f t : ℕ}
    (rb : ReadsBack N C) (unique : UniqueReaders N C f) :
    Closed N C (insert t ((cones N C).getD t []).toFinset \
      insert t (insert f ((cones N C).getD f []).toFinset)) [N+f] := by
  intro j hj w hw
  by_cases ws : w < N
  · exact Or.inl ws
  have eq : w = N+(w-N) := by omega
  have hjIn := mem_inner.mp hj
  have hjlt := (inCone_lt N C j t hjIn.1).1.trans (inCone_lt N C j t hjIn.1).2
  rcases pred_inner rb unique hjlt hjIn (eq ▸ hw) with h | h
  · exact Or.inr (Or.inl (by rw [eq, h]; simp))
  · exact Or.inr (Or.inr ⟨w-N,mem_inner.mpr h,eq⟩)
private theorem closed_outer {N : ℕ} {C : Circuit} {f t : ℕ}
    (rb : ReadsBack N C) (unique : UniqueReaders N C f) (ft : InCone N C f t) :
    Closed N C (entire C \ insert t ((cones N C).getD t []).toFinset) [N+f,N+t] := by
  intro j hj w hw
  by_cases ws : w < N
  · exact Or.inl ws
  have eq : w = N+(w-N) := by omega
  have hj' := mem_outer.mp hj
  have hlt := rb j hj'.1 w hw
  have hk : w-N < C.size := by omega
  rcases pred_outer unique ft hj'.1 hj'.2 (eq ▸ hw) with h | h | h
  · exact Or.inr (Or.inl (by rw [eq, h]; simp))
  · exact Or.inr (Or.inl (by rw [eq, h]; simp))
  · exact Or.inr (Or.inr ⟨w-N,mem_outer.mpr ⟨hk,h⟩,eq⟩)
private theorem ports_inner {N : ℕ} {C : Circuit} {f t : ℕ} :
    Ports N [N+f] (insert t ((cones N C).getD t []).toFinset \
      insert t (insert f ((cones N C).getD f []).toFinset)) := by
  intro w hw
  have e := List.mem_singleton.mp hw
  subst w
  refine ⟨by omega, ?_⟩
  intro hm
  have hf := (mem_inner.mp hm).2
  exact hf (Or.inl (by omega))
private theorem ports_outer {N : ℕ} {C : Circuit} {f t : ℕ}
    (ft : InCone N C f t) :
    Ports N [N+f,N+t] (entire C \ insert t ((cones N C).getD t []).toFinset) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact fun hm => (mem_outer.mp hm).2.2 ft
  · refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact fun hm => (mem_outer.mp hm).2.1 rfl
private theorem available_inner_root {N : ℕ} {C : Circuit} {f t k : ℕ}
    (hk : k = f ∨ inInner N C f t k) :
    Available N [N+f] (insert t ((cones N C).getD t []).toFinset \
      insert t (insert f ((cones N C).getD f []).toFinset)) (N+k) := by
  rcases hk with rfl | hk
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr ⟨k,mem_inner.mpr hk,rfl⟩)

private def actualUse (D : Circuit) (w : ℕ) : ℕ :=
  readsIn D (Finset.range D.size) w + (if D.output = w then 1 else 0)
private def tree (n : ℕ) (D : Circuit) : Prop :=
  (∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
  ReadsBack n D ∧
  (D.output+1 = n+D.size ∨ (D.size = 0 ∧ D.output < n)) ∧
  (∀ i < n, actualUse D i ≤ 1) ∧
  (∀ j < D.size, actualUse D (n+j) = 1)
private theorem build_use (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (hp : Ports N P S) (hc : Closed N C S P) (ho : Available N P S o)
    {w : ℕ} (hw : Available N P S w) :
    actualUse (build N C S P o) (loc N P S w) =
      readsIn C S w + (if o = w then 1 else 0) := by
  unfold actualUse
  rw [readsIn_build N C S P o hp hc hw]
  change readsIn C S w + (if loc N P S o = loc N P S w then 1 else 0) = _
  by_cases h : o = w
  · simp [h]
  · have hne : loc N P S o ≠ loc N P S w := fun he => h (loc_inj N P S hp ho hw he)
    simp [h, hne]
private theorem build_tree (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (hs : S ⊆ Finset.range C.size) (hp : Ports N P S) (hnd : P.Nodup)
    (hc : Closed N C S P) (hb : ReadsBack N C)
    (hops : ∀ j ∈ S, ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      (gateAt C j).inputs.length = 2)
    (ho : Available N P S o)
    (hin : ∀ w, w < N ∨ w ∈ P → readsIn C S w + (if o = w then 1 else 0) ≤ 1)
    (hgate : ∀ j ∈ S, readsIn C S (N+j) + (if o = N+j then 1 else 0) = 1) :
    tree (N+P.length) (build N C S P o) := by
  let D := build N C S P o
  let n := N+P.length
  have hBack : ReadsBack n D := build_readsBack N C S P o hs hp hc hb
  have hIn (i : ℕ) (hi : i < n) : actualUse D i ≤ 1 := by
    by_cases hr : i < N
    · have hUse := build_use N C S P o hp hc ho (w := i) (Or.inl hr)
      rw [loc_raw N P S hr] at hUse
      change actualUse D i = _ at hUse
      rw [hUse]
      exact hin i (Or.inl hr)
    · have idxlt : i-N < P.length := by dsimp [n] at hi; omega
      let w := P[i-N]'idxlt
      have hw : w ∈ P := List.getElem_mem _
      have hwIdx : P.idxOf w = i-N := hnd.idxOf_getElem (i-N) idxlt
      have locEq : loc N P S w = i := by
        rw [loc_port N P S hp hw, hwIdx]
        omega
      have hUse := build_use N C S P o hp hc ho (w := w) (Or.inr (Or.inl hw))
      rw [locEq] at hUse
      change actualUse D i = _ at hUse
      rw [hUse]
      exact hin w (Or.inr hw)
  have hGate (j : ℕ) (hj : j < D.size) : actualUse D (n+j) = 1 := by
    have hj' : j < S.card := by simpa [D] using hj
    obtain ⟨g, hg, he⟩ := rank_surj S hj'
    have hUse := build_use N C S P o hp hc ho (w := N+g) (Or.inr (Or.inr ⟨g,hg,rfl⟩))
    rw [loc_gate N P S hp hg, he] at hUse
    change actualUse D (n+j) = _ at hUse
    exact hUse.trans (hgate g hg)
  have hOutLt : D.output < n+D.size := by
    change loc N P S o < n + (build N C S P o).size
    rw [build_size]
    exact loc_valid N P S hp ho
  have hOut : D.output+1 = n+D.size ∨ (D.size = 0 ∧ D.output < n) := by
    by_cases he : D.size = 0
    · exact Or.inr ⟨he, by omega⟩
    left
    let last := D.size-1
    have hLast : last < D.size := by dsimp [last]; omega
    have hEq : actualUse D (n+last) = 1 := hGate last hLast
    have hNor : readsIn D (Finset.range D.size) (n+last) = 0 := by
      unfold readsIn
      apply Finset.sum_eq_zero
      intro g hg
      have hGLt : g < D.size := Finset.mem_range.mp hg
      have hNot : n+last ∉ (gateAt D g).inputs := by
        intro hMem
        have hlt := hBack g hGLt (n+last) hMem
        dsimp [last] at hlt
        omega
      exact List.count_eq_zero.mpr hNot
    unfold actualUse at hEq
    rw [hNor, zero_add] at hEq
    by_cases hLastOut : D.output = n+last
    · dsimp [last] at hLastOut
      omega
    · simp [hLastOut] at hEq
  exact ⟨build_ops N C S P o hops, hBack, hOut, hIn, hGate⟩

private def traceStep (N : ℕ) (force : ℕ → Option Bool) (ys : List Bool) (g : Gate) :
    List Bool :=
  ys ++ [(force (ys.length - N)).getD
    (g.op.eval (g.inputs.map fun i => ys.getD i false))]
private def forcedTrace (N : ℕ) (C : Circuit) (xs : List Bool) (force : ℕ → Option Bool) :
    List Bool :=
  C.gates.foldl (traceStep N force) xs
private theorem forcedTrace_unforced (N : ℕ) (C : Circuit) (xs : List Bool) :
    forcedTrace N C xs (fun _ => none) = C.wires xs := rfl
private theorem forcedTrace_override (N : ℕ) (C : Circuit) (xs : List Bool)
    (f t : ℕ) (a b : Bool) :
    forcedTrace N C xs (fun j => if j = f then some a else if j = t then some b else none) =
      C.gates.foldl (fun (ys : List Bool) g =>
        let j := ys.length-N
        ys ++ [if j = f then a else if j = t then b
               else g.op.eval (g.inputs.map (fun i => ys.getD i false))]) xs := by
  unfold forcedTrace
  congr 1
  funext ys g
  simp only [traceStep]
  split_ifs <;> rfl
private theorem traceFold_length (N : ℕ) (force : ℕ → Option Bool) (gs : List Gate)
    (xs : List Bool) : (gs.foldl (traceStep N force) xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [traceStep, List.length_append, List.length_cons, List.length_nil]
    omega
private theorem traceFold_input (N : ℕ) (force : ℕ → Option Bool) (gs : List Gate)
    (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (gs.foldl (traceStep N force) xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [traceStep]; omega)]
    exact List.getD_append _ _ _ _ hi
private theorem forcedTrace_input (N : ℕ) (C : Circuit) (xs : List Bool)
    (force : ℕ → Option Bool) (i : ℕ) (hi : i < xs.length) :
    (forcedTrace N C xs force).getD i false = xs.getD i false :=
  traceFold_input N force C.gates xs i hi
private theorem forcedTrace_gate (N : ℕ) (C : Circuit) (xs : List Bool) (force : ℕ → Option Bool)
    (hxs : xs.length = N) (hb : ReadsBack N C) (j : ℕ) (hj : j < C.size) :
    (forcedTrace N C xs force).getD (N+j) false =
      (force j).getD ((gateAt C j).op.eval
        ((gateAt C j).inputs.map (fun i => (forcedTrace N C xs force).getD i false))) := by
  have hj' : j < C.gates.length := hj
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j+1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj']
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
  let pre := C.gates.take j
  let post := C.gates.drop (j+1)
  let g := gateAt C j
  let ys := pre.foldl (traceStep N force) xs
  have hlen : ys.length = N+j := by
    simp [ys, pre, traceFold_length, hxs, Nat.min_eq_left (Nat.le_of_lt hj')]
  let appendBit := (force j).getD (g.op.eval (g.inputs.map (fun i => ys.getD i false)))
  have hstep : traceStep N force ys g = ys ++ [appendBit] := by
    simp [traceStep, appendBit, hlen]
  have hfull : forcedTrace N C xs force = post.foldl (traceStep N force) (ys ++ [appendBit]) :=
    calc
      _ = (pre ++ g :: post).foldl (traceStep N force) xs := by
        unfold forcedTrace
        congr 1
      _ = post.foldl (traceStep N force) (traceStep N force ys g) := by
        simp only [List.foldl_append, List.foldl_cons, ys]
      _ = _ := by rw [hstep]
  have hfullIn (i : ℕ) (hi : i < N+j) :
      (forcedTrace N C xs force).getD i false = ys.getD i false := by
    rw [hfull, traceFold_input _ _ _ _ _ (by simp [hlen]; omega)]
    exact List.getD_append _ _ _ _ (by simpa only [hlen])
  have hread : g.inputs.map (fun i => (forcedTrace N C xs force).getD i false) =
      g.inputs.map (fun i => ys.getD i false) :=
    List.map_congr_left (fun i hi => hfullIn i (hb j hj' i hi))
  have hvalue : (forcedTrace N C xs force).getD (N+j) false = appendBit := by
    rw [hfull, traceFold_input _ _ _ _ _ (by simp [hlen])]
    rw [← hlen, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  rw [hvalue, hread]
private theorem forcedTrace_port (N : ℕ) (C : Circuit) (xs : List Bool) (force : ℕ → Option Bool)
    (hxs : xs.length = N) (hb : ReadsBack N C) (j : ℕ) (hj : j < C.size)
    (b : Bool) (hf : force j = some b) :
    (forcedTrace N C xs force).getD (N+j) false = b := by
  rw [forcedTrace_gate N C xs force hxs hb j hj, hf]
  rfl
private theorem append_raw (N : ℕ) (xs extra : List Bool) (hxs : xs.length = N) :
    ∀ i < N, (xs ++ extra).getD i false = xs.getD i false := by
  intro i hi
  exact List.getD_append _ _ _ _ (hxs.symm ▸ hi)
private theorem append_port (N : ℕ) (xs extra : List Bool) (hxs : xs.length = N) (i : ℕ) :
    (xs ++ extra).getD (N+i) false = extra.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega), hxs]
  simp

private theorem copy_trace (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (xs ys : List Bool) (force : ℕ → Option Bool)
    (hxs : xs.length = N) (hys : ys.length = N+P.length)
    (hs : S ⊆ Finset.range C.size) (hp : Ports N P S) (hc : Closed N C S P)
    (hb : ReadsBack N C) (hn : ∀ j ∈ S, force j = none)
    (hraw : ∀ i < N, ys.getD i false = xs.getD i false)
    (hport : ∀ w ∈ P, ys.getD (N + P.idxOf w) false = (forcedTrace N C xs force).getD w false) :
      ∀ w, (w < N ∨ w ∈ P ∨ ∃ j ∈ S, w = N+j) →
        ((build N C S P o).wires ys).getD (loc N P S w) false =
          (forcedTrace N C xs force).getD w false := by
  change ∀ w, _ → (forcedTrace (N+P.length) (build N C S P o) ys (fun _ => none)).getD
    (loc N P S w) false = _
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro (hwr | hwp | ⟨j, hj, rfl⟩)
    · rw [loc_raw N P S hwr, forcedTrace_input _ _ _ _ _ (by omega),
        forcedTrace_input _ _ _ _ _ (by omega)]
      exact hraw w hwr
    · rw [loc_port N P S hp hwp, forcedTrace_input _ _ _ _ _]
      · exact hport w hwp
      · rw [hys]
        exact Nat.add_lt_add_left (List.idxOf_lt_length_iff.mpr hwp) N
    · have hbr := build_readsBack N C S P o hs hp hc hb
      have hjC := Finset.mem_range.mp (hs hj)
      have hjD : rank S j < (build N C S P o).size := by
        rw [build_size]
        exact rank_bound S hj
      rw [loc_gate N P S hp hj, forcedTrace_gate _ _ _ _ hys hbr _ hjD,
        forcedTrace_gate N C xs force hxs hb j hjC, hn j hj, gateAt_build N C S P o hj]
      simp only [Option.getD_none, List.map_map]
      congr 1
      exact List.map_congr_left (fun i hi => ih i (hb j hjC i hi) (hc j hj i hi))
private theorem copy_eval (N : ℕ) (C : Circuit) (S : Finset ℕ) (P : List ℕ) (o : ℕ)
    (xs ys : List Bool) (force : ℕ → Option Bool)
    (hxs : xs.length = N) (hys : ys.length = N+P.length)
    (hs : S ⊆ Finset.range C.size) (hp : Ports N P S) (hc : Closed N C S P)
    (hb : ReadsBack N C) (hn : ∀ j ∈ S, force j = none)
    (hraw : ∀ i < N, ys.getD i false = xs.getD i false)
    (hport : ∀ w ∈ P, ys.getD (N + P.idxOf w) false = (forcedTrace N C xs force).getD w false)
    (ho : o < N ∨ o ∈ P ∨ ∃ j ∈ S, o = N+j) :
    (build N C S P o).eval ys = (forcedTrace N C xs force).getD o false :=
  copy_trace N C S P o xs ys force hxs hys hs hp hc hb hn hraw hport o ho

private theorem decomposition_eval (N : ℕ) (C : Circuit) (f t : Fin C.size)
    (F H D : Finset ℕ) (h : ℕ) (hft : f < t) (hb : ReadsBack N C)
    (hF : F ⊆ Finset.range C.size) (hH : H ⊆ Finset.range C.size)
    (hD : D ⊆ Finset.range C.size)
    (hcF : Closed N C F []) (hcH : Closed N C H [N+f.val])
    (hcD : Closed N C D [N+f.val, N+t.val])
    (hpH : Ports N [N+f.val] H) (hpD : Ports N [N+f.val, N+t.val] D)
    (hfF : f.val ∈ F) (htH : t.val ∉ H)
    (hh : h < N ∨ h ∈ [N+f.val] ∨ ∃ j ∈ H, h = N+j)
    (ho : C.output < N ∨ C.output ∈ [N+f.val, N+t.val] ∨ ∃ j ∈ D, C.output = N+j) :
    ∀ (x : Fin N → Bool) (a b : Bool),
      let xs := List.ofFn x
      let v := C.gates.foldl (fun (ys : List Bool) g =>
        let j := ys.length-N
        ys ++ [if j = f.val then a else if j = t.val then b
               else g.op.eval (g.inputs.map (fun i => ys.getD i false))]) xs
      (build N C F [] (N+f.val)).eval xs = (C.wires xs).getD (N+f.val) false ∧
      (build N C H [N+f.val] h).eval (xs++[a]) = v.getD h false ∧
      (build N C D [N+f.val, N+t.val] C.output).eval (xs++[a,b]) = v.getD C.output false := by
  intro x a b
  dsimp only
  let xs := List.ofFn x
  have hxs : xs.length = N := List.length_ofFn
  rw [← forcedTrace_override N C xs f.val t.val a b, ← forcedTrace_unforced N C xs]
  let force : ℕ → Option Bool := fun j => if j = f.val then some a else if j = t.val then some b else none
  have hft' : f.val < t.val := hft
  have hne' : t.val ≠ f.val := Nat.ne_of_gt hft'
  have hfVal : (forcedTrace N C xs force).getD (N+f.val) false = a :=
    forcedTrace_port N C xs force hxs hb f.val f.isLt a (by simp [force])
  have htVal : (forcedTrace N C xs force).getD (N+t.val) false = b :=
    forcedTrace_port N C xs force hxs hb t.val t.isLt b (by simp [force, hne'])
  have hfH : f.val ∉ H := by
    simpa using (hpH (N+f.val) (by simp)).2
  have hfD : f.val ∉ D := by
    simpa using (hpD (N+f.val) (by simp)).2
  have htD : t.val ∉ D := by
    simpa using (hpD (N+t.val) (by simp)).2
  refine ⟨?_, ?_, ?_⟩
  · exact copy_eval N C F [] (N+f.val) xs xs (fun _ => none) hxs (by simpa)
      hF (by simp [Ports]) hcF hb (by simp) (by simp) (by simp) (Or.inr (Or.inr ⟨_, hfF, rfl⟩))
  · apply copy_eval N C H [N+f.val] h xs (xs++[a]) force hxs (by simp [hxs])
      hH hpH hcH hb (hraw := append_raw N xs [a] hxs) (ho := hh)
    · intro j hj
      have hf : j ≠ f.val := fun he => hfH (he ▸ hj)
      have ht : j ≠ t.val := fun he => htH (he ▸ hj)
      simp [force, hf, ht]
    · intro w hw
      rw [List.mem_singleton] at hw
      subst w
      rw [hfVal]
      simpa using append_port N xs [a] hxs 0
  · apply copy_eval N C D [N+f.val, N+t.val] C.output xs (xs++[a,b]) force hxs (by simp [hxs])
      hD hpD hcD hb (hraw := append_raw N xs [a,b] hxs) (ho := ho)
    · intro j hj
      have hf : j ≠ f.val := fun he => hfD (he ▸ hj)
      have ht : j ≠ t.val := fun he => htD (he ▸ hj)
      simp [force, hf, ht]
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rw [hfVal]
        simpa using append_port N xs [a,b] hxs 0
      · rw [htVal]
        simpa [List.idxOf_cons, hft'.ne] using append_port N xs [a,b] hxs 1

end PEqualNP.Outside.L_meta_29750

open PEqualNP.Outside.L_meta_29750 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership in
theorem PEqualNP.Outside.L_meta_29750 : (∀ (N : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (f t : Fin C.size),
  let atGate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := fun (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size)
  let use := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (w : Nat) => reads D w + (if D.output = w then 1 else 0)
  let tree := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ (D.output+1 = n+D.size ∨ (D.size = 0 ∧ D.output < n)) ∧
    (∀ i < n, use D i ≤ 1) ∧ (∀ j < D.size, use D (n+j) = 1)
  f < t → C.output+1 = N+C.size → PEqualNP.MetaComplexity.NestedCover.ReadsBack N C →
  (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  (∀ j : Fin C.size, (atGate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = t) →
  (∀ i < N, reads C i ≤ 1) →
  (∀ j : Fin C.size, reads C (N+j.val) = if j = f then 2 else if j.val+1 = C.size then 0 else 1) →
  PEqualNP.EdgeOwnership.InCone N C f.val t.val →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (insert t.val (((PEqualNP.EdgeOwnership.cones N C).getD t.val []).toFinset)) (N+f.val) = 1 →
  ∃ W H D : PEqualNP.CircuitLowerBounds.Circuit, tree N W ∧ tree (N+1) H ∧ tree (N+2) D ∧
    W.size+H.size+D.size+1 = C.size ∧
    (∀ i < N, use W i + use H i + use D i = reads C i) ∧
    use H N = 1 ∧ use D N = 1 ∧ use D (N+1) = 1 ∧
    ∀ (x : Fin N → Bool) (a b : Bool),
      let xs := List.ofFn x
      let v := C.gates.foldl (fun (ys : List Bool) g =>
        let j := ys.length-N
        ys ++ [if j = f.val then a else if j = t.val then b
               else g.op.eval (g.inputs.map (fun i => ys.getD i false))]) xs
      W.eval xs = (C.wires xs).getD (N+f.val) false ∧
      H.eval (xs++[a]) = v.getD ((atGate t.val).inputs.headD (N+C.size)) false ∧
      D.eval (xs++[a,b]) = v.getD C.output false) := by
  intro N C f t
  dsimp only
  intro hft htop hback hgate hnot hraw hread hcone hfread
  have cft : f.val < t.val := hft
  have hlen : 0 < C.size := by have := t.isLt; omega
  have gate_mem (j : ℕ) (hj : j < C.size) : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop : (gateAt C t.val).op = GateOp.not := (hnot t).2 rfl
  have unary : (gateAt C t.val).inputs.length = 1 := by
    rcases hgate _ (gate_mem t.val t.isLt) with ⟨h | h, _⟩ | h
    · exact (by rw [hop] at h; contradiction)
    · exact (by rw [hop] at h; contradiction)
    · exact h.2
  obtain ⟨k, hkt, hhead, -, hk⟩ := not_operand hcone unary
  let F := insert f.val ((cones N C).getD f.val []).toFinset
  let T := insert t.val ((cones N C).getD t.val []).toFinset
  let H := T \ insert t.val F
  let D := entire C \ T
  have fdata : ConeData N C F f.val := coneData_of_root hback f.isLt
  have tdata : ConeData N C T t.val := coneData_of_root hback t.isLt
  have hFT : F ⊆ T := cone_subset_of_inCone hcone
  have hreads (j : ℕ) (hj : j ∈ entire C) : readsIn C (entire C) (N+j) =
      if j = f.val then 2 else if j+1 = C.size then 0 else 1 := by
    let r : Fin C.size := ⟨j, Finset.mem_range.mp hj⟩
    simpa only [entire, Fin.ext_iff, r] using hread r
  have unique : UniqueReaders N C f.val := unique_readers_of_bound hback (by
    intro j hj hne
    have h := hreads j (Finset.mem_range.mpr hj)
    rw [ite_eq_right hne] at h
    split at h <;> omega)
  have sc : SplitCounts N C f.val t.val (N+k) F H D :=
    splitCounts N C f.val t.val (N+k) F T fdata tdata hFT cft hback htop
      hreads hfread hhead (by omega)
  have fs : F ⊆ Finset.range C.size := fdata.subset
  have hs : H ⊆ Finset.range C.size := fun j hj =>
    tdata.subset (Finset.mem_sdiff.mp hj).1
  have ds : D ⊆ Finset.range C.size := fun j hj => (Finset.mem_sdiff.mp hj).1
  have htH : t.val ∉ H := fun h =>
    inCone_irrefl N C t.val (mem_inner.mp h).1
  have fp : Ports N [] F := by simp [Ports]
  have hp : Ports N [N+f.val] H := ports_inner
  have dp : Ports N [N+f.val,N+t.val] D := ports_outer hcone
  have fc : Closed N C F [] := closed_fork fdata
  have hc : Closed N C H [N+f.val] := closed_inner hback unique
  have dc : Closed N C D [N+f.val,N+t.val] := closed_outer hback unique hcone
  have fo : Available N [] F (N+f.val) := Or.inr (Or.inr ⟨_,fdata.root,rfl⟩)
  have ho : Available N [N+f.val] H (N+k) := available_inner_root hk
  have do' : Available N [N+f.val,N+t.val] D C.output :=
    Or.inr (Or.inr ⟨_,sc.last_mem,by omega⟩)
  have posGate (j : ℕ) (hj : j < C.size) (hne : j ≠ t.val) :
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
        (gateAt C j).inputs.length = 2 := by
    rcases hgate _ (gate_mem j hj) with h | ⟨hn,_⟩
    · exact h
    · exact False.elim (hne (congrArg Fin.val ((hnot ⟨j,hj⟩).1 hn)))
  have fpos (j : ℕ) (hj : j ∈ F) := posGate j (Finset.mem_range.mp (fs hj)) (by
    have := fdata.order j hj
    omega)
  have hpos (j : ℕ) (hj : j ∈ H) := posGate j (Finset.mem_range.mp (hs hj))
    (fun h => htH (h ▸ hj))
  have dpos (j : ℕ) (hj : j ∈ D) := posGate j (mem_outer.mp hj).1 (mem_outer.mp hj).2.1
  have fr (w : ℕ) (hw : w < N ∨ w ∈ ([] : List ℕ)) :
      useOld C F (N+f.val) w ≤ 1 := by
    have hw' : w < N := hw.resolve_right (List.not_mem_nil)
    have s := sc.raw w hw'
    have r := hraw w hw'
    change readsIn C (entire C) w ≤ 1 at r
    omega
  have hr (w : ℕ) (hw : w < N ∨ w ∈ [N+f.val]) :
      useOld C H (N+k) w ≤ 1 := by
    rcases hw with hw | hw
    · have s := sc.raw w hw
      have r := hraw w hw
      change readsIn C (entire C) w ≤ 1 at r
      omega
    · obtain rfl := List.mem_singleton.mp hw
      exact sc.forkH.le
  have dr (w : ℕ) (hw : w < N ∨ w ∈ [N+f.val,N+t.val]) :
      useOld C D C.output w ≤ 1 := by
    rcases hw with hw | hw
    · have s := sc.raw w hw
      have r := hraw w hw
      change readsIn C (entire C) w ≤ 1 at r
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact sc.forkD.le
      · exact sc.notD.le
  let W := build N C F [] (N+f.val)
  let B := build N C H [N+f.val] (N+k)
  let R := build N C D [N+f.val,N+t.val] C.output
  have dnd : ([N+f.val,N+t.val] : List ℕ).Nodup := by
    simp [show f.val ≠ t.val by omega]
  refine ⟨W,B,R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact build_tree N C F [] (N+f.val) fs fp (by simp) fc hback fpos fo fr sc.intF
  · exact build_tree N C H [N+f.val] (N+k) hs hp (by simp) hc hback hpos ho hr sc.intH
  · exact build_tree N C D [N+f.val,N+t.val] C.output ds dp dnd dc hback dpos do' dr sc.intD
  · simpa [W,B,R,build_size] using sc.size
  · intro i hi
    have fw := build_use N C F [] (N+f.val) fp fc fo (Or.inl hi)
    have bw := build_use N C H [N+f.val] (N+k) hp hc ho (Or.inl hi)
    have rw' := build_use N C D [N+f.val,N+t.val] C.output dp dc do' (Or.inl hi)
    simp only [loc_raw _ _ _ hi] at fw bw rw'
    change actualUse W i + actualUse B i + actualUse R i = readsIn C (entire C) i
    rw [fw, bw, rw']
    exact sc.raw i hi
  · have hin : N+f.val ∈ ([N+f.val] : List ℕ) := by simp
    have he := build_use N C H [N+f.val] (N+k) hp hc ho (Or.inr (Or.inl hin))
    change actualUse B N = 1
    simpa [loc_port _ _ _ hp hin, useOld] using he.trans sc.forkH
  · have hin : N+f.val ∈ ([N+f.val,N+t.val] : List ℕ) := by simp
    have he := build_use N C D [N+f.val,N+t.val] C.output dp dc do' (Or.inr (Or.inl hin))
    change actualUse R N = 1
    simpa [loc_port _ _ _ dp hin, useOld] using he.trans sc.forkD
  · have hin : N+t.val ∈ ([N+f.val,N+t.val] : List ℕ) := by simp
    have he := build_use N C D [N+f.val,N+t.val] C.output dp dc do' (Or.inr (Or.inl hin))
    change actualUse R (N+1) = 1
    simpa [loc_port _ _ _ dp hin, List.idxOf_cons, show f.val ≠ t.val by omega, useOld]
      using he.trans sc.notD
  · simpa only [hhead, List.headD_cons] using
      decomposition_eval N C f t F H D (N+k) hft hback fs hs ds fc hc dc hp dp
        fdata.root htH ho do'
