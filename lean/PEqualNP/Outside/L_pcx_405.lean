import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_405_aux


def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Consistent {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ j : Fin p.length, q (p.take j.val) x = p.get j

def Cert {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) : Prop :=
  Shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V, Consistent q p x → ok x (out p)

def Fits {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
    (depth leaves : O → ℕ) (H K : ℕ) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
    Cert qs ok N J q out ∧ (∀ p ∈ N \ J, p.length + depth (out p) ≤ H) ∧
      (N \ J).sum (fun p => leaves (out p)) ≤ K

def Qs (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Set (V → Bool) :=
  {f | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}

theorem fits_mono {V O : Type} {qs : Set (V → Bool)} {ok ok' : V → O → Prop}
    {depth leaves : O → ℕ} {H H' K K' : ℕ} (hok : ∀ x o, ok x o → ok' x o) (hH : H ≤ H')
    (hK : K ≤ K') (h : Fits qs ok depth leaves H K) : Fits qs ok' depth leaves H' K' := by
  obtain ⟨N, J, q, out, ⟨hs, hq, hl⟩, hd, hk⟩ := h
  exact ⟨N, J, q, out, ⟨hs, hq, fun p hp x hx => hok _ _ (hl p hp x hx)⟩,
    fun p hp => (hd p hp).trans hH, hk.trans hK⟩

theorem fits_leaf {V O : Type} {qs : Set (V → Bool)} {ok : V → O → Prop}
    {depth leaves : O → ℕ} {H K : ℕ} (o : O) (hok : ∀ x, ok x o) (hH : depth o ≤ H)
    (hK : leaves o ≤ K) : Fits qs ok depth leaves H K := by
  refine ⟨{[]}, ∅, fun _ _ => true, fun _ => o, ⟨⟨by simp, by simp, ?_, by simp⟩, by simp, ?_⟩,
    ?_, ?_⟩
  · intro p b h; simp at h
  · intro p _ x _; exact hok x
  · intro p hp; simp at hp; subst hp; simpa using hH
  · simpa using hK

theorem consistent_cons {V : Type} (q : List Bool → V → Bool) (b : Bool) (p : List Bool) (x : V) :
    Consistent q (b :: p) x ↔ q [] x = b ∧ Consistent (fun p' => q (b :: p')) p x := by
  unfold Consistent
  constructor
  · intro h
    refine ⟨h ⟨0, by simp⟩, fun j => ?_⟩
    have := h ⟨j.val + 1, by simp⟩
    simpa using this
  · rintro ⟨h0, h⟩ j
    rcases j with ⟨j, hj⟩
    cases j with
    | zero => simpa using h0
    | succ j =>
      have := h ⟨j, by simpa using hj⟩
      simpa using this

theorem split_sum {β : Type} [AddCommMonoid β] (S : Finset (List Bool)) (hS : [] ∉ S)
    (g : List Bool → β) :
    S.sum g = (S.preimage (List.cons false) List.cons_injective.injOn).sum (fun p => g (false :: p)) +
      (S.preimage (List.cons true) List.cons_injective.injOn).sum (fun p => g (true :: p)) := by
  have hS' : S = (S.preimage (List.cons false) List.cons_injective.injOn).image (List.cons false) ∪
      (S.preimage (List.cons true) List.cons_injective.injOn).image (List.cons true) := by
    ext p
    rcases p with _ | ⟨b, p⟩
    · simp [hS]
    · cases b <;> simp
  conv_lhs => rw [hS']
  rw [Finset.sum_union, Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_image] at ha hb
  obtain ⟨_, _, rfl⟩ := ha
  obtain ⟨_, _, h⟩ := hb
  simp at h

theorem preimage_sdiff (N J : Finset (List Bool)) (b : Bool) :
    N.preimage (List.cons b) List.cons_injective.injOn \ J.preimage (List.cons b) List.cons_injective.injOn
      = (N \ J).preimage (List.cons b) List.cons_injective.injOn := by
  ext p; simp

theorem sub_cert {V O : Type} {qs : Set (V → Bool)} {ok : V → O → Prop}
    {N J : Finset (List Bool)} {q : List Bool → V → Bool} {out : List Bool → O}
    (hc : Cert qs ok N J q out) (hroot : [] ∈ J) (b : Bool) :
    Cert qs (fun x o => q [] x = b → ok x o) (N.preimage (List.cons b) List.cons_injective.injOn)
      (J.preimage (List.cons b) List.cons_injective.injOn) (fun p => q (b :: p))
      (fun p => out (b :: p)) := by
  obtain ⟨⟨_, hJN, hpar, hch⟩, hq, hl⟩ := hc
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Finset.mem_preimage]
    cases b
    · exact (hch _ hroot).1
    · exact (hch _ hroot).2
  · intro p hp; simp only [Finset.mem_preimage] at hp ⊢; exact hJN hp
  · intro p c hp; simp only [Finset.mem_preimage] at hp ⊢; exact hpar (b :: p) c hp
  · intro p hp; simp only [Finset.mem_preimage] at hp ⊢; exact hch _ hp
  · intro p hp; simp only [Finset.mem_preimage] at hp; exact hq _ hp
  · intro p hp x hx hb
    simp only [Finset.mem_sdiff, Finset.mem_preimage] at hp
    exact hl (b :: p) (Finset.mem_sdiff.2 hp) x ((consistent_cons q b p x).2 ⟨hb, hx⟩)

theorem fits_cases {V O : Type} {qs : Set (V → Bool)} {ok : V → O → Prop}
    {depth leaves : O → ℕ} {H K : ℕ} (h : Fits qs ok depth leaves H K) :
    (∃ o, (∀ x, ok x o) ∧ depth o ≤ H ∧ leaves o ≤ K) ∨
    (∃ H', H = H' + 1 ∧ ∃ f ∈ qs, ∃ K0 K1, K0 + K1 ≤ K ∧
      Fits qs (fun x o => f x = false → ok x o) depth leaves H' K0 ∧
      Fits qs (fun x o => f x = true → ok x o) depth leaves H' K1) := by
  obtain ⟨N, J, q, out, hc, hd, hk⟩ := h
  have hc' := hc
  obtain ⟨⟨hN0, hJN, hpar, hch⟩, hq, hl⟩ := hc'
  by_cases hroot : [] ∈ J
  · right
    obtain ⟨p, hpN, hpmax⟩ := N.exists_max_image List.length ⟨[], hN0⟩
    have hpJ : p ∉ J := fun hpJ => by
      have := hpmax _ (hch p hpJ).1; simp at this
    have hp0 : p ≠ [] := fun h => hpJ (h ▸ hroot)
    have hH1 : 1 ≤ H := by
      have h1 := hd p (Finset.mem_sdiff.2 ⟨hpN, hpJ⟩)
      have h2 : 0 < p.length := List.length_pos_iff.2 hp0
      omega
    have hsub : ∀ b : Bool, Fits qs (fun x o => q [] x = b → ok x o) depth leaves (H - 1)
        (((N \ J).preimage (List.cons b) List.cons_injective.injOn).sum
          (fun p => leaves (out (b :: p)))) := by
      intro b
      refine ⟨_, _, _, _, sub_cert hc hroot b, ?_, ?_⟩
      · intro p hp
        rw [preimage_sdiff] at hp
        have := hd _ (Finset.mem_preimage.1 hp)
        simp only [List.length_cons] at this
        omega
      · rw [preimage_sdiff]
    refine ⟨H - 1, by omega, q [], hq _ hroot, _, _, ?_, hsub false, hsub true⟩
    rw [split_sum (N \ J) (by simp [hroot]) (fun p => leaves (out p))] at hk
    exact hk
  · left
    have hmem : [] ∈ N \ J := Finset.mem_sdiff.2 ⟨hN0, hroot⟩
    refine ⟨out [], fun x => hl [] hmem x (fun j => j.elim0), ?_, ?_⟩
    · simpa using hd [] hmem
    · exact (Finset.single_le_sum (f := fun p => leaves (out p)) (fun _ _ => Nat.zero_le _) hmem).trans hk

theorem fits_node {V O : Type} {qs : Set (V → Bool)} {ok : V → O → Prop}
    {depth leaves : O → ℕ} {H K0 K1 : ℕ} (f : V → Bool) (hf : f ∈ qs)
    (h0 : Fits qs (fun x o => f x = false → ok x o) depth leaves H K0)
    (h1 : Fits qs (fun x o => f x = true → ok x o) depth leaves H K1) :
    Fits qs ok depth leaves (H + 1) (K0 + K1) := by
  obtain ⟨N0, J0, q0, out0, ⟨⟨hN0, hJN0, hpar0, hch0⟩, hq0, hl0⟩, hd0, hk0⟩ := h0
  obtain ⟨N1, J1, q1, out1, ⟨⟨hN1, hJN1, hpar1, hch1⟩, hq1, hl1⟩, hd1, hk1⟩ := h1
  let N : Finset (List Bool) := insert [] (N0.image (List.cons false) ∪ N1.image (List.cons true))
  let J : Finset (List Bool) := insert [] (J0.image (List.cons false) ∪ J1.image (List.cons true))
  let q : List Bool → V → Bool := fun p => match p with
    | [] => f
    | false :: p' => q0 p'
    | true :: p' => q1 p'
  let out : List Bool → O := fun p => match p with
    | [] => out0 []
    | false :: p' => out0 p'
    | true :: p' => out1 p'
  have mN : ∀ b p, b :: p ∈ N ↔ (if b then p ∈ N1 else p ∈ N0) := by
    intro b p; cases b <;> simp [N]
  have mJ : ∀ b p, b :: p ∈ J ↔ (if b then p ∈ J1 else p ∈ J0) := by
    intro b p; cases b <;> simp [J]
  have hJ0 : [] ∈ J := Finset.mem_insert_self _ _
  have hpre : ∀ b, (N \ J).preimage (List.cons b) List.cons_injective.injOn =
      if b then N1 \ J1 else N0 \ J0 := by
    intro b; ext p; cases b <;> simp [N, J]
  refine ⟨N, J, q, out, ⟨⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨b, p⟩
    · exact Finset.mem_insert_self _ _
    · rw [mJ] at hp; rw [mN]; cases b
      · exact hJN0 hp
      · exact hJN1 hp
  · intro p c hp
    rcases p with _ | ⟨b, p⟩
    · exact hJ0
    · have hp' : b :: (p ++ [c]) ∈ N := hp
      rw [mN] at hp'; rw [mJ]; cases b
      · exact hpar0 p c hp'
      · exact hpar1 p c hp'
  · intro p hp
    rcases p with _ | ⟨b, p⟩
    · exact ⟨(mN false []).2 hN0, (mN true []).2 hN1⟩
    · rw [mJ] at hp
      have e : ∀ c, (b :: p) ++ [c] = b :: (p ++ [c]) := fun c => rfl
      rw [e, e, mN, mN]; cases b
      · exact hch0 p hp
      · exact hch1 p hp
  · intro p hp
    rcases p with _ | ⟨b, p⟩
    · exact hf
    · rw [mJ] at hp; cases b
      · exact hq0 p hp
      · exact hq1 p hp
  · intro p hp x hx
    rcases p with _ | ⟨b, p⟩
    · exact absurd hJ0 (Finset.mem_sdiff.1 hp).2
    · have hp' : p ∈ (N \ J).preimage (List.cons b) List.cons_injective.injOn :=
        Finset.mem_preimage.2 hp
      rw [hpre] at hp'
      rw [consistent_cons] at hx
      cases b
      · exact hl0 p hp' x hx.2 hx.1
      · exact hl1 p hp' x hx.2 hx.1
  · intro p hp
    rcases p with _ | ⟨b, p⟩
    · exact absurd hJ0 (Finset.mem_sdiff.1 hp).2
    · have hp' : p ∈ (N \ J).preimage (List.cons b) List.cons_injective.injOn :=
        Finset.mem_preimage.2 hp
      rw [hpre] at hp'
      simp only [List.length_cons]
      cases b
      · have := hd0 p hp'; simp only [out]; omega
      · have := hd1 p hp'; simp only [out]; omega
  · rw [split_sum (N \ J) (by simp [hJ0]) (fun p => leaves (out p)), hpre, hpre]
    exact Nat.add_le_add hk0 hk1


theorem zdec : ∀ (v b : ZMod 2) (c : Bool), decide (v = b) = c ↔ v = (if c = true then b else b + 1) := by
  decide

theorem plane3 : ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 : ZMod 2, ¬ (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) →
    ¬ (a0 = c0 ∧ a1 = c1 ∧ a2 = c2) → ¬ (b0 = c0 ∧ b1 = c1 ∧ b2 = c2) →
    a2 + a0 * a1 = b2 + b0 * b1 → a2 + a0 * a1 = c2 + c0 * c1 →
    a2 + a0 * a1 ≠ (a2 - b2 + c2) + (a0 - b0 + c0) * (a1 - b1 + c1) := by
  set_option synthInstance.maxSize 2000 in
  set_option synthInstance.maxHeartbeats 400000 in
  decide

def tgt {r : ℕ} (z : Fin r → Fin 3 → ZMod 2) : Fin r → ZMod 2 := fun i => z i 2 + z i 0 * z i 1

def Ts {r : ℕ} (s : Finset (Fin r)) (z : Fin r → Fin 3 → ZMod 2) : Fin r → ZMod 2 :=
  fun i => if i ∈ s then tgt z i else 0

def Aff {V : Type} [AddCommGroup V] (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x - y + z ∈ S

def tt (w : Fin 3 → ZMod 2) : ZMod 2 := w 2 + w 0 * w 1

theorem ne3 {x y : Fin 3 → ZMod 2} (h : x ≠ y) : ¬ (x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2) := by
  rintro ⟨h0, h1, h2⟩
  apply h; funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem small_fiber (P : Finset (Fin 3 → ZMod 2)) (hP : Aff P) (c : ZMod 2)
    (hc : ∀ w ∈ P, tt w = c) : P.card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 h
  have e1 := hc x hx
  have e2 := hc y hy
  have e3 := hc z hz
  have e4 := hc _ (hP x hx y hy z hz)
  simp only [tt, Pi.add_apply, Pi.sub_apply] at e1 e2 e3 e4
  exact plane3 _ _ _ _ _ _ _ _ _ (ne3 hxy) (ne3 hxz) (ne3 hyz) (e1.trans e2.symm)
    (e1.trans e3.symm) (e1.trans e4.symm)

theorem ts_shift {r : ℕ} {s : Finset (Fin r)} {a : Fin r} (ha : a ∉ s) (w : Fin 3 → ZMod 2)
    (z : Fin r → Fin 3 → ZMod 2) : Ts s (z - Pi.single a w) = Ts s z := by
  funext i
  unfold Ts
  split_ifs with hi
  · have hne : i ≠ a := fun h => ha (h ▸ hi)
    simp [tgt, Pi.single_apply, hne]
  · rfl

theorem ts_proj {r : ℕ} (s : Finset (Fin r)) (a : Fin r) (z : Fin r → Fin 3 → ZMod 2) :
    Ts s z = (fun y : Fin r → ZMod 2 => fun i => if i ∈ s then y i else 0) (Ts (insert a s) z) := by
  funext i
  simp only [Ts]
  split_ifs with h1 h2 <;> simp_all

theorem card8 : Fintype.card (Fin 3 → ZMod 2) = 8 := by
  simp [Fintype.card_fun, ZMod.card]

theorem key {r : ℕ} (s : Finset (Fin r)) : ∀ S : Finset (Fin r → Fin 3 → ZMod 2), Aff S →
    (∀ z ∈ S, ∀ i ∉ s, z i = 0) → S.card ≤ 2 ^ s.card * 4 ^ Nat.log 2 (S.image (Ts s)).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro S _ hz
    have hsub : S ⊆ {0} := fun z hz' => by
      rw [Finset.mem_singleton]; funext i; exact hz z hz' i (Finset.notMem_empty i)
    calc S.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
      _ ≤ _ := by simp [Nat.one_le_pow]
  | insert a s ha ih =>
    intro S hS hz
    let F : (Fin 3 → ZMod 2) → Finset (Fin r → Fin 3 → ZMod 2) := fun w => S.filter (fun z => z a = w)
    have memF : ∀ w z, z ∈ F w ↔ z ∈ S ∧ z a = w := fun w z => Finset.mem_filter
    have hFb : ∀ w, (F w).card ≤ 2 ^ s.card * 4 ^ Nat.log 2 ((F w).image (Ts s)).card := by
      intro w
      have h := ih ((F w).image (fun z => z - Pi.single a w)) ?_ ?_
      · rw [Finset.card_image_of_injective _ (sub_left_injective), Finset.image_image] at h
        have e : (Ts s ∘ fun z => z - Pi.single a w) = Ts s := funext (fun z => ts_shift ha w z)
        rwa [e] at h
      · intro x hx y hy z hz'
        simp only [Finset.mem_image] at hx hy hz' ⊢
        obtain ⟨x, hx, rfl⟩ := hx
        obtain ⟨y, hy, rfl⟩ := hy
        obtain ⟨z, hz', rfl⟩ := hz'
        refine ⟨x - y + z, ?_, by abel⟩
        rw [memF] at hx hy hz' ⊢
        refine ⟨hS _ hx.1 _ hy.1 _ hz'.1, ?_⟩
        simp [hx.2, hy.2, hz'.2]
      · intro z hz' i hi
        simp only [Finset.mem_image] at hz'
        obtain ⟨z, hz', rfl⟩ := hz'
        rw [memF] at hz'
        by_cases hia : i = a
        · subst hia; simp [hz'.2]
        · have := hz z hz'.1 i (by simp [hia, hi])
          simp [this, Pi.single_apply, hia]
    let U := S.image (Ts (insert a s))
    have hproj : ∀ w, ((F w).image (Ts s)).card ≤ ((F w).image (Ts (insert a s))).card := by
      intro w
      have e : (F w).image (Ts s) = ((F w).image (Ts (insert a s))).image
          (fun y : Fin r → ZMod 2 => fun i => if i ∈ s then y i else 0) := by
        rw [Finset.image_image]; congr 1; funext z; exact ts_proj s a z
      rw [e]; exact Finset.card_image_le
    have hsubU : ∀ w, (F w).image (Ts (insert a s)) ⊆ U :=
      fun w => Finset.image_subset_image (Finset.filter_subset _ _)
    have heq : ∀ w w', (F w).Nonempty → (F w').Nonempty → (F w).card ≤ (F w').card := by
      intro w w' ⟨z0, hz0⟩ ⟨z1, hz1⟩
      rw [memF] at hz0 hz1
      refine Finset.card_le_card_of_injOn (fun x => x - z0 + z1) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, memF] at hx ⊢
        refine ⟨hS _ hx.1 _ hz0.1 _ hz1.1, ?_⟩
        simp [hx.2, hz0.2, hz1.2]
      · intro x _ y _ h
        simpa using h
    have hsum : S.card = ∑ w, (F w).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun z => z a) (t := Finset.univ) (by simp)]
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    have tta : ∀ w, ∀ z ∈ F w, Ts (insert a s) z a = tt w := by
      intro w z hz'
      rw [memF] at hz'
      simp [Ts, tgt, tt, hz'.2]
    rcases S.eq_empty_or_nonempty with h0 | ⟨z0, hz0⟩
    · simp [h0]
    have hF0 : (F (z0 a)).Nonempty := ⟨z0, (memF _ _).2 ⟨hz0, rfl⟩⟩
    by_cases hboth : ∃ w1 w2, (F w1).Nonempty ∧ (F w2).Nonempty ∧ tt w1 ≠ tt w2
    · obtain ⟨w1, w2, hn1, hn2, ht⟩ := hboth
      set n1 := ((F w1).image (Ts s)).card with hn1d
      set n2 := ((F w2).image (Ts s)).card with hn2d
      have p1 : 0 < n1 := Finset.card_pos.2 (hn1.image _)
      have p2 : 0 < n2 := Finset.card_pos.2 (hn2.image _)
      set m := min (Nat.log 2 n1) (Nat.log 2 n2) with hm
      have hB : ∀ w, (F w).card ≤ 2 ^ s.card * 4 ^ m := by
        intro w
        rcases (F w).eq_empty_or_nonempty with he | hne
        · simp [he]
        rcases min_choice (Nat.log 2 n1) (Nat.log 2 n2) with h | h
        · rw [hm, h]; exact (heq _ _ hne hn1).trans (hFb w1)
        · rw [hm, h]; exact (heq _ _ hne hn2).trans (hFb w2)
      have hdisj : Disjoint ((F w1).image (Ts (insert a s))) ((F w2).image (Ts (insert a s))) := by
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        simp only [Finset.mem_image] at hy1 hy2
        obtain ⟨z1, hz1, rfl⟩ := hy1
        obtain ⟨z2, hz2, e⟩ := hy2
        apply ht
        rw [← tta w1 z1 hz1, ← tta w2 z2 hz2, e]
      have hU : n1 + n2 ≤ U.card := by
        calc n1 + n2 ≤ ((F w1).image (Ts (insert a s))).card +
              ((F w2).image (Ts (insert a s))).card := Nat.add_le_add (hproj w1) (hproj w2)
          _ = (((F w1).image (Ts (insert a s))) ∪ ((F w2).image (Ts (insert a s)))).card :=
              (Finset.card_union_of_disjoint hdisj).symm
          _ ≤ U.card := Finset.card_le_card (Finset.union_subset (hsubU w1) (hsubU w2))
      have hm1 : 2 ^ m ≤ n1 := (Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)).trans
        (Nat.pow_log_le_self 2 p1.ne')
      have hm2 : 2 ^ m ≤ n2 := (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans
        (Nat.pow_log_le_self 2 p2.ne')
      have hlog : m + 1 ≤ Nat.log 2 U.card := by
        apply Nat.le_log_of_pow_le (by norm_num)
        rw [pow_succ]; omega
      calc S.card = ∑ w, (F w).card := hsum
        _ ≤ ∑ _w : Fin 3 → ZMod 2, 2 ^ s.card * 4 ^ m := Finset.sum_le_sum (fun w _ => hB w)
        _ = 8 * (2 ^ s.card * 4 ^ m) := by simp [card8]
        _ = 2 ^ (s.card + 1) * 4 ^ (m + 1) := by ring
        _ ≤ 2 ^ (insert a s).card * 4 ^ Nat.log 2 U.card := by
          rw [hcard]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlog)
    · push Not at hboth
      let P := Finset.univ.filter (fun w => (F w).Nonempty)
      have hP : Aff P := by
        intro x hx y hy z hz'
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz' ⊢
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        obtain ⟨z', hz''⟩ := hz'
        rw [memF] at hx' hy' hz''
        refine ⟨x' - y' + z', (memF _ _).2 ⟨hS _ hx'.1 _ hy'.1 _ hz''.1, ?_⟩⟩
        simp [hx'.2, hy'.2, hz''.2]
      have hPc : P.card ≤ 2 := small_fiber P hP (tt (z0 a)) (fun w hw => by
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        exact hboth w (z0 a) hw hF0)
      have hB : ∀ w ∈ P, (F w).card ≤ 2 ^ s.card * 4 ^ Nat.log 2 U.card := by
        intro w hw
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        refine (heq _ _ hw hF0).trans ((hFb _).trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by norm_num) (Nat.log_mono_right ?_))))
        exact (hproj _).trans (Finset.card_le_card (hsubU _))
      have hsum' : ∑ w ∈ P, (F w).card = ∑ w, (F w).card := by
        apply Finset.sum_filter_of_ne
        intro w _ hw
        exact Finset.card_pos.1 (Nat.pos_of_ne_zero hw)
      calc S.card = ∑ w ∈ P, (F w).card := hsum.trans hsum'.symm
        _ ≤ P.card • (2 ^ s.card * 4 ^ Nat.log 2 U.card) := Finset.sum_le_card_nsmul _ _ _ hB
        _ ≤ 2 * (2 ^ s.card * 4 ^ Nat.log 2 U.card) := by
          rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hPc
        _ = 2 ^ (insert a s).card * 4 ^ Nat.log 2 U.card := by rw [hcard]; ring

theorem key_univ {r : ℕ} (S : Finset (Fin r → Fin 3 → ZMod 2)) (hS : Aff S) :
    S.card ≤ 2 ^ r * 4 ^ Nat.log 2 (S.image tgt).card := by
  have h := key Finset.univ S hS (fun z _ i hi => absurd (Finset.mem_univ i) hi)
  have e : Ts (Finset.univ : Finset (Fin r)) = tgt := by
    funext z i; simp [Ts]
  rw [e, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem lower_leaf {r L K : ℕ} (S : Finset (Fin r → Fin 3 → ZMod 2)) (hS : Aff S)
    (o : Finset (Fin r → ZMod 2)) (hok : ∀ z, z ∈ S → tgt z ∈ o ∧ o.card ≤ L) (hK : 1 ≤ K) :
    S.card ≤ K * (2 ^ r * 4 ^ min r (Nat.log 2 L)) := by
  rcases S.eq_empty_or_nonempty with h0 | ⟨z0, hz0⟩
  · simp [h0]
  have hsub : S.image tgt ⊆ o := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact (hok z hz).1
  have hc : (S.image tgt).card ≤ L := (Finset.card_le_card hsub).trans (hok z0 hz0).2
  have hc2 : (S.image tgt).card ≤ 2 ^ r := (Finset.card_le_univ _).trans (by simp [ZMod.card])
  have hlog : Nat.log 2 (S.image tgt).card ≤ min r (Nat.log 2 L) := by
    refine le_min ?_ (Nat.log_mono_right hc)
    calc Nat.log 2 (S.image tgt).card ≤ Nat.log 2 (2 ^ r) := Nat.log_mono_right hc2
      _ = r := Nat.log_pow (by norm_num) r
  calc S.card ≤ 2 ^ r * 4 ^ Nat.log 2 (S.image tgt).card := key_univ S hS
    _ ≤ 2 ^ r * 4 ^ min r (Nat.log 2 L) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlog)
    _ ≤ K * (2 ^ r * 4 ^ min r (Nat.log 2 L)) := Nat.le_mul_of_pos_left _ hK

theorem aff_filter {r : ℕ} (S : Finset (Fin r → Fin 3 → ZMod 2)) (hS : Aff S)
    (l : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (c : Bool) :
    Aff (S.filter (fun x => decide (l x = b) = c)) := by
  intro x hx y hy z hz
  rw [Finset.mem_filter, zdec] at hx hy hz ⊢
  refine ⟨hS _ hx.1 _ hy.1 _ hz.1, ?_⟩
  rw [map_add, map_sub, hx.2, hy.2, hz.2]
  abel

theorem lower {r L : ℕ} (H : ℕ) : ∀ (S : Finset (Fin r → Fin 3 → ZMod 2)) (K : ℕ), Aff S →
    Fits (Qs (Fin r → Fin 3 → ZMod 2))
      (fun z (o : Finset (Fin r → ZMod 2)) => z ∈ S → tgt z ∈ o ∧ o.card ≤ L)
      (fun _ => 0) (fun _ => 1) H K → S.card ≤ K * (2 ^ r * 4 ^ min r (Nat.log 2 L)) := by
  induction H with
  | zero =>
    intro S K hS h
    rcases fits_cases h with ⟨o, hok, _, hK⟩ | ⟨H', hH, _⟩
    · exact lower_leaf S hS o hok hK
    · omega
  | succ H ih =>
    intro S K hS h
    rcases fits_cases h with ⟨o, hok, _, hK⟩ | ⟨H', hH, f, hf, K0, K1, hK, h0, h1⟩
    · exact lower_leaf S hS o hok hK
    rw [show H' = H by omega] at h0 h1
    obtain ⟨l, b, rfl⟩ := hf
    have g : ∀ (c : Bool) (Kc : ℕ), Fits (Qs (Fin r → Fin 3 → ZMod 2))
        (fun z (o : Finset (Fin r → ZMod 2)) => decide (l z = b) = c → z ∈ S → tgt z ∈ o ∧ o.card ≤ L)
        (fun _ => 0) (fun _ => 1) H Kc →
        (S.filter (fun x => decide (l x = b) = c)).card ≤ Kc * (2 ^ r * 4 ^ min r (Nat.log 2 L)) := by
      intro c Kc hc
      refine ih _ Kc (aff_filter S hS l b c) (fits_mono ?_ le_rfl le_rfl hc)
      intro z o h hz
      rw [Finset.mem_filter] at hz
      exact h hz.2 hz.1
    have e : S.card = (S.filter (fun x => decide (l x = b) = true)).card +
        (S.filter (fun x => decide (l x = b) = false)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun x => decide (l x = b)) (t := Finset.univ)
        (fun x _ => Finset.mem_univ _), Fintype.sum_bool]
    rw [e]
    have := g true K1 h1
    have := g false K0 h0
    have h3 := Nat.mul_le_mul_right (2 ^ r * 4 ^ min r (Nat.log 2 L)) hK
    rw [add_mul] at h3
    omega

theorem stepz : ∀ (a0 a1 a2 : ZMod 2) (b0 b1 : Bool), decide (a0 = 1) = b0 →
    decide ((if b0 = true then a2 + a1 else a2) = 1) = b1 →
    a2 + a0 * a1 = (if b1 = true then 1 else 0) := by
  decide

def pr {r : ℕ} (i : Fin r) (t : Fin 3) : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) t).comp
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin r => Fin 3 → ZMod 2) i)

theorem pr_apply {r : ℕ} (i : Fin r) (t : Fin 3) (z : Fin r → Fin 3 → ZMod 2) : pr i t z = z i t := rfl

def l1 {r : ℕ} (i : Fin r) (b0 : Bool) : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  pr i 2 + (if b0 = true then pr i 1 else 0)

theorem l1_apply {r : ℕ} (i : Fin r) (b0 : Bool) (z : Fin r → Fin 3 → ZMod 2) :
    l1 i b0 z = (if b0 = true then z i 2 + z i 1 else z i 2) := by
  cases b0 <;> simp [l1, pr_apply]

theorem build {r L k : ℕ} (hL : 2 ^ k ≤ L) : ∀ (d s : ℕ), s + d = r → k ≤ s →
    ∀ c : Fin r → ZMod 2, Fits (Qs (Fin r → Fin 3 → ZMod 2))
      (fun z (o : {o : Finset (Fin r → ZMod 2) // o.card ≤ L}) =>
        (∀ j : Fin r, k ≤ j.val → j.val < s → tgt z j = c j) → tgt z ∈ o.1)
      (fun _ => 0) (fun _ => 1) (2 * d) (4 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro s hs hks c
    let o : Finset (Fin r → ZMod 2) := Finset.univ.image
      (fun w : Fin k → ZMod 2 => fun j : Fin r => if h : j.val < k then w ⟨j.val, h⟩ else c j)
    have ho : o.card ≤ L := Finset.card_image_le.trans (by simpa [ZMod.card] using hL)
    refine fits_leaf ⟨o, ho⟩ (fun z hz => ?_) (by simp) (by simp)
    simp only [o, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨fun i => tgt z ⟨i.val, by omega⟩, ?_⟩
    funext j
    split_ifs with h
    · rfl
    · exact (hz j (by omega) (by omega)).symm
  | succ d ih =>
    intro s hs hks c
    have hsr : s < r := by omega
    let i : Fin r := ⟨s, hsr⟩
    let f0 : (Fin r → Fin 3 → ZMod 2) → Bool := fun z => decide (pr i 0 z = 1)
    have hf0 : f0 ∈ Qs _ := ⟨pr i 0, 1, rfl⟩
    have inner : ∀ b0 : Bool, Fits (Qs (Fin r → Fin 3 → ZMod 2))
        (fun z (o : {o : Finset (Fin r → ZMod 2) // o.card ≤ L}) => f0 z = b0 →
          (∀ j : Fin r, k ≤ j.val → j.val < s → tgt z j = c j) → tgt z ∈ o.1)
        (fun _ => 0) (fun _ => 1) (2 * d + 1) (4 ^ d + 4 ^ d) := by
      intro b0
      let f1 : (Fin r → Fin 3 → ZMod 2) → Bool := fun z => decide (l1 i b0 z = 1)
      have hf1 : f1 ∈ Qs _ := ⟨l1 i b0, 1, rfl⟩
      have leafs : ∀ b1 : Bool, Fits (Qs (Fin r → Fin 3 → ZMod 2))
          (fun z (o : {o : Finset (Fin r → ZMod 2) // o.card ≤ L}) => f1 z = b1 → f0 z = b0 →
            (∀ j : Fin r, k ≤ j.val → j.val < s → tgt z j = c j) → tgt z ∈ o.1)
          (fun _ => 0) (fun _ => 1) (2 * d) (4 ^ d) := by
        intro b1
        refine fits_mono ?_ le_rfl le_rfl
          (ih (s + 1) (by omega) (by omega) (Function.update c i (if b1 = true then 1 else 0)))
        intro z o h hb1 hb0 hz
        apply h
        intro j hkj hjs
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          simp only [f0, f1, pr_apply, l1_apply] at hb0 hb1
          exact stepz _ _ _ b0 b1 hb0 hb1
        · rw [Function.update_of_ne hji]
          refine hz j hkj ?_
          have : j.val ≠ s := fun h => hji (Fin.ext h)
          omega
      exact fits_node (ok := fun z (o : {o : Finset (Fin r → ZMod 2) // o.card ≤ L}) => f0 z = b0 →
          (∀ j : Fin r, k ≤ j.val → j.val < s → tgt z j = c j) → tgt z ∈ o.1)
        f1 hf1 (leafs false) (leafs true)
    refine fits_mono (fun _ _ h => h) (by omega) (by rw [pow_succ]; omega)
      (fits_node (ok := fun z (o : {o : Finset (Fin r → ZMod 2) // o.card ≤ L}) =>
          (∀ j : Fin r, k ≤ j.val → j.val < s → tgt z j = c j) → tgt z ∈ o.1)
        f0 hf0 (inner false) (inner true))

theorem pre_mem {N J : Finset (List Bool)} (hJN : J ⊆ N)
    (hpar : ∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) :
    ∀ (s p : List Bool), p ++ s ∈ N → s ≠ [] → p ∈ J := by
  intro s
  induction s with
  | nil => intro p _ h; exact absurd rfl h
  | cons b s ih =>
    intro p hp _
    by_cases hs : s = []
    · subst hs; exact hpar p b hp
    · exact hpar p b (hJN (ih (p ++ [b]) (by simpa [List.append_assoc] using hp) hs))

theorem take_mem {N J : Finset (List Bool)} (hJN : J ⊆ N)
    (hpar : ∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) (p : List Bool) (hp : p ∈ N)
    (j : ℕ) (hj : j < p.length) : p.take j ∈ J := by
  refine pre_mem hJN hpar (p.drop j) (p.take j) (by rwa [List.take_append_drop]) ?_
  intro h
  rw [List.drop_eq_nil_iff] at h
  omega

end PEqualNP.Outside.L_pcx_405_aux

open PEqualNP.Outside.L_pcx_405_aux

theorem PEqualNP.Outside.L_pcx_405 : (∀ (r L K : ℕ) (_ : 0 < L),
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let Y := Fin r → F
  let target := fun (z : X) (i : Fin r) => z i 2 + z i 0 * z i 1
  let k := min r L.log2
  (∃ (N J : Finset (List Bool)) (query : List Bool → X →ₗ[F] F)
     (bias : List Bool → F) (out : List Bool → Finset Y),
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
    (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
    (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, (out p).card ≤ L ∧
      ∀ z : X, (∀ j : Fin p.length,
        decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → target z ∈ out p) ↔
    2^(2*(r-k)) ≤ K) := by
  intro r L K hL F X Y target k
  show (∃ (N J : Finset (List Bool)) (query : List Bool → (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
     (bias : List Bool → ZMod 2) (out : List Bool → Finset (Fin r → ZMod 2)),
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
    (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
    (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, (out p).card ≤ L ∧
      ∀ z : Fin r → Fin 3 → ZMod 2, (∀ j : Fin p.length,
        decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → tgt z ∈ out p) ↔
    2^(2*(r - min r L.log2)) ≤ K
  rw [Nat.log2_eq_log_two]
  have hpos : 0 < 2 ^ r * 4 ^ min r (Nat.log 2 L) := by positivity
  have e4 : 2 ^ (2 * (r - min r (Nat.log 2 L))) = 4 ^ (r - min r (Nat.log 2 L)) := by
    rw [pow_mul]; norm_num
  rw [e4]
  constructor
  · rintro ⟨N, J, query, bias, out, hN0, hJN, hpar, hch, hK, hleaf⟩
    have hfits : Fits (Qs (Fin r → Fin 3 → ZMod 2))
        (fun z (o : Finset (Fin r → ZMod 2)) => z ∈ (Finset.univ : Finset (Fin r → Fin 3 → ZMod 2)) →
          tgt z ∈ o ∧ o.card ≤ L) (fun _ => 0) (fun _ => 1) (N.sup List.length) K := by
      refine ⟨N, J, fun p z => decide (query p z = bias p), out,
        ⟨⟨hN0, hJN, hpar, hch⟩, fun p _ => ⟨query p, bias p, rfl⟩,
          fun p hp z hz _ => ⟨(hleaf p hp).2 z hz, (hleaf p hp).1⟩⟩, ?_, ?_⟩
      · intro p hp
        simpa using Finset.le_sup (f := List.length) (Finset.mem_sdiff.1 hp).1
      · simpa using hK
    have haff : Aff (Finset.univ : Finset (Fin r → Fin 3 → ZMod 2)) :=
      fun _ _ _ _ _ _ => Finset.mem_univ _
    have h := lower (L := L) _ Finset.univ K haff hfits
    have hc : (Finset.univ : Finset (Fin r → Fin 3 → ZMod 2)).card =
        4 ^ (r - min r (Nat.log 2 L)) * (2 ^ r * 4 ^ min r (Nat.log 2 L)) := by
      rw [Finset.card_univ, Fintype.card_fun, card8, Fintype.card_fin]
      have hm : min r (Nat.log 2 L) ≤ r := min_le_left _ _
      calc 8 ^ r = 2 ^ r * 4 ^ r := by rw [← mul_pow]; norm_num
        _ = 2 ^ r * 4 ^ (r - min r (Nat.log 2 L) + min r (Nat.log 2 L)) := by
          rw [Nat.sub_add_cancel hm]
        _ = _ := by rw [pow_add]; ring
    rw [hc] at h
    exact Nat.le_of_mul_le_mul_right h hpos
  · intro hK
    have hL' : 2 ^ min r (Nat.log 2 L) ≤ L :=
      (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans
        (Nat.pow_log_le_self 2 hL.ne')
    obtain ⟨N, J, q, out, ⟨⟨h1, h2, h3, h4⟩, hq, hl⟩, -, hsum⟩ :=
      build (r := r) hL' (r - min r (Nat.log 2 L)) (min r (Nat.log 2 L)) (by have := min_le_left r (Nat.log 2 L); omega) le_rfl 0
    classical
    let query : List Bool → (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun p =>
      if h : p ∈ J then Classical.choose (hq p h) else 0
    let bias : List Bool → ZMod 2 := fun p =>
      if h : p ∈ J then Classical.choose (Classical.choose_spec (hq p h)) else 0
    have hqb : ∀ p ∈ J, q p = fun z => decide (query p z = bias p) := by
      intro p hp
      simp only [query, bias, dif_pos hp]
      exact Classical.choose_spec (Classical.choose_spec (hq p hp))
    refine ⟨N, J, query, bias, fun p => (out p).1, h1, h2, h3, h4, ?_, fun p hp => ⟨(out p).2, ?_⟩⟩
    · simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega
    · intro z hz
      refine hl p hp z (fun j => ?_) (fun j a b => by omega)
      have hmem := take_mem h2 h3 p (Finset.mem_sdiff.1 hp).1 j.val j.isLt
      rw [hqb _ hmem]
      exact hz j
