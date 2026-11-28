import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33644

abbrev W (k : Nat) := Fin k → Bool

def ix (k : Nat) (hk : 0 < k) (v : Nat) : Fin k := ⟨v % k, Nat.mod_lt _ hk⟩

def add {k : Nat} (x y : W k) (p : Fin k) := xor (x p) (y p)

def mix {k : Nat} (hk : 0 < k) (gap : Nat) (x : W k) (p : Fin k) :=
  xor (xor (x (ix k hk (p.val + k - gap % k))) (x p)) (x (ix k hk (p.val + gap)))

def step {k : Nat} (hk : 0 < k) (z : W k) (p : Fin k) :=
  xor (z p) (!(z (ix k hk (p.val + 1))) && z (ix k hk (p.val + 2)))

def run {k : Nat} (hk : 0 < k) (d : Nat) (initial : W k → W k)
    (inj : Nat → W k → W k) (name x : W k) (r : Nat) : W k :=
  (List.range r).foldl (fun z t => add (step hk (mix hk d z)) (inj t x))
    (add name (initial x))

private theorem ix_forward {k} (hk : 0 < k) (a b : Nat) :
    ix k hk ((ix k hk a).val + b) = ix k hk (a + b) := by
  apply Fin.ext
  exact Nat.mod_add_mod a k b

private theorem ix_backward {k} (hk : 0 < k) (a d : Nat) :
    ix k hk ((ix k hk (a+d)).val + k - d % k) = ix k hk a := by
  apply Fin.ext
  change (((a+d) % k + k - d % k) % k) = a % k
  have hd : d % k ≤ k := Nat.le_of_lt (Nat.mod_lt _ hk)
  have H : d + (k - d % k) = k * (d / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mod_add_div d k
    omega
  rw [Nat.add_sub_assoc hd, Nat.mod_add_mod, Nat.add_assoc, H]
  simp

private theorem shiftedMix {k} (hk : 0 < k) (d : Nat) (z : W k) (a : Nat) :
    mix hk d z (ix k hk (a+d)) =
      xor (xor (z (ix k hk a)) (z (ix k hk (a+d)))) (z (ix k hk (a+2*d))) := by
  unfold mix
  rw [ix_backward, ix_forward, show a + d + d = a + 2 * d by omega]

private theorem mixAdd {k} (hk : 0 < k) (d : Nat) (u v : W k) (p : Fin k) :
    mix hk d (add u v) p = xor (mix hk d u p) (mix hk d v p) := by
  have shuffle : ∀ a b c e f g : Bool,
      xor (xor (xor a b) (xor c e)) (xor f g) =
        xor (xor (xor a c) f) (xor (xor b e) g) := by decide
  exact shuffle _ _ _ _ _ _

private theorem stepAt {k} (hk : 0 < k) (z : W k) (p : Nat) :
    step hk z (ix k hk p) =
      xor (z (ix k hk p)) (!(z (ix k hk (p+1))) && z (ix k hk (p+2))) := by
  unfold step
  rw [ix_forward, ix_forward]

private theorem runSucc {k} (hk : 0 < k) (d : Nat) (initial : W k → W k)
    (inj : Nat → W k → W k) (name x : W k) (r : Nat) :
    run hk d initial inj name x (r+1) =
      add (step hk (mix hk d (run hk d initial inj name x r))) (inj r x) := by
  simp [run, List.range_succ, List.foldl_append]

theorem firstLocal {k} (hk : 0 < k) (d : Nat) (initial : W k → W k)
    (inj : Nat → W k → W k) (a b x : W k) (p : Nat)
    (hn : ∀ j, 0 < j → j ≤ 2 → mix hk d a (ix k hk (p+j)) = mix hk d b (ix k hk (p+j))) :
    (run hk d initial inj a x 1 (ix k hk p) = run hk d initial inj b x 1 (ix k hk p)) ↔
      (mix hk d a (ix k hk p) = mix hk d b (ix k hk p)) := by
  rw [show 1 = 0+1 by rfl, runSucc, runSucc]
  change (add (step hk (mix hk d (add a (initial x)))) (inj 0 x) (ix k hk p) =
    add (step hk (mix hk d (add b (initial x)))) (inj 0 x) (ix k hk p)) ↔ _
  simp only [add, stepAt, mixAdd, hn 1 (by decide) (by decide), hn 2 (by decide) (by decide),
    Bool.xor_left_inj]

theorem nextLocal {k} (hk : 0 < k) (d : Nat) (hd : 0 < d) (initial : W k → W k)
    (inj : Nat → W k → W k) (a b x : W k) (r p : Nat)
    (hn : ∀ j, 0 < j → j ≤ 2*d+2 →
      run hk d initial inj a x r (ix k hk (p+j)) = run hk d initial inj b x r (ix k hk (p+j))) :
    (run hk d initial inj a x (r+1) (ix k hk (p+d)) = run hk d initial inj b x (r+1) (ix k hk (p+d))) ↔
      (run hk d initial inj a x r (ix k hk p) = run hk d initial inj b x r (ix k hk p)) := by
  let A := run hk d initial inj a x r
  let B := run hk d initial inj b x r
  have rn (j : Nat) (hj : 0 < j) (hh : j ≤ 2) :
      mix hk d A (ix k hk (p+d+j)) = mix hk d B (ix k hk (p+d+j)) := by
    rw [show p+d+j = p+j+d by omega, shiftedMix, shiftedMix,
      show p+j+d = p+(j+d) by omega, show p+j+2*d = p+(j+2*d) by omega]
    change xor (xor (run _ _ _ _ _ _ _ _) _) _ = _
    rw [show A (ix k hk (p + (j+d))) = B (ix k hk (p + (j+d))) from hn _ (by omega) (by omega),
        show A (ix k hk (p + (j+2*d))) = B (ix k hk (p + (j+2*d))) from hn _ (by omega) (by omega),
        hn j hj (by omega)]
  rw [runSucc, runSucc]
  change (add (step hk (mix hk d A)) _ _ = add (step hk (mix hk d B)) _ _) ↔ (A _ = B _)
  simp only [add, stepAt, rn 1 (by decide) (by decide), rn 2 (by decide) (by decide),
    shiftedMix, Bool.xor_left_inj]
  rw [show A (ix k hk (p+d)) = B (ix k hk (p+d)) from hn _ (by omega) (by omega),
      show A (ix k hk (p+2*d)) = B (ix k hk (p+2*d)) from hn _ (by omega) (by omega)]
  simp

theorem traceCore (d : ℕ) (u v : ℕ → Bool) (A B : ℕ → ℕ → Bool)
    (first : ∀ p, (∀ j : ℕ, 0 < j → j ≤ 2 → u (p+j) = v (p+j)) →
      (A 1 p = B 1 p ↔ u p = v p))
    (next : ∀ r p, (∀ j : ℕ, 0 < j → j ≤ 2*d+2 → A r (p+j) = B r (p+j)) →
      (A (r+1) (p+d) = B (r+1) (p+d) ↔ A r p = B r p)) :
    ∀ n p : ℕ, (∀ t : ℕ, 0 < t → t ≤ 2+n*(2*d+2) → u (p+t) = v (p+t)) →
      (A (n+1) (p+n*d) = B (n+1) (p+n*d) ↔ u p = v p) := by
  intro n
  induction n with
  | zero =>
    intro p h
    simpa using first p (by intro j hj hj2; exact h j hj (by simpa using hj2))
  | succ n ih =>
    intro p h
    have hi : ∀ t : ℕ, 0 < t → t ≤ 2+n*(2*d+2) → u (p+t) = v (p+t) := by
      intro t ht he
      apply h t ht
      rw [Nat.succ_mul n (2*d+2)]
      omega
    have hn : ∀ j : ℕ, 0 < j → j ≤ 2*d+2 →
        A (n+1) (p+n*d+j) = B (n+1) (p+n*d+j) := by
      intro j hj hjs
      rw [show p+n*d+j = p+j+n*d by omega]
      apply (ih (p+j) (by
        intro t ht hbound
        rw [Nat.add_assoc]
        apply h (j+t) (by omega)
        rw [Nat.succ_mul n (2*d+2)]
        omega)).mpr
      apply h j hj
      rw [Nat.succ_mul n (2*d+2)]
      omega
    have hx := (next (n+1) (p+n*d) hn).trans (ih p hi)
    simpa [Nat.succ_mul, Nat.add_assoc] using hx

theorem traceInfluence (d : ℕ) (u v : ℕ → Bool) (A B : ℕ → ℕ → Bool)
    (first : ∀ p, (∀ j : ℕ, 0 < j → j ≤ 2 → u (p+j) = v (p+j)) →
      (A 1 p = B 1 p ↔ u p = v p))
    (next : ∀ r p, (∀ j : ℕ, 0 < j → j ≤ 2*d+2 → A r (p+j) = B r (p+j)) →
      (A (r+1) (p+d) = B (r+1) (p+d) ↔ A r p = B r p))
    (n p : ℕ) (h : ∀ t : ℕ, t < 2+n*(2*d+2) → u (p+1+t) = v (p+1+t)) :
    A (n+1) (p+n*d) = B (n+1) (p+n*d) ↔ u p = v p := by
  apply traceCore d u v A B first next n p
  intro j hj hbound
  have hh := h (j-1) (by omega)
  rwa [show p+1+(j-1) = p+j by omega] at hh

theorem roundInfluence {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d)
    (initial : W k → W k) (inj : ℕ → W k → W k) (a b x : W k) (n p : ℕ)
    (h : ∀ t : ℕ, t < 2+n*(2*d+2) →
      mix hk d a (ix k hk (p+1+t)) = mix hk d b (ix k hk (p+1+t))) :
    (run hk d initial inj a x (n+1) (ix k hk (p+n*d)) =
      run hk d initial inj b x (n+1) (ix k hk (p+n*d))) ↔
      mix hk d a (ix k hk p) = mix hk d b (ix k hk p) := by
  exact traceInfluence d
    (fun q => mix hk d a (ix k hk q)) (fun q => mix hk d b (ix k hk q))
    (fun r q => run hk d initial inj a x r (ix k hk q))
    (fun r q => run hk d initial inj b x r (ix k hk q))
    (firstLocal hk d initial inj a b x) (nextLocal hk d hd initial inj a b x) n p h

def segment {A : Type*} (v : A → ℕ → Bool) (h w : ℕ) (a : A) (i : Fin (h+w)) := v a i
def suffix {A : Type*} (v : A → ℕ → Bool) (h w : ℕ) (a : A) (i : Fin w) := v a (h+i)

theorem segmentFacts {A B : Type*} {h w : ℕ} (v : A → ℕ → Bool)
    (R : A → B → Fin h → Bool) (goal : B → Fin h → Bool)
    (locality : ∀ a a' b (j : Fin h),
      (∀ t < w, v a (j.val+1+t) = v a' (j.val+1+t)) →
      ((R a b j = R a' b j) ↔ v a j.val = v a' j.val)) :
    (∀ a a' b, segment v h w a = segment v h w a' →
      ((R a b = goal b) ↔ R a' b = goal b)) ∧
    (∀ a a' b, R a b = goal b → R a' b = goal b → suffix v h w a = suffix v h w a' →
      segment v h w a = segment v h w a') := by
  constructor
  · intro a a' b hs
    have eql (i : ℕ) (hi : i<h+w) : v a i = v a' i :=
      congrFun hs (⟨i,hi⟩ : Fin (h+w))
    have same : R a b = R a' b := by
      funext j
      apply (locality a a' b j (fun t ht => eql _ (by omega))).mpr
      exact eql _ (by omega)
    rw [same]
  · intro a a' b ha hb hs
    have tailEq (i : ℕ) (hi : h ≤ i) (upper : i<h+w) : v a i = v a' i := by
      have e := congrFun hs (⟨i-h, by omega⟩ : Fin w)
      simpa [suffix, Nat.add_sub_of_le hi] using e
    have allEq : ∀ l : ℕ, ∀ i, i<h+w → h+w-i=l → v a i=v a' i := by
      intro l
      induction l using Nat.strong_induction_on with
      | ind l ih =>
        intro i bound eq
        by_cases hh : h ≤ i
        · exact tailEq i hh bound
        · let j : Fin h := ⟨i,by omega⟩
          have after (t : ℕ) (ht : t<w) : v a (j.val+1+t) = v a' (j.val+1+t) := by
            change v a (i+1+t) = v a' (i+1+t)
            apply ih (h+w-(i+1+t)) (by omega) _ (by omega) rfl
          exact (locality a a' b j after).mp (congrFun (ha.trans hb.symm) j)
    funext j
    exact allEq _ j.val j.isLt rfl

noncomputable def liveSet {A B : Type*} [Fintype A] (P : A → B → Prop) (S : Finset B) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => ∀ b ∈ S, P a b)

theorem mem_liveSet {A B : Type*} [Fintype A] (P : A → B → Prop) (S : Finset B) (a : A) :
    a ∈ liveSet P S ↔ ∀ b ∈ S, P a b := by classical simp [liveSet]

theorem familyBound {A B C D : Type*} [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (P : A → B → Prop) (sig : A → C) (tail : A → D)
    (factor : ∀ a a' b, sig a = sig a' → (P a b ↔ P a' b))
    (separate : ∀ a a' b, P a b → P a' b → tail a = tail a' → sig a = sig a')
    (K : Finset B) (hK : K.Nonempty) :
    ∃ S ⊆ K, S.Nonempty ∧ liveSet P S = liveSet P K ∧
      (S.card ≤ 2 ∨ S.card + ((liveSet P K).image sig).card ≤ (Finset.univ.image tail).card) := by
  classical
  let good (S : Finset B) := S ⊆ K ∧ S.Nonempty ∧ liveSet P S = liveSet P K
  have existsGood : ∃ n, ∃ S : Finset B, S.card = n ∧ good S :=
    ⟨K.card, K, rfl, Finset.Subset.rfl, hK, rfl⟩
  obtain ⟨S, hn, hsub, hne, hsame⟩ := Nat.find_spec existsGood
  refine ⟨S, hsub, hne, hsame, ?_⟩
  by_cases small : S.card ≤ 2
  · exact Or.inl small
  right
  have third (s t : B) : ∃ u ∈ S, u ≠ s ∧ u ≠ t := by
    by_contra! bad
    have hsub' : S ⊆ {s,t} := by
      intro u hu
      by_cases h : u = s
      · simp [h]
      · simp [bad u hu h]
    exact small ((Finset.card_le_card hsub').trans Finset.card_le_two)
  have witness (s : ↥S) : ∃ a : A, (¬ P a s.val) ∧ ∀ t ∈ S, t ≠ s.val → P a t := by
    have preserve : liveSet P (S.erase s.val) ≠ liveSet P K := by
      intro hp
      obtain ⟨t,ht,hts,_⟩ := third s.val s.val
      have hgood : good (S.erase s.val) := ⟨Finset.Subset.trans (Finset.erase_subset ..) hsub,
        ⟨t,Finset.mem_erase.mpr ⟨hts,ht⟩⟩,hp⟩
      have le := Nat.find_min' existsGood ⟨S.erase s.val,rfl,hgood⟩
      rw [←hn,Finset.card_erase_of_mem s.property] at le
      omega
    have extra : ¬ liveSet P (S.erase s.val) ⊆ liveSet P S := by
      intro inc
      apply preserve
      rw [←hsame]
      apply Finset.Subset.antisymm inc
      intro a ha
      apply (mem_liveSet ..).mpr
      intro b hb
      exact (mem_liveSet ..).mp ha b (Finset.mem_of_mem_erase hb)
    obtain ⟨a,ha,hnS⟩ := Finset.not_subset.mp extra
    have others (t) (ht : t ∈ S) (h : t ≠ s.val) : P a t :=
      (mem_liveSet ..).mp ha t (Finset.mem_erase.mpr ⟨h,ht⟩)
    refine ⟨a, ?_, others⟩
    intro hav
    apply hnS
    apply (mem_liveSet ..).mpr
    intro t ht
    by_cases eq : t = s.val
    · simpa [eq] using hav
    · exact others t ht eq
  choose w hwfail hwpass using witness
  let V := (liveSet P K).image sig
  have rep (v : ↥V) : ∃ a ∈ liveSet P K, sig a = v.val :=
    Finset.mem_image.mp v.property
  choose get live repr using rep
  have survive (v : ↥V) (b) (hb : b ∈ S) : P (get v) b := (mem_liveSet ..).mp (live v) b (hsub hb)
  have sepW (s t : ↥S) (eq : tail (w s) = tail (w t)) : s = t := by
    by_contra ne
    have vst : s.val ≠ t.val := fun h => ne (Subtype.ext h)
    obtain ⟨u,hu,hus,hut⟩ := third s.val t.val
    have hsig := separate _ _ u (hwpass _ _ hu hus) (hwpass _ _ hu hut) eq
    exact hwfail s ((factor _ _ s.val hsig).mpr (hwpass _ _ s.property vst))
  have sepWV (s : ↥S) (v : ↥V) : tail (w s) ≠ tail (get v) := by
    intro eq
    obtain ⟨u,hu,hus,_⟩ := third s.val s.val
    have hsig := separate _ _ u (hwpass _ _ hu hus) (survive _ _ hu) eq
    exact hwfail s ((factor _ _ s.val hsig).mpr (survive _ _ s.property))
  have sepV (v v' : ↥V) (eq : tail (get v) = tail (get v')) : v = v' := by
    obtain ⟨b,hb⟩ := hne
    have hsig := separate _ _ b (survive _ _ hb) (survive _ _ hb) eq
    exact Subtype.ext ((repr _).symm.trans (hsig.trans (repr _)))
  let enc (u : ↥S ⊕ ↥V) : ↥(Finset.univ.image tail) :=
    let a : A := Sum.elim w get u
    ⟨tail a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
  have inj : Function.Injective enc := by
    intro u v he
    have hv := congrArg Subtype.val he
    rcases u with u|u <;> rcases v with v|v
    · exact congrArg Sum.inl (sepW _ _ hv)
    · exact (sepWV _ _ hv).elim
    · exact (sepWV _ _ hv.symm).elim
    · exact congrArg Sum.inr (sepV _ _ hv)
  simpa [V,Fintype.card_sum] using Fintype.card_le_of_injective enc inj

end PEqualNP.Outside.L_meta_33644

open PEqualNP.Outside.L_meta_33644 in
theorem PEqualNP.Outside.L_meta_33644 : (∀ (k h d n origin : Nat) (hk : 0 < k), 0 < h → h ≤ k → 0 < d →
  let W := Fin k → Bool
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (p : Fin k) => xor (x p) (y p)
  let mix := fun (gap : Nat) (x : W) (p : Fin k) =>
    xor (xor (x (ix (p.val + k - gap % k))) (x p)) (x (ix (p.val + gap)))
  let step := fun (z : W) (p : Fin k) =>
    xor (z p) (!(z (ix (p.val+1))) && z (ix (p.val+2)))
  ∀ (initial : W → W) (inj : Nat → W → W) (target : W → Fin h → Bool),
    let width := 2+n*(2*d+2)
    let sig := fun (name : W) (j : Fin (h+width)) => mix d name (ix (origin+j.val))
    let tail := fun (name : W) (j : Fin width) => mix d name (ix (origin+h+j.val))
    let H := (Finset.univ.image tail).card
    let reply := fun (name x : W) (j : Fin h) =>
      let state := (List.range (n+1)).foldl (fun z t => add (step (mix d z)) (inj t x))
        (add name (initial x))
      state (ix (origin+n*d+j.val))
    let surv := fun (keys : Finset W) =>
      Finset.univ.filter (fun name : W => ∀ x ∈ keys, reply name x = target x)
    ∀ K : Finset W, K.Nonempty →
      ∃ S ⊆ K, S.Nonempty ∧ surv S = surv K ∧
        (S.card ≤ 2 ∨ S.card + ((surv K).image sig).card ≤ H)) := by
  classical
  intro k h d n origin hk hh hhk hd
  dsimp only
  intro initial inj target
  intro K hK
  let width := 2+n*(2*d+2)
  let mixed (a : W k) (i : ℕ) := mix hk d a (ix k hk (origin+i))
  let resp (a x : W k) (j : Fin h) := run hk d initial inj a x (n+1) (ix k hk (origin+n*d+j.val))
  have local_rule (a b x : W k) (j : Fin h)
      (ht : ∀ t < width, mixed a (j.val+1+t) = mixed b (j.val+1+t)) :
      (resp a x j = resp b x j) ↔ mixed a j.val = mixed b j.val := by
    have ht' (t : ℕ) (hlt : t < 2+n*(2*d+2)) :
       mix hk d a (ix k hk ((origin+j.val)+1+t)) = mix hk d b (ix k hk ((origin+j.val)+1+t)) := by
      simpa only [mixed,Nat.add_assoc] using ht t hlt
    have v := roundInfluence hk d hd initial inj a b x n (origin+j.val) ht'
    simpa only [resp,mixed,show origin + j.val + n*d = origin+n*d+j.val by omega] using v
  obtain ⟨fac,sep⟩ := segmentFacts (h:=h) (w:=width) mixed resp target local_rule
  have result := familyBound (fun a x => resp a x = target x)
    (segment mixed h width) (suffix mixed h width) fac sep K hK
  have tailEq : suffix mixed h width =
      (fun (name : W k) (j : Fin width) => mix hk d name (ix k hk (origin+h+j.val))) := by
    funext name j
    simp only [suffix, mixed, Nat.add_assoc]
  rw [tailEq] at result
  let actual (T : Finset (W k)) := Finset.univ.filter (fun a : W k => ∀ x ∈ T, resp a x = target x)
  have liveEq (T : Finset (W k)) : liveSet (fun a x => resp a x = target x) T = actual T := by
    ext a
    simp only [actual, mem_liveSet, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨S, hsub, hne, hsame, hcard⟩ := result
  rw [liveEq, liveEq] at hsame
  rw [liveEq] at hcard
  refine ⟨S, hsub, hne, ?_, ?_⟩
  · convert hsame using 1 <;> ext a <;>
      simp only [actual, Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  · convert hcard using 1 <;> first | rfl | congr 2 <;> ext a <;> simp [actual, resp, run, add, step, mix, ix]
