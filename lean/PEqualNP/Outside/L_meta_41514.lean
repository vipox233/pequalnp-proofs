import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41514_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono_k {ops : α → α → Finset α} {goal : α} {k₁ k₂ : ℕ} {av : Finset α}
    (hle : k₁ ≤ k₂) (h : build ops goal k₁ av) : build ops goal k₂ av := by
  induction hle with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono_av {ops : α → α → Finset α} {goal : α} {k : ℕ} {av₁ av₂ : Finset α}
    (hsub : av₁ ⊆ av₂) (h : build ops goal k av₁) : build ops goal k av₂ := by
  induction k generalizing av₁ av₂ with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn; apply sub; intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := fun u hu =>
          (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hu).2)).resolve_left (Finset.mem_erase.mp hu).1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

theorem live_map {α β : Type} [DecidableEq α] [DecidableEq β]
    {ops1 : α → α → Finset α} {ops2 : β → β → Finset β}
    {g1 : α} {g2 : β} (f : α → β)
    (hinj : Function.Injective f) (hgoal : f g1 = g2)
    (hops : ∀ a b z, z ∈ ops1 a b → f z ∈ ops2 (f a) (f b))
    {k : ℕ} {s : Finset α} (h : live ops1 g1 k s) :
    live ops2 g2 k (s.image f) := by
  induction k generalizing s with
  | zero => change s = {g1} at h; subst h; simp [live, hgoal]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun he => hab (hinj he), f z, hops a b z hz, ?_, rest.image f, ?_, ?_⟩
      · intro hm
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
        exact hout (hinj he ▸ hu)
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih tail

end Live

def ops (n : ℕ) (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (n : ℕ) (a b : BitVec n) : Finset (BitVec n) :=
  ((ops n a b).filter (fun z => z != 0 && z != BitVec.allOnes n)).toFinset
def nrm (n : ℕ) (u : BitVec n) : BitVec n := if u.getLsbD 0 then ~~~u else u

theorem ops_swap (n : ℕ) (a b : BitVec n) : basicOps n a b = basicOps n b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem ops_diff_ij {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (a b z : BitVec n)
    (hz : z ∈ basicOps n a b) (hd : z.getLsbD i ≠ z.getLsbD j) :
    a.getLsbD i ≠ a.getLsbD j ∨ b.getLsbD i ≠ b.getLsbD j := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz.1 with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      decide_eq_true hi, decide_eq_true hj, Bool.true_and, ha, hb]

def dif (n : ℕ) (w : BitVec n) (d : ℕ) : BitVec n := (w ^^^ (w >>> d)) &&& (BitVec.allOnes n >>> d)
def unionDif (n : ℕ) (ws : List (BitVec n)) (d : ℕ) : BitVec n := ws.foldr (fun w s => dif n w d ||| s) 0
def cover (n : ℕ) (jumps : List ℕ) (t : BitVec n) (ws : List (BitVec n)) : Bool :=
  jumps.all fun d => (dif n t d &&& unionDif n ws d) == dif n t d

theorem bit_dif {n : ℕ} {w : BitVec n} {d i : ℕ} (_hi : i < n) :
    (dif n w d).getLsbD i = true ↔ i + d < n ∧ w.getLsbD i ≠ w.getLsbD (i + d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

theorem bit_union (n : ℕ) (ws : List (BitVec n)) (d i : ℕ) :
    (unionDif n ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif n w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif n w d ||| unionDif n ws d).getLsbD i = true ↔ _
    simp [ih]

theorem live_cover {n k : ℕ} {jumps : List ℕ} {goal : BitVec n} {ws : List (BitVec n)}
    (h : live (basicOps n) goal k ws.toFinset) : cover n jumps goal ws = true := by
  apply List.all_eq_true.mpr; intro d _
  apply beq_iff_eq.mpr; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif n goal d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    obtain ⟨w, hw, hdw⟩ := live_separates (fun u : BitVec n => u.getLsbD i ≠ u.getLsbD (i + d))
      hne (ops_diff_ij i (i + d) hi hj) h
    rw [(bit_union n ws d i).mpr ⟨w, List.mem_toFinset.mp hw, (bit_dif hi).mpr ⟨hj, hdw⟩⟩]; rfl

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {α : Type} [DecidableEq α] {xs ys : List α} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def actN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p2 :: ps, n => Nat.bit (Nat.beq (Nat.mod (Nat.div n p2) 2) 1) (actN ps n)

def actB (n : ℕ) (ps : List ℕ) (x : BitVec n) : BitVec n := BitVec.ofNat n (actN ps x.toNat)

theorem mod_div_two_pow_eq_testBit (n p : ℕ) :
    Nat.beq (Nat.mod (Nat.div n (2 ^ p)) 2) 1 = n.testBit p := by
  change Nat.beq (n / 2 ^ p % 2) 1 = n.testBit p
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases h : n / 2 ^ p % 2 with
  | zero => rfl
  | succ k =>
    have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : k = 0 := by omega
    subst hk; rfl

theorem actN_testBit : ∀ (pi ps : List ℕ) (n k : ℕ),
    ps = pi.map (fun p => 2 ^ p) →
    (actN ps n).testBit k = (pi[k]?.map n.testBit).getD false
  | [], _, _, _, rfl => by simp [actN]
  | p :: pi, _, n, 0, rfl => by simp [actN, mod_div_two_pow_eq_testBit]
  | p :: pi, _, n, k + 1, rfl => by
    simp [actN, Nat.testBit_bit_succ, actN_testBit pi (pi.map (fun q => 2 ^ q)) n k rfl]

theorem actB_getLsbD (n : ℕ) (pi : List ℕ) (x : BitVec n) (k : ℕ) (hk : k < n) :
    (actB n (pi.map (fun p => 2 ^ p)) x).getLsbD k = (pi[k]?.map x.getLsbD).getD false := by
  unfold actB
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, actN_testBit pi _ x.toNat k rfl]
  cases pi[k]? <;> rfl

def symValid (n gsize : ℕ) (G_idx G_pow : Array (List ℕ)) (G_inv : Array ℕ) (goal : BitVec n) (g : ℕ) : Bool :=
  let pi := G_idx[g]?.getD []
  let inv := G_idx[G_inv[g]?.getD 0]?.getD []
  let ps := G_pow[g]?.getD []
  Nat.blt (G_inv[g]?.getD 0) gsize &&
  Nat.beq (G_inv[G_inv[g]?.getD 0]?.getD 0) g &&
  Nat.beq pi.length n &&
  Nat.beq inv.length n &&
  (ps == pi.map (fun p => 2 ^ p)) &&
  (actB n ps goal == goal) &&
  (List.range n).all (fun k => match pi[k]? with
    | some p => Nat.blt p n && (inv[p]? == some k)
    | none => false)

theorem actB_spec {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) :
    G_inv[g]?.getD 0 < gsize ∧
    G_inv[G_inv[g]?.getD 0]?.getD 0 = g ∧
    G_pow[g]?.getD [] = (G_idx[g]?.getD []).map (fun p => 2 ^ p) ∧
    actB n (G_pow[g]?.getD []) goal = goal ∧
    (∀ k < n, ∃ p < n, (G_idx[g]?.getD [])[k]? = some p ∧ (G_idx[G_inv[g]?.getD 0]?.getD [])[p]? = some k) := by
  have hv := List.all_eq_true.mp hvalid g (List.mem_range.mpr hg)
  unfold symValid at hv
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at hv
  refine ⟨hv.1.1.1.1.1.1, Nat.eq_of_beq_eq_true hv.1.1.1.1.1.2, hv.1.1.2, hv.1.2, fun k hk => ?_⟩
  have h1 := hv.2 k hk
  cases hp : (G_idx[g]?.getD [])[k]? with
  | none => simp [hp] at h1
  | some p =>
    simp only [hp, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h1
    exact ⟨p, h1.1, rfl, h1.2⟩

theorem actB_inv_left {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (x : BitVec n) :
    actB n (G_pow[G_inv[g]?.getD 0]?.getD []) (actB n (G_pow[g]?.getD []) x) = x := by
  obtain ⟨hinv_lt, hinv2, hpow, _, _⟩ := actB_spec hv g hg
  obtain ⟨_, _, hpow', _, hpi'⟩ := actB_spec hv (G_inv[g]?.getD 0) hinv_lt
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow', actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, hpk⟩ := hpi' k hk
  rw [hinv2] at hpk
  rw [hkp]; simp only [Option.map_some, Option.getD_some]
  rw [hpow, actB_getLsbD n _ _ p hp, hpk]; simp

theorem actB_inj {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : Function.Injective (actB n (G_pow[g]?.getD [])) :=
  Function.LeftInverse.injective (actB_inv_left hv g hg)

theorem actB_and {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a &&& b) = actB n (G_pow[g]?.getD []) a &&& actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_and]

theorem actB_or {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a ||| b) = actB n (G_pow[g]?.getD []) a ||| actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_or]

theorem actB_not {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a : BitVec n) :
    actB n (G_pow[g]?.getD []) (~~~a) = ~~~actB n (G_pow[g]?.getD []) a := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  simp [hkp, hk, hp]

theorem actB_zero {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) 0 = 0 := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp]

theorem actB_allOnes {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) (BitVec.allOnes n) = BitVec.allOnes n := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  rw [hkp]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_allOnes, hk, hp, decide_true]

theorem actB_ops {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b z : BitVec n) (hz : z ∈ basicOps n a b) :
    actB n (G_pow[g]?.getD []) z ∈ basicOps n (actB n (G_pow[g]?.getD []) a) (actB n (G_pow[g]?.getD []) b) := by
  simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hz ⊢
  refine ⟨?_, fun e => hz.2.1 (actB_inj hv g hg (e.trans (actB_zero hv g hg).symm)),
               fun e => hz.2.2 (actB_inj hv g hg (e.trans (actB_allOnes hv g hg).symm))⟩
  have hz' := hz.1
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz' ⊢
  rcases hz' with rfl | rfl | rfl | rfl
  · left; exact actB_and hv g hg a b
  · right; left; exact actB_or hv g hg a b
  · right; right; left; rw [actB_and hv g hg, actB_not hv g hg]
  · right; right; right; rw [actB_and hv g hg, actB_not hv g hg]

def checkChildP (n k : ℕ) (targets : List (List (BitVec n))) (nxt : List (BitVec n)) : Bool :=
  decide (nxt.length > k) || targets.any (fun t => sameSet nxt t)

def checkStepP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (k extra : ℕ)
    (targets : List (List (BitVec n))) (a b : BitVec n) (r : List (BitVec n)) : Bool :=
  (ops n a b).all fun w =>
    (w == 0 || w == BitVec.allOnes n || w == a || w == b || r.contains w) ||
    (!cover n jumps goal (w :: r) || checkChildP n k targets (w :: r)) &&
    ((extra == 0) ||
      ((!cover n jumps goal (w :: a :: r) || checkChildP n k targets (w :: a :: r)) &&
       (!cover n jumps goal (w :: b :: r) || checkChildP n k targets (w :: b :: r)))) &&
    ((extra < 2) || !cover n jumps goal (w :: a :: b :: r) || checkChildP n k targets (w :: a :: b :: r))

def checkNodeP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hs) =>
    decide ws.Nodup && !(ws.contains goal) && decide (ws.length ≤ k + 1) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepP n jumps goal k extra targets a b r)

def checkBlockP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeP n jumps goal gsize G_pow k cur prev (start + m) &&
      checkBlockP n jumps goal gsize G_pow k cur prev start m

theorem checkBlockP_at {n gsize k start m : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h : checkBlockP n jumps goal gsize G_pow k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeP n jumps goal gsize G_pow k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_P {n gsize k i : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hchk : checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hs⟩
  have hget : cur[i]? = some (ws, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeP at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps n) goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (G_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB n (G_pow[G_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [])).1.map (actB n (G_pow[g]?.getD []))).toFinset.image
        (actB n (G_pow[G_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB n (G_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec n} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps n a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps n) goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover n jumps goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepP at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes n || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildP n k targets (z :: kept) = true) : False := by
        unfold checkChildP at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with hgt | ⟨t, ht, hss⟩
        · omega
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap n a b ▸ hz)

theorem level_sound_P {n gsize k : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset :=
  fun i hi => node_sound_P hk hi hvalid hprev (hblk i hi)

theorem no_build_of_top {n gsize k rg : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {rows top_ws : List (BitVec n)}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hrg : rg < gsize)
    (hsub : rows.sublists.filter (fun ws => cover n jumps goal ws) = [rows])
    (hmatch : sameSet (rows.map (actB n (G_pow[rg]?.getD []))) top_ws = true)
    (hdead : ¬ live (basicOps n) goal k top_ws.toFinset) :
    ¬ build (basicOps n) goal k rows.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := rows.filter (· ∈ s)
  have hsubl : ws.Sublist rows := List.filter_sublist
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hcov : cover n jumps goal ws = true := live_cover (heq.symm ▸ hl)
  have hmem : ws ∈ rows.sublists.filter (fun zs => cover n jumps goal zs) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr hsubl, hcov⟩
  rw [hsub, List.mem_singleton] at hmem
  have hs_eq : s = rows.toFinset := by rw [← heq, hmem]
  have hl_rows : live (basicOps n) goal k rows.toFinset := hs_eq ▸ hl
  have hrg_g := (actB_spec hvalid rg hrg).2.2.2.1
  have hrot := live_map (actB n (G_pow[rg]?.getD [])) (actB_inj hvalid rg hrg) hrg_g (actB_ops hvalid rg hrg) hl_rows
  have himg : rows.toFinset.image (actB n (G_pow[rg]?.getD [])) =
      (rows.map (actB n (G_pow[rg]?.getD []))).toFinset := by
    ext u; simp [List.mem_map]
  rw [himg, sameSet_sound hmatch] at hrot
  exact hdead hrot


def jumps4 : List ℕ := [1,2,4,8]

def jumps5 : List ℕ := [1,2,4,8,16]

def jumps6 : List ℕ := [1,2,4,8,16,32]

def rows4 : List (BitVec 16) := [0xaaaa,0xcccc,0xf0f0,0xff00]

def rows5 : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def rows6 : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def goal6 : BitVec 64 := 0xfeeeeee0faeaea80

def projN {m : ℕ} : List ℕ → BitVec m → ℕ
  | [], _ => 0
  | idx :: idxs, w => Nat.bit (w.getLsbD idx) (projN idxs w)

theorem projN_testBit {m : ℕ} : ∀ (idxs : List ℕ) (w : BitVec m) (k : ℕ),
    (projN idxs w).testBit k = (idxs[k]?.map w.getLsbD).getD false
  | [], _, _ => by simp [projN]
  | idx :: idxs, w, 0 => by simp [projN]
  | idx :: idxs, w, k + 1 => by simp [projN, Nat.testBit_bit_succ, projN_testBit idxs w k]

def projB (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := BitVec.ofNat n (projN idxs w)
def projS (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := nrm n (projB n idxs w)

theorem projB_getLsbD (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) (k : ℕ) (hk : k < n) :
    (projB n idxs w).getLsbD k = (idxs[k]?.map w.getLsbD).getD false := by
  unfold projB; rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, projN_testBit]

theorem projB_and (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a &&& b) = projB n idxs a &&& projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_and]

theorem projB_or (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a ||| b) = projB n idxs a ||| projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_or]

theorem projB_not (n : ℕ) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n) (hlt : ∀ idx ∈ idxs, idx < m) (a : BitVec m) :
    projB n idxs (~~~a) = ~~~projB n idxs a := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  have hk' : k < idxs.length := by omega
  rw [List.getElem?_eq_getElem hk']
  have hmem := hlt idxs[k] (List.getElem_mem hk')
  simp [hk, hmem]

theorem projB_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projB n idxs (0 : BitVec m) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk]; cases idxs[k]? <;> simp

theorem projB_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projB n idxs (w &&& mask) = projB n idxs w := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases h : idxs[k]? with
  | none => rfl
  | some idx =>
    have hmem : idx ∈ idxs := List.mem_of_getElem? h
    simp [BitVec.getLsbD_and, hm idx hmem]

theorem nrm_bit0 (n : ℕ) (hn : 0 < n) (u : BitVec n) : (nrm n u).getLsbD 0 = false := by
  unfold nrm
  cases h : u.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]

theorem projS_ne_allOnes (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (w : BitVec m) :
    projS n idxs w ≠ BitVec.allOnes n := by
  intro h
  have := nrm_bit0 n hn (projB n idxs w)
  change (projS n idxs w).getLsbD 0 = false at this
  rw [h, BitVec.getLsbD_allOnes, decide_eq_true hn] at this
  exact Bool.noConfusion this

theorem nrm_zero (n : ℕ) : nrm n 0 = 0 := by unfold nrm; simp
theorem projS_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projS n idxs (0 : BitVec m) = 0 := by
  unfold projS; rw [projB_zero, nrm_zero]
theorem projS_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projS n idxs (w &&& mask) = projS n idxs w := by
  unfold projS; rw [projB_mask n idxs mask hm w]

theorem nrm_neg (n : ℕ) (hn : 0 < n) (u : BitVec n) : nrm n (~~~u) = nrm n u := by
  unfold nrm
  cases h : u.getLsbD 0
  · have h1 : (~~~u).getLsbD 0 = true := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_false]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · have h1 : (~~~u).getLsbD 0 = false := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true]

theorem projS_not (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (w : BitVec m) :
    projS n idxs (~~~w) = projS n idxs w := by
  unfold projS; rw [projB_not n idxs hlen hlt w, nrm_neg n hn]

theorem nrm_ops (n : ℕ) (hn : 0 < n) (x y z : BitVec n) (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false)
    (hz : z ∈ ops n x y ∨ z ∈ ops n (~~~x) y ∨ z ∈ ops n x (~~~y) ∨ z ∈ ops n (~~~x) (~~~y)) :
    nrm n z ∈ ops n x y := by
  have nrm_f (u : BitVec n) (hu : u.getLsbD 0 = false) : nrm n u = u := by
    unfold nrm; simp only [hu, Bool.false_eq_true, ite_false]
  have nrm_t (u : BitVec n) (hu : u.getLsbD 0 = true) : nrm n u = ~~~u := by
    unfold nrm; simp only [hu, ite_true]
  have b_eq (u v : BitVec n) (h : ∀ i < n, u.getLsbD i = v.getLsbD i) : u = v := BitVec.eq_of_getLsbD_eq h
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, hx, hy, Bool.and_false])
  · right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_or, hx, hy, Bool.or_false])
  · right; right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.and_false])]
    exact BitVec.and_comm ..
  · right; right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.or_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem projS_ops (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (a b z : BitVec m) (hz : z ∈ ops m a b) :
    projS n idxs z ∈ ops n (projS n idxs a) (projS n idxs b) := by
  have hrest : projB n idxs z ∈ ops n (projB n idxs a) (projB n idxs b) := by
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · left; exact projB_and n idxs a b
    · right; left; exact projB_or n idxs a b
    · right; right; left; rw [projB_and, projB_not n idxs hlen hlt]
    · right; right; right; rw [projB_and, projB_not n idxs hlen hlt]
  apply nrm_ops n hn (projS n idxs a) (projS n idxs b) (projB n idxs z) (nrm_bit0 n hn _) (nrm_bit0 n hn _)
  unfold projS nrm
  cases ha : (projB n idxs a).getLsbD 0 <;> cases hb : (projB n idxs b).getLsbD 0 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · exact Or.inl hrest
  · exact Or.inr (Or.inr (Or.inl hrest))
  · exact Or.inr (Or.inl hrest)
  · exact Or.inr (Or.inr (Or.inr hrest))

theorem ops_zero_left (n : ℕ) (y : BitVec n) : ∀ w ∈ ops n 0 y, w = 0 ∨ w = y := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.zero_and
  · right; exact BitVec.zero_or
  · left; exact BitVec.zero_and
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]

theorem ops_zero_right (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x 0, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.and_zero
  · right; exact BitVec.or_zero
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]
  · left; exact BitVec.zero_and

theorem ops_self (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x x, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · right; exact BitVec.and_self
  · right; exact BitVec.or_self
  · left; exact BitVec.and_not_self x
  · left; exact BitVec.and_not_self x

def zCount {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : ℕ :=
  (s.filter (fun w => f w = 0)).card
def nonZeroImg {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : Finset (BitVec n) :=
  (s.image f).erase 0

set_option maxRecDepth 100000 in
theorem live_restrict {m n : ℕ} (hn : 0 < n) (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) {opsM : BitVec m → BitVec m → Finset (BitVec m)}
    (hopsM : ∀ a b z, z ∈ opsM a b → z ∈ ops m a b)
    {g : BitVec m} {goalN : BitVec n} (hg : projS n idxs g = goalN) (hgnz : goalN ≠ 0)
    {k : ℕ} {s : Finset (BitVec m)} (h : live opsM g k s) :
    build (basicOps n) goalN (k - zCount (projS n idxs) s) (nonZeroImg (projS n idxs) s) := by
  let f : BitVec m → BitVec n := projS n idxs
  change build (basicOps n) goalN (k - zCount f s) (nonZeroImg f s)
  induction k generalizing s with
  | zero =>
    change s = {g} at h; subst h
    have hzc : zCount f {g} = 0 := by
      unfold zCount; rw [Finset.filter_singleton, if_neg (by change projS n idxs g ≠ 0; rw [hg]; exact hgnz)]; rfl
    rw [hzc]; change goalN ∈ nonZeroImg f {g}
    exact Finset.mem_erase.mpr ⟨hgnz, Finset.mem_image.mpr ⟨g, Finset.mem_singleton_self g, hg⟩⟩
  | succ k ih =>
    have hsc := live_card h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs_eq, tail⟩
    · exact build_mono_k (by omega) (ih skip)
    · have htail := ih tail
      have hz_ops : f z ∈ ops n (f a) (f b) := projS_ops n hn idxs hlen hlt a b z (hopsM a b z hz)
      have hsub_rest : nonZeroImg f rest ⊆ nonZeroImg f s := by
        intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu ⊢
        obtain ⟨hne, v, hv, rfl⟩ := hu; exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
      have hcard_rest : zCount f rest ≤ zCount f (insert z rest) := by
        unfold zCount; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert z rest))
      by_cases hza : f a = 0
      · have hzb_or := ops_zero_left n (f b) (f z) (hza ▸ hz_ops)
        have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
          obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
          · rcases hzb_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, b, hb, h1.symm⟩
          · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
        have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
          by_cases hzb : f b = 0
          · have hzz : f z = 0 := by rcases hzb_or with h0 | h1; exact h0; exact h1.trans hzb
            have hz_nr : z ∉ rest := fun hm => hout (by rw [hs_eq]; simp [hm])
            have h1 : zCount f (insert z rest) = zCount f rest + 1 := by
              unfold zCount; rw [Finset.filter_insert, if_pos hzz, Finset.card_insert_of_notMem (by simp [hz_nr])]
            have h2 : zCount f s ≤ zCount f rest + 2 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_pos hza]
              have hc1 := Finset.card_insert_le a (insert b (rest.filter (fun w => f w = 0)))
              have hc2 := Finset.card_insert_le b (rest.filter (fun w => f w = 0))
              omega
            omega
          · have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_pos hza]
              exact Finset.card_insert_le a (rest.filter (fun w => f w = 0))
            omega
        exact build_mono_k (by omega) (build_mono_av hsub htail)
      · by_cases hzb : f b = 0
        · have hza_or := ops_zero_right n (f a) (f z) (hzb ▸ hz_ops)
          have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
            intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
            obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
            · rcases hza_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
            · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
          have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
            have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_neg hza]
              exact Finset.card_insert_le b (rest.filter (fun w => f w = 0))
            omega
          exact build_mono_k (by omega) (build_mono_av hsub htail)
        · have hzc_eq : zCount f s = zCount f rest := by
            unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_neg hza]
          have hzc_le : zCount f s ≤ k := by
            have hsubf : insert a (insert b (s.filter (fun w => f w = 0))) ⊆ s := by
              intro u hu
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact ha
              · rcases Finset.mem_insert.mp hu with rfl | hu
                · exact hb
                · exact (Finset.mem_filter.mp hu).1
            have han : a ∉ insert b (s.filter (fun w => f w = 0)) := by
              simp only [Finset.mem_insert, Finset.mem_filter, not_or]; exact ⟨hab, fun h => hza h.2⟩
            have hbn : b ∉ s.filter (fun w => f w = 0) := by
              simp only [Finset.mem_filter]; exact fun h => hzb h.2
            have hle := Finset.card_le_card hsubf
            rw [Finset.card_insert_of_notMem han, Finset.card_insert_of_notMem hbn] at hle
            unfold zCount; omega
          by_cases hzz : f z = 0
          · have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
              intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
              obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
              · exact (hne hzz).elim
              · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
            exact build_mono_k (by omega) (build_mono_av hsub htail)
          · by_cases heqab : f a = f b
            · have hsame := ops_self n (f a) (f z) (heqab ▸ hz_ops)
              have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
                intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
                obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                · rcases hsame with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
                · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
              exact build_mono_k (by omega) (build_mono_av hsub htail)
            · have hstep : build (basicOps n) goalN ((k - zCount f (insert z rest)) + 1) (nonZeroImg f s) := by
                refine Or.inr ⟨f a, ?_, f b, ?_, heqab, f z, ?_, ?_⟩
                · exact Finset.mem_erase.mpr ⟨hza, Finset.mem_image_of_mem f ha⟩
                · exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_image_of_mem f hb⟩
                · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
                  exact ⟨hz_ops, hzz, projS_ne_allOnes n hn idxs z⟩
                · apply build_mono_av _ htail
                  intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu
                  obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                  · exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (hsub_rest (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f hv⟩))
              exact build_mono_k (by omega) hstep

def b4_0_goal : BitVec 16 := 0xfee8
def b4_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_0_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_0_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_0_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_0_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_0_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_0_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_0_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_0_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_0_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_0_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_0_s6 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_0_p6 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_0_s7 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_0_p7 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_0_s8 : List ℕ := [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15]
def b4_0_p8 : List ℕ := [1,4,16,64,2,8,32,128,256,1024,4096,16384,512,2048,8192,32768]
def b4_0_s9 : List ℕ := [0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15]
def b4_0_p9 : List ℕ := [1,4,16,64,256,1024,4096,16384,2,8,32,128,512,2048,8192,32768]
def b4_0_s10 : List ℕ := [0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15]
def b4_0_p10 : List ℕ := [1,4,256,1024,2,8,512,2048,16,64,4096,16384,32,128,8192,32768]
def b4_0_s11 : List ℕ := [0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15]
def b4_0_p11 : List ℕ := [1,4,256,1024,16,64,4096,16384,2,8,512,2048,32,128,8192,32768]
def b4_0_s12 : List ℕ := [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15]
def b4_0_p12 : List ℕ := [1,16,2,32,4,64,8,128,256,4096,512,8192,1024,16384,2048,32768]
def b4_0_s13 : List ℕ := [0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15]
def b4_0_p13 : List ℕ := [1,16,2,32,256,4096,512,8192,4,64,8,128,1024,16384,2048,32768]
def b4_0_s14 : List ℕ := [0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15]
def b4_0_p14 : List ℕ := [1,16,4,64,2,32,8,128,256,4096,1024,16384,512,8192,2048,32768]
def b4_0_s15 : List ℕ := [0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15]
def b4_0_p15 : List ℕ := [1,16,4,64,256,4096,1024,16384,2,32,8,128,512,8192,2048,32768]
def b4_0_s16 : List ℕ := [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]
def b4_0_p16 : List ℕ := [1,16,256,4096,2,32,512,8192,4,64,1024,16384,8,128,2048,32768]
def b4_0_s17 : List ℕ := [0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15]
def b4_0_p17 : List ℕ := [1,16,256,4096,4,64,1024,16384,2,32,512,8192,8,128,2048,32768]
def b4_0_s18 : List ℕ := [0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15]
def b4_0_p18 : List ℕ := [1,256,2,512,4,1024,8,2048,16,4096,32,8192,64,16384,128,32768]
def b4_0_s19 : List ℕ := [0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15]
def b4_0_p19 : List ℕ := [1,256,2,512,16,4096,32,8192,4,1024,8,2048,64,16384,128,32768]
def b4_0_s20 : List ℕ := [0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15]
def b4_0_p20 : List ℕ := [1,256,4,1024,2,512,8,2048,16,4096,64,16384,32,8192,128,32768]
def b4_0_s21 : List ℕ := [0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15]
def b4_0_p21 : List ℕ := [1,256,4,1024,16,4096,64,16384,2,512,8,2048,32,8192,128,32768]
def b4_0_s22 : List ℕ := [0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15]
def b4_0_p22 : List ℕ := [1,256,16,4096,2,512,32,8192,4,1024,64,16384,8,2048,128,32768]
def b4_0_s23 : List ℕ := [0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15]
def b4_0_p23 : List ℕ := [1,256,16,4096,4,1024,64,16384,2,512,32,8192,8,2048,128,32768]
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0,b4_0_s1,b4_0_s2,b4_0_s3,b4_0_s4,b4_0_s5,b4_0_s6,b4_0_s7,b4_0_s8,b4_0_s9,b4_0_s10,b4_0_s11,b4_0_s12,b4_0_s13,b4_0_s14,b4_0_s15,b4_0_s16,b4_0_s17,b4_0_s18,b4_0_s19,b4_0_s20,b4_0_s21,b4_0_s22,b4_0_s23]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0,b4_0_p1,b4_0_p2,b4_0_p3,b4_0_p4,b4_0_p5,b4_0_p6,b4_0_p7,b4_0_p8,b4_0_p9,b4_0_p10,b4_0_p11,b4_0_p12,b4_0_p13,b4_0_p14,b4_0_p15,b4_0_p16,b4_0_p17,b4_0_p18,b4_0_p19,b4_0_p20,b4_0_p21,b4_0_p22,b4_0_p23]
def b4_0_inv : Array ℕ := Array.mk [0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_G_valid : (List.range 24).all (symValid 16 24 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xff0,0xaaaa,0xcccc],[]),
([0xaaaa,0xfccc,0xfff0],[]),
([0xeaea,0xfcfc,0xffc0],[]),
([0xaaa,0xfccc,0xfff0],[]),
([0xff0,0xaaaa,0xfccc],[]),
([0xaaaa,0xdccc,0xfff0],[]),
([0xaaaa,0xaff0,0xcccc],[]),
([0xaaa,0xff0,0xcccc],[]),
([0xaaaa,0xfcec,0xfff0],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeeee,0xf0f0,0xff00],[(16,0),(16,1),(17,1)]),
([0xaa,0xcccc,0xfaf0,0xff00],[(12,1)]),
([0xaa,0x5500,0xcccc,0xf0f0],[(12,0)]),
([0xaaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xcccc,0xf0f0,0xff80],[]),
([0x2aaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xfccc,0xfff0],[]),
([0xaaaa,0xcccc,0xfaf0,0xffaa],[]),
([0xaaaa,0xcccc,0xf8f8,0xff88],[(8,2)]),
([0xaaa,0xf0f0,0xfccc,0xff00],[(0,3)]),
([0x8888,0xeeee,0xf0f0,0xff88],[(8,2),(16,3),(16,4)]),
([0xaaaa,0xcccc,0xfaaa,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xff08],[(16,5)]),
([0x8aaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xcccc,0xf0f0,0xff88],[(16,1)]),
([0x88,0xeeee,0xf0f0,0xff00],[(16,1),(17,5),(17,6)]),
([0xaaa,0xccc,0xf0f0,0xff00],[]),
([0xaaa,0xcccc,0xf000,0xfff0],[(0,3),(0,7),(6,1)]),
([0xff0,0xaaaa,0xcccc],[]),
([0xff0,0xaaaa,0xcccc,0xf000],[(0,4),(0,7),(6,4),(6,7)]),
([0xff0,0xaaaa,0xcccc,0xfff0],[]),
([0xff0,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xfcfc,0xffcc,0xfff0],[(0,1),(2,1),(3,1)]),
([0xa8a8,0xcccc,0xfafa,0xff00],[(13,8),(15,1)]),
([0xaaaa,0xcccc,0xf0f0,0xffa8],[(13,8),(16,8)]),
([0x2aa,0xcccc,0xf0f0,0xff00],[]),
([0xaaa8,0xcccc,0xf0f0,0xff00],[]),
([0xfe,0xaaaa,0xcccc,0xf0f0],[]),
([0xaa,0xcccc,0xdd00,0xf0f0],[(12,6)]),
([0xaa,0x55aa,0xcccc,0xf0f0],[])
]
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaa,0xaa00,0xcccc,0xf0f0,0xff00],[(0,0),(0,2),(0,3),(2,2),(3,1)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,3)]),
([0x8080,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,5),(3,4),(9,6),(13,4),(16,4)]),
([0xaaaa,0xcccc,0xf0f0,0xff88],[(4,2),(4,8),(16,7),(18,2),(18,8)]),
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff88],[(0,9),(0,11),(4,2),(16,10),(17,4),(18,2)]),
([0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00],[(3,12)]),
([0x88,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,15),(0,16),(1,13),(16,14)]),
([0xaaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaa,0xcccc,0xf000,0xf0f0,0xff00],[(0,10),(0,17),(0,18),(22,15)]),
([0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeeee,0xf0f0,0xff00],[(0,11),(0,16),(1,11),(1,16),(16,7),(16,12),(16,18),(16,19),(16,20),(16,21),(17,7),(17,12),(17,18)]),
([0x8888,0xaaaa,0xeeee,0xf0f0,0xff00],[(4,8),(5,8),(16,22)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(0,3),(3,1)]),
([0xaaaa,0xcccc,0xf0f0,0xffaa,0xffcc],[(0,15),(1,24),(7,24),(8,23)]),
([0xaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,16)]),
([0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,24),(0,25),(1,15),(2,24),(4,15),(21,26)]),
([0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00],[(0,28),(9,27)]),
([0xee,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0xa,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,1),(0,15),(1,15),(16,4),(17,4)]),
([0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00],[]),
([0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00],[(17,4),(21,29)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,1)]),
([0xaa,0xa0a,0xcccc,0xf0f0,0xff00],[(0,4),(2,29),(3,29)]),
([0xaa,0x5500,0xcccc,0xf0f0],[(0,30),(12,19),(21,30)]),
([0xaa,0x5500,0xaaaa,0xcccc,0xf0f0],[(12,22)])
]
def b4_0_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,2),(0,3),(0,4),(0,6),(0,10),(0,11),(1,2),(1,3),(1,4),(1,6),(4,0),(4,1),(6,11),(8,5),(9,5),(16,7),(16,8),(16,9),(17,7),(17,8),(17,9),(18,0),(18,1)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,10),(0,11),(0,14),(0,16),(0,17),(1,14),(1,16),(1,17),(4,1),(4,12),(4,13),(5,13),(6,11),(6,14),(7,14),(8,15),(9,15),(16,18),(17,18),(18,1),(18,12),(18,13),(19,13)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,6),(0,12),(0,14),(0,18),(0,23),(0,24),(0,25),(2,6),(2,14),(2,18),(2,23),(3,19),(3,22),(6,20),(8,20),(19,21),(21,25),(22,21)])
]
def b4_0_L6 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(3,0),(3,1),(4,2),(6,2),(7,2),(8,2),(9,2),(10,2),(11,2),(12,0),(12,1),(13,0),(13,1),(16,0),(16,1),(18,2),(20,2),(21,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_0_L2.size = 9 := by decide +kernel
  exact checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 3 b4_0_L3 b4_0_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_1 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 3 b4_0_L3 b4_0_L2 16 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true := by
  intro i hi
  have hsz : b4_0_L3.size = 31 := by decide +kernel
  have hi' : i < 31 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockP_at b4_0_chk_3_0 i (by omega) (by omega)
  ·
    exact checkBlockP_at b4_0_chk_3_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 4 b4_0_L4 b4_0_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_1 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 4 b4_0_L4 b4_0_L3 16 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true := by
  intro i hi
  have hsz : b4_0_L4.size = 26 := by decide +kernel
  have hi' : i < 26 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockP_at b4_0_chk_4_0 i (by omega) (by omega)
  ·
    exact checkBlockP_at b4_0_chk_4_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_5_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 5 b4_0_L5 b4_0_L4 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_5 : ∀ i < b4_0_L5.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 5 b4_0_L5 b4_0_L4 i = true := by
  intro i hi
  have hsz : b4_0_L5.size = 3 := by decide +kernel
  exact checkBlockP_at b4_0_chk_5_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_6_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 6 b4_0_L6 b4_0_L5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_6 : ∀ i < b4_0_L6.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 6 b4_0_L6 b4_0_L5 i = true := by
  intro i hi
  have hsz : b4_0_L6.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_6_0 i (Nat.zero_le _) (by omega)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
theorem b4_0_L5_sound : ∀ i < b4_0_L5.size, ¬ live (basicOps 16) b4_0_goal 5 (b4_0_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L4_sound b4_0_chk_5
theorem b4_0_L6_sound : ∀ i < b4_0_L6.size, ¬ live (basicOps 16) b4_0_goal 6 (b4_0_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L5_sound b4_0_chk_6
set_option maxRecDepth 100000 in
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 6 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L6_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xeaa8
def b4_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_1_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_1_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_1_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_1_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_1_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_1_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_1_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_1_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_1_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_1_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1,b4_1_s2,b4_1_s3,b4_1_s4,b4_1_s5]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1,b4_1_p2,b4_1_p3,b4_1_p4,b4_1_p5]
def b4_1_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 6).all (symValid 16 6 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x55aa,0xcccc,0xf0f0],[]),
([0xff0,0xaaaa,0xcccc],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff88],[]),
([0x44cc,0xaaaa,0xf0f0,0xff00],[]),
([0xaaaa,0xc8c8,0xf0f0,0xff00],[]),
([0xee,0xaaaa,0xcccc,0xf0f0],[]),
([0xaa,0x5500,0xcccc,0xf0f0],[(0,0)]),
([0xaaaa,0xc0c0,0xfcfc,0xff00],[(3,1)]),
([0xaaaa,0xcccc,0xf0f0,0xff0c],[]),
([0xaaaa,0xc0cc,0xf0f0,0xff00],[]),
([0xcc,0x3300,0xaaaa,0xf0f0],[(2,1)])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(1,0),(4,1),(5,1)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,3),(1,3),(2,2),(3,2)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,4)]),
([0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[(4,4)]),
([0xaaaa,0xc0c0,0xcccc,0xf0f0,0xff00],[(0,5)]),
([0xaaaa,0xcccc,0xf0f0,0xfcfc,0xff00],[(0,5)]),
([0xcc,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,8),(1,6),(4,7)])
]
def b4_1_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5),(1,6),(2,0),(2,1),(2,3),(2,6),(3,0),(3,1),(3,3),(3,6),(4,2),(4,4),(4,5),(4,6),(5,6)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 9 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
  intro i hi
  have hsz : b4_1_L4.size = 7 := by decide +kernel
  exact checkBlockP_at b4_1_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_5_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 5 b4_1_L5 b4_1_L4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_5 : ∀ i < b4_1_L5.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 5 b4_1_L5 b4_1_L4 i = true := by
  intro i hi
  have hsz : b4_1_L5.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_5_0 i (Nat.zero_le _) (by omega)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
theorem b4_1_L5_sound : ∀ i < b4_1_L5.size, ¬ live (basicOps 16) b4_1_goal 5 (b4_1_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L4_sound b4_1_chk_5
set_option maxRecDepth 100000 in
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L5[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 5 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L5_sound 0 (by decide))

def b4_2_goal : BitVec 16 := 0xa880
def b4_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_2_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_2_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_2_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_2_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_2_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_2_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_2_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_2_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_2_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_2_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_2_idx : Array (List ℕ) := Array.mk [b4_2_s0,b4_2_s1,b4_2_s2,b4_2_s3,b4_2_s4,b4_2_s5]
def b4_2_pow : Array (List ℕ) := Array.mk [b4_2_p0,b4_2_p1,b4_2_p2,b4_2_p3,b4_2_p4,b4_2_p5]
def b4_2_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_G_valid : (List.range 6).all (symValid 16 6 b4_2_idx b4_2_pow b4_2_inv b4_2_goal) = true := by decide +kernel
def b4_2_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xa0a0,0xff00],[])
]
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xf0f0,0xff00],[(0,0),(1,0)]),
([0xaa,0xaaaa,0xcccc,0xf0f0],[])
]
def b4_2_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,1),(2,0),(3,0),(4,1)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_2_0 : checkBlockP 16 jumps4 b4_2_goal 6 b4_2_pow 2 b4_2_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_2 : ∀ i < b4_2_L2.size, checkNodeP 16 jumps4 b4_2_goal 6 b4_2_pow 2 b4_2_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_2_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_2_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_3_0 : checkBlockP 16 jumps4 b4_2_goal 6 b4_2_pow 3 b4_2_L3 b4_2_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_3 : ∀ i < b4_2_L3.size, checkNodeP 16 jumps4 b4_2_goal 6 b4_2_pow 3 b4_2_L3 b4_2_L2 i = true := by
  intro i hi
  have hsz : b4_2_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_2_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_4_0 : checkBlockP 16 jumps4 b4_2_goal 6 b4_2_pow 4 b4_2_L4 b4_2_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_4 : ∀ i < b4_2_L4.size, checkNodeP 16 jumps4 b4_2_goal 6 b4_2_pow 4 b4_2_L4 b4_2_L3 i = true := by
  intro i hi
  have hsz : b4_2_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_2_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_2_L2_sound : ∀ i < b4_2_L2.size, ¬ live (basicOps 16) b4_2_goal 2 (b4_2_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid (fun j hj => by simp at hj) b4_2_chk_2
theorem b4_2_L3_sound : ∀ i < b4_2_L3.size, ¬ live (basicOps 16) b4_2_goal 3 (b4_2_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid b4_2_L2_sound b4_2_chk_3
theorem b4_2_L4_sound : ∀ i < b4_2_L4.size, ¬ live (basicOps 16) b4_2_goal 4 (b4_2_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid b4_2_L3_sound b4_2_chk_4
set_option maxRecDepth 100000 in
theorem b4_2_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_2_goal ws) = [rows4] := by decide +kernel
theorem b4_2_top_match : sameSet (rows4.map (actB 16 (b4_2_pow[0]?.getD []))) (b4_2_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_2_no_build : ¬ build (basicOps 16) b4_2_goal 4 rows4.toFinset :=
  no_build_of_top b4_2_G_valid (by decide) b4_2_sublists b4_2_top_match (b4_2_L4_sound 0 (by decide))

def b4_3_goal : BitVec 16 := 0xeee8
def b4_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_3_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_3_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_3_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_3_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_3_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_3_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0,b4_3_s1,b4_3_s2,b4_3_s3]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0,b4_3_p1,b4_3_p2,b4_3_p3]
def b4_3_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_G_valid : (List.range 4).all (symValid 16 4 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[])
]
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_3_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_2_0 : checkBlockP 16 jumps4 b4_3_goal 4 b4_3_pow 2 b4_3_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_2 : ∀ i < b4_3_L2.size, checkNodeP 16 jumps4 b4_3_goal 4 b4_3_pow 2 b4_3_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_3_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 4 b4_3_pow 3 b4_3_L3 b4_3_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 4 b4_3_pow 3 b4_3_L3 b4_3_L2 i = true := by
  intro i hi
  have hsz : b4_3_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_4_0 : checkBlockP 16 jumps4 b4_3_goal 4 b4_3_pow 4 b4_3_L4 b4_3_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_4 : ∀ i < b4_3_L4.size, checkNodeP 16 jumps4 b4_3_goal 4 b4_3_pow 4 b4_3_L4 b4_3_L3 i = true := by
  intro i hi
  have hsz : b4_3_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_3_L2_sound : ∀ i < b4_3_L2.size, ¬ live (basicOps 16) b4_3_goal 2 (b4_3_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid (fun j hj => by simp at hj) b4_3_chk_2
theorem b4_3_L3_sound : ∀ i < b4_3_L3.size, ¬ live (basicOps 16) b4_3_goal 3 (b4_3_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid b4_3_L2_sound b4_3_chk_3
theorem b4_3_L4_sound : ∀ i < b4_3_L4.size, ¬ live (basicOps 16) b4_3_goal 4 (b4_3_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid b4_3_L3_sound b4_3_chk_4
set_option maxRecDepth 100000 in
theorem b4_3_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_3_goal ws) = [rows4] := by decide +kernel
theorem b4_3_top_match : sameSet (rows4.map (actB 16 (b4_3_pow[0]?.getD []))) (b4_3_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_3_no_build : ¬ build (basicOps 16) b4_3_goal 4 rows4.toFinset :=
  no_build_of_top b4_3_G_valid (by decide) b4_3_sublists b4_3_top_match (b4_3_L4_sound 0 (by decide))

def b4_4_goal : BitVec 16 := 0xe888
def b4_4_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_4_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_4_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_4_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_4_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_4_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_4_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_4_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_4_idx : Array (List ℕ) := Array.mk [b4_4_s0,b4_4_s1,b4_4_s2,b4_4_s3]
def b4_4_pow : Array (List ℕ) := Array.mk [b4_4_p0,b4_4_p1,b4_4_p2,b4_4_p3]
def b4_4_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_G_valid : (List.range 4).all (symValid 16 4 b4_4_idx b4_4_pow b4_4_inv b4_4_goal) = true := by decide +kernel
def b4_4_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[])
]
def b4_4_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[]),
([0xaaaa,0xcccc,0xf000,0xf0f0],[]),
([0xf0,0xaaaa,0xcccc,0xf0f0],[(0,0)])
]
def b4_4_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_2_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 2 b4_4_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_2 : ∀ i < b4_4_L2.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 2 b4_4_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_4_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_3_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 3 b4_4_L3 b4_4_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_3 : ∀ i < b4_4_L3.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 3 b4_4_L3 b4_4_L2 i = true := by
  intro i hi
  have hsz : b4_4_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_4_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_4_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 4 b4_4_L4 b4_4_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_4 : ∀ i < b4_4_L4.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 4 b4_4_L4 b4_4_L3 i = true := by
  intro i hi
  have hsz : b4_4_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_4_L2_sound : ∀ i < b4_4_L2.size, ¬ live (basicOps 16) b4_4_goal 2 (b4_4_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid (fun j hj => by simp at hj) b4_4_chk_2
theorem b4_4_L3_sound : ∀ i < b4_4_L3.size, ¬ live (basicOps 16) b4_4_goal 3 (b4_4_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid b4_4_L2_sound b4_4_chk_3
theorem b4_4_L4_sound : ∀ i < b4_4_L4.size, ¬ live (basicOps 16) b4_4_goal 4 (b4_4_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid b4_4_L3_sound b4_4_chk_4
set_option maxRecDepth 100000 in
theorem b4_4_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_4_goal ws) = [rows4] := by decide +kernel
theorem b4_4_top_match : sameSet (rows4.map (actB 16 (b4_4_pow[0]?.getD []))) (b4_4_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_4_no_build : ¬ build (basicOps 16) b4_4_goal 4 rows4.toFinset :=
  no_build_of_top b4_4_G_valid (by decide) b4_4_sublists b4_4_top_match (b4_4_L4_sound 0 (by decide))

def b4_5_goal : BitVec 16 := 0xeae8
def b4_5_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_5_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_5_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_5_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_5_idx : Array (List ℕ) := Array.mk [b4_5_s0,b4_5_s1]
def b4_5_pow : Array (List ℕ) := Array.mk [b4_5_p0,b4_5_p1]
def b4_5_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_G_valid : (List.range 2).all (symValid 16 2 b4_5_idx b4_5_pow b4_5_inv b4_5_goal) = true := by decide +kernel
def b4_5_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfaf0],[]),
([0xaaaa,0xcccc,0xf3f0],[])
]
def b4_5_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaa00,0xaaaa,0xcccc,0xf0f0],[(0,0),(1,0)]),
([0xaa,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcccc,0xf0f0,0xffcc],[]),
([0xf00,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_5_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_2_0 : checkBlockP 16 jumps4 b4_5_goal 2 b4_5_pow 2 b4_5_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_2 : ∀ i < b4_5_L2.size, checkNodeP 16 jumps4 b4_5_goal 2 b4_5_pow 2 b4_5_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_5_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_5_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_3_0 : checkBlockP 16 jumps4 b4_5_goal 2 b4_5_pow 3 b4_5_L3 b4_5_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_3 : ∀ i < b4_5_L3.size, checkNodeP 16 jumps4 b4_5_goal 2 b4_5_pow 3 b4_5_L3 b4_5_L2 i = true := by
  intro i hi
  have hsz : b4_5_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_5_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_4_0 : checkBlockP 16 jumps4 b4_5_goal 2 b4_5_pow 4 b4_5_L4 b4_5_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_4 : ∀ i < b4_5_L4.size, checkNodeP 16 jumps4 b4_5_goal 2 b4_5_pow 4 b4_5_L4 b4_5_L3 i = true := by
  intro i hi
  have hsz : b4_5_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_5_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_5_L2_sound : ∀ i < b4_5_L2.size, ¬ live (basicOps 16) b4_5_goal 2 (b4_5_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_5_G_valid (fun j hj => by simp at hj) b4_5_chk_2
theorem b4_5_L3_sound : ∀ i < b4_5_L3.size, ¬ live (basicOps 16) b4_5_goal 3 (b4_5_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_5_G_valid b4_5_L2_sound b4_5_chk_3
theorem b4_5_L4_sound : ∀ i < b4_5_L4.size, ¬ live (basicOps 16) b4_5_goal 4 (b4_5_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_5_G_valid b4_5_L3_sound b4_5_chk_4
set_option maxRecDepth 100000 in
theorem b4_5_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_5_goal ws) = [rows4] := by decide +kernel
theorem b4_5_top_match : sameSet (rows4.map (actB 16 (b4_5_pow[0]?.getD []))) (b4_5_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_5_no_build : ¬ build (basicOps 16) b4_5_goal 4 rows4.toFinset :=
  no_build_of_top b4_5_G_valid (by decide) b4_5_sublists b4_5_top_match (b4_5_L4_sound 0 (by decide))

def b4_6_goal : BitVec 16 := 0xeac8
def b4_6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_6_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_6_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_6_idx : Array (List ℕ) := Array.mk [b4_6_s0,b4_6_s1]
def b4_6_pow : Array (List ℕ) := Array.mk [b4_6_p0,b4_6_p1]
def b4_6_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_6_G_valid : (List.range 2).all (symValid 16 2 b4_6_idx b4_6_pow b4_6_inv b4_6_goal) = true := by decide +kernel
def b4_6_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_6_chk_3_0 : checkBlockP 16 jumps4 b4_6_goal 2 b4_6_pow 3 b4_6_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_6_chk_3 : ∀ i < b4_6_L3.size, checkNodeP 16 jumps4 b4_6_goal 2 b4_6_pow 3 b4_6_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_6_L3.size = 1 := by decide +kernel
  exact checkBlockP_at b4_6_chk_3_0 i (Nat.zero_le _) (by omega)
theorem b4_6_L3_sound : ∀ i < b4_6_L3.size, ¬ live (basicOps 16) b4_6_goal 3 (b4_6_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_6_G_valid (fun j hj => by simp at hj) b4_6_chk_3
set_option maxRecDepth 100000 in
theorem b4_6_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_6_goal ws) = [rows4] := by decide +kernel
theorem b4_6_top_match : sameSet (rows4.map (actB 16 (b4_6_pow[0]?.getD []))) (b4_6_L3[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_6_no_build : ¬ build (basicOps 16) b4_6_goal 3 rows4.toFinset :=
  no_build_of_top b4_6_G_valid (by decide) b4_6_sublists b4_6_top_match (b4_6_L3_sound 0 (by decide))

theorem no_build5_of_proj4 (k4 : ℕ) (base_goal : BitVec 16) (hbnz : base_goal ≠ 0)
    (hbase : ¬ build (basicOps 16) base_goal k4 rows4.toFinset)
    (goal5 : BitVec 32) (idxs4 : List ℕ) (u p0 p1 : ℕ)
    (hp0 : p0 < 32) (hp1 : p1 < 32) (hlen : idxs4.length = 16) (hlt : ∀ idx ∈ idxs4, idx < 32)
    (hpg : projS 16 idxs4 goal5 = base_goal)
    (hxu : projS 16 idxs4 (rows5.getD u 0) = 0)
    (hsub : rows5.all (fun w => projS 16 idxs4 w == 0 || rows4.contains (projS 16 idxs4 w)) = true)
    (hess : rows5.all (fun w => w == rows5.getD u 0 || w.getLsbD p0 == w.getLsbD p1) = true)
    (hdiff : goal5.getLsbD p0 ≠ goal5.getLsbD p1) :
    ¬ build (basicOps 32) goal5 (k4 + 1) rows5.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  obtain ⟨w, hw, hdw⟩ := live_separates (fun v : BitVec 32 => v.getLsbD p0 ≠ v.getLsbD p1)
    hdiff (ops_diff_ij p0 p1 hp0 hp1) hl
  have hw_eq : w = rows5.getD u 0 := by
    have h1 := List.all_eq_true.mp hess w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    exact h1.resolve_right hdw
  have hmem_z : rows5.getD u 0 ∈ s.filter (fun v => projS 16 idxs4 v = 0) :=
    Finset.mem_filter.mpr ⟨hw_eq ▸ hw, hxu⟩
  have hzc_pos : 1 ≤ zCount (projS 16 idxs4) s := Finset.one_le_card.mpr ⟨_, hmem_z⟩
  have hops32 : ∀ a b z : BitVec 32, z ∈ basicOps 32 a b → z ∈ ops 32 a b := fun a b z hz =>
    (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
  have hb16 := live_restrict (by decide : 0 < 16) idxs4 hlen hlt hops32 hpg hbnz hl
  have hsub16 : nonZeroImg (projS 16 idxs4) s ⊆ rows4.toFinset := by
    intro v hv
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hv
    obtain ⟨hne, y, hy, rfl⟩ := hv
    have h1 := List.all_eq_true.mp hsub y (List.mem_toFinset.mp (hs hy))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact hbase (build_mono_k (by omega) (build_mono_av hsub16 hb16))

def nrmM32 (m : BitVec 32) (b0 : ℕ) (u : BitVec 32) : BitVec 32 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM32 (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 32) :
    projS 16 idxs (nrmM32 m b0 u) = projS 16 idxs u := by
  unfold nrmM32
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 16 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 16 idxs m hm (~~~u), projS_not 16 (by decide) idxs hlen hlt u]

abbrev W5Node := List (BitVec 32) × List (BitVec 32 × BitVec 32 × BitVec 32) × List ℕ × List (ℕ × ℕ)

def checkReplay32 (m : BitVec 32) (b0 : ℕ) (bank : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → Bool
  | [], targets => targets.all (fun t => nrmM32 m b0 t == 0 || bank.contains (nrmM32 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 32 a b).contains v &&
    checkReplay32 m b0 (v :: bank) rest targets

theorem checkReplay32_sound (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 16)
    (steps : List (BitVec 32 × BitVec 32 × BitVec 32)) (targets : List (BitVec 32)) :
    ∀ (bank : List (BitVec 32)) (k : ℕ),
      checkReplay32 m b0 bank steps targets = true →
      build (basicOps 16) g k (nonZeroImg (projS 16 idxs) targets.toFinset) →
      build (basicOps 16) g (k + steps.length) (nonZeroImg (projS 16 idxs) bank.toFinset) := by
  let f : BitVec 32 → BitVec 16 := projS 16 idxs
  have hn : 0 < 16 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay32, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM32 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM32 m b0 t, hmem, projS_nrmM32 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay32, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 16 (f a) (f b) := projS_ops 16 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 16 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 16 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 16 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 16 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed32 (stock needed : List (BitVec 32)) (u : BitVec 32) : List (BitVec 32) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded32 (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM32 m b0 w
    let needed' := if needed.contains pw then addNeed32 stock (addNeed32 stock needed (nrmM32 m b0 a)) (nrmM32 m b0 b) else needed
    buildNeeded32 m b0 stock rest needed'

def buildSteps32 (m : BitVec 32) (b0 : ℕ) (needed : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32 × BitVec 32 × BitVec 32)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM32 m b0 w
    let pa := nrmM32 m b0 a
    let pb := nrmM32 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 32 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps32 m b0 needed rest (pw :: bank)
    else
      buildSteps32 m b0 needed rest bank

def checkCofClose32 (lb fuel : ℕ) (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM32 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeed32 stock acc (nrmM32 m b0 u)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeeded32 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildSteps32 m b0 needed hist stock
        Nat.blt (steps.length + rem) lb && checkReplay32 m b0 stock steps nxt
      else false
    else false
  else false

theorem checkCofClose32_sound_aux (goal5 : BitVec 32) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 32)) (g : BitVec 16) (hgnz : g ≠ 0)
    (hg : projS 16 idxs goal5 = g)
    (hstock : stock.all (fun w => rows4.contains (projS 16 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 16) g (lb - 1) rows4.toFinset)
    (fuel : ℕ) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32))
    (hnd : nxt.Nodup) (hchk : checkCofClose32 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 32) goal5 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose32 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops32 : ∀ a b z : BitVec 32, z ∈ basicOps 32 a b → z ∈ ops 32 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 16) idxs hlen hlt hops32 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM32 m b0 u == 0)).length ≤ zCount (projS 16 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM32 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM32 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay32_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 16 idxs) stock.toFinset ⊆ rows4.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW5 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose32 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW5 (goal5 : BitVec 32) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (a b : BitVec 32) (r : List (BitVec 32)) : Bool :=
  (ops 32 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 32 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 32 jumps5 goal5 (w :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 32 jumps5 goal5 (w :: a :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 32 jumps5 goal5 (w :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 32 jumps5 goal5 (w :: a :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW5 (goal5 : BitVec 32) (gsize : ℕ) (g5_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal5) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW5 goal5 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW5 (goal5 : BitVec 32) (gsize : ℕ) (g5_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW5_at {goal5 : BitVec 32} {gsize ncf k start m : ℕ} {g5_pow : Array (List ℕ)}
    {cfLBs cfB0s : Array ℕ} {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (h : checkBlockW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W5 {goal5 : BitVec 32} {gsize ncf k i : ℕ}
    {g5_idx g5_pow : Array (List ℕ)} {g5_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 32 gsize g5_idx g5_pow g5_inv goal5) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW5 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 32) goal5 (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (g5_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 32 (g5_pow[g5_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[g]?.getD []))).toFinset.image
        (actB 32 (g5_pow[g5_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 32 (g5_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal5 ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 32} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 32 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 32) goal5 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 32 jumps5 goal5 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW5 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 32 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW5 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact hcof c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 32 a b ▸ hz)

theorem level_sound_W5 {goal5 : BitVec 32} {gsize ncf k : ℕ}
    {g5_idx g5_pow : Array (List ℕ)} {g5_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 32 gsize g5_idx g5_pow g5_inv goal5) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W5 hk hi hvalid hcof hprev (hblk i hi)

def u0 : BitVec 32 := 0xaaaaaaaa
def u1 : BitVec 32 := 0xcccccccc
def u2 : BitVec 32 := 0xf0f0f0f0
def u3 : BitVec 32 := 0xff00ff00
def u4 : BitVec 32 := 0xffff0000
def u5 : BitVec 32 := 0xaaaa0000
def u6 : BitVec 32 := 0xfff0fff0
def u7 : BitVec 32 := 0x88888888
def u8 : BitVec 32 := 0xcc00cc
def u9 : BitVec 32 := 0xf000f000
def u10 : BitVec 32 := 0xaa00aa
def u11 : BitVec 32 := 0xc0c0c0c0
def u12 : BitVec 32 := 0xa0a0a0a0
def u13 : BitVec 32 := 0xaaaa
def u14 : BitVec 32 := 0xfafafafa
def u15 : BitVec 32 := 0xaa00aa00
def u16 : BitVec 32 := 0x44444444
def u17 : BitVec 32 := 0xcc00cc00
def u18 : BitVec 32 := 0xaaa0aaa0
def u19 : BitVec 32 := 0xf000f0
def u20 : BitVec 32 := 0x33003300
def u21 : BitVec 32 := 0x22222222
def u22 : BitVec 32 := 0x30303030
def u23 : BitVec 32 := 0xff0000
def u24 : BitVec 32 := 0xcccc0000
def u25 : BitVec 32 := 0xeeeeeeee
def u26 : BitVec 32 := 0xffaaffaa
def u27 : BitVec 32 := 0x55005500
def u28 : BitVec 32 := 0x55550000
def u29 : BitVec 32 := 0xff00ff0
def u30 : BitVec 32 := 0x33cc33cc
def u31 : BitVec 32 := 0x33330000
def u32 : BitVec 32 := 0xff000000
def u33 : BitVec 32 := 0xf0f00000
def u34 : BitVec 32 := 0xf000f00
def u35 : BitVec 32 := 0x50505050
def u36 : BitVec 32 := 0xfaf0faf0
def u37 : BitVec 32 := 0xfcfcfcfc
def u38 : BitVec 32 := 0x55aa55aa
def u39 : BitVec 32 := 0xc8c8c8c8
def u40 : BitVec 32 := 0xffa0ffa0
def u41 : BitVec 32 := 0xfafaf0f0
def u42 : BitVec 32 := 0xccc0ccc0
def u43 : BitVec 32 := 0xf0f0000
def u44 : BitVec 32 := 0x4444cccc
def u45 : BitVec 32 := 0xffccffcc
def u46 : BitVec 32 := 0xf8f8f8f8
def u47 : BitVec 32 := 0xc0c0c0c
def u48 : BitVec 32 := 0xfa00fa
def u49 : BitVec 32 := 0xa0a0a0a
def u50 : BitVec 32 := 0xcc88cc88
def u51 : BitVec 32 := 0x22aa22aa
def u52 : BitVec 32 := 0xc0f0c0f0
def u53 : BitVec 32 := 0xf3f0f3f0
def u54 : BitVec 32 := 0xf0faf0fa
def u55 : BitVec 32 := 0xee00ee
def u56 : BitVec 32 := 0x33ff0000
def u57 : BitVec 32 := 0xa000a
def u58 : BitVec 32 := 0xeaeac0c0
def u59 : BitVec 32 := 0xccc0ccc
def u60 : BitVec 32 := 0xc4c4c4c4
def u61 : BitVec 32 := 0xaaa0aaa
def u62 : BitVec 32 := 0xa8a8a8a8
def u63 : BitVec 32 := 0x50f050f0
def u64 : BitVec 32 := 0xeeeecccc
def u65 : BitVec 32 := 0xf0fcf0fc
def u66 : BitVec 32 := 0xffaaff00
def u67 : BitVec 32 := 0xff30ff30
def u68 : BitVec 32 := 0xbbbb0000
def u69 : BitVec 32 := 0xaaff0000
def u70 : BitVec 32 := 0x5050f0f0
def u71 : BitVec 32 := 0xeeee0000
def u72 : BitVec 32 := 0x5a5a5a5a
def u73 : BitVec 32 := 0x55505550
def u74 : BitVec 32 := 0xcccccc
def u75 : BitVec 32 := 0xf2f2f2f2
def u76 : BitVec 32 := 0x88aa88aa
def u77 : BitVec 32 := 0xf0fff0f0
def u78 : BitVec 32 := 0xfcf0fcf0
def u79 : BitVec 32 := 0xfff0f0f0
def u80 : BitVec 32 := 0x88cc88cc
def u81 : BitVec 32 := 0xf888f888
def u82 : BitVec 32 := 0x44cc44cc
def u83 : BitVec 32 := 0x80808080
def u84 : BitVec 32 := 0xc0ccc0cc
def u85 : BitVec 32 := 0x88880000
def u86 : BitVec 32 := 0xc0c0cccc
def u87 : BitVec 32 := 0xfaaaf000
def u88 : BitVec 32 := 0xfaa0faa0
def u89 : BitVec 32 := 0x880088
def u90 : BitVec 32 := 0xc8c8c0c0
def u91 : BitVec 32 := 0xcc44cc44
def u92 : BitVec 32 := 0xa2a2a2a2
def u93 : BitVec 32 := 0x33303330
def u94 : BitVec 32 := 0xaaf0aaf0
def u95 : BitVec 32 := 0xfcfcf0f0
def u96 : BitVec 32 := 0xa0aaa0aa
def u97 : BitVec 32 := 0xbbb0bbb0
def u98 : BitVec 32 := 0xc080c080
def u99 : BitVec 32 := 0xe0e0e0e0

def c5_0_goal : BitVec 32 := 0xeee0e8a0
def c5_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s1 : List ℕ := [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15,16,20,24,28,17,21,25,29,18,22,26,30,19,23,27,31]
def c5_0_p1 : List ℕ := [1,16,256,4096,2,32,512,8192,4,64,1024,16384,8,128,2048,32768,65536,1048576,16777216,268435456,131072,2097152,33554432,536870912,262144,4194304,67108864,1073741824,524288,8388608,134217728,2147483648]
def c5_0_idx : Array (List ℕ) := Array.mk [c5_0_s0,c5_0_s1]
def c5_0_pow : Array (List ℕ) := Array.mk [c5_0_p0,c5_0_p1]
def c5_0_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_G_valid : (List.range 2).all (symValid 32 2 c5_0_idx c5_0_pow c5_0_inv c5_0_goal) = true := by decide +kernel
def c5_0_m0 : BitVec 32 := 0x55555555
def c5_0_st0 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_0_ix0 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_0 : c5_0_ix0.length = 16 ∧ (∀ idx ∈ c5_0_ix0, idx < 32) ∧ (∀ idx ∈ c5_0_ix0, c5_0_m0.getLsbD idx = true) ∧ projS 16 c5_0_ix0 c5_0_goal = b4_2_goal ∧ c5_0_st0.all (fun w => rows4.contains (projS 16 c5_0_ix0 w)) = true := by decide +kernel
def c5_0_m1 : BitVec 32 := 0xf0f0f0f
def c5_0_st1 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_0_ix1 : List ℕ := [0,8,1,9,2,10,3,11,16,24,17,25,18,26,19,27]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_1 : c5_0_ix1.length = 16 ∧ (∀ idx ∈ c5_0_ix1, idx < 32) ∧ (∀ idx ∈ c5_0_ix1, c5_0_m1.getLsbD idx = true) ∧ projS 16 c5_0_ix1 c5_0_goal = b4_2_goal ∧ c5_0_st1.all (fun w => rows4.contains (projS 16 c5_0_ix1 w)) = true := by decide +kernel
def c5_0_m2 : BitVec 32 := 0xcccccccc
def c5_0_st2 : List (BitVec 32) := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def c5_0_ix2 : List ℕ := [2,6,10,14,3,7,11,15,18,22,26,30,19,23,27,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_2 : c5_0_ix2.length = 16 ∧ (∀ idx ∈ c5_0_ix2, idx < 32) ∧ (∀ idx ∈ c5_0_ix2, c5_0_m2.getLsbD idx = true) ∧ projS 16 c5_0_ix2 c5_0_goal = b4_3_goal ∧ c5_0_st2.all (fun w => rows4.contains (projS 16 c5_0_ix2 w)) = true := by decide +kernel
def c5_0_m3 : BitVec 32 := 0xffff
def c5_0_st3 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_0_ix3 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_3 : c5_0_ix3.length = 16 ∧ (∀ idx ∈ c5_0_ix3, idx < 32) ∧ (∀ idx ∈ c5_0_ix3, c5_0_m3.getLsbD idx = true) ∧ projS 16 c5_0_ix3 c5_0_goal = b4_4_goal ∧ c5_0_st3.all (fun w => rows4.contains (projS 16 c5_0_ix3 w)) = true := by decide +kernel
def c5_0_m4 : BitVec 32 := 0xff00ff00
def c5_0_st4 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_0_ix4 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_4 : c5_0_ix4.length = 16 ∧ (∀ idx ∈ c5_0_ix4, idx < 32) ∧ (∀ idx ∈ c5_0_ix4, c5_0_m4.getLsbD idx = true) ∧ projS 16 c5_0_ix4 c5_0_goal = b4_3_goal ∧ c5_0_st4.all (fun w => rows4.contains (projS 16 c5_0_ix4 w)) = true := by decide +kernel
def c5_0_cfMasks : Array (BitVec 32) := Array.mk [c5_0_m0,c5_0_m1,c5_0_m2,c5_0_m3,c5_0_m4]
def c5_0_cfB0s : Array ℕ := Array.mk [0,0,2,0,8]
def c5_0_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_0_st0,c5_0_st1,c5_0_st2,c5_0_st3,c5_0_st4]
def c5_0_cfLBs : Array ℕ := Array.mk [5,5,5,5,5]
theorem c5_0_cof_sound (c fuel : ℕ) (hc : c < 5) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_0_cfLBs[c]?.getD 0) fuel (c5_0_cfMasks[c]?.getD 0) (c5_0_cfB0s[c]?.getD 0) (c5_0_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_0_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix0 c5_0_cspec_0.1 c5_0_cspec_0.2.1 c5_0_m0 c5_0_cspec_0.2.2.1 0 c5_0_st0 b4_2_goal (by decide) c5_0_cspec_0.2.2.2.1 c5_0_cspec_0.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix1 c5_0_cspec_1.1 c5_0_cspec_1.2.1 c5_0_m1 c5_0_cspec_1.2.2.1 0 c5_0_st1 b4_2_goal (by decide) c5_0_cspec_1.2.2.2.1 c5_0_cspec_1.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix2 c5_0_cspec_2.1 c5_0_cspec_2.2.1 c5_0_m2 c5_0_cspec_2.2.2.1 2 c5_0_st2 b4_3_goal (by decide) c5_0_cspec_2.2.2.2.1 c5_0_cspec_2.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix3 c5_0_cspec_3.1 c5_0_cspec_3.2.1 c5_0_m3 c5_0_cspec_3.2.2.1 0 c5_0_st3 b4_4_goal (by decide) c5_0_cspec_3.2.2.2.1 c5_0_cspec_3.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix4 c5_0_cspec_4.1 c5_0_cspec_4.2.1 c5_0_m4 c5_0_cspec_4.2.2.1 8 c5_0_st4 b4_3_goal (by decide) c5_0_cspec_4.2.2.2.1 c5_0_cspec_4.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | c + 5 => omega
def c5_0_L4 : Array W5Node := Array.mk [
([u0,0xccccc8c8,u2,u3,u4],[],[],[])
]
def c5_0_L5 : Array W5Node := Array.mk [
([u0,0xafaaafaa,u1,u2,u3,u4],[],[],[]),
([0x4040404,u0,u1,u2,u3,u4],[],[],[]),
([0xc000c00,u0,u1,u2,u3,u4],[],[],[]),
([u0,0xbb00bb00,u1,u2,u3,u4],[],[],[]),
([u0,u1,u2,u3,u4,0xffff0f00],[],[],[]),
([0xf00,u0,u1,u2,u3,u4],[],[],[]),
([u47,u16,u0,u2,u3,u4],[(u16,u0,u1),(u47,u2,u1)],[0,1],[]),
([u34,u0,u17,u1,u2,u4],[(u34,u2,u3),(u17,u1,u3)],[1,2],[]),
([0xcccc,u16,u0,u2,u3,u4],[(u16,u0,u1),(0xcccc,u1,u4)],[0,3],[]),
([u0,u39,u1,u2,u3,u4],[],[],[]),
([u0,u1,u2,u3,u4,0xfffffafa],[(u14,u0,u2),(0xfffffafa,u14,u4)],[2,4],[(0,0),(1,0)]),
([0xfafa,u0,u1,u2,u3,u4],[],[],[]),
([u0,0xaeaeaeae,u1,u2,u3,u4],[(u47,u2,u1),(0xaeaeaeae,u47,u0)],[0],[]),
([u80,u0,u1,u2,u3,u4],[],[],[]),
([u0,u1,u2,u3,u4,0xffff0c0c],[],[],[]),
([0xc0c,u0,u1,u2,u3,u4],[],[],[]),
([u0,0xcccc8888,u1,u2,u3,u4],[(0xffffaaaa,u0,u4),(0xcccc8888,u1,0xffffaaaa)],[0,2],[]),
([u0,u1,u2,u3,0xffffaaaa,0xfffff0f0],[(0xffffaaaa,u0,u4),(0xfffff0f0,u2,u4)],[0,1],[]),
([0xf0f0a0a,u0,u1,u2,u3,u4],[],[],[]),
([0xcccc,u0,u1,u2,u3,0xfffff0f0],[(0xfffff0f0,u2,u4),(0xcccc,u1,u4)],[1,2],[]),
([u0,0xccccc0c0,u1,u2,u3,u4],[],[],[]),
([u0,u1,0xeeaaeeaa,u2,u3,u4],[(u17,u1,u3),(0xeeaaeeaa,u0,u17)],[0],[]),
([u0,u1,u2,u3,u4,0xffffcc00],[(u17,u1,u3),(0xffffcc00,u17,u4)],[2,3,4],[]),
([0xcc00,u0,u1,u2,u3,u4],[],[],[]),
([u0,0xaaaaeeee,u1,u2,u3,u4],[(0xcccc,u1,u4),(0xaaaaeeee,0xcccc,u0)],[0],[]),
([u0,0xaaaaffaa,u1,u2,u3,u4],[],[],[]),
([u0,0xcccc00cc,u1,u2,u3,u4],[],[],[]),
([0xcccc,0xff00,u0,u1,u2,u3],[(0xcccc,u1,u4),(0xff00,u3,u4)],[2,4],[])
]
def c5_0_L6 : Array W5Node := Array.mk [
([u34,u0,u1,u2,u3,u4],[(u34,u2,u3)],[0,1,2,3,4],[(0,0),(0,2),(0,4),(0,5),(0,7),(1,1),(1,3),(1,6),(1,8)]),
([u0,u1,u2,u14,u3,u4],[(u14,u0,u2)],[0,1,2,3,4],[(0,1),(0,9),(0,10),(0,11),(1,1),(1,9)]),
([u47,u0,u1,u2,u3,u4],[(u47,u2,u1)],[0,1,2,3,4],[(0,1),(0,2),(0,6),(0,12),(0,14),(0,15),(1,13)]),
([u0,u1,u2,u3,u4,0xffffaaaa],[(0xffffaaaa,u0,u4)],[0,1,2,3,4],[(0,10),(0,16),(0,17),(0,18),(1,5),(1,15),(1,19),(1,20)]),
([u0,u17,u1,u2,u3,u4],[(u17,u1,u3)],[0,1,2,3,4],[(0,2),(0,7),(0,21),(0,22),(0,23),(1,2),(1,7),(1,21)]),
([0xcccc,u0,u1,u2,u3,u4],[(0xcccc,u1,u4)],[0,1,2,3,4],[(0,8),(0,15),(0,19),(0,23),(0,24),(0,27),(1,5),(1,25),(1,26)])
]
def c5_0_L7 : Array W5Node := Array.mk [
([u0,u1,u2,u3,u4],[],[0,1,2,3,4],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_4 : ∀ i < c5_0_L4.size, checkNodeW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_0_L4.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_1 : checkBlockW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 16 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_5 : ∀ i < c5_0_L5.size, checkNodeW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 i = true := by
  intro i hi
  have hsz : c5_0_L5.size = 28 := by decide +kernel
  have hi' : i < 28 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_0_chk_5_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_0_chk_5_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_6 : ∀ i < c5_0_L6.size, checkNodeW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 i = true := by
  intro i hi
  have hsz : c5_0_L6.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_7 : ∀ i < c5_0_L7.size, checkNodeW5 c5_0_goal 2 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 i = true := by
  intro i hi
  have hsz : c5_0_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_0_L4_sound : ∀ i < c5_0_L4.size, ¬ live (basicOps 32) c5_0_goal 4 (c5_0_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound (fun j hj => by simp at hj) c5_0_chk_4
theorem c5_0_L5_sound : ∀ i < c5_0_L5.size, ¬ live (basicOps 32) c5_0_goal 5 (c5_0_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L4_sound c5_0_chk_5
theorem c5_0_L6_sound : ∀ i < c5_0_L6.size, ¬ live (basicOps 32) c5_0_goal 6 (c5_0_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L5_sound c5_0_chk_6
theorem c5_0_L7_sound : ∀ i < c5_0_L7.size, ¬ live (basicOps 32) c5_0_goal 7 (c5_0_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L6_sound c5_0_chk_7
set_option maxRecDepth 100000 in
theorem c5_0_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_0_goal ws) = [rows5] := by decide +kernel
theorem c5_0_top_match : sameSet (rows5.map (actB 32 (c5_0_pow[0]?.getD []))) (c5_0_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 7 rows5.toFinset :=
  no_build_of_top c5_0_G_valid (by decide) c5_0_sublists c5_0_top_match (c5_0_L7_sound 0 (by decide))

def c5_1_goal : BitVec 32 := 0xeaa8e8a8
def c5_1_idxs4 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_1_no_build : ¬ build (basicOps 32) c5_1_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_1_goal (by decide) b4_1_no_build c5_1_goal c5_1_idxs4 4 9 25 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_2_goal : BitVec 32 := 0xfeeefee8
def c5_2_idxs4 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_2_no_build : ¬ build (basicOps 32) c5_2_goal 7 rows5.toFinset :=
  no_build5_of_proj4 6 b4_0_goal (by decide) b4_0_no_build c5_2_goal c5_2_idxs4 4 1 17 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_3_goal : BitVec 32 := 0xeaa8c880
def c5_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_3_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]
def c5_3_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_3_idx : Array (List ℕ) := Array.mk [c5_3_s0,c5_3_s1]
def c5_3_pow : Array (List ℕ) := Array.mk [c5_3_p0,c5_3_p1]
def c5_3_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_G_valid : (List.range 2).all (symValid 32 2 c5_3_idx c5_3_pow c5_3_inv c5_3_goal) = true := by decide +kernel
def c5_3_m0 : BitVec 32 := 0xaaaaaaaa
def c5_3_st0 : List (BitVec 32) := [0x88888888,0xa0a0a0a0,0xaa00aa00,0xaaaa0000]
def c5_3_ix0 : List ℕ := [1,3,17,19,5,7,21,23,9,11,25,27,13,15,29,31]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_0 : c5_3_ix0.length = 16 ∧ (∀ idx ∈ c5_3_ix0, idx < 32) ∧ (∀ idx ∈ c5_3_ix0, c5_3_m0.getLsbD idx = true) ∧ projS 16 c5_3_ix0 c5_3_goal = b4_3_goal ∧ c5_3_st0.all (fun w => rows4.contains (projS 16 c5_3_ix0 w)) = true := by decide +kernel
def c5_3_m1 : BitVec 32 := 0xffff0000
def c5_3_st1 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_3_ix1 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_1 : c5_3_ix1.length = 16 ∧ (∀ idx ∈ c5_3_ix1, idx < 32) ∧ (∀ idx ∈ c5_3_ix1, c5_3_m1.getLsbD idx = true) ∧ projS 16 c5_3_ix1 c5_3_goal = b4_1_goal ∧ c5_3_st1.all (fun w => rows4.contains (projS 16 c5_3_ix1 w)) = true := by decide +kernel
def c5_3_m2 : BitVec 32 := 0xf0f0f0f
def c5_3_st2 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_3_ix2 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_2 : c5_3_ix2.length = 16 ∧ (∀ idx ∈ c5_3_ix2, idx < 32) ∧ (∀ idx ∈ c5_3_ix2, c5_3_m2.getLsbD idx = true) ∧ projS 16 c5_3_ix2 c5_3_goal = b4_2_goal ∧ c5_3_st2.all (fun w => rows4.contains (projS 16 c5_3_ix2 w)) = true := by decide +kernel
def c5_3_m3 : BitVec 32 := 0xcccccccc
def c5_3_st3 : List (BitVec 32) := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def c5_3_ix3 : List ℕ := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_3 : c5_3_ix3.length = 16 ∧ (∀ idx ∈ c5_3_ix3, idx < 32) ∧ (∀ idx ∈ c5_3_ix3, c5_3_m3.getLsbD idx = true) ∧ projS 16 c5_3_ix3 c5_3_goal = b4_5_goal ∧ c5_3_st3.all (fun w => rows4.contains (projS 16 c5_3_ix3 w)) = true := by decide +kernel
def c5_3_m4 : BitVec 32 := 0xff00ff
def c5_3_st4 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_3_ix4 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_4 : c5_3_ix4.length = 16 ∧ (∀ idx ∈ c5_3_ix4, idx < 32) ∧ (∀ idx ∈ c5_3_ix4, c5_3_m4.getLsbD idx = true) ∧ projS 16 c5_3_ix4 c5_3_goal = b4_2_goal ∧ c5_3_st4.all (fun w => rows4.contains (projS 16 c5_3_ix4 w)) = true := by decide +kernel
def c5_3_m5 : BitVec 32 := 0xffff
def c5_3_st5 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_3_ix5 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_5 : c5_3_ix5.length = 16 ∧ (∀ idx ∈ c5_3_ix5, idx < 32) ∧ (∀ idx ∈ c5_3_ix5, c5_3_m5.getLsbD idx = true) ∧ projS 16 c5_3_ix5 c5_3_goal = b4_2_goal ∧ c5_3_st5.all (fun w => rows4.contains (projS 16 c5_3_ix5 w)) = true := by decide +kernel
def c5_3_m6 : BitVec 32 := 0xf0f0f0f0
def c5_3_st6 : List (BitVec 32) := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]
def c5_3_ix6 : List ℕ := [4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_6 : c5_3_ix6.length = 16 ∧ (∀ idx ∈ c5_3_ix6, idx < 32) ∧ (∀ idx ∈ c5_3_ix6, c5_3_m6.getLsbD idx = true) ∧ projS 16 c5_3_ix6 c5_3_goal = b4_6_goal ∧ c5_3_st6.all (fun w => rows4.contains (projS 16 c5_3_ix6 w)) = true := by decide +kernel
def c5_3_m7 : BitVec 32 := 0xff00ff00
def c5_3_st7 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_3_ix7 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_7 : c5_3_ix7.length = 16 ∧ (∀ idx ∈ c5_3_ix7, idx < 32) ∧ (∀ idx ∈ c5_3_ix7, c5_3_m7.getLsbD idx = true) ∧ projS 16 c5_3_ix7 c5_3_goal = b4_6_goal ∧ c5_3_st7.all (fun w => rows4.contains (projS 16 c5_3_ix7 w)) = true := by decide +kernel
def c5_3_cfMasks : Array (BitVec 32) := Array.mk [c5_3_m0,c5_3_m1,c5_3_m2,c5_3_m3,c5_3_m4,c5_3_m5,c5_3_m6,c5_3_m7]
def c5_3_cfB0s : Array ℕ := Array.mk [1,16,0,2,0,0,4,8]
def c5_3_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_3_st0,c5_3_st1,c5_3_st2,c5_3_st3,c5_3_st4,c5_3_st5,c5_3_st6,c5_3_st7]
def c5_3_cfLBs : Array ℕ := Array.mk [5,6,5,5,5,5,4,4]
theorem c5_3_cof_sound (c fuel : ℕ) (hc : c < 8) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_3_cfLBs[c]?.getD 0) fuel (c5_3_cfMasks[c]?.getD 0) (c5_3_cfB0s[c]?.getD 0) (c5_3_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_3_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix0 c5_3_cspec_0.1 c5_3_cspec_0.2.1 c5_3_m0 c5_3_cspec_0.2.2.1 1 c5_3_st0 b4_3_goal (by decide) c5_3_cspec_0.2.2.2.1 c5_3_cspec_0.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_3_goal 6 c5_3_ix1 c5_3_cspec_1.1 c5_3_cspec_1.2.1 c5_3_m1 c5_3_cspec_1.2.2.1 16 c5_3_st1 b4_1_goal (by decide) c5_3_cspec_1.2.2.2.1 c5_3_cspec_1.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix2 c5_3_cspec_2.1 c5_3_cspec_2.2.1 c5_3_m2 c5_3_cspec_2.2.2.1 0 c5_3_st2 b4_2_goal (by decide) c5_3_cspec_2.2.2.2.1 c5_3_cspec_2.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix3 c5_3_cspec_3.1 c5_3_cspec_3.2.1 c5_3_m3 c5_3_cspec_3.2.2.1 2 c5_3_st3 b4_5_goal (by decide) c5_3_cspec_3.2.2.2.1 c5_3_cspec_3.2.2.2.2 b4_5_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix4 c5_3_cspec_4.1 c5_3_cspec_4.2.1 c5_3_m4 c5_3_cspec_4.2.2.1 0 c5_3_st4 b4_2_goal (by decide) c5_3_cspec_4.2.2.2.1 c5_3_cspec_4.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix5 c5_3_cspec_5.1 c5_3_cspec_5.2.1 c5_3_m5 c5_3_cspec_5.2.2.1 0 c5_3_st5 b4_2_goal (by decide) c5_3_cspec_5.2.2.2.1 c5_3_cspec_5.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose32_sound_aux c5_3_goal 4 c5_3_ix6 c5_3_cspec_6.1 c5_3_cspec_6.2.1 c5_3_m6 c5_3_cspec_6.2.2.1 4 c5_3_st6 b4_6_goal (by decide) c5_3_cspec_6.2.2.2.1 c5_3_cspec_6.2.2.2.2 b4_6_no_build fuel hist nxt hnd hchk
  | 7 => exact checkCofClose32_sound_aux c5_3_goal 4 c5_3_ix7 c5_3_cspec_7.1 c5_3_cspec_7.2.1 c5_3_m7 c5_3_cspec_7.2.2.1 8 c5_3_st7 b4_6_goal (by decide) c5_3_cspec_7.2.2.2.1 c5_3_cspec_7.2.2.2.2 b4_6_no_build fuel hist nxt hnd hchk
  | c + 8 => omega
def c5_3_L2 : Array W5Node := Array.mk [
([0xa55aa55a,u1,u4],[],[],[])
]
def c5_3_L3 : Array W5Node := Array.mk [
([u5,u1,0xf8f0f8f0,0xff88ff88],[],[],[]),
([0x77887788,u5,u1,u2],[],[],[]),
([u5,u1,u46,u40],[(u7,u0,u1),(u46,u7,u2),(u12,u0,u2),(u40,u12,u3),(u5,u0,u4)],[0],[]),
([u7,u5,0xcacac0c0,u3],[],[],[]),
([u5,u1,u81,u6],[(u7,u0,u1),(u5,u0,u4),(u9,u2,u3),(u81,u7,u9),(u6,u2,u3)],[0],[]),
([u7,u5,u52,u3],[],[],[]),
([u18,u1,u81,u4],[(u7,u0,u1),(u9,u2,u3),(u81,u7,u9),(u6,u2,u3),(u18,u0,u6)],[0],[]),
([u29,u0,u1,u71],[],[],[]),
([0xee00ee0,u0,u1,u4],[],[],[]),
([u0,u1,0xe00ee00e,u4],[],[],[]),
([u18,u68,u1,u9],[],[],[]),
([u5,u97,u1,u9],[(u16,u0,u1),(u5,u0,u4),(u9,u2,u3),(u6,u2,u3),(u97,u16,u6)],[0],[]),
([u38,u1,0xd0e0d0e0,u4],[],[],[]),
([0xde00de,u72,u1,u4],[],[],[]),
([u38,u1,0xf8f4f8f4,u4],[],[],[]),
([u38,0x70b070b0,u1,u4],[],[],[]),
([u38,0x77bb0000,u1,u2],[],[],[]),
([0x5a005a,0x5a005a00,u1,u4],[],[],[]),
([0x5a005a,u72,u1,u4],[],[],[]),
([0x50a050a0,u1,0xf5faf5fa,u4],[],[],[(0,0)]),
([0x50a050a0,u38,u1,u4],[],[],[]),
([0x5a005a,0xa500a500,u1,u4],[],[],[(0,0)]),
([u38,0xeeddcccc,u2,u4],[],[],[]),
([0x4488cccc,u38,u2,u4],[],[],[]),
([u38,u1,0xfaf5f0f0,u4],[],[],[]),
([0x50a0f0f0,u38,u1,u4],[],[],[]),
([u56,u72,u1,u3],[],[],[]),
([u8,u20,u72,u4],[],[],[]),
([u30,u12,u14,u4],[],[],[]),
([u12,u17,0xfac8fac8,u4],[],[],[]),
([u18,u98,u50,u4],[(u26,u0,u3),(u50,u1,u26),(u98,u50,u2),(u6,u2,u3),(u18,u0,u6)],[0],[]),
([0x37c837c8,u0,u2,u4],[],[],[]),
([0xc800c8,u18,u39,u4],[],[],[]),
([u18,u11,u50,u4],[],[],[]),
([u8,u18,u39,u4],[],[],[]),
([0x32c832c8,u0,u2,u4],[],[],[]),
([u0,0xc382c382,u3,u4],[],[],[]),
([u30,u0,u2,0xfafa0000],[],[],[]),
([u38,0xc0e0c0e0,u1,u4],[],[],[]),
([0xce00ce,u72,u1,u4],[],[],[]),
([0x33bb0000,u38,u1,u2],[],[],[]),
([u5,u0,u1,0xf00af00a],[],[],[]),
([u13,u0,u1,0xf00af00a],[],[],[]),
([u18,u5,u1,u9],[(u10,u0,u3),(u57,u10,u2),(u5,u0,u4),(u9,u2,u3),(u18,u57,u0)],[0],[]),
([u10,u5,u1,0xfa0afa0a],[],[],[]),
([u30,u0,0xafaf0000,u2],[],[],[]),
([u62,u69,u11,u3],[],[],[]),
([u18,u1,u58,u3],[],[],[]),
([u18,u5,u1,u87],[],[],[]),
([u59,u18,u5,u1],[],[],[]),
([u5,u1,u88],[],[],[]),
([u18,u5,u1,u88],[],[],[]),
([u5,u1,u88,u6],[],[],[]),
([u29,u73,u5,u1],[],[],[]),
([u18,u1,u87,u4],[],[],[]),
([u5,u1,u88,u4],[],[],[]),
([u30,u5,u0,u2],[],[],[]),
([u30,u0,0xaaee0000,u2],[],[],[]),
([u30,u0,0xbbee0000,u2],[],[],[]),
([u30,u0,0xf1f4f1f4,u4],[],[],[]),
([u30,u0,0xe0b0e0b0,u4],[],[],[]),
([u30,u0,0xeebb0000,u2],[],[],[]),
([0x30c030c0,u0,0xf3fcf3fc,u4],[],[],[]),
([u30,u0,u2,0xf3fc0000],[],[],[]),
([u30,u0,0xf3fcf0f0,u4],[],[],[]),
([u30,u0,0xc030f0f0,u4],[],[],[]),
([u29,u0,0xaaaf0000,u1],[],[],[]),
([u29,0x333f0000,u0,u1],[],[],[]),
([u93,u0,0xc00cc00c,u4],[],[],[]),
([0xaa00aa0,0xaffaaffa,u1,u4],[],[],[(0,0)]),
([u29,u0,0xcddccddc,u4],[],[],[]),
([u29,u0,0xc88cc88c,u4],[],[],[]),
([u29,u0,u1,0xfaaf0000],[],[],[]),
([0x5500550,0xa00aa00a,u1,u4],[],[],[(0,0)]),
([u29,u0,u1,0xf33f0000],[],[],[]),
([0xcc00cc0,u0,0xcffccffc,u4],[],[],[]),
([u29,u0,0xcffccccc,u4],[],[],[]),
([u29,u0,0xc00ccccc,u4],[],[],[])
]
set_option maxRecDepth 100000 in
def c5_3_L4 : Array W5Node := Array.mk [
([u82,u7,u5,u2,u3],[],[],[]),
([u0,u1,0xf8f0f8f0,0xff88ff88,u4],[],[],[(0,0)]),
([u7,u5,u1,u2,0xff80ff80],[],[],[(1,0)]),
([0x70f070f0,u7,u5,u1,u3],[],[],[]),
([0x77887788,u0,u1,u2,u4],[],[],[(0,1)]),
([u83,u5,u1,u46,u3],[(u7,u0,u1),(u83,u7,u2),(u46,u7,u2),(u5,u0,u4)],[1],[(1,0),(1,1)]),
([u0,u1,u46,u40,u4],[(u7,u0,u1),(u46,u7,u2),(u12,u0,u2),(u40,u12,u3)],[0],[(0,2)]),
([u12,u5,u1,u46,u3],[(u7,u0,u1),(u46,u7,u2),(u12,u0,u2),(u5,u0,u4)],[0],[(0,2)]),
([u7,u5,u11,u46,u3],[],[],[]),
([u7,u5,u60,u2,u3],[],[],[]),
([u89,0x77007700,u5,u1,u2],[],[],[(0,1)]),
([u7,u5,u1,u2,u40],[(u7,u0,u1),(u12,u0,u2),(u40,u12,u3),(u5,u0,u4)],[2],[(0,2)]),
([u63,u7,u5,u1,u3],[],[],[]),
([u10,u7,u5,u17,u2],[],[],[]),
([u44,u7,0xaaaa8888,u2,u3],[],[],[]),
([0x66664444,u7,u5,u2,u3],[],[],[]),
([u7,u5,0xe0e0c0c0,u3],[],[],[]),
([u22,u7,u5,u41,u3],[],[],[(0,3)]),
([u7,u5,u90,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u41,u5,u2),(u90,u1,u41)],[1],[]),
([u7,u5,u58,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2),(u58,u5,u11)],[2,3],[]),
([u7,u5,u11,u3,u6],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2),(u6,u2,u3)],[2],[]),
([u7,u1,u58,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2),(u58,u5,u11)],[3],[]),
([u7,u5,0xb8b8b8b8,u2,u3],[],[],[]),
([u7,u5,0xbaba3030,u2,u3],[],[],[]),
([u7,u5,u52,u3],[],[],[]),
([u5,u1,u2,u81,u3],[(u7,u0,u1),(u5,u0,u4),(u9,u2,u3),(u81,u7,u9)],[0],[(0,4)]),
([0x8880888,u5,u1,u2,u3],[],[],[]),
([u7,u5,u1,u9,u6],[(u7,u0,u1),(u5,u0,u4),(u9,u2,u3),(u6,u2,u3)],[2],[(0,4)]),
([0x88808880,u5,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u6,u2,u3),(0x88808880,u7,u6)],[1],[]),
([0x77707770,u5,u1,u2,u3],[],[],[]),
([u7,u5,u42,u2,u3],[],[],[]),
([u7,u5,u84,u2,u3],[],[],[]),
([u7,u5,u0,0xe0e0c0c0,u3],[],[],[]),
([u7,u0,u58,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2),(u58,u5,u11)],[2],[]),
([u7,u5,u0,u52,u3],[],[],[]),
([u7,u5,u52,u3,u4],[],[],[]),
([u7,u5,u11,u2,u3],[],[],[]),
([u22,u7,u5,u2,u3],[],[],[(1,5)]),
([u7,u0,0xc0c0eaea,u2,u3],[],[],[]),
([u13,u7,u0,u52,u3],[],[],[(0,5)]),
([u28,u7,u52,u3,u4],[],[],[(0,5)]),
([u7,u18,u11,u3,u4],[(u7,u0,u1),(u11,u1,u2),(u6,u2,u3),(u18,u0,u6)],[0,2],[]),
([u0,u1,u81,u6,u4],[(u7,u0,u1),(u9,u2,u3),(u81,u7,u9),(u6,u2,u3)],[0],[(0,4),(0,6)]),
([u7,u18,u1,u9,u4],[(u7,u0,u1),(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[2],[(0,6)]),
([u29,u7,u0,u1,u4],[],[],[]),
([u74,u0,u99,u3,u4],[],[],[]),
([u61,u1,u71,u2,u3],[],[],[]),
([u0,u1,u71,u9,u6],[(u25,u0,u1),(u71,u25,u4),(u9,u2,u3),(u6,u2,u3)],[0],[(0,7)]),
([u19,u34,u0,u1,u71],[],[],[(0,7)]),
([0xeee0eee,u0,u1,u6,u4],[],[],[(0,8)]),
([u0,u1,0xeee0eee0,u9,u4],[(u25,u0,u1),(u9,u2,u3),(u6,u2,u3),(0xeee0eee0,u25,u6)],[0],[(0,8)]),
([u29,u0,u1,u25,u4],[(u25,u0,u1),(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[1],[(0,7),(0,8),(0,9)]),
([u19,u0,u1,0xe0eee0ee,u4],[],[],[(0,9)]),
([u0,u1,u75,u40,u4],[],[],[]),
([u19,u34,u21,u16,u4],[],[],[]),
([u44,u7,u5,u2,u3],[],[],[]),
([u21,u0,u58,u2,u3],[],[],[]),
([u21,u0,0xc0c0eaea,u2,u3],[],[],[]),
([u0,u1,0xf222f222,u6,u4],[],[],[]),
([u21,0xc444c444,u2,u3,u4],[],[],[]),
([u29,u21,u0,u1,u4],[],[],[]),
([0x4f404f4,u0,u1,u3,u4],[],[],[]),
([u0,u1,u2,0xfbfbc0c0,u3],[],[],[]),
([u0,u68,u1,u9,u6],[],[],[(0,10)]),
([u18,u68,u1,u2,u3],[],[],[(0,10)]),
([u44,u1,0xeeee4444,u2,u3],[],[],[]),
([u16,u1,u58,u2,u3],[],[],[]),
([u5,u1,u2,0xf444f444,u3],[],[],[]),
([u16,u5,u1,u9,u6],[(u16,u0,u1),(u5,u0,u4),(u9,u2,u3),(u6,u2,u3)],[0],[(0,11)]),
([u5,u97,u1,u2,u3],[],[],[(0,11)]),
([0x77ff4444,u0,u1,u2,u3],[],[],[]),
([u0,u97,u1,u9,u4],[(u16,u0,u1),(u9,u2,u3),(u6,u2,u3),(u97,u16,u6)],[0],[(0,11)]),
([u16,u18,u1,u9,u4],[(u16,u0,u1),(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0],[(0,10)]),
([u29,u16,u0,u1,u4],[],[],[]),
([u16,0xa2a22222,u2,u3,u4],[],[],[]),
([u18,u5,u1,u2,u40],[(u12,u0,u2),(u40,u12,u3),(u18,u0,u40),(u5,u0,u4)],[0],[]),
([u5,u0,u1,u36,u66],[(u15,u0,u3),(u36,u15,u2),(u5,u0,u4),(u66,u5,u3)],[0],[]),
([u8,u5,u0,u1,u36],[(u15,u0,u3),(u36,u15,u2),(u5,u0,u4),(u8,u1,u3)],[0],[]),
([u19,u5,u0,u1,u36],[(u15,u0,u3),(u36,u15,u2),(u5,u0,u4),(u19,u3,u36)],[0],[]),
([u0,u1,u36,u66,u4],[],[],[]),
([u13,u8,u0,u1,u36],[],[],[]),
([u13,u19,u0,u1,u36],[],[],[]),
([u0,u1,0xf3a0f3a0,u40,u4],[],[],[]),
([u8,u0,0xc8c0c8c0,u36,u4],[],[],[]),
([u8,0x32303230,u0,u36,u4],[],[],[]),
([0x337f0000,u0,u1,u2,u40],[],[],[]),
([u0,u1,u53,u40,u4],[],[],[]),
([u0,u1,0xf3f3f0f0,u40,u4],[],[],[]),
([u0,u84,u1,u40,u4],[],[],[]),
([u12,u5,u1,u36,u3],[(u15,u0,u3),(u36,u15,u2),(u12,u0,u2),(u5,u0,u4)],[0],[]),
([u18,u5,u1,u2,u3],[(u15,u0,u3),(u36,u15,u2),(u18,u0,u36),(u5,u0,u4)],[2],[]),
([u56,u0,u1,u2,u40],[],[],[]),
([u0,u1,u2,0xfa30fa30,u4],[],[],[]),
([0x44884488,u38,u1,u2,u4],[],[],[]),
([u38,u1,0xddeeddee,u2,u4],[],[],[(0,12),(1,13)]),
([0x11221122,u38,u1,u2,u4],[],[],[]),
([u38,0x88448844,u1,u2,u4],[(u15,u0,u3),(u26,u0,u3),(u38,u15,u26),(0x88448844,u38,u1)],[1],[(0,14),(0,15),(0,16)]),
([0x50a050a0,u38,u1,u4],[],[],[(1,17),(1,18)]),
([0x50a050a0,u38,u1,u2,u4],[],[],[(0,19),(1,17)]),
([u38,u1,u2,0xf5faf5fa,u4],[],[],[(0,19),(1,18)]),
([0x5a005a,u72,u1,u4],[],[],[(0,17),(1,20)]),
([0x5a005a,u72,u1,u3,u4],[],[],[(0,17),(0,21)]),
([u38,0xa050a050,u1,u2,u4],[],[],[(0,20),(1,21)]),
([0x55aa0000,u38,u1,u2,u4],[],[],[]),
([u38,0xaa550000,u1,u2,u4],[],[],[(0,22),(0,23),(0,24),(0,25)]),
([u38,u11,u1,u2,u4],[(u15,u0,u3),(u26,u0,u3),(u38,u15,u26),(u11,u1,u2)],[1],[(1,26)]),
([u38,u1,u2,u37,u4],[],[],[]),
([u8,u72,u1,u3,u4],[],[],[(0,27)]),
([u22,u38,u1,u2,u4],[],[],[]),
([u38,u24,u1,u2,u4],[(u15,u0,u3),(u26,u0,u3),(u38,u15,u26),(u24,u1,u4)],[1],[]),
([u31,u38,u1,u2,u4],[(u15,u0,u3),(u26,u0,u3),(u38,u15,u26),(u31,u1,u4)],[1],[]),
([u38,u1,u33,u2,u4],[(u15,u0,u3),(u26,u0,u3),(u38,u15,u26),(u33,u2,u4)],[1],[]),
([u23,u72,u1,u3,u4],[(u12,u0,u2),(u14,u0,u2),(u72,u12,u14),(u23,u3,u4)],[1],[]),
([u1,0xeac0eac0,u2,u26,u4],[],[],[]),
([u56,u12,u1,u14,u3],[],[],[(0,26)]),
([u12,u17,u14,u45,u4],[],[],[(0,28),(0,29)]),
([u12,u1,0xfac8fac8,u3,u4],[],[],[(0,29)]),
([u8,u20,u12,u14,u4],[],[],[(0,27),(0,28)]),
([0x505a505a,u0,u1,u3,u4],[(u12,u0,u2),(u10,u0,u3),(u54,u10,u2),(0x505a505a,u12,u54)],[0],[]),
([u5,u0,u94,u1,u2],[(u15,u0,u3),(u5,u0,u4),(u19,u3,u2),(u94,u19,u15)],[0],[]),
([u13,u0,u94,u1,u2],[],[],[]),
([u12,0xaa88aa88,u17,u2,u4],[],[],[]),
([u30,u12,u0,u2,u4],[],[],[(0,28)]),
([u8,u0,0xafa0afa0,u1,u4],[],[],[]),
([u51,u39,u2,u3,u4],[],[],[]),
([0x37ff0000,u0,u39,u2,u3],[],[],[]),
([u0,u98,u50,u6,u4],[(u26,u0,u3),(u50,u1,u26),(u98,u50,u2),(u6,u2,u3)],[0],[(0,30)]),
([u0,u98,0xfcf8fcf8,u3,u4],[],[],[]),
([0xc800c8,0x37003700,u0,u2,u4],[],[],[(0,31)]),
([0xc800c8,u0,u39,u6,u4],[],[],[(0,32)]),
([u18,u39,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u6,u2,u3),(u18,u0,u6)],[0],[(0,32),(1,30)]),
([u56,u0,u39,u2,u3],[],[],[]),
([u0,u11,u50,u6,u4],[],[],[(0,33)]),
([u8,u0,u39,u6,u4],[],[],[(0,34)]),
([u18,u39,u1,u3,u4],[],[],[(0,34),(1,33)]),
([0x32fa32fa,u0,u2,u45,u4],[],[],[(0,35)]),
([u0,0xc080ffaa,u1,u2,u3],[],[],[]),
([u48,u56,u0,u1,u2],[],[],[]),
([u18,u11,u1,u26,u4],[(u26,u0,u3),(u11,u1,u2),(u6,u2,u3),(u18,u0,u6)],[0],[(0,33)]),
([u0,u1,u2,0xfefacc00,u3],[],[],[]),
([u0,u11,0xfca8fca8,u3,u4],[],[],[]),
([u0,u11,u37,u3,0xffaa0000],[],[],[]),
([u22,u0,0xf3a2f3a2,u3,u4],[],[],[]),
([u0,u1,0xf3a2f3a2,u6,u4],[],[],[]),
([u30,u0,u2,u14,u4],[(u14,u0,u2),(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1],[(0,28),(0,35),(0,37),(1,36)]),
([u8,u0,0xc8fac8fa,u2,u4],[],[],[(1,36)]),
([u8,u20,u0,u2,0xfafa0000],[],[],[(0,37)]),
([u8,u18,u1,u14,u4],[],[],[(0,34)]),
([0x505a505a,u18,u1,u3,u4],[(u14,u0,u2),(u6,u2,u3),(u18,u0,u6),(0x505a505a,u18,u14)],[0],[]),
([u48,0x33fb0000,u0,u1,u2],[],[],[]),
([u38,u1,0xcceeccee,u2,u4],[],[],[(0,38),(1,39)]),
([u10,u27,0xc0e0c0e0,u1,u4],[],[],[(0,38)]),
([u10,0xc0e0c0e,u27,u1,u4],[],[],[(1,39)]),
([u0,u1,0xeeeec4c4,u2,u3],[],[],[]),
([u0,0xc4c4eeee,u1,u2,u3],[],[],[]),
([0xaaaa8080,u60,u1,u2,u3],[],[],[]),
([u38,u91,u1,u2,u4],[(u10,u0,u3),(u91,u10,u1),(u27,u0,u3),(u38,u10,u27)],[1],[(0,40)]),
([u10,0x33bb0000,u27,u1,u2],[],[],[(0,40)]),
([u19,u5,u0,u1,u54],[],[],[(0,41)]),
([u13,u19,u0,u1,u54],[],[],[(0,42)]),
([0x30fa30fa,u0,u1,u2,u4],[],[],[]),
([u0,u1,0xf00af00a,u4],[],[],[(0,41),(0,42)]),
([u38,u1,u2,u54,u4],[],[],[]),
([u57,u5,u0,u1,u9],[(u10,u0,u3),(u57,u10,u2),(u5,u0,u4),(u9,u2,u3)],[0],[(0,41),(0,43)]),
([u13,u57,u0,u1,u9],[],[],[(0,42)]),
([u18,u0,u1,u9,u4],[(u10,u0,u3),(u57,u10,u2),(u9,u2,u3),(u18,u57,u0)],[0],[(0,43)]),
([u57,u59,u0,u1,u4],[],[],[]),
([u38,u1,0xf050f050,u2,u4],[],[],[]),
([u38,u1,u2,0xff550000,u4],[],[],[]),
([u10,u49,u5,u1,u9],[],[],[(0,44),(1,44)]),
([u10,u0,u1,0xfa0afa0a,u4],[],[],[(0,44)]),
([u10,0x50a050a0,u38,u1,u4],[],[],[]),
([0x5a005a,u49,u72,u1,u4],[],[],[]),
([u10,0x3f3f0000,u27,u1,u2],[],[],[(1,26)]),
([u10,u47,u22,u27,u4],[],[],[]),
([u10,u0,u1,0xeeaacc00,u2],[(u10,u0,u3),(u5,u0,u4),(u17,u1,u3),(0xeeaacc00,u5,u17)],[3],[]),
([u5,u0,u1,0xf0aaf0aa,u2],[],[],[(1,44)]),
([u10,u0,0xcc00eeaa,u1,u2],[],[],[]),
([u13,u0,u1,0xf0aaf0aa,u2],[],[],[]),
([u80,u0,u11,u6,u4],[],[],[]),
([u0,u1,0xeaffc0c0,u2,u3],[],[],[]),
([u62,u69,u1,u2,u3],[],[],[]),
([u8,u20,u0,0xafaf0000,u2],[],[],[(0,45)]),
([u0,u69,u1,u2,u67],[],[],[]),
([u0,0xaac0aac0,u1,u2,u4],[],[],[]),
([0x73ff5050,u0,u1,u2,u3],[],[],[]),
([0xa8fca8fc,u0,u11,u3,u4],[],[],[]),
([u0,u69,u11,u37,u3],[],[],[]),
([u35,0xaa88aa88,u17,u2,u4],[],[],[(1,46)]),
([u30,u35,u0,u2,u4],[(u35,u0,u2),(u17,u1,u3),(u45,u1,u3),(u30,u17,u45)],[1],[(0,45)]),
([u0,u94,u11,u1,u4],[],[],[]),
([u0,u90,u64,u2,u3],[(u5,u0,u4),(u64,u5,u1),(u41,u5,u2),(u90,u1,u41)],[1,3],[]),
([u0,u1,u58,u2,u3],[],[],[]),
([0xa0a0a8a8,u5,u1,u2,u3],[],[],[]),
([u44,u62,u5,u2,u3],[],[],[]),
([u62,u5,u1,u41,u3],[(u5,u0,u4),(u41,u5,u2),(u37,u1,u2),(u62,u0,u37)],[3],[]),
([u5,u0,u90,u37,u3],[],[],[]),
([u76,u5,u1,u2,u66],[],[],[]),
([u5,u0,0xcacac0c0,u1,u3],[],[],[(0,3)]),
([u5,u0,u1,u53,u66],[],[],[]),
([u18,u5,u1,u2,u66],[(u5,u0,u4),(u66,u5,u3),(u6,u3,u2),(u18,u0,u6)],[2],[]),
([u5,u0,0xccc8ccc0,u2,u3],[],[],[]),
([0xa0a0aaa0,u5,u1,u2,u3],[],[],[]),
([u5,u0,0xaacc00cc,u1,u2],[],[],[]),
([u70,u62,u5,u1,u3],[],[],[]),
([u70,u18,u5,u1,u3],[(u5,u0,u4),(u70,u5,u2),(u6,u2,u3),(u18,u0,u6)],[2],[]),
([u0,u1,u58,u3,u6],[],[],[(0,47)]),
([0xa8a0a8a0,u5,u1,u2,u3],[],[],[]),
([u18,u5,u11,u1,u3],[(u5,u0,u4),(u11,u1,u2),(u6,u2,u3),(u18,u0,u6)],[2],[(0,47)]),
([0xaaa2aaa2,u5,u1,u2,u3],[],[],[]),
([u30,u5,u0,u2],[(u5,u0,u4),(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1],[]),
([u8,u30,u5,u0,u2],[],[],[]),
([u8,u18,u5,u1,u2],[(u5,u0,u4),(u8,u1,u3),(u6,u2,u3),(u18,u0,u6)],[2],[]),
([u5,u0,u1,u87,u6],[(u5,u0,u4),(u9,u2,u3),(u87,u5,u9),(u6,u2,u3)],[0],[(0,48)]),
([u5,0xc444c444,u1,u2,u3],[],[],[]),
([u59,u5,u0,u1,u6],[(u5,u0,u4),(u9,u2,u3),(u59,u1,u9),(u6,u2,u3)],[0],[(0,49)]),
([u18,u5,u1,u9],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0,2],[(0,48),(0,49),(0,50),(0,51)]),
([u18,u5,u0,u1,u9],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0],[]),
([u18,u5,u1,u9,u6],[],[],[(0,52)]),
([u73,u5,u1,u9,u6],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3),(u73,u0,u6)],[0],[(0,43),(0,53)]),
([u29,u5,u0,u1,u6],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[0],[(0,53)]),
([0x444c444c,u5,u1,u2,u3],[],[],[]),
([u0,u1,0xeeeaccc0,u2,u3],[(u5,u0,u4),(u6,u2,u3),(u42,u1,u6),(0xeeeaccc0,u5,u42)],[1],[]),
([u0,0xcacac0c0,u1,u3,u4],[],[],[]),
([u0,u1,u53,u66,u4],[],[],[]),
([u30,u5,u0,u2,u4],[(u5,u0,u4),(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1],[]),
([u0,u1,u87,u6,u4],[],[],[(0,54)]),
([u18,u5,u1,u9,u4],[],[],[(0,54),(0,55)]),
([u29,u5,u0,u1,u4],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[1],[]),
([u62,u5,u1,u2,u3],[],[],[]),
([u76,u5,u1,u2,u3],[],[],[]),
([u5,u0,u1,u2,u67],[],[],[]),
([u5,u0,u52,u1,u3],[],[],[(0,5)]),
([u8,u20,u5,u0,u2],[],[],[(0,56)]),
([u61,u5,u1,u2,u3],[],[],[]),
([u5,u0,u1,u9,u6],[(u13,u0,u4),(u5,u13,u0),(u9,u2,u3),(u6,u2,u3)],[0],[(0,43)]),
([u0,0xc0c0eaea,u1,u3,u6],[],[],[]),
([u13,u30,u0,u2],[(u13,u0,u4),(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1],[(0,56)]),
([u13,u8,u30,u0,u2],[],[],[]),
([u13,u59,u0,u1,u6],[],[],[]),
([u13,u18,u0,u1,u9],[(u13,u0,u4),(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0],[(0,43)]),
([u13,u29,u0,u1,u6],[],[],[]),
([u0,0xccc0eeea,u1,u2,u3],[],[],[]),
([0x8888cccc,u0,u52,u3,u4],[],[],[]),
([u30,u28,u0,u2,u4],[(u28,u0,u4),(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1],[(0,56)]),
([0xaaa0fff0,u0,u1,u9,u4],[(u28,u0,u4),(u9,u2,u3),(u6,u2,u3),(0xaaa0fff0,u28,u6)],[0],[]),
([u28,u18,u1,u9,u4],[(u28,u0,u4),(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0],[(0,43)]),
([u29,u28,u0,u1,u4],[(u28,u0,u4),(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[1],[]),
([u51,0x8800aaaa,u1,u2,u3],[],[],[]),
([u51,0xaaaa8800,u1,u2,u3],[],[],[]),
([u0,u1,u2,0xf3ffc0c0,u3],[],[],[]),
([u0,u1,0xeae0eae0,u3,u4],[(u11,u1,u2),(u6,u2,u3),(u18,u0,u6),(0xeae0eae0,u18,u11)],[0],[]),
([u8,u20,u0,0xaaee0000,u2],[],[],[(0,57)]),
([u30,u0,0xaaeeaaee,u2,u4],[(u8,u1,u3),(0xaaeeaaee,u8,u0),(u20,u1,u3),(u30,u8,u20)],[1],[(0,57)]),
([u30,0xaa22aa22,u0,u2,u4],[],[],[]),
([u30,u0,u2,u65,u4],[],[],[]),
([u30,u0,0xf030f030,u2,u4],[],[],[]),
([u30,u0,u2,0xff330000,u4],[],[],[]),
([0x22882288,u30,u0,u2,u4],[],[],[]),
([u30,u0,0xbbeebbee,u2,u4],[(u8,u1,u3),(u20,u1,u3),(u30,u8,u20),(0xbbeebbee,u30,u0)],[1],[(0,58)]),
([0x11441144,u30,u0,u2,u4],[(u8,u1,u3),(u20,u1,u3),(u30,u8,u20),(0x11441144,u30,u0)],[1],[(0,59),(0,60),(0,61)]),
([u30,0x88228822,u0,u2,u4],[],[],[]),
([0x30c030c0,u30,u0,u2,u4],[],[],[(0,62)]),
([u30,u0,u2,0xf3fcf3fc,u4],[(u8,u1,u3),(u20,u1,u3),(u30,u8,u20),(0xf3fcf3fc,u30,u2)],[1],[(0,62),(0,63)]),
([0x3c003c,0x3c3c3c3c,u0,u3,u4],[],[],[]),
([u30,u0,0xc030c030,u2,u4],[],[],[]),
([0x33cc0000,u30,u0,u2,u4],[],[],[(0,64),(0,65)]),
([u30,u0,0xcc330000,u2,u4],[],[],[]),
([u10,0x3c3c3c3c,u0,u3,u4],[],[],[]),
([u30,u0,u33,u2,u4],[],[],[]),
([u23,0x3c3c3c3c,u0,u3,u4],[],[],[]),
([0xa0eea0ee,u0,u1,u2,u4],[],[],[]),
([u0,0xaaef0000,u1,u2,u67],[],[],[]),
([u0,0xc0cfc0c0,u1,u3,u4],[],[],[]),
([0x3330fff0,u0,u1,u9,u4],[],[],[]),
([u29,u0,u24,u1,u4],[],[],[]),
([u0,u1,0xf333f000,u6,u4],[],[],[]),
([u29,u31,u0,u1,u4],[(u31,u1,u4),(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[1],[]),
([0xcc00cc0,u0,u1,u6,u4],[],[],[]),
([u0,u1,0xf330f330,u6,u4],[],[],[]),
([u59,u18,u0,u1,u4],[(u9,u2,u3),(u59,u1,u9),(u6,u2,u3),(u18,u0,u6)],[0],[(0,49)]),
([u59,u0,u42,u6,u4],[],[],[]),
([u59,u93,u0,u6,u4],[],[],[]),
([u0,u1,u88,u4],[(u9,u2,u3),(u6,u2,u3),(u18,u0,u6),(u88,u18,u9)],[0],[(0,50),(0,55)]),
([u18,u0,u1,u88,u4],[(u9,u2,u3),(u6,u2,u3),(u18,u0,u6),(u88,u18,u9)],[0],[(0,51)]),
([u0,u1,u88,u6,u4],[],[],[(0,52)]),
([u29,u18,u0,u1,u4],[(u9,u2,u3),(u6,u2,u3),(u18,u0,u6),(u29,u9,u6)],[0,2],[]),
([u0,0xaaaf0000,u1,u9,u6],[(u9,u2,u3),(u6,u2,u3),(u73,u0,u6),(0xaaaf0000,u73,u4)],[0],[(0,66)]),
([u29,u73,u0,u1,u4],[],[],[(0,53),(0,66)]),
([0x333f0000,u0,u1,u9,u6],[],[],[(0,67)]),
([u29,u0,u42,u1,u4],[],[],[(0,67)]),
([u29,u93,u0,u1,u4],[(u9,u2,u3),(u6,u2,u3),(u93,u1,u6),(u29,u9,u6)],[2],[(0,68)]),
([0xaa00aa0,u29,u0,u1,u4],[],[],[(0,69)]),
([u29,u0,0xaffaaffa,u1,u4],[],[],[(0,69)]),
([0x5500550,u29,u0,u1,u4],[(u9,u2,u3),(u6,u2,u3),(u29,u9,u6),(0x5500550,u29,u0)],[1],[(0,70),(0,71),(0,72),(0,73)]),
([u29,0xa00aa00a,u0,u1,u4],[],[],[(0,73)]),
([0xcc00cc0,u29,u0,u1,u4],[(u9,u2,u3),(u6,u2,u3),(u29,u9,u6),(0xcc00cc0,u29,u1)],[1],[(0,74),(0,75)]),
([u29,u0,u1,0xcffccffc,u4],[],[],[(0,75)]),
([0x3300330,u29,u0,u1,u4],[],[],[]),
([u29,u0,0xc00cc00c,u1,u4],[],[],[]),
([0xff00000,u29,u0,u1,u4],[(u9,u2,u3),(u6,u2,u3),(u29,u9,u6),(0xff00000,u29,u4)],[1],[(0,76),(0,77)]),
([u29,u0,u1,0xf00f0000,u4],[],[],[]),
([u0,0xc00cc00c,u1,u6,u4],[(u9,u2,u3),(u6,u2,u3),(u29,u9,u6),(0xc00cc00c,u29,u1)],[2],[(0,68)]),
([u29,u0,u1,0xfff00000,u4],[],[],[]),
([0xaaaa8880,u42,u1,u2,u3],[],[],[])
]
set_option maxRecDepth 100000 in
def c5_3_L5 : Array W5Node := Array.mk [
([u51,u7,u1,u2,u3,u4],[(u7,u0,u1),(0x88008800,u7,u3),(u51,0x88008800,u0)],[1,4,5],[]),
([u82,u7,u0,u2,u3,u4],[(u7,u0,u1),(0x88008800,u7,u3),(u82,0x88008800,u1)],[1,4],[(0,0)]),
([u7,u0,u1,u2,0xff80ff80,u4],[(u7,u0,u1),(u83,u7,u2),(0xff80ff80,u83,u3)],[2],[(0,2),(1,1)]),
([0x70f070f0,u7,u0,u1,u3,u4],[],[],[(0,3)]),
([0x77ff0000,u7,u0,u1,u2,u3],[(u7,u0,u1),(0x88008800,u7,u3),(0x77ff0000,0x88008800,u4)],[5],[]),
([u83,u0,u1,u46,u3,u4],[(u7,u0,u1),(u83,u7,u2),(u46,u7,u2)],[1],[(0,5),(1,1),(1,4)]),
([u83,u7,u5,u1,u2,u3],[(u7,u0,u1),(u83,u7,u2),(u5,u0,u4)],[1,5],[(0,2),(0,5),(1,0),(1,3)]),
([u12,u0,u1,u46,u3,u4],[(u7,u0,u1),(u46,u7,u2),(u12,u0,u2)],[0],[(0,6),(0,7)]),
([u5,u0,u1,u2,u46,u3],[(u7,u0,u1),(u46,u7,u2),(u5,u0,u4)],[0,3],[(0,7)]),
([u13,u0,u1,u2,u46,u3],[(u7,u0,u1),(u46,u7,u2),(u13,u0,u4)],[0],[]),
([u0,u11,u1,u46,u3,u4],[(u7,u0,u1),(u46,u7,u2),(u11,u1,u2)],[1],[]),
([u19,u0,u1,u46,u3,u4],[(u7,u0,u1),(u46,u7,u2),(u19,u2,u3)],[0],[]),
([u7,u5,u1,u2,u46,u3],[(u7,u0,u1),(u46,u7,u2),(u5,u0,u4)],[0,3],[(0,5),(0,8)]),
([u7,u0,u11,u46,u3,u4],[],[],[(0,8)]),
([u92,u0,u1,u2,u3,u4],[],[],[]),
([u0,u60,u1,u2,u3,u4],[(u7,u0,u1),(0x8080808,u7,u2),(u60,0x8080808,u1)],[1,5],[]),
([u89,u5,u0,u1,u2,u3],[],[],[]),
([u13,u89,u0,u1,u2,u3],[],[],[]),
([u7,u92,u1,u2,u3,u4],[(u7,u0,u1),(0x8080808,u7,u2),(u92,0x8080808,u0)],[1,6],[]),
([u7,u0,u60,u2,u3,u4],[(u7,u0,u1),(0x8080808,u7,u2),(u60,0x8080808,u1)],[1],[(0,9)]),
([u89,0x77007700,u0,u1,u2,u4],[],[],[(0,4),(0,10)]),
([u89,u7,u5,u1,u2,u3],[],[],[(0,10),(1,9)]),
([0x70707070,u7,u5,u1,u2,u3],[(u7,u0,u1),(0x70707070,u7,u2),(u5,u0,u4)],[0,2,3],[(1,10)]),
([0x2222aaaa,u7,u1,u2,u3,u4],[(u7,u0,u1),(u85,u7,u4),(0x2222aaaa,u85,u0)],[1,5],[]),
([u44,u7,u0,u2,u3,u4],[(u7,u0,u1),(u85,u7,u4),(u44,u85,u1)],[1,5],[]),
([u7,u0,u1,u2,0xff88ff00,u4],[(u7,u0,u1),(u85,u7,u4),(0xff88ff00,u85,u3)],[1,5],[]),
([0x7070f0f0,u7,u0,u1,u3,u4],[(u7,u0,u1),(u85,u7,u4),(0x7070f0f0,u85,u2)],[5],[]),
([u7,u0,u1,u2,u40,u4],[(u7,u0,u1),(u12,u0,u2),(u40,u12,u3)],[2],[(0,6),(0,11)]),
([u63,u7,u0,u1,u3,u4],[],[],[(0,12)]),
([u7,u12,u5,u1,u2,u3],[(u7,u0,u1),(u12,u0,u2),(u5,u0,u4)],[2,3],[(0,7),(0,11),(1,0),(1,12)]),
([u10,u7,u5,u1,u2,u3],[(u7,u0,u1),(u10,u0,u3),(u5,u0,u4)],[3,4],[(0,13),(1,9)]),
([u10,u7,u0,u17,u2,u4],[(u7,u0,u1),(u10,u0,u3),(u17,u1,u3)],[0,3],[(0,13)]),
([u7,u5,0xaaaa8888,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(0xaaaa8888,u7,u5)],[0,1,3],[(0,14)]),
([u7,u5,u64,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u64,u5,u1)],[2,3,4,5],[(0,15),(0,16),(1,16)]),
([u44,u7,u5,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u44,u5,u1)],[0,1,2,3,4],[(0,14)]),
([u44,u7,u5,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u44,u5,u1)],[0,1,3],[]),
([u7,u5,u1,u2,u41,u3],[(u7,u0,u1),(u5,u0,u4),(u41,u5,u2)],[1,3,5],[(0,17),(0,18)]),
([u70,u7,u5,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u70,u5,u2)],[2,3,5],[]),
([u7,u5,u11,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2)],[0,2,3,4,5],[(0,8),(0,19),(0,20)]),
([u7,u5,u11,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2)],[3,5],[(0,21)]),
([u8,u7,u5,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u8,u1,u3)],[3,4],[]),
([u22,u7,u5,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u22,u1,u2)],[2,3,4],[(0,17),(0,22),(0,23),(1,24)]),
([u7,u5,u1,u9,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u9,u2,u3)],[2,3],[(0,25),(0,26),(0,27)]),
([u7,u5,u1,u2,u3,u6],[(u7,u0,u1),(u5,u0,u4),(u6,u2,u3)],[3],[(0,20),(0,27),(0,28),(0,29),(0,30),(1,20)]),
([u19,u7,u5,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u19,u2,u3)],[2,3],[(1,31)]),
([u7,u5,u0,u64,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u64,u5,u1)],[0,3],[(0,32),(1,32)]),
([u44,u7,u5,u0,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u44,u5,u1)],[0,1,3],[]),
([u7,u5,u0,u11,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2)],[0,2],[(0,33),(1,13)]),
([u22,u7,u5,u0,u2,u3],[(u7,u0,u1),(u5,u0,u4),(u22,u1,u2)],[0],[(1,34)]),
([u7,u5,u11,u2,u3,u4],[(u7,u0,u1),(u5,u0,u4),(u11,u1,u2)],[2,5],[]),
([u22,u7,u5,u2,u3,u4],[],[],[(1,35)]),
([u7,u5,u1,u2,u3],[(u7,u0,u1),(u13,u0,u4),(u5,u13,u0)],[0,1,5],[(0,36),(0,37),(1,36),(1,37)]),
([u13,u7,u0,u11,u2,u3],[(u7,u0,u1),(u13,u0,u4),(u11,u1,u2)],[0],[(0,36),(0,38)]),
([u13,u22,u7,u0,u2,u3],[],[],[(0,37),(1,39)]),
([u7,u1,0xdddd8888,u2,u3,u4],[(u7,u0,u1),(u28,u0,u4),(0xdddd8888,u28,u7)],[0],[]),
([u28,u7,u11,u2,u3,u4],[],[],[(0,36)]),
([u22,u28,u7,u2,u3,u4],[],[],[(0,37),(1,40)]),
([u7,u0,u11,u3,u6,u4],[(u7,u0,u1),(u11,u1,u2),(u6,u2,u3)],[0,2],[(0,20),(0,41)]),
([u23,u7,u0,u17,u2,u4],[(u7,u0,u1),(u17,u1,u3),(u23,u3,u4)],[5],[]),
([u56,u7,u0,u1,u2,u3],[(u7,u0,u1),(u17,u1,u3),(u56,u17,u4)],[5],[]),
([u7,u0,0xb8b8b8b8,u2,u3,u4],[(u7,u0,u1),(u22,u1,u2),(0xb8b8b8b8,u22,u7)],[3],[(0,22)]),
([u7,u0,u52,u3,u4],[(u7,u0,u1),(u20,u1,u3),(u52,u20,u2)],[3],[(0,24),(0,34),(0,35),(0,39),(0,40)]),
([u0,u1,u2,u81,u3,u4],[(u7,u0,u1),(u9,u2,u3),(u81,u7,u9)],[0],[(0,25),(0,42)]),
([0x8880888,u0,u1,u2,u3,u4],[],[],[(0,26)]),
([u7,u0,u1,u9,u6,u4],[(u7,u0,u1),(u9,u2,u3),(u6,u2,u3)],[2],[(0,27),(0,42),(0,43),(0,44)]),
([0x88808880,u0,u1,u2,u3,u4],[(u7,u0,u1),(u6,u2,u3),(0x88808880,u7,u6)],[1,2,4,5],[(0,28)]),
([0x77707770,u0,u1,u2,u3,u4],[],[],[(0,29)]),
([u7,u18,u1,u2,u3,u4],[(u7,u0,u1),(u6,u2,u3),(u18,u0,u6)],[3,6,7],[(0,41),(0,43),(1,41)]),
([u7,u0,u42,u2,u3,u4],[(u7,u0,u1),(u6,u2,u3),(u42,u1,u6)],[0,6,7],[(0,30)]),
([0x88f888f8,u0,u1,u2,u3,u4],[(u7,u0,u1),(u19,u2,u3),(0x88f888f8,u19,u7)],[2],[]),
([0x80888088,u0,u1,u2,u3,u4],[(u7,u0,u1),(u34,u3,u2),(0x80888088,u34,u7)],[2],[]),
([u7,u0,u84,u2,u3,u4],[(u7,u0,u1),(u34,u3,u2),(u84,u34,u1)],[0,4],[(0,31)]),
([u19,u34,u7,u0,u1,u4],[],[],[(0,44)]),
([u0,u1,u2,0xf8f88888,u3,u4],[(u7,u0,u1),(u33,u2,u4),(0xf8f88888,u7,u33)],[1,2,5],[]),
([0x888888,u0,u1,u2,u3,u4],[(u7,u0,u1),(u32,u3,u4),(0x888888,u7,u32)],[5],[]),
([0x88ff8888,u0,u1,u2,u3,u4],[(u7,u0,u1),(u23,u3,u4),(0x88ff8888,u23,u7)],[5],[]),
([0x80808888,u0,u1,u2,u3,u4],[(u7,u0,u1),(u43,u2,u4),(0x80808888,u43,u7)],[2,5],[]),
([u7,u0,u86,u2,u3,u4],[(u7,u0,u1),(u43,u2,u4),(u86,u43,u1)],[0,5],[]),
([u0,u1,u99,u32,u3,u4],[(u25,u0,u1),(u99,u25,u2),(u32,u3,u4)],[3],[(0,45)]),
([u23,u0,u1,u99,u3,u4],[(u25,u0,u1),(u99,u25,u2),(u23,u3,u4)],[1],[]),
([u55,u0,u1,u2,0xf0fef0fe,u4],[(u25,u0,u1),(u55,u25,u3),(0xf0fef0fe,u55,u2)],[7],[]),
([u55,u0,u1,0xf010f010,u2,u4],[(u25,u0,u1),(u55,u25,u3),(0xf010f010,u55,u2)],[7],[]),
([u55,u0,u1,u2,0xff110000,u4],[],[],[]),
([u55,u0,u1,u33,u2,u4],[(u25,u0,u1),(u55,u25,u3),(u33,u2,u4)],[1],[]),
([u55,u43,u0,u1,u2,u4],[(u25,u0,u1),(u55,u25,u3),(u43,u2,u4)],[1],[]),
([u55,u0,u1,u9,u2,u4],[(u25,u0,u1),(u55,u25,u3),(u9,u2,u3)],[6],[]),
([u55,u34,u0,u1,u2,u4],[(u25,u0,u1),(u55,u25,u3),(u34,u2,u3)],[2],[]),
([u55,u0,u1,u2,u32,u4],[],[],[]),
([u0,u1,u71,u9,u2,u3],[(u25,u0,u1),(u71,u25,u4),(u9,u2,u3)],[0],[(0,46),(0,47)]),
([u0,u1,u71,u2,u3,u6],[],[],[(0,47)]),
([u19,u0,u1,u71,u2,u3],[],[],[(0,48)]),
([u61,u1,u25,u2,u3,u4],[(u25,u0,u1),(u9,u2,u3),(u61,u0,u9)],[2,4],[(0,46)]),
([0xeee0eee,u0,u1,u2,u3,u4],[(u25,u0,u1),(u9,u2,u3),(0xeee0eee,u25,u9)],[0],[(0,49)]),
([u0,u1,u25,u9,u6,u4],[(u25,u0,u1),(u9,u2,u3),(u6,u2,u3)],[0,1,2,6],[(0,47),(0,49),(0,50),(0,51)]),
([u0,u1,0xeee0eee0,u2,u3,u4],[(u25,u0,u1),(u6,u2,u3),(0xeee0eee0,u25,u6)],[0],[(0,50)]),
([u0,u1,0xe0eee0ee,u2,u3,u4],[(u25,u0,u1),(u34,u3,u2),(0xe0eee0ee,u34,u25)],[0],[(0,52)]),
([u19,u34,u0,u1,u25,u4],[(u25,u0,u1),(u19,u2,u3),(u34,u2,u3)],[1,2,4],[(0,48),(0,51),(0,52),(1,52)]),
([u74,u0,u25,u2,u3,u4],[(u25,u0,u1),(u32,u3,u4),(u74,u1,u32)],[4,5],[(0,45)]),
([0xeeeeee,u0,u1,u2,u3,u4],[(u25,u0,u1),(u32,u3,u4),(0xeeeeee,u25,u32)],[1],[]),
([u0,u1,0xe0e0eeee,u2,u3,u4],[(u25,u0,u1),(u43,u2,u4),(0xe0e0eeee,u43,u25)],[1],[]),
([u7,u5,u1,u2,u3,u4],[(u21,u0,u1),(u7,u21,u0),(u5,u0,u4)],[1],[]),
([u7,u0,u11,u2,u3,u4],[(u21,u0,u1),(u7,u21,u0),(u11,u1,u2)],[0],[(0,36)]),
([u12,u0,u1,u75,u3,u4],[(u21,u0,u1),(u75,u21,u2),(u12,u0,u2)],[0],[(0,53)]),
([u5,u0,u1,u2,u75,u3],[(u21,u0,u1),(u75,u21,u2),(u5,u0,u4)],[0,3],[]),
([u13,u0,u1,u2,u75,u3],[(u21,u0,u1),(u75,u21,u2),(u13,u0,u4)],[0,3],[]),
([u19,u0,u1,u75,u3,u4],[],[],[]),
([u0,u1,u33,u75,u3,u4],[],[],[]),
([u21,u16,u9,u2,u3,u4],[],[],[]),
([u21,u16,u2,u3,u6,u4],[],[],[]),
([u19,u21,u16,u2,u3,u4],[],[],[(0,54)]),
([u21,u16,u33,u2,u3,u4],[(u21,u0,u1),(u16,u0,u1),(u33,u2,u4)],[1],[]),
([u23,u21,u16,u2,u3,u4],[(u21,u0,u1),(u16,u0,u1),(u23,u3,u4)],[1],[]),
([u21,u82,u0,u2,u3,u4],[(u21,u0,u1),(u15,u0,u3),(u82,u15,u1)],[0],[]),
([u21,u0,u1,u2,u40,u4],[(u21,u0,u1),(u12,u0,u2),(u40,u12,u3)],[0,2],[(0,53)]),
([u21,u63,u0,u1,u3,u4],[(u21,u0,u1),(u15,u0,u3),(u63,u15,u2)],[0],[]),
([u21,u0,u60,u2,u3,u4],[(u21,u0,u1),(u49,u0,u2),(u60,u49,u1)],[0],[]),
([u10,u21,u0,u17,u2,u4],[(u21,u0,u1),(u10,u0,u3),(u17,u1,u3)],[0,3],[]),
([u21,u44,u5,u0,u2,u3],[(u21,u0,u1),(u5,u0,u4),(u44,u5,u1)],[0,1,3],[(0,55)]),
([u21,u5,u0,u11,u2,u3],[],[],[(0,36),(0,56)]),
([u21,u44,u0,u2,u3,u4],[(u21,u0,u1),(u5,u0,u4),(u44,u5,u1)],[1,3],[]),
([u13,u21,u0,u11,u2,u3],[],[],[(0,57)]),
([u21,u0,u11,u3,u6,u4],[(u21,u0,u1),(u11,u1,u2),(u6,u2,u3)],[2],[]),
([u23,u21,u0,u17,u2,u4],[],[],[]),
([u0,u1,u2,0xf222f222,u3,u4],[(u21,u0,u1),(u9,u2,u3),(0xf222f222,u21,u9)],[0],[(0,58)]),
([u61,u21,u1,u2,u3,u4],[(u21,u0,u1),(u9,u2,u3),(u61,u0,u9)],[2],[(0,59)]),
([u21,u0,u1,u9,u6,u4],[(u21,u0,u1),(u9,u2,u3),(u6,u2,u3)],[0,2],[(0,58),(0,60)]),
([u0,u1,0xddd0ddd0,u2,u3,u4],[(u21,u0,u1),(u6,u2,u3),(0xddd0ddd0,u21,u6)],[1,5],[]),
([u21,u0,u42,u2,u3,u4],[],[],[]),
([0x22f222f2,u0,u1,u2,u3,u4],[],[],[]),
([u21,u0,u84,u2,u3,u4],[],[],[]),
([u19,u34,u21,u0,u1,u4],[],[],[(0,54),(0,60)]),
([u0,u1,u2,0xf2f22222,u3,u4],[],[],[]),
([0x22ff2222,u0,u1,u2,u3,u4],[(u21,u0,u1),(u23,u3,u4),(0x22ff2222,u23,u21)],[3],[]),
([u21,u0,u86,u2,u3,u4],[(u21,u0,u1),(u43,u2,u4),(u86,u43,u1)],[3],[]),
([u0,u11,u1,0xf4f4f4f4,u3,u4],[],[],[]),
([u0,u1,u9,u2,0xff44ff44,u4],[(u16,u0,u1),(0xff44ff44,u16,u3),(u9,u3,u2)],[6],[(1,61)]),
([u0,u68,u11,u1,u2,u3],[(u16,u0,u1),(u68,u16,u4),(u11,u1,u2)],[5],[(0,62)]),
([u8,u0,u68,u1,u2,u3],[(u16,u0,u1),(u68,u16,u4),(u8,u1,u3)],[3],[]),
([u0,u68,u1,u9,u2,u3],[],[],[(0,63)]),
([u0,u68,u1,u2,u3,u6],[(u16,u0,u1),(u68,u16,u4),(u6,u2,u3)],[0],[(0,63),(0,64)]),
([u19,u0,u68,u1,u2,u3],[],[],[]),
([u5,u1,0xeeee4444,u2,u3],[(u16,u0,u1),(u5,u0,u4),(0xeeee4444,u16,u5)],[0,1,5],[(0,65)]),
([u16,u44,u5,u1,u2,u3],[(u16,u0,u1),(u5,u0,u4),(u44,u5,u1)],[1,3],[(0,55),(0,65)]),
([u16,u5,u1,u2,u41,u3],[(u16,u0,u1),(u5,u0,u4),(u41,u5,u2)],[5],[]),
([u16,u70,u5,u1,u2,u3],[(u16,u0,u1),(u5,u0,u4),(u70,u5,u2)],[5],[]),
([u16,u5,u11,u1,u2,u3],[(u16,u0,u1),(u5,u0,u4),(u11,u1,u2)],[5],[(0,36),(0,66)]),
([u8,u16,u5,u1,u2,u3],[(u16,u0,u1),(u5,u0,u4),(u8,u1,u3)],[3],[]),
([u16,u5,u1,u9,u2,u3],[(u16,u0,u1),(u5,u0,u4),(u9,u2,u3)],[0],[(0,67),(0,68)]),
([u16,u5,u1,u2,u3,u6],[(u16,u0,u1),(u5,u0,u4),(u6,u2,u3)],[0],[(0,68),(0,69)]),
([u19,u16,u5,u1,u2,u3],[],[],[]),
([u51,u16,u1,u2,u3,u4],[(u16,u0,u1),(u17,u1,u3),(u51,u0,u17)],[0,5],[]),
([u56,u16,u0,u1,u2,u3],[(u16,u0,u1),(u17,u1,u3),(u56,u17,u4)],[3,5],[(0,70)]),
([u16,u92,u1,u2,u3,u4],[(u16,u0,u1),(u47,u1,u2),(u92,u47,u0)],[0],[]),
([0x2222aaaa,u16,u1,u2,u3,u4],[(u16,u0,u1),(u24,u1,u4),(0x2222aaaa,u0,u24)],[1,5],[]),
([u0,u1,u2,0xf444f444,u3,u4],[],[],[(0,67)]),
([u16,u0,u1,u9,u6,u4],[(u16,u0,u1),(u9,u2,u3),(u6,u2,u3)],[0,1,6],[(0,63),(0,68),(0,71),(0,72),(0,73)]),
([u0,u97,u1,u2,u3,u4],[(u16,u0,u1),(u6,u2,u3),(u97,u16,u6)],[0],[(0,69),(0,71)]),
([u16,u18,u1,u2,u3,u4],[(u16,u0,u1),(u6,u2,u3),(u18,u0,u6)],[0],[(0,64),(0,72)]),
([0x44f444f4,u0,u1,u2,u3,u4],[(u16,u0,u1),(u19,u2,u3),(0x44f444f4,u19,u16)],[0],[]),
([u19,u34,u16,u0,u1,u4],[],[],[(0,54),(0,73)]),
([u0,u1,u2,0xf4f44444,u3,u4],[(u16,u0,u1),(u33,u2,u4),(0xf4f44444,u16,u33)],[1,5],[]),
([u74,u16,u0,u2,u3,u4],[(u16,u0,u1),(u32,u3,u4),(u74,u1,u32)],[4,5],[(1,74)]),
([0x44ff4444,u0,u1,u2,u3,u4],[(u16,u0,u1),(u23,u3,u4),(0x44ff4444,u23,u16)],[1,5],[]),
([u82,u5,u0,u1,u2,u3],[(u15,u0,u3),(u82,u15,u1),(u5,u0,u4)],[0],[(0,0)]),
([u13,u82,u0,u1,u2,u3],[],[],[]),
([u18,u0,u1,u2,u40,u4],[(u12,u0,u2),(u40,u12,u3),(u18,u0,u40)],[0],[(0,75)]),
([u5,u0,u1,u2,u40],[(u12,u0,u2),(u40,u12,u3),(u5,u0,u4)],[0,1,2],[(0,11),(0,75),(1,76),(1,77),(1,78)]),
([u5,u0,u1,u2,u40,u4],[(u12,u0,u2),(u40,u12,u3),(u5,u0,u4)],[0,1,2],[(1,79)]),
([u13,u0,u1,u2,u40],[(u12,u0,u2),(u40,u12,u3),(u13,u0,u4)],[0,1,2],[(1,80),(1,81)]),
([u8,u0,u1,u36,u4],[(u15,u0,u3),(u36,u15,u2),(u8,u1,u3)],[0,2,4],[(0,77),(0,80),(0,83),(0,84),(1,82)]),
([u0,0xc8c0c8c0,u1,u36,u3,u4],[(u15,u0,u3),(u36,u15,u2),(0xc8c0c8c0,u1,u36)],[1,2,4,6],[(0,83),(1,85)]),
([0x32303230,u0,u1,u36,u3,u4],[(u15,u0,u3),(u36,u15,u2),(0x32303230,u1,u36)],[4,6],[(0,84),(1,86)]),
([u0,u24,u1,u2,u40,u4],[(u12,u0,u2),(u40,u12,u3),(u24,u1,u4)],[1],[]),
([u31,u0,u1,u2,u40,u4],[(u12,u0,u2),(u40,u12,u3),(u31,u1,u4)],[1,2],[(0,87)]),
([u19,u0,u1,u36,u4],[(u15,u0,u3),(u36,u15,u2),(u19,u3,u36)],[0,2],[(0,78),(0,81),(1,88)]),
([u0,u1,u2,0xffa00000,u40,u4],[],[],[]),
([u12,u0,u1,u36,u3,u4],[(u15,u0,u3),(u36,u15,u2),(u12,u0,u2)],[0,4],[(0,89)]),
([u18,u0,u1,u2,u3,u4],[(u15,u0,u3),(u36,u15,u2),(u18,u0,u36)],[0,2],[(0,90)]),
([u5,u0,u1,u2,u36,u3],[(u15,u0,u3),(u36,u15,u2),(u5,u0,u4)],[0,4],[(0,78),(0,89),(0,90)]),
([u13,u0,u1,u2,u36,u3],[(u15,u0,u3),(u36,u15,u2),(u13,u0,u4)],[0,4],[(0,81)]),
([u0,u11,u1,u36,u3,u4],[(u15,u0,u3),(u36,u15,u2),(u11,u1,u2)],[1,2],[(1,91)]),
([u22,u0,u1,u36,u3,u4],[(u15,u0,u3),(u36,u15,u2),(u22,u1,u2)],[4],[(1,86)]),
([u0,0xc8c0c8c0,u1,u2,u3,u4],[(u15,u0,u3),(u36,u15,u2),(0xc8c0c8c0,u1,u36)],[1,4,5,6],[]),
([u8,u0,u1,u2,u36,u4],[(u15,u0,u3),(u36,u15,u2),(u8,u1,u3)],[2,3],[(0,92)]),
([u0,u1,u33,u36,u3,u4],[],[],[]),
([u63,u5,u0,u1,u3],[(u15,u0,u3),(u63,u15,u2),(u5,u0,u4)],[0,1],[(0,12)]),
([u63,u5,u0,u1,u3,u4],[(u15,u0,u3),(u63,u15,u2),(u5,u0,u4)],[1],[]),
([u13,u63,u0,u1,u3],[(u15,u0,u3),(u63,u15,u2),(u13,u0,u4)],[0,1],[]),
([u63,u0,u24,u1,u3,u4],[(u15,u0,u3),(u63,u15,u2),(u24,u1,u4)],[1],[]),
([u31,u63,u0,u1,u3,u4],[(u15,u0,u3),(u63,u15,u2),(u31,u1,u4)],[1],[]),
([u38,u1,u2,u4],[(u15,u0,u3),(u26,u0,u3),(u38,u15,u26)],[1],[(0,93),(0,94),(0,95),(0,96),(0,97),(0,98),(0,99),(0,102),(0,103),(0,104),(0,105),(0,106),(0,108),(0,109),(0,110),(0,111),(1,100),(1,101),(1,107),(1,112)]),
([u12,u17,u1,u14,u3,u4],[(u12,u0,u2),(u14,u0,u2),(u17,u1,u3)],[1,2],[(0,114),(0,115),(1,105),(1,113)]),
([u12,u1,u14,u3,u45,u4],[(u12,u0,u2),(u14,u0,u2),(u45,u1,u3)],[0],[(0,115),(0,116),(1,106)]),
([u8,u12,u1,u14,u3,u4],[],[],[(0,107),(0,117)]),
([u22,u15,u1,u2,u26,u4],[],[],[(0,108)]),
([u12,u24,u1,u14,u3,u4],[(u12,u0,u2),(u14,u0,u2),(u24,u1,u4)],[1],[(1,109)]),
([u31,u12,u1,u14,u3,u4],[(u12,u0,u2),(u14,u0,u2),(u31,u1,u4)],[1],[(1,110)]),
([u12,u1,u14,u32,u3,u4],[],[],[(1,111)]),
([u23,u12,u1,u14,u3,u4],[(u12,u0,u2),(u14,u0,u2),(u23,u3,u4)],[1],[(0,112)]),
([u12,u15,u5,u1,u2,u3],[(u12,u0,u2),(u15,u0,u3),(u5,u0,u4)],[2],[(0,89),(0,90),(1,89)]),
([u12,u0,u1,u54,u3,u4],[(u12,u0,u2),(u10,u0,u3),(u54,u10,u2)],[0,7],[(0,118)]),
([u12,u5,u0,u1,u41,u3],[(u12,u0,u2),(u5,u0,u4),(u41,u5,u2)],[0,1,2],[(1,76)]),
([u8,u15,u5,u0,u1,u2],[(u15,u0,u3),(u5,u0,u4),(u8,u1,u3)],[0],[(0,77)]),
([u19,u15,u5,u0,u1,u2],[(u15,u0,u3),(u5,u0,u4),(u19,u3,u2)],[0],[(0,78),(0,119)]),
([u12,u0,u1,u41,u3,u4],[(u12,u0,u2),(u5,u0,u4),(u41,u5,u2)],[1,2],[(1,79)]),
([u13,u8,u15,u0,u1,u2],[],[],[(0,80)]),
([u13,u19,u15,u0,u1,u2],[],[],[(0,81),(0,120)]),
([u8,u0,0xaaccaacc,u1,u2,u4],[(u15,u0,u3),(u8,u1,u3),(0xaaccaacc,u8,u15)],[4],[]),
([u0,u1,0xeac0eac0,u2,u3,u4],[(u15,u0,u3),(u11,u1,u2),(0xeac0eac0,u15,u11)],[0,2,4],[(0,113)]),
([u56,u12,u0,u1,u2,u3],[(u12,u0,u2),(u17,u1,u3),(u56,u17,u4)],[4],[(0,91),(0,114)]),
([u12,u0,u17,u2,u45,u4],[],[],[(0,115),(0,121),(0,122)]),
([0x54fc54fc,u0,u1,u2,u3,u4],[(u15,u0,u3),(u37,u1,u2),(0x54fc54fc,u15,u37)],[2],[]),
([u12,0xaa88aa88,u1,u2,u3,u4],[(u12,u0,u2),(u45,u1,u3),(0xaa88aa88,u0,u45)],[3,6,7],[(0,121)]),
([0xfc00fc,u15,u0,u1,u2,u4],[(u15,u0,u3),(u37,u1,u2),(0xfc00fc,u3,u37)],[0,6],[]),
([0xa0eca0ec,u0,u1,u2,u3,u4],[(u12,u0,u2),(u8,u1,u3),(0xa0eca0ec,u8,u12)],[2],[]),
([u12,u0,u1,u65,u3,u4],[(u12,u0,u2),(u8,u1,u3),(u65,u8,u2)],[7],[]),
([u8,u20,u12,u0,u2,u4],[],[],[(0,117),(0,122)]),
([u8,u34,u12,u0,u1,u4],[],[],[(0,123)]),
([u0,0xb3a0b3a0,u1,u2,u3,u4],[(u12,u0,u2),(u20,u1,u3),(0xb3a0b3a0,u20,u12)],[2,3],[]),
([u12,u0,u1,u53,u3,u4],[(u12,u0,u2),(u20,u1,u3),(u53,u20,u2)],[4],[(0,86)]),
([u0,u1,0xececa0a0,u2,u3,u4],[(u12,u0,u2),(u24,u1,u4),(0xececa0a0,u12,u24)],[1],[]),
([u0,0xb3b3a0a0,u1,u2,u3,u4],[],[],[]),
([u12,u0,u1,0xf3f3f0f0,u3,u4],[],[],[(0,87)]),
([u0,u94,u1,u2,u4],[(u15,u0,u3),(u19,u3,u2),(u94,u19,u15)],[0,2,4],[(0,119),(0,120),(1,123)]),
([u12,u0,u84,u1,u3,u4],[],[],[(0,88)]),
([u0,u1,u2,0xfaf0aa00,u3,u4],[(u15,u0,u3),(u33,u2,u4),(0xfaf0aa00,u15,u33)],[1],[]),
([0xa0ffa0a0,u0,u1,u2,u3,u4],[(u12,u0,u2),(u23,u3,u4),(0xa0ffa0a0,u23,u12)],[1],[]),
([u12,u0,u1,u77,u3,u4],[(u12,u0,u2),(u23,u3,u4),(u77,u23,u2)],[7],[]),
([u0,u98,u50,u2,u3,u4],[(u26,u0,u3),(u50,u1,u26),(u98,u50,u2)],[0,1,4,7],[(0,126),(1,124),(1,125)]),
([u0,u39,u2,u3,0xffc8ffc8,u4],[],[],[(1,127)]),
([0xc800c8,u0,u39,u2,u3,u4],[],[],[(0,128),(0,129)]),
([0x30703070,u0,u50,u2,u3,u4],[(u26,u0,u3),(u50,u1,u26),(0x30703070,u50,u2)],[4,7],[(1,128)]),
([u0,0xc8c80000,u39,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14),(0xc8c80000,u39,u4)],[1,2,6],[]),
([0x33770000,u0,u50,u2,u3,u4],[(u26,u0,u3),(u50,u1,u26),(0x33770000,u50,u4)],[1],[]),
([u0,u39,u3,u6,u4],[(u14,u0,u2),(u39,u1,u14),(u6,u2,u3)],[0,2,6],[(0,129),(0,130),(1,126)]),
([u19,u0,u39,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u19,u2,u3)],[0,2,6],[]),
([u0,u39,u2,u32,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u32,u3,u4)],[2,6],[]),
([u23,u0,u39,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u23,u3,u4)],[1],[]),
([u0,u11,u50,u2,u3,u4],[(u26,u0,u3),(u50,u1,u26),(u11,u1,u2)],[0,1,4,7],[(0,132),(1,124),(1,131)]),
([u0,u39,u2,u3,u45,u4],[(u14,u0,u2),(u39,u1,u14),(u45,u1,u3)],[4],[]),
([u8,u0,u39,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u8,u1,u3)],[0,4],[(0,133)]),
([u22,u0,u50,u2,u3,u4],[(u26,u0,u3),(u50,u1,u26),(u22,u1,u2)],[4,6,7],[]),
([u0,u39,u24,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u24,u1,u4)],[1,2,6],[]),
([u31,u0,u39,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14),(u31,u1,u4)],[1],[]),
([u0,u39,u1,u3,u6,u4],[(u14,u0,u2),(u39,u1,u14),(u6,u2,u3)],[4],[(0,133),(0,134),(1,132)]),
([u19,u0,u39,u1,u3,u4],[],[],[]),
([0x32323232,u0,u2,u32,u3,u4],[],[],[]),
([u23,0x32323232,u0,u2,u3,u4],[(u14,u0,u2),(0x32323232,u1,u14),(u23,u3,u4)],[1],[]),
([u51,u1,u2,u14,u3,u4],[(u14,u0,u2),(u17,u1,u3),(u51,u0,u17)],[2,4],[(0,124)]),
([0x32fa32fa,u0,u1,u2,u3,u4],[(u14,u0,u2),(u17,u1,u3),(0x32fa32fa,u17,u14)],[0,1,5],[(0,135)]),
([u56,u0,u1,u2,u14,u3],[(u14,u0,u2),(u17,u1,u3),(u56,u17,u4)],[3,4,5],[(0,114),(0,131),(0,137),(1,136)]),
([u0,u11,u1,u26,u6,u4],[(u26,u0,u3),(u11,u1,u2),(u6,u2,u3)],[0,2],[(0,132),(0,138)]),
([u48,u0,u17,u1,u2,u4],[(u14,u0,u2),(u17,u1,u3),(u48,u3,u14)],[1,3],[(0,137)]),
([u0,u11,u1,u2,u3,0xffaa0000],[(u26,u0,u3),(u11,u1,u2),(0xffaa0000,u26,u4)],[5],[(1,139)]),
([u0,u11,u37,u3,u26,u4],[],[],[]),
([u0,u1,u2,0xfac8fac8,u3,u4],[(u14,u0,u2),(u45,u1,u3),(0xfac8fac8,u14,u45)],[0],[(0,116),(1,140)]),
([u0,u1,u2,0xfafa0000,u3,u45],[],[],[(1,141)]),
([u0,u1,u2,0xf3a2f3a2,u3,u4],[(u26,u0,u3),(u47,u1,u2),(0xf3a2f3a2,u47,u26)],[0],[(0,142),(0,143)]),
([u8,u20,u0,u2,u14,u4],[(u14,u0,u2),(u8,u1,u3),(u20,u1,u3)],[1,3,7],[(0,117),(0,144),(0,145),(0,146),(1,142)]),
([u8,u0,u1,u14,u6,u4],[(u14,u0,u2),(u8,u1,u3),(u6,u2,u3)],[4],[(0,133),(0,147),(1,143)]),
([u8,u0,u1,u2,0xfafa0000,u3],[],[],[(0,146)]),
([u0,0xc8fac8fa,u1,u2,u3,u4],[(u14,u0,u2),(u20,u1,u3),(0xc8fac8fa,u20,u14)],[0,3],[(0,145)]),
([u48,u20,u0,u1,u2,u4],[(u14,u0,u2),(u20,u1,u3),(u48,u3,u14)],[2,6,7],[]),
([u22,u0,u1,u2,u3,0xffaa0000],[(u26,u0,u3),(u22,u1,u2),(0xffaa0000,u26,u4)],[4,7],[(1,146)]),
([0x3232fafa,u0,u1,u2,u3,u4],[(u14,u0,u2),(u24,u1,u4),(0x3232fafa,u24,u14)],[1],[]),
([u0,u24,u1,0xf0a0f0a0,u3,u4],[(u26,u0,u3),(u24,u1,u4),(0xf0a0f0a0,u26,u2)],[1,4,7],[]),
([u48,u0,u24,u1,u2,u4],[(u14,u0,u2),(u24,u1,u4),(u48,u14,u3)],[1],[]),
([u0,0xc8c8fafa,u1,u2,u3,u4],[(u14,u0,u2),(u31,u1,u4),(0xc8c8fafa,u31,u14)],[1],[]),
([u31,u0,u1,0xf0a0f0a0,u3,u4],[(u26,u0,u3),(u31,u1,u4),(0xf0a0f0a0,u26,u2)],[1],[]),
([u48,u31,u0,u1,u2,u4],[(u14,u0,u2),(u31,u1,u4),(u48,u14,u3)],[1],[]),
([u18,u1,u2,u26,u4],[(u26,u0,u3),(u6,u3,u2),(u18,u0,u6)],[0],[(0,138),(1,130),(1,134),(1,147),(1,148)]),
([u0,u1,0xf0aaf0aa,u2,u4],[(u26,u0,u3),(u34,u3,u2),(0xf0aaf0aa,u34,u26)],[0,7],[]),
([u48,u0,u1,0xccfeccfe,u2,u4],[(u14,u0,u2),(u48,u14,u3),(0xccfeccfe,u48,u1)],[2,6,7],[]),
([u48,u0,0xcc04cc04,u1,u2,u4],[(u14,u0,u2),(u48,u14,u3),(0xcc04cc04,u48,u1)],[1,7],[(0,149)]),
([u48,u0,u1,u2,0xff050000,u4],[],[],[]),
([u0,0xc0c4c0c4,u1,u2,u3,u4],[(u26,u0,u3),(0xf0a0f0a,u26,u2),(0xc0c4c0c4,0xf0a0f0a,u1)],[0,1,5],[]),
([u48,u0,u1,u2,u32,u4],[],[],[]),
([0xfafafa,u0,u1,u2,u3,u4],[(u14,u0,u2),(u32,u3,u4),(0xfafafa,u32,u14)],[1],[]),
([u0,u1,0xf0a0ffaa,u2,u3,u4],[(u26,u0,u3),(u43,u2,u4),(0xf0a0ffaa,u43,u26)],[1],[]),
([u10,u27,u1,0xcceeccee,u2,u4],[],[],[(0,150),(0,151),(0,152)]),
([u10,u0,0xc0e0c0e0,u1,u3,u4],[],[],[(0,151)]),
([u10,0xc0e0c0e,u0,u1,u3,u4],[],[],[(0,152)]),
([u5,u0,u60,u1,u2,u3],[(u49,u0,u2),(u60,u49,u1),(u5,u0,u4)],[0,5],[(0,9),(0,153)]),
([u13,u0,u60,u1,u2,u3],[(u49,u0,u2),(u60,u49,u1),(u13,u0,u4)],[1],[(0,154)]),
([u0,u60,u1,u2,u3,0xffffc4c4],[(u49,u0,u2),(u60,u49,u1),(0xffffc4c4,u60,u4)],[5],[(0,155)]),
([0x33bb0000,u0,u91,u1,u2,u3],[(u10,u0,u3),(u91,u10,u1),(0x33bb0000,u91,u4)],[1],[]),
([u10,u27,u91,u1,u2,u4],[(u10,u0,u3),(u91,u10,u1),(u27,u0,u3)],[1,7],[(0,156),(0,157)]),
([u10,0x33bb0000,u0,u1,u2,u3],[],[],[(0,157)]),
([u5,u0,u1,u2,u54,u3],[(u10,u0,u3),(u54,u10,u2),(u5,u0,u4)],[0],[(0,158)]),
([u13,u0,u1,u2,u54,u3],[(u10,u0,u3),(u54,u10,u2),(u13,u0,u4)],[0],[(0,159)]),
([u0,0xc0c8c0c8,u1,u2,u3,u4],[],[],[]),
([u0,u11,u1,u3,0xff0aff0a,u4],[(u49,u0,u2),(0xff0aff0a,u49,u3),(u11,u1,u2)],[3,4],[(1,160)]),
([u8,u0,u1,u2,u54,u4],[],[],[]),
([u19,u0,u1,u54,u4],[(u10,u0,u3),(u54,u10,u2),(u19,u2,u3)],[2,6],[(0,158),(0,159),(0,161)]),
([u10,u27,u1,u2,u54,u4],[(u10,u0,u3),(u54,u10,u2),(u27,u0,u3)],[7],[(0,162)]),
([u0,0xccc4ccc4,u1,u2,u3,u4],[(u10,u0,u3),(u57,u10,u2),(0xccc4ccc4,u57,u1)],[1,5],[]),
([u57,u5,u0,u1,u2,u3],[],[],[(0,90),(0,163)]),
([u13,u57,u0,u1,u2,u3],[],[],[(0,164)]),
([u57,u0,u11,u1,u3,u4],[(u10,u0,u3),(u57,u10,u2),(u11,u1,u2)],[2],[]),
([u57,u0,u1,u9,u4],[(u10,u0,u3),(u57,u10,u2),(u9,u2,u3)],[0,2,6],[(0,161),(0,163),(0,164),(0,165),(0,166)]),
([u10,u27,u1,0xf050f050,u2,u4],[(u10,u0,u3),(0xf050f050,u10,u2),(u27,u0,u3)],[7],[(0,167)]),
([u10,u27,u1,u2,0xff550000,u4],[],[],[(0,168)]),
([u10,u49,u5,u1,u2,u3],[(u10,u0,u3),(u49,u0,u2),(u5,u0,u4)],[2,4],[(0,169)]),
([u10,u49,u0,u1,u9,u4],[(u10,u0,u3),(u49,u0,u2),(u9,u2,u3)],[0,2],[(0,169),(0,170),(1,170)]),
([u10,u38,u1,u2,u4],[(u10,u0,u3),(u27,u0,u3),(u38,u10,u27)],[0,1,7],[(0,150),(0,156),(0,162),(0,167),(0,168),(0,171),(1,172)]),
([u10,u27,u11,u1,u2,u4],[(u10,u0,u3),(u27,u0,u3),(u11,u1,u2)],[1],[(0,105),(0,173)]),
([u10,u27,u1,u2,u37,u4],[],[],[(0,106)]),
([u10,u47,u27,u1,u2,u4],[],[],[(0,174),(1,107)]),
([u10,u22,u27,u1,u2,u4],[],[],[(0,108),(0,174)]),
([u10,u27,u24,u1,u2,u4],[(u10,u0,u3),(u27,u0,u3),(u24,u1,u4)],[1],[(0,109)]),
([u10,u31,u27,u1,u2,u4],[(u10,u0,u3),(u27,u0,u3),(u31,u1,u4)],[1],[(0,110)]),
([u10,u27,u1,u33,u2,u4],[(u10,u0,u3),(u27,u0,u3),(u33,u2,u4)],[1],[(0,111)]),
([u10,u43,u27,u1,u2,u4],[(u10,u0,u3),(u27,u0,u3),(u43,u2,u4)],[1],[(1,112)]),
([u10,u5,u0,u1,u2,u66],[(u10,u0,u3),(u5,u0,u4),(u66,u5,u3)],[0,1],[]),
([u10,0x5500ff00,u5,u0,u1,u2],[(u10,u0,u3),(u5,u0,u4),(0x5500ff00,u5,u3)],[0,1,4],[]),
([u10,u5,u0,u17,u1,u2],[(u10,u0,u3),(u5,u0,u4),(u17,u1,u3)],[0,3],[(0,13),(0,175)]),
([u10,u8,u5,u0,u1,u2],[(u10,u0,u3),(u5,u0,u4),(u8,u1,u3)],[0,3],[]),
([u10,u5,u0,u1,u9,u2],[(u10,u0,u3),(u5,u0,u4),(u9,u2,u3)],[0],[(0,163),(0,169),(0,176)]),
([u10,u19,u5,u0,u1,u2],[(u10,u0,u3),(u5,u0,u4),(u19,u2,u3)],[0],[(0,158)]),
([u13,u10,u0,u17,u1,u2],[(u10,u0,u3),(u13,u0,u4),(u17,u1,u3)],[3],[(0,177)]),
([u13,u10,u8,u0,u1,u2],[(u10,u0,u3),(u13,u0,u4),(u8,u1,u3)],[0,3],[]),
([u13,u10,u0,u1,u9,u2],[],[],[(0,164),(0,178)]),
([u13,u10,u19,u0,u1,u2],[(u10,u0,u3),(u13,u0,u4),(u19,u2,u3)],[0],[(0,159)]),
([u0,0xc0eac0ea,u1,u2,u3,u4],[(u10,u0,u3),(u11,u1,u2),(0xc0eac0ea,u10,u11)],[0,2,3],[]),
([u10,0x2a2a2a2a,u1,u2,u3,u4],[(u10,u0,u3),(u11,u1,u2),(0x2a2a2a2a,u0,u11)],[2,4],[]),
([u10,0x3f3f0000,u0,u1,u2,u3],[],[],[(0,173)]),
([u0,u1,u2,0xf5c4f5c4,u3,u4],[],[],[]),
([0xace0ace,u0,u1,u2,u3,u4],[(u49,u0,u2),(u8,u1,u3),(0xace0ace,u49,u8)],[3],[]),
([u10,u47,u22,u0,u3,u4],[],[],[(0,174)]),
([u10,u19,u47,u0,u1,u4],[],[],[]),
([0x30ba30ba,u0,u1,u2,u3,u4],[(u10,u0,u3),(u22,u1,u2),(0x30ba30ba,u10,u22)],[3],[]),
([u10,u0,0xccaaccaa,u1,u2,u4],[(u10,u0,u3),(u17,u1,u3),(0xccaaccaa,u10,u17)],[0,2,4,7],[]),
([u0,u1,0xccee00aa,u2,u3,u4],[],[],[]),
([0x33bb00aa,u0,u1,u2,u3,u4],[(u10,u0,u3),(u31,u1,u4),(0x33bb00aa,u10,u31)],[5],[]),
([u10,u0,u1,0xf0aaf0aa,u2,u4],[(u10,u0,u3),(u9,u2,u3),(0xf0aaf0aa,u10,u9)],[0,2,4,7],[]),
([u10,u59,u0,u1,u2,u4],[],[],[(0,166)]),
([u10,u0,0xcc0ccc0c,u1,u2,u4],[],[],[]),
([u0,u1,u2,0xf0fa00aa,u3,u4],[],[],[]),
([0xaff0a0a,u0,u1,u2,u3,u4],[],[],[]),
([u80,u0,u11,u2,u3,u4],[(u27,u0,u3),(u80,u27,u1),(u11,u1,u2)],[0,4],[(0,179)]),
([u22,u80,u0,u2,u3,u4],[(u27,u0,u3),(u80,u27,u1),(u22,u1,u2)],[4],[]),
([u80,u0,u1,u2,u6,u4],[(u27,u0,u3),(u80,u27,u1),(u6,u2,u3)],[2],[(0,179)]),
([u0,u11,u1,0xf5f0f5f0,u3,u4],[],[],[]),
([u0,0xc4c0c4c0,u1,u2,u3,u4],[(u27,u0,u3),(0xf5f0f5f0,u27,u2),(0xc4c0c4c0,u1,0xf5f0f5f0)],[1,5],[]),
([u0,u69,u11,u1,u2,u3],[(u27,u0,u3),(u69,u27,u4),(u11,u1,u2)],[5],[(0,180)]),
([u0,u69,u1,u2,u37,u3],[(u27,u0,u3),(u69,u27,u4),(u37,u1,u2)],[0],[(0,181)]),
([u8,u0,0xafaf0000,u1,u2,u3],[],[],[(0,182)]),
([u22,u0,u69,u1,u2,u3],[(u27,u0,u3),(u69,u27,u4),(u22,u1,u2)],[4],[(0,183),(1,182)]),
([u0,u1,0xd5c0d5c0,u2,u3,u4],[(u27,u0,u3),(u11,u1,u2),(0xd5c0d5c0,u27,u11)],[1,5],[]),
([u35,u0,u1,u78,u3,u4],[],[],[(1,184)]),
([u56,u35,u0,u1,u2,u3],[(u35,u0,u2),(u17,u1,u3),(u56,u17,u4)],[5],[(0,185),(1,173)]),
([u35,u0,u17,u2,u45,u4],[(u35,u0,u2),(u17,u1,u3),(u45,u1,u3)],[1,3],[(0,188),(0,189),(1,186),(1,187)]),
([u35,u0,u17,u1,u6,u4],[(u35,u0,u2),(u17,u1,u3),(u6,u2,u3)],[0],[(1,179),(1,190)]),
([0xa8fca8fc,u0,u1,u2,u3,u4],[],[],[]),
([u35,0xaa88aa88,u1,u2,u3,u4],[],[],[(0,188),(1,181)]),
([0x50dc50dc,u0,u1,u2,u3,u4],[],[],[]),
([u8,u20,u35,u0,u2,u4],[(u35,u0,u2),(u8,u1,u3),(u20,u1,u3)],[1],[(0,182),(0,189),(1,174)]),
([u8,u35,u0,u1,u6,u4],[(u35,u0,u2),(u8,u1,u3),(u6,u2,u3)],[0],[(0,123)]),
([0x73507350,u0,u1,u2,u3,u4],[(u35,u0,u2),(u20,u1,u3),(0x73507350,u20,u35)],[3],[]),
([u35,u0,u1,u53,u3,u4],[(u35,u0,u2),(u20,u1,u3),(u53,u20,u2)],[1],[(1,183)]),
([u0,u1,0xdcdc5050,u2,u3,u4],[(u35,u0,u2),(u24,u1,u4),(0xdcdc5050,u35,u24)],[1],[]),
([u35,u0,u1,u95,u3,u4],[(u35,u0,u2),(u24,u1,u4),(u95,u24,u2)],[5],[]),
([0x73735050,u0,u1,u2,u3,u4],[(u35,u0,u2),(u31,u1,u4),(0x73735050,u31,u35)],[1],[]),
([u0,u94,u1,u2,u6,u4],[(u27,u0,u3),(u6,u3,u2),(u94,u27,u6)],[0,4],[]),
([u0,u1,u2,0xf5f05500,u3,u4],[(u27,u0,u3),(u33,u2,u4),(0xf5f05500,u27,u33)],[1],[]),
([u35,u0,u1,u3,u79,u4],[(u35,u0,u2),(u32,u3,u4),(u79,u2,u32)],[5],[]),
([0x50ff5050,u0,u1,u2,u3,u4],[(u35,u0,u2),(u23,u3,u4),(0x50ff5050,u23,u35)],[1],[]),
([u0,u1,u64,u2,u41,u3],[(u5,u0,u4),(u64,u5,u1),(u41,u5,u2)],[1,2,3],[(0,191),(0,192)]),
([u8,u5,u0,u64,u2,u3],[(u5,u0,u4),(u64,u5,u1),(u8,u1,u3)],[4,5],[]),
([u5,u0,u1,0xe0e0c0c0,u3],[(u5,u0,u4),(u64,u5,u1),(0xe0e0c0c0,u64,u2)],[1,2,3],[(0,16),(0,32)]),
([0xee00cc,u5,u0,u1,u2],[(u5,u0,u4),(u64,u5,u1),(0xee00cc,u64,u3)],[1,3],[]),
([0xee00cc,u5,u0,u1,u2,u3],[],[],[]),
([u5,u0,u1,u2,0xf4f4fcfc,u3],[(u5,u0,u4),(u44,u5,u1),(0xf4f4fcfc,u44,u2)],[0],[(0,193)]),
([0x4400cc,u5,u0,u1,u2,u3],[],[],[]),
([u44,u5,u0,u2,u37,u3],[],[],[(0,194)]),
([u8,u44,u5,u0,u2,u3],[(u5,u0,u4),(u44,u5,u1),(u8,u1,u3)],[4,5],[]),
([u5,u0,u1,u2,u66,u45],[(u5,u0,u4),(u66,u5,u3),(u45,u1,u3)],[3,5],[(1,195),(1,196)]),
([u22,u5,u0,u1,u41,u3],[(u5,u0,u4),(u41,u5,u2),(u22,u1,u2)],[3],[(0,17),(0,198),(1,197),(1,199)]),
([u5,u0,u90,u1,u2,u3],[(u5,u0,u4),(u41,u5,u2),(u90,u1,u41)],[5],[(0,18),(0,191),(0,192)]),
([u5,u0,u1,u2,u66,u6],[(u5,u0,u4),(u66,u5,u3),(u6,u3,u2)],[2,5],[(0,200)]),
([u19,u5,u0,u1,u41,u3],[],[],[]),
([u5,u0,u1,u2,u3,0xfffafff0],[(u5,u0,u4),(u41,u5,u2),(0xfffafff0,u41,u3)],[0,1,3],[(0,201)]),
([0xfa00f0,u5,u0,u1,u2,u3],[],[],[]),
([0x88cc00cc,u5,u0,u1,u2,u3],[(u5,u0,u4),(0x5500ff00,u5,u3),(0x88cc00cc,0x5500ff00,u1)],[4],[]),
([u5,u0,u1,u2,0xf5f0fff0,u3],[(u5,u0,u4),(0x5500ff00,u5,u3),(0xf5f0fff0,0x5500ff00,u2)],[0],[(0,202)]),
([u70,u5,u0,u1,u37,u3],[],[],[(0,204),(1,203)]),
([u70,u5,u0,u1,u3,u6],[(u5,u0,u4),(u70,u5,u2),(u6,u2,u3)],[2],[(0,205)]),
([u0,u1,u58,u2,u3],[(u5,u0,u4),(u11,u1,u2),(u58,u5,u11)],[1,2,3,5],[(0,21),(0,33),(0,56),(0,66),(0,206),(1,175)]),
([u5,u0,u1,u58,u2,u3],[(u5,u0,u4),(u11,u1,u2),(u58,u5,u11)],[2,3,5],[(0,19)]),
([u51,u5,u0,u1,u2,u3],[(u5,u0,u4),(u17,u1,u3),(u51,u0,u17)],[1,4],[]),
([u8,u5,u0,u1,u2,u3],[(u5,u0,u4),(u17,u1,u3),(u8,u17,u1)],[3],[]),
([u5,u0,u1,u2,u78,u3],[(u5,u0,u4),(u17,u1,u3),(u78,u17,u2)],[0],[(0,207)]),
([u5,u0,u11,u1,u3,u6],[(u5,u0,u4),(u11,u1,u2),(u6,u2,u3)],[2],[(0,20),(0,206),(0,208)]),
([0x5454fcfc,u5,u0,u1,u2,u3],[(u5,u0,u4),(u37,u1,u2),(0x5454fcfc,u5,u37)],[0,1],[]),
([u62,u5,u1,u2,u3],[(u5,u0,u4),(u37,u1,u2),(u62,u0,u37)],[0,1,2,3],[(0,194),(0,195),(0,204)]),
([u62,u5,u0,u1,u2,u3],[],[],[]),
([0xfc00fc,u5,u0,u1,u2,u3],[],[],[]),
([u5,u0,0xaaee00cc,u1,u2,u3],[(u5,u0,u4),(u8,u1,u3),(0xaaee00cc,u8,u5)],[3,5],[]),
([u92,u5,u0,u1,u2,u3],[],[],[]),
([u5,u0,u1,u2,u65,u3],[],[],[]),
([0xc000c,u5,u0,u1,u2,u3],[(u5,u0,u4),(u8,u1,u3),(0xc000c,u8,u2)],[0],[(0,209)]),
([u8,u20,u5,u0,u2],[(u5,u0,u4),(u8,u1,u3),(u20,u1,u3)],[1,3],[(0,210),(0,211)]),
([u8,u5,u0,u1,u2,u6],[(u5,u0,u4),(u8,u1,u3),(u6,u2,u3)],[2,3],[(0,212)]),
([u8,u34,u5,u0,u1,u2],[],[],[]),
([u5,u0,0xbaba3030,u1,u2,u3],[(u5,u0,u4),(u22,u1,u2),(0xbaba3030,u22,u5)],[0,1],[(0,23)]),
([u76,u5,u1,u2,u3],[(u5,u0,u4),(u20,u1,u3),(u76,u20,u0)],[0,1,3,4],[(0,197)]),
([u76,u5,u0,u1,u2,u3],[],[],[]),
([u5,u0,u1,u2,u67],[(u5,u0,u4),(u22,u1,u2),(u67,u22,u3)],[1,2,3],[(1,199)]),
([u5,u0,u1,u2,u53,u3],[],[],[]),
([u5,u0,u52,u1,u3],[(u5,u0,u4),(u20,u1,u3),(u52,u20,u2)],[1,3],[(0,24),(0,34)]),
([u5,u0,u1,u2,u87,u3],[(u5,u0,u4),(u9,u2,u3),(u87,u5,u9)],[0,1],[(0,213)]),
([u61,u5,u1,u2,u3],[(u5,u0,u4),(u9,u2,u3),(u61,u0,u9)],[1],[(0,26),(0,214)]),
([u61,u5,u0,u1,u2,u3],[],[],[]),
([u59,u5,u0,u1,u2,u3],[(u5,u0,u4),(u9,u2,u3),(u59,u1,u9)],[0],[(0,26),(0,215)]),
([u5,u0,u1,u9,u6],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3)],[0,1,2],[(0,27),(0,68),(0,163),(0,213),(0,215),(0,216),(0,217),(0,218),(0,219),(0,220)]),
([0x5550fff0,u5,u0,u1,u2,u3],[(u5,u0,u4),(u6,u2,u3),(0x5550fff0,u5,u6)],[0,1],[]),
([u18,u5,u1,u2,u3],[(u5,u0,u4),(u6,u2,u3),(u18,u0,u6)],[0,1,2,4],[(0,28),(0,75),(0,200),(0,205),(0,208),(0,212),(0,216),(0,221),(1,75),(1,200),(1,205),(1,208),(1,212)]),
([u18,u5,u0,u1,u2,u3],[(u5,u0,u4),(u6,u2,u3),(u18,u0,u6)],[0],[(0,217)]),
([u18,u5,u1,u2,u3,u6],[(u5,u0,u4),(u6,u2,u3),(u18,u0,u6)],[0,2,4],[(0,218)]),
([u73,u5,u1,u2,u3,u6],[],[],[(0,90),(0,219)]),
([u5,u0,u42,u1,u2,u3],[(u5,u0,u4),(u6,u2,u3),(u42,u1,u6)],[0,5],[(0,28),(0,30),(0,222)]),
([u5,u0,0xaafa00f0,u1,u2,u3],[],[],[]),
([u96,u5,u0,u1,u2,u3],[(u5,u0,u4),(u34,u3,u2),(u96,u34,u0)],[0],[]),
([u5,u0,u84,u1,u2,u3],[],[],[(0,31)]),
([u5,u0,u1,u2,u3,u6],[(u5,u0,u4),(u19,u2,u3),(u6,u19,u3)],[0,2],[(0,90)]),
([u44,u0,u2,u37,u3,u4],[],[],[]),
([u8,u44,u0,u2,u3,u4],[(u5,u0,u4),(u44,u5,u1),(u8,u1,u3)],[4,5],[]),
([u22,u0,u1,u41,u3,u4],[(u5,u0,u4),(u41,u5,u2),(u22,u1,u2)],[3],[(0,223),(1,224)]),
([u0,u90,u1,u2,u3,u4],[(u5,u0,u4),(u41,u5,u2),(u90,u1,u41)],[1,5],[]),
([u19,u0,u1,u41,u3,u4],[],[],[]),
([u0,u1,u58,u2,u3,u4],[(u5,u0,u4),(u11,u1,u2),(u58,u5,u11)],[0,1,2,3,5],[]),
([0x5454fcfc,u0,u1,u2,u3,u4],[(u5,u0,u4),(u37,u1,u2),(0x5454fcfc,u5,u37)],[0],[]),
([u62,u5,u1,u2,u3,u4],[(u5,u0,u4),(u37,u1,u2),(u62,u0,u37)],[1,6],[]),
([u0,0xaaee00cc,u1,u2,u3,u4],[(u5,u0,u4),(u8,u1,u3),(0xaaee00cc,u8,u5)],[0,3,5],[]),
([u8,u20,u5,u0,u2,u4],[(u5,u0,u4),(u8,u1,u3),(u20,u1,u3)],[1],[(0,225)]),
([u0,0xbaba3030,u1,u2,u3,u4],[(u5,u0,u4),(u22,u1,u2),(0xbaba3030,u22,u5)],[0],[]),
([u76,u5,u1,u2,u3,u4],[(u5,u0,u4),(u20,u1,u3),(u76,u20,u0)],[1,4],[]),
([u5,u0,u1,u2,u67,u4],[(u5,u0,u4),(u22,u1,u2),(u67,u22,u3)],[1,2],[(1,224)]),
([u5,u0,u52,u1,u3,u4],[(u5,u0,u4),(u20,u1,u3),(u52,u20,u2)],[1],[(0,35)]),
([u0,u1,u2,u87,u3,u4],[(u5,u0,u4),(u9,u2,u3),(u87,u5,u9)],[0],[(0,226)]),
([u61,u5,u1,u2,u3,u4],[(u5,u0,u4),(u9,u2,u3),(u61,u0,u9)],[1],[]),
([u5,u0,u1,u9,u6,u4],[(u5,u0,u4),(u9,u2,u3),(u6,u2,u3)],[0,1,2],[(0,226),(0,227),(0,228)]),
([0x5550fff0,u0,u1,u2,u3,u4],[(u5,u0,u4),(u6,u2,u3),(0x5550fff0,u5,u6)],[0],[]),
([u18,u5,u1,u2,u3,u4],[(u5,u0,u4),(u6,u2,u3),(u18,u0,u6)],[1,6,7],[(0,227)]),
([u0,0xaafa00f0,u1,u2,u3,u4],[(u5,u0,u4),(u19,u2,u3),(0xaafa00f0,u19,u5)],[0],[]),
([u19,u34,u5,u0,u1,u4],[(u5,u0,u4),(u19,u2,u3),(u34,u2,u3)],[1],[(0,228)]),
([u5,u0,u11,u1,u2,u3],[(u13,u0,u4),(u5,u13,u0),(u11,u1,u2)],[5],[(0,36),(0,192)]),
([u5,u0,u1,u2,u37,u3],[(u13,u0,u4),(u5,u13,u0),(u37,u1,u2)],[0],[(0,229)]),
([u22,u5,u0,u1,u2,u3],[(u13,u0,u4),(u5,u13,u0),(u22,u1,u2)],[0],[(0,37),(0,231),(1,230),(1,232),(1,233)]),
([u5,u0,u1,u9,u2,u3],[(u13,u0,u4),(u5,u13,u0),(u9,u2,u3)],[0],[(0,234),(0,235)]),
([u19,u5,u0,u1,u2,u3],[],[],[]),
([u0,0xc0c0eaea,u1,u2,u3],[(u13,u0,u4),(u11,u1,u2),(0xc0c0eaea,u13,u11)],[2,5],[(0,38),(0,57),(0,236),(1,177)]),
([u13,u51,u0,u1,u2,u3],[(u13,u0,u4),(u17,u1,u3),(u51,u0,u17)],[1,5],[]),
([u13,u8,u0,u1,u2,u3],[(u13,u0,u4),(u17,u1,u3),(u8,u17,u1)],[3],[]),
([u13,u0,u1,u2,u78,u3],[],[],[]),
([u13,u0,u11,u1,u3,u6],[(u13,u0,u4),(u11,u1,u2),(u6,u2,u3)],[2],[(0,236)]),
([u13,u62,u0,u1,u2,u3],[],[],[(0,229)]),
([u13,0xfc00fc,u0,u1,u2,u3],[],[],[]),
([u13,u92,u0,u1,u2,u3],[],[],[]),
([u13,u0,u1,u2,u65,u3],[],[],[]),
([u13,0xc000c,u0,u1,u2,u3],[],[],[]),
([u13,u8,u20,u0,u2],[(u13,u0,u4),(u8,u1,u3),(u20,u1,u3)],[1,3],[(0,233),(0,237),(0,238)]),
([u13,u8,u0,u1,u2,u6],[(u13,u0,u4),(u8,u1,u3),(u6,u2,u3)],[2,3],[]),
([u13,u8,u34,u0,u1,u2],[],[],[]),
([u13,u76,u0,u1,u2,u3],[],[],[(0,230)]),
([u13,u0,u1,u2,u67],[(u13,u0,u4),(u22,u1,u2),(u67,u22,u3)],[1,3],[(0,231)]),
([u13,u0,u1,u2,u53,u3],[],[],[]),
([u13,u0,u52,u1,u3],[(u13,u0,u4),(u20,u1,u3),(u52,u20,u2)],[1,3],[(0,39),(0,232)]),
([u13,u61,u0,u1,u2,u3],[],[],[(0,234)]),
([u13,u59,u0,u1,u2,u3],[],[],[(0,239)]),
([u13,u0,u1,u9,u6],[(u13,u0,u4),(u9,u2,u3),(u6,u2,u3)],[0,1,2],[(0,164),(0,235),(0,239),(0,240),(0,241)]),
([u13,u18,u0,u1,u2,u3],[(u13,u0,u4),(u6,u2,u3),(u18,u0,u6)],[0],[(0,90),(0,240)]),
([u13,u0,u42,u1,u2,u3],[(u13,u0,u4),(u6,u2,u3),(u42,u1,u6)],[1],[(0,242)]),
([u13,u96,u0,u1,u2,u3],[(u13,u0,u4),(u34,u3,u2),(u96,u34,u0)],[0],[]),
([u13,u0,u84,u1,u2,u3],[],[],[]),
([u13,u0,u1,u2,u3,u6],[(u13,u0,u4),(u19,u2,u3),(u6,u19,u3)],[2],[]),
([0x8888cccc,u0,u11,u2,u3,u4],[(u28,u0,u4),(0x8888cccc,u28,u1),(u11,u1,u2)],[0,5],[]),
([u22,0x8888cccc,u0,u2,u3,u4],[],[],[(1,243)]),
([u0,u11,u1,0xf5f5f0f0,u3,u4],[(u28,u0,u4),(0xf5f5f0f0,u28,u2),(u11,u1,u2)],[5],[]),
([u0,0xc4c4c0c0,u1,u2,u3,u4],[(u28,u0,u4),(0xf5f5f0f0,u28,u2),(0xc4c4c0c0,u1,0xf5f5f0f0)],[1,5],[]),
([u0,u1,u9,u2,0xff55ff00,u4],[(u28,u0,u4),(0xff55ff00,u28,u3),(u9,u3,u2)],[6],[]),
([u0,u1,0xd5d5c0c0,u2,u3,u4],[(u28,u0,u4),(u11,u1,u2),(0xd5d5c0c0,u28,u11)],[1,5],[]),
([0xa8a8fcfc,u0,u1,u2,u3,u4],[],[],[]),
([u28,u62,u1,u2,u3,u4],[],[],[(0,229)]),
([0x55dd00cc,u0,u1,u2,u3,u4],[],[],[]),
([u8,u20,u28,u0,u2,u4],[(u28,u0,u4),(u8,u1,u3),(u20,u1,u3)],[1],[(0,233),(0,244)]),
([0x75753030,u0,u1,u2,u3,u4],[],[],[]),
([u28,u76,u1,u2,u3,u4],[],[],[(0,230)]),
([u28,u0,u1,u2,u67,u4],[(u28,u0,u4),(u22,u1,u2),(u67,u22,u3)],[1],[(0,231)]),
([u28,u0,u52,u1,u3,u4],[(u28,u0,u4),(u20,u1,u3),(u52,u20,u2)],[1,3],[(0,40),(0,232),(0,243)]),
([u0,u1,u2,0xf555f000,u3,u4],[],[],[]),
([u61,u28,u1,u2,u3,u4],[],[],[(0,234)]),
([u28,u0,u1,u9,u6,u4],[(u28,u0,u4),(u9,u2,u3),(u6,u2,u3)],[0,1,6],[(0,235),(0,245),(0,246),(0,247)]),
([0xaaa0fff0,u0,u1,u2,u3,u4],[],[],[(0,245)]),
([u28,u18,u1,u2,u3,u4],[],[],[(0,90),(0,246)]),
([0x55f500f0,u0,u1,u2,u3,u4],[],[],[]),
([u19,u34,u28,u0,u1,u4],[(u28,u0,u4),(u19,u2,u3),(u34,u2,u3)],[1],[(0,247)]),
([0x22aa0000,u51,u0,u1,u2,u3],[(u17,u1,u3),(u51,u0,u17),(0x22aa0000,u51,u4)],[1],[(0,248)]),
([0x22aa,u51,u0,u1,u2,u3],[(u17,u1,u3),(u51,u0,u17),(0x22aa,u51,u4)],[5],[(0,249)]),
([0xa8a0a8a0,u0,u1,u2,u3,u4],[(u17,u1,u3),(u78,u17,u2),(0xa8a0a8a0,u0,u78)],[2,4,6],[(0,207)]),
([u0,u11,u1,u78,u3,u4],[],[],[]),
([u0,u42,u1,u2,u3,u4],[(u17,u1,u3),(u78,u17,u2),(u42,u1,u78)],[1,5],[]),
([0x8080aaaa,u0,u1,u2,u3],[(u11,u1,u2),(0x3f3f0000,u11,u4),(0x8080aaaa,0x3f3f0000,u0)],[5],[]),
([u56,u0,u11,u1,u2,u3],[(u17,u1,u3),(u56,u17,u4),(u11,u1,u2)],[5],[(0,250)]),
([u8,0x3f3f0000,u0,u1,u2,u3],[(u11,u1,u2),(0x3f3f0000,u11,u4),(u8,u1,u3)],[3],[]),
([u0,u11,u17,u1,u6,u4],[(u11,u1,u2),(u17,u1,u3),(u6,u2,u3)],[2,3],[]),
([u0,u11,u1,u65,u3,u4],[(u11,u1,u2),(u8,u1,u3),(u65,u8,u2)],[1],[]),
([u8,u0,u11,u1,u6,u4],[(u11,u1,u2),(u8,u1,u3),(u6,u2,u3)],[2,3],[]),
([u0,u11,u1,u95,u3,u4],[(u11,u1,u2),(u24,u1,u4),(u95,u24,u2)],[1,5],[]),
([u18,u0,u11,u1,u3,u4],[(u11,u1,u2),(u6,u2,u3),(u18,u0,u6)],[0,2],[(0,41),(0,138),(0,208),(0,251)]),
([0x33f033f0,u0,u1,u2,u6,u4],[(u17,u1,u3),(u6,u3,u2),(0x33f033f0,u17,u6)],[2,4],[]),
([0xa0a0aaaa,u0,u11,u1,u3,u4],[(u11,u1,u2),(u43,u2,u4),(0xa0a0aaaa,u43,u0)],[5],[]),
([u0,u11,u1,u3,0xff0fff00,u4],[(u11,u1,u2),(u43,u2,u4),(0xff0fff00,u43,u3)],[3],[]),
([u0,u1,u2,0xfcf0cc00,u3,u4],[(u17,u1,u3),(u33,u2,u4),(0xfcf0cc00,u17,u33)],[1],[]),
([u74,u0,u11,u2,u3,u4],[(u11,u1,u2),(u32,u3,u4),(u74,u1,u32)],[4,5],[]),
([u0,u11,u1,u3,u79,u4],[(u11,u1,u2),(u32,u3,u4),(u79,u2,u32)],[5],[]),
([u0,0xc0ffc0c0,u1,u2,u3,u4],[(u11,u1,u2),(u23,u3,u4),(0xc0ffc0c0,u23,u11)],[1,3],[]),
([0xa0a2a0a2,u0,u1,u2,u3,u4],[(u45,u1,u3),(0xf0c0f0c,u45,u2),(0xa0a2a0a2,0xf0c0f0c,u0)],[2],[]),
([0xfc00fc,u0,u1,u2,u32,u4],[],[],[]),
([u0,u11,u37,u32,u3,u4],[],[],[]),
([0xfcfcfc,u0,u1,u2,u3,u4],[],[],[]),
([u0,u86,u2,u3,u45,u4],[(u45,u1,u3),(u43,u2,u4),(u86,u43,u1)],[4],[]),
([u0,u1,0xf0c0ffcc,u2,u3,u4],[],[],[]),
([u8,u0,0xaaee0000,u1,u2,u3],[],[],[(0,252)]),
([u8,u20,u0,0xaaeeaaee,u2,u4],[(u8,u1,u3),(0xaaeeaaee,u8,u0),(u20,u1,u3)],[1],[(0,252),(0,253)]),
([u8,u20,0xaa22aa22,u0,u2,u4],[(u8,u1,u3),(0xaa22aa22,u8,u0),(u20,u1,u3)],[7],[(0,254)]),
([0xa0a8a0a8,u0,u1,u2,u3,u4],[(u8,u1,u3),(u65,u8,u2),(0xa0a8a0a8,u0,u65)],[2],[]),
([u8,u20,u0,u2,u65,u4],[(u8,u1,u3),(u65,u8,u2),(u20,u1,u3)],[7],[(0,255)]),
([0xaaa2aaa2,u0,u1,u2,u3,u4],[],[],[(0,209)]),
([u8,u20,u0,0xf030f030,u2,u4],[(u8,u1,u3),(0xf030f030,u8,u2),(u20,u1,u3)],[7],[(0,256)]),
([u8,u20,u0,u2,0xff330000,u4],[],[],[(0,257)]),
([u8,u47,u0,u1,u6,u4],[(u8,u1,u3),(u47,u1,u2),(u6,u2,u3)],[2,3],[]),
([u30,u0,u2,u4],[(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1],[(0,122),(0,144),(0,189),(0,210),(0,225),(0,237),(0,244),(0,258),(0,259),(0,260),(0,261),(0,262),(0,263),(0,265),(0,266),(0,267),(0,269),(1,264),(1,268),(1,270)]),
([u8,u30,u0,u2,u4],[(u8,u1,u3),(u20,u1,u3),(u30,u8,u20)],[1,3,7],[(0,211),(0,238),(0,253),(0,254),(0,255),(0,256),(0,257)]),
([u8,u20,u0,u33,u2,u4],[],[],[(0,269)]),
([u8,u43,u20,u0,u2,u4],[(u8,u1,u3),(u20,u1,u3),(u43,u2,u4)],[1],[(1,270)]),
([u8,u18,u0,u1,u2,u4],[(u8,u1,u3),(u6,u2,u3),(u18,u0,u6)],[0,2,4],[(0,147),(0,212)]),
([u8,0xfcc0fcc,u0,u1,u2,u4],[(u8,u1,u3),(u34,u2,u3),(0xfcc0fcc,u8,u34)],[4],[]),
([u8,u96,u0,u1,u2,u4],[(u8,u1,u3),(u34,u2,u3),(u96,u34,u0)],[0],[(0,271)]),
([u0,u1,u2,0xf0fc00cc,u3,u4],[(u8,u1,u3),(u33,u2,u4),(0xf0fc00cc,u8,u33)],[1],[]),
([0xcff0c0c,u0,u1,u2,u3,u4],[(u47,u1,u2),(u23,u3,u4),(0xcff0c0c,u47,u23)],[3],[]),
([u8,u0,u86,u2,u3,u4],[(u8,u1,u3),(u43,u2,u4),(u86,u43,u1)],[4,5],[]),
([u8,u0,u1,u2,0xffcc00cc,u4],[(u8,u1,u3),(u32,u3,u4),(0xffcc00cc,u8,u32)],[4],[]),
([0xaaaaaa,u8,u0,u1,u2,u4],[(u8,u1,u3),(u32,u3,u4),(0xaaaaaa,u0,u32)],[5],[]),
([u8,u0,u1,u2,u79,u4],[],[],[]),
([u8,0xaa00aaaa,u0,u1,u2,u4],[(u8,u1,u3),(u23,u3,u4),(0xaa00aaaa,u23,u0)],[5],[]),
([u8,u0,u1,u2,u77,u4],[],[],[]),
([0xa2a0a2a0,u0,u1,u53,u3,u4],[(u20,u1,u3),(u53,u20,u2),(0xa2a0a2a0,u0,u53)],[4,6],[(0,86)]),
([0x51505150,u0,u1,u53,u3,u4],[(u20,u1,u3),(u53,u20,u2),(0x51505150,u0,u53)],[1,6],[(1,272)]),
([u0,u1,u2,0xff300000,u67,u4],[],[],[]),
([0xa2a0a2a0,u0,u1,u2,u3,u4],[(u20,u1,u3),(u53,u20,u2),(0xa2a0a2a0,u0,u53)],[2,3,6],[]),
([u0,u1,u33,u53,u3,u4],[],[],[]),
([u0,u1,u2,0xf3f03300,u3,u4],[(u20,u1,u3),(u33,u2,u4),(0xf3f03300,u20,u33)],[1],[]),
([u74,u22,u0,u2,u3,u4],[(u22,u1,u2),(u32,u3,u4),(u74,u1,u32)],[4],[]),
([0x30ff3030,u0,u1,u2,u3,u4],[(u22,u1,u2),(u23,u3,u4),(0x30ff3030,u23,u22)],[1],[]),
([u22,u0,u1,u77,u3,u4],[(u22,u1,u2),(u23,u3,u4),(u77,u23,u2)],[7],[(0,273)]),
([0xa8a8a0a0,u0,u1,u2,u3,u4],[(u24,u1,u4),(u95,u24,u2),(0xa8a8a0a0,u0,u95)],[4,5,6,7],[]),
([u0,u1,u9,u2,0xffccff00,u4],[(u24,u1,u4),(0xffccff00,u24,u3),(u9,u3,u2)],[6],[]),
([u0,u1,u2,0xfcccf000,u3,u4],[],[],[]),
([u0,u24,u1,u9,u6,u4],[(u24,u1,u4),(u9,u2,u3),(u6,u2,u3)],[1,6],[(0,274),(0,275)]),
([0x3330fff0,u0,u1,u2,u3,u4],[],[],[(0,274)]),
([u0,u42,u24,u2,u3,u4],[(u24,u1,u4),(u6,u2,u3),(u42,u1,u6)],[1],[]),
([u0,u1,0xccfc00f0,u2,u3,u4],[(u24,u1,u4),(u19,u2,u3),(0xccfc00f0,u19,u24)],[1],[]),
([u19,u34,u0,u24,u1,u4],[],[],[(0,275)]),
([0xa2a2a0a0,u0,u1,u2,u3,u4],[],[],[]),
([u19,u0,u1,0xf3f3f0f0,u3,u4],[],[],[]),
([u0,u1,u2,0xf333f000,u3,u4],[],[],[(0,276)]),
([u31,u0,u1,u9,u6,u4],[(u31,u1,u4),(u9,u2,u3),(u6,u2,u3)],[1,2],[(0,276),(0,277)]),
([u0,0xccc0fff0,u1,u2,u3,u4],[(u31,u1,u4),(u6,u2,u3),(0xccc0fff0,u31,u6)],[5],[]),
([u31,u0,u42,u2,u3,u4],[(u31,u1,u4),(u6,u2,u3),(u42,u1,u6)],[1],[]),
([0x33f300f0,u0,u1,u2,u3,u4],[],[],[]),
([u19,u34,u31,u0,u1,u4],[(u31,u1,u4),(u19,u2,u3),(u34,u2,u3)],[1],[(0,277)]),
([u0,0xc444c444,u1,u2,u3,u4],[(u9,u2,u3),(u61,u0,u9),(0xc444c444,u61,u1)],[1,2,5],[(0,59),(0,214)]),
([0xa222a222,u0,u1,u2,u3,u4],[],[],[]),
([u59,u0,u1,u6,u4],[(u9,u2,u3),(u59,u1,u9),(u6,u2,u3)],[0,2],[(0,166),(0,215),(0,239),(0,278),(0,279),(0,280),(0,281),(0,282)]),
([u18,u0,u1,u9,u4],[(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0,2,6],[(0,43),(0,72),(0,216),(0,217),(0,227),(0,240),(0,246),(0,280),(0,283),(0,284)]),
([u18,u0,u1,u9,u6,u4],[(u9,u2,u3),(u6,u2,u3),(u18,u0,u6)],[0,6],[(0,218),(0,285),(0,286)]),
([u73,u0,u1,u9,u6,u4],[(u9,u2,u3),(u6,u2,u3),(u73,u0,u6)],[0,1,6],[(0,165),(0,219),(0,287),(0,288)]),
([u0,u42,u1,u9,u6,u4],[(u9,u2,u3),(u6,u2,u3),(u42,u1,u6)],[1,2,6],[(0,278),(0,281),(0,289),(0,290)]),
([u93,u0,u1,u9,u6,u4],[(u9,u2,u3),(u6,u2,u3),(u93,u1,u6)],[2,6],[(0,279),(0,282),(0,291)]),
([u29,u0,u1,u4],[(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[1],[(0,44),(0,51),(0,60),(0,73),(0,228),(0,247),(0,275),(0,277),(0,292),(0,293),(0,294),(0,295),(0,296),(0,297),(0,298),(0,299),(0,300),(0,301)]),
([u29,u0,u1,u6,u4],[(u9,u2,u3),(u6,u2,u3),(u29,u9,u6)],[0,1,2,6],[(0,220),(0,241),(0,278),(0,286),(0,288),(0,290),(0,291),(0,302),(0,303)]),
([u0,u1,u9,0xfff00000,u6,u4],[(u9,u2,u3),(u6,u2,u3),(0xfff00000,u6,u4)],[1],[(0,303)]),
([0x444c444c,u0,u1,u2,u3,u4],[],[],[(0,221)]),
([u0,0xaaaf0000,u1,u2,u3,u6],[],[],[(0,287)]),
([0x222a222a,u0,u1,u2,u3,u4],[(u6,u2,u3),(u42,u1,u6),(0x222a222a,u0,u42)],[1,5],[]),
([u0,u42,u1,u2,u3,0xffffccc0],[(u6,u2,u3),(u42,u1,u6),(0xffffccc0,u42,u4)],[5],[(0,304)]),
([0x333f0000,u0,u42,u1,u2,u3],[(u6,u2,u3),(u42,u1,u6),(0x333f0000,u42,u4)],[1],[]),
([0x333f0000,u0,u1,u2,u3,u6],[],[],[(0,289)]),
([0x44c444c4,u0,u1,u2,u3,u4],[(u19,u2,u3),(0xaa0aaa0a,u19,u0),(0x44c444c4,0xaa0aaa0a,u1)],[1,5],[]),
([0x22a222a2,u0,u1,u2,u3,u4],[],[],[]),
([u0,0xc4c44444,u1,u2,u3,u4],[(u33,u2,u4),(0xa0aaaaa,u0,u33),(0xc4c44444,0xa0aaaaa,u1)],[1,5],[]),
([0xa2a22222,u0,u1,u2,u3,u4],[(u33,u2,u4),(0xc0ccccc,u1,u33),(0xa2a22222,0xc0ccccc,u0)],[2],[(0,74)]),
([0xaaa0a0a0,u0,u1,u2,u3,u4],[(u32,u3,u4),(u79,u32,u2),(0xaaa0a0a0,u0,u79)],[2,4,6],[]),
([u0,0xccc0c0c0,u1,u2,u3,u4],[(u32,u3,u4),(u79,u32,u2),(0xccc0c0c0,u1,u79)],[1,5],[]),
([0x44cc4444,u0,u1,u2,u3,u4],[(u23,u3,u4),(0xaa00aaaa,u23,u0),(0x44cc4444,0xaa00aaaa,u1)],[1,5],[]),
([0x22aa2222,u0,u1,u2,u3,u4],[(u23,u3,u4),(0xcc00cccc,u23,u1),(0x22aa2222,u0,0xcc00cccc)],[5],[]),
([0xa0aaa0a0,u0,u1,u2,u3,u4],[(u23,u3,u4),(u77,u23,u2),(0xa0aaa0a0,u0,u77)],[2],[]),
([u0,0xc0ccc0c0,u1,u2,u3,u4],[(u23,u3,u4),(u77,u23,u2),(0xc0ccc0c0,u1,u77)],[1,5],[])
]
set_option maxRecDepth 100000 in
def c5_3_L6 : Array W5Node := Array.mk [
([u83,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u83,u7,u2)],[1,2,6],[(0,2),(0,5),(0,6),(1,0),(1,1),(1,3),(1,4)]),
([u0,u1,u2,u46,u3,u4],[(u7,u0,u1),(u46,u7,u2)],[0,1,2,3,4,5,6,7],[(0,7),(0,8),(0,9),(0,10),(0,11)]),
([u7,u0,u1,u2,u46,u3,u4],[(u7,u0,u1),(u46,u7,u2)],[0,2,3,6],[(0,5),(0,12),(0,13)]),
([u89,u0,u1,u2,u3,u4],[(u7,u0,u1),(u89,u7,u3)],[1,2,4,5,6,7],[(0,16),(0,17),(1,14),(1,15)]),
([u89,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u89,u7,u3)],[4,7],[(0,20),(0,21),(1,18),(1,19)]),
([0x70707070,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(0x70707070,u7,u2)],[0,2,3,6],[(0,22),(1,20)]),
([u85,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u85,u7,u4)],[1,5],[(0,23),(0,24),(0,25),(0,26),(1,25),(1,26)]),
([0x77770000,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(0x77770000,u7,u4)],[1,3,5],[]),
([u7,u12,u0,u1,u2,u3,u4],[(u7,u0,u1),(u12,u0,u2)],[0,2,3,6],[(0,7),(0,27),(0,29),(1,1),(1,28)]),
([u10,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u10,u0,u3)],[0,3,4,7],[(0,30),(0,31),(1,19)]),
([u7,u5,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4)],[0,1,3,5],[(0,6),(0,12),(0,21),(0,22),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(1,6),(1,12),(1,21),(1,22),(1,36),(1,37),(1,38),(1,39),(1,40),(1,41),(1,44)]),
([u7,u5,u0,u1,u2,u3],[(u7,u0,u1),(u5,u0,u4)],[0,1,2,3,4,5],[(0,8),(0,16),(0,29),(0,30),(0,45),(0,46),(0,47),(0,48),(1,8),(1,16),(1,29),(1,30),(1,47),(1,48)]),
([u7,u5,u1,u2,u3,u4],[(u7,u0,u1),(u5,u0,u4)],[0,1,3,5],[(0,49),(0,50),(1,49),(1,50)]),
([u7,u5,u0,u1,u2,u3,u4],[(u7,u0,u1),(u5,u0,u4)],[0,1,3,5],[(0,24)]),
([u13,u7,u0,u1,u2,u3],[(u7,u0,u1),(u13,u0,u4)],[0,1,2,3,4],[(0,9),(0,17),(0,51),(0,52),(0,53),(1,9),(1,17),(1,52),(1,53)]),
([u28,u7,u1,u2,u3,u4],[(u7,u0,u1),(u28,u0,u4)],[0,1,3],[(0,51),(0,54),(0,55),(0,56),(1,55),(1,56)]),
([u7,u0,u11,u2,u3,u4],[(u7,u0,u1),(u11,u1,u2)],[0,2,3,4],[(0,13),(0,38),(0,47),(0,49),(0,52),(0,55),(0,57),(1,31),(1,58)]),
([u7,u0,u11,u1,u2,u3,u4],[(u7,u0,u1),(u11,u1,u2)],[0,1,2,3,6],[(0,10),(0,39),(1,0),(1,59)]),
([u8,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u8,u1,u3)],[0,3,4,7],[(0,40),(1,18)]),
([u22,u7,u0,u2,u3,u4],[(u7,u0,u1),(u22,u1,u2)],[0,2,3,4],[(0,41),(0,48),(0,50),(0,53),(0,56),(0,60),(1,61)]),
([u7,u0,u24,u1,u2,u3,u4],[(u7,u0,u1),(u24,u1,u4)],[0,1,5],[(0,23)]),
([u7,u0,u1,u9,u2,u3,u4],[(u7,u0,u1),(u9,u2,u3)],[2,3],[(0,42),(0,62),(0,63),(0,64)]),
([u7,u0,u1,u2,u3,u6,u4],[(u7,u0,u1),(u6,u2,u3)],[0,2,3,4,6,7],[(0,43),(0,57),(0,64),(0,65),(0,66),(0,67),(0,68),(1,57)]),
([u19,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u19,u2,u3)],[2,3],[(0,11),(0,44),(0,69),(0,72),(1,70),(1,71)]),
([u7,u0,u1,u33,u2,u3,u4],[(u7,u0,u1),(u33,u2,u4)],[1,2,5],[(0,73),(1,74)]),
([u23,u7,u0,u1,u2,u3,u4],[(u7,u0,u1),(u23,u3,u4)],[1,3,5],[(0,58),(0,75),(1,76),(1,77)]),
([u0,u1,u99,u3,u4],[(u25,u0,u1),(u99,u25,u2)],[0,1,2,3],[(0,78),(0,79)]),
([u55,u0,u1,u2,u4],[(u25,u0,u1),(u55,u25,u3)],[0,1,3,7],[(0,80),(0,81),(0,82),(0,83),(0,84)]),
([u55,u0,u1,u2,u3,u4],[(u25,u0,u1),(u55,u25,u3)],[0,1,2,3,5,6,7],[(0,85),(0,86),(0,87)]),
([u0,u1,u71,u2,u3],[(u25,u0,u1),(u71,u25,u4)],[0,1,3,5],[(0,88),(0,89),(0,90),(1,90)]),
([u0,u1,u25,u9,u2,u3,u4],[(u25,u0,u1),(u9,u2,u3)],[0,1,2,4],[(0,85),(0,88),(0,91),(0,92),(0,93),(1,85)]),
([u0,u1,u25,u2,u3,u6,u4],[(u25,u0,u1),(u6,u2,u3)],[0,1,2,4,6,7],[(0,89),(0,93),(0,94)]),
([u19,u0,u1,u25,u2,u3,u4],[(u25,u0,u1),(u19,u2,u3)],[0,1,2,4,7],[(0,90),(0,96),(1,86),(1,95)]),
([u0,u1,u25,u33,u2,u3,u4],[(u25,u0,u1),(u33,u2,u4)],[0,1,2,3,5],[(0,83),(1,78),(1,87),(1,97),(1,98)]),
([u23,u0,u1,u25,u2,u3,u4],[(u25,u0,u1),(u23,u3,u4)],[0,1,4,5,7],[(0,79),(1,84),(1,99)]),
([u7,u0,u1,u2,u3,u4],[(u21,u0,u1),(u7,u21,u0)],[0,1,2,3,4,5,6,7],[(0,51),(0,100),(0,101),(1,101)]),
([u0,u1,u2,u75,u3,u4],[(u21,u0,u1),(u75,u21,u2)],[0,1,2,3,4,5,6,7],[(0,14),(0,102),(0,103),(0,104),(0,105),(0,106)]),
([u21,u16,u2,u3,u4],[(u21,u0,u1),(u16,u0,u1)],[0,1,3],[(0,107),(0,108),(0,109),(0,110),(0,111),(1,109),(1,110),(1,111)]),
([u21,u12,u0,u1,u2,u3,u4],[(u21,u0,u1),(u12,u0,u2)],[0,2,3],[(0,14),(0,102),(0,113),(1,112),(1,114)]),
([u10,u21,u0,u1,u2,u3,u4],[(u21,u0,u1),(u10,u0,u3)],[0,3,4,7],[(0,116),(1,115)]),
([u21,u5,u0,u1,u2,u3],[(u21,u0,u1),(u5,u0,u4)],[0,1,2,3,4,5],[(0,51),(0,103),(0,117),(0,118),(1,103),(1,118)]),
([u21,u5,u0,u1,u2,u3,u4],[(u21,u0,u1),(u5,u0,u4)],[0,1,3,5],[(0,100),(0,119)]),
([u13,u21,u0,u1,u2,u3],[(u21,u0,u1),(u13,u0,u4)],[0,1,2,3,4],[(0,104),(0,120),(1,104),(1,120)]),
([u21,u0,u11,u2,u3,u4],[(u21,u0,u1),(u11,u1,u2)],[0,2,3,4],[(0,101),(0,118),(0,120),(0,121),(1,116),(1,122)]),
([u21,u0,u1,u9,u2,u3,u4],[(u21,u0,u1),(u9,u2,u3)],[0,2,3],[(0,107),(0,123),(0,124),(0,125)]),
([u21,u0,u1,u2,u3,u6,u4],[(u21,u0,u1),(u6,u2,u3)],[2,3,4,6,7],[(0,108),(0,121),(0,125),(0,126),(0,127),(1,121)]),
([u19,u21,u0,u1,u2,u3,u4],[(u21,u0,u1),(u19,u2,u3)],[2,3],[(0,105),(0,109),(0,128),(0,130),(1,129)]),
([u21,u0,u1,u33,u2,u3,u4],[(u21,u0,u1),(u33,u2,u4)],[1,2,3],[(0,106),(0,110),(0,131)]),
([u23,u21,u0,u1,u2,u3,u4],[(u21,u0,u1),(u23,u3,u4)],[1,3,4,5,7],[(0,111),(0,122),(0,132),(1,133)]),
([u0,u1,u2,0xf4f4f4f4,u3,u4],[(u16,u0,u1),(0xf4f4f4f4,u16,u2)],[0,1,3,4,5,6,7],[(0,15),(0,134),(1,135)]),
([u0,u68,u1,u2,u3],[(u16,u0,u1),(u68,u16,u4)],[0,1,3,5],[(0,136),(0,137),(0,138),(0,139),(0,140),(1,136),(1,137),(1,140)]),
([u16,u5,u1,u2,u3],[(u16,u0,u1),(u5,u0,u4)],[0,3,5],[(0,51),(0,141),(0,142),(0,143),(0,144),(0,145),(0,146),(0,147),(0,148),(0,149),(1,143),(1,144),(1,145),(1,146),(1,149)]),
([u16,u5,u1,u2,u3,u4],[(u16,u0,u1),(u5,u0,u4)],[0,1,3,5],[(0,100)]),
([u16,u0,u11,u1,u2,u3,u4],[(u16,u0,u1),(u11,u1,u2)],[0,1,2,3],[(0,15),(0,101),(0,134),(0,136),(0,145),(1,150),(1,151)]),
([u8,u16,u0,u1,u2,u3,u4],[(u16,u0,u1),(u8,u1,u3)],[0,1,3,4,7],[(0,137),(0,146),(1,152)]),
([u16,u0,u24,u1,u2,u3,u4],[(u16,u0,u1),(u24,u1,u4)],[0,1,3,5],[(0,153)]),
([u16,u0,u1,u9,u2,u3,u4],[(u16,u0,u1),(u9,u2,u3)],[0,1,2,4],[(0,107),(0,135),(0,138),(0,147),(0,154),(0,155),(1,135)]),
([u16,u0,u1,u2,u3,u6,u4],[(u16,u0,u1),(u6,u2,u3)],[0,1,6],[(0,108),(0,139),(0,148),(0,155),(0,156),(0,157)]),
([u19,u16,u0,u1,u2,u3,u4],[(u16,u0,u1),(u19,u2,u3)],[0,1,2,4,7],[(0,109),(0,140),(0,149),(0,158),(0,159)]),
([u16,u0,u1,u33,u2,u3,u4],[(u16,u0,u1),(u33,u2,u4)],[0,1,2,3,5],[(0,110),(0,160),(1,161)]),
([u23,u16,u0,u1,u2,u3,u4],[(u16,u0,u1),(u23,u3,u4)],[0,1,5],[(0,111),(0,162)]),
([u10,u0,u1,u2,u3,u4],[(u15,u0,u3),(u10,u15,u0)],[0,1,2,3,4,5,6,7],[(1,15)]),
([u82,u0,u1,u2,u3,u4],[(u15,u0,u3),(u82,u15,u1)],[0,1,2,3,4,5,6,7],[(0,1),(0,112),(0,163),(0,164),(1,14)]),
([u0,u1,u2,u40,u4],[(u12,u0,u2),(u40,u12,u3)],[0,1,2,7],[(0,27),(0,113),(0,165),(0,166),(0,167),(0,168),(0,172),(0,173),(0,175),(1,169),(1,170),(1,171),(1,174)]),
([u0,u1,u2,u36,u3,u4],[(u15,u0,u3),(u36,u15,u2)],[0,1,2,3,4,5,6],[(0,174),(0,176),(0,177),(0,178),(0,179),(0,180),(0,181),(0,182),(0,183),(0,184)]),
([u63,u0,u1,u3,u4],[(u15,u0,u3),(u63,u15,u2)],[0,1,2,4],[(0,28),(0,114),(0,185),(0,186),(0,187),(0,188),(0,189)]),
([u12,u1,u14,u3,u4],[(u12,u0,u2),(u14,u0,u2)],[0,1,2],[(0,191),(0,192),(0,193),(0,195),(0,196),(0,197),(0,198),(1,190),(1,194)]),
([u12,u15,u0,u1,u2,u3,u4],[(u12,u0,u2),(u15,u0,u3)],[0,2,4],[(0,176),(0,177),(0,199),(1,176)]),
([u10,u12,u0,u1,u2,u3,u4],[(u12,u0,u2),(u10,u0,u3)],[0,2,4,6,7],[(0,200)]),
([u12,u5,u0,u1,u2,u3],[(u12,u0,u2),(u5,u0,u4)],[0,1,2,3,4,5],[(0,29),(0,166),(0,199),(0,201),(1,163),(1,178),(1,185),(1,202),(1,203)]),
([u12,u5,u0,u1,u2,u3,u4],[(u12,u0,u2),(u5,u0,u4)],[0,1,2,5],[(0,167),(0,204),(1,186)]),
([u13,u12,u0,u1,u2,u3],[(u12,u0,u2),(u13,u0,u4)],[0,1,2,3,4],[(0,168),(1,164),(1,179),(1,187),(1,205),(1,206)]),
([u8,u15,u0,u1,u2,u4],[(u15,u0,u3),(u8,u1,u3)],[0,2,3,4,5,7],[(0,169),(0,183),(0,202),(0,205),(0,207)]),
([u12,u0,u17,u1,u2,u3,u4],[(u12,u0,u2),(u17,u1,u3)],[1,2,4],[(0,191),(0,209),(0,210),(1,180),(1,208)]),
([u12,u0,u1,u2,u3,u45,u4],[(u12,u0,u2),(u45,u1,u3)],[0,2,3,4,7],[(0,192),(0,210),(0,212),(1,211),(1,213)]),
([u8,u12,u0,u1,u2,u3,u4],[(u12,u0,u2),(u8,u1,u3)],[2,4,7],[(0,193),(0,214),(0,215),(0,216),(0,217)]),
([u22,u15,u0,u1,u2,u3,u4],[(u15,u0,u3),(u22,u1,u2)],[2,3,4],[(0,181),(0,194),(1,216),(1,218),(1,219)]),
([u12,u0,u24,u1,u2,u3,u4],[(u12,u0,u2),(u24,u1,u4)],[1,2,5],[(0,172),(0,195),(0,220),(1,188)]),
([u31,u12,u0,u1,u2,u3,u4],[(u12,u0,u2),(u31,u1,u4)],[1,2,3,5],[(0,173),(0,196),(0,221),(0,222),(1,189)]),
([u19,u15,u0,u1,u2,u4],[(u15,u0,u3),(u19,u3,u2)],[0,2,4,7],[(0,174),(0,203),(0,206),(0,223),(1,217),(1,224)]),
([u12,u0,u1,u2,u32,u3,u4],[(u12,u0,u2),(u32,u3,u4)],[2,4],[(0,197),(1,184),(1,225)]),
([u23,u12,u0,u1,u2,u3,u4],[(u12,u0,u2),(u23,u3,u4)],[1,2,4,5,7],[(0,198),(0,226),(0,227)]),
([u0,u39,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14)],[0,1,2,6],[(0,229),(0,230),(0,232),(0,234),(0,235),(0,236),(0,237),(1,228),(1,231),(1,233)]),
([u0,u39,u1,u2,u3,u4],[(u14,u0,u2),(u39,u1,u14)],[0,1,2,3,4,5,6,7],[(0,239),(0,240),(0,242),(0,243),(0,244),(0,245),(1,238),(1,241)]),
([0x32323232,u0,u2,u3,u4],[(u14,u0,u2),(0x32323232,u1,u14)],[0,1,2,3,6],[(0,246),(0,247)]),
([u0,u11,u1,u2,u3,u26,u4],[(u26,u0,u3),(u11,u1,u2)],[0,1,2,3,4,7],[(0,238),(0,251),(0,253),(1,191),(1,248),(1,249),(1,250),(1,252)]),
([u0,u1,u2,u14,u3,u45,u4],[(u14,u0,u2),(u45,u1,u3)],[0,1,3,4,7],[(0,192),(0,239),(0,255),(0,256),(1,254)]),
([u8,u0,u1,u2,u14,u3,u4],[(u14,u0,u2),(u8,u1,u3)],[0,1,3,4,7],[(0,193),(0,240),(0,258),(0,259),(0,260),(1,257)]),
([u22,u0,u1,u2,u3,u26,u4],[(u26,u0,u3),(u22,u1,u2)],[0,1,2,3,4,7],[(0,194),(0,241),(0,263),(1,258),(1,261),(1,262)]),
([u0,u24,u1,u2,u14,u3,u4],[(u14,u0,u2),(u24,u1,u4)],[0,1,2,3,5,6],[(0,195),(0,242),(0,264),(0,266),(1,265)]),
([u31,u0,u1,u2,u14,u3,u4],[(u14,u0,u2),(u31,u1,u4)],[0,1,3,5],[(0,196),(0,243),(0,267),(0,269),(1,268)]),
([u0,u1,u2,u26,u6,u4],[(u26,u0,u3),(u6,u3,u2)],[0,2,4,7],[(0,251),(0,270),(1,234),(1,244),(1,259)]),
([u19,u0,u1,u14,u3,u4],[(u14,u0,u2),(u19,u2,u3)],[0,2,4,6],[(0,235),(0,245),(1,271)]),
([u0,u1,0xf0a0f0a0,u3,u4],[(u26,u0,u3),(0xf0a0f0a0,u26,u2)],[0,1,2,4,7],[(0,265),(0,268)]),
([u48,u0,u1,u2,u4],[(u14,u0,u2),(u48,u14,u3)],[0,1,2,6,7],[(0,266),(0,269),(0,272),(0,273),(0,274)]),
([u48,u0,u1,u2,u3,u4],[(u14,u0,u2),(u48,u14,u3)],[0,1,2,3,5,6,7],[(0,252),(0,262),(0,276),(1,275)]),
([u0,u1,u2,0xfafa0000,u3],[(u14,u0,u2),(0xfafa0000,u14,u4)],[0,1,2,5,6],[(0,256),(0,260),(1,253),(1,263)]),
([u0,u1,u33,u2,u3,u26,u4],[(u26,u0,u3),(u33,u2,u4)],[0,1,2,4,5,7],[(1,197),(1,236),(1,246),(1,276),(1,277)]),
([u23,u0,u1,u2,u14,u3,u4],[(u14,u0,u2),(u23,u3,u4)],[0,1,4,5,7],[(0,198),(0,237),(0,247),(1,278)]),
([u10,u0,u1,0xcceeccee,u2,u3,u4],[(u10,u0,u3),(0xcceeccee,u10,u1)],[0,3,4,7],[(0,279),(0,280),(0,281),(1,15)]),
([u0,u60,u1,u2,u3,u4],[(u49,u0,u2),(u60,u49,u1)],[0,1,2,3,4,5,6,7],[(0,19),(0,115),(0,282),(0,283),(0,284),(1,285)]),
([u10,u0,u91,u1,u2,u3,u4],[(u10,u0,u3),(u91,u10,u1)],[0,1,3,4,7],[(0,286),(0,287)]),
([u0,u1,u2,u54,u3,u4],[(u10,u0,u3),(u54,u10,u2)],[0,1,2,3,4,5,6,7],[(0,200),(0,288),(0,289),(0,290),(0,292),(0,293),(1,291)]),
([u10,u0,u1,u2,u54,u3,u4],[(u10,u0,u3),(u54,u10,u2)],[0,2,6,7],[(0,294)]),
([u57,u0,u1,u2,u3,u4],[(u10,u0,u3),(u57,u10,u2)],[0,1,2,3,4,5,6,7],[(0,177),(0,295),(0,296),(0,297),(0,298),(0,299),(1,298)]),
([u10,u0,u1,0xf050f050,u2,u3,u4],[(u10,u0,u3),(0xf050f050,u10,u2)],[0,2,6,7],[(0,300)]),
([u10,u0,u1,u2,u3,0xff550000,u4],[(u10,u0,u3),(0xff550000,u10,u4)],[1,5],[(0,301)]),
([u10,u49,u0,u1,u2,u3,u4],[(u10,u0,u3),(u49,u0,u2)],[0,2,4,6,7],[(0,302),(0,303)]),
([u10,u27,u1,u2,u4],[(u10,u0,u3),(u27,u0,u3)],[0,1,7],[(0,190),(0,279),(0,286),(0,294),(0,300),(0,301),(0,304),(0,305),(0,306),(0,307),(0,308),(0,309),(0,310),(0,311),(0,312)]),
([u10,u5,u0,u1,u2,u3],[(u10,u0,u3),(u5,u0,u4)],[0,1,2,3,4,5],[(0,16),(0,30),(0,288),(0,296),(0,302),(0,313),(0,314),(0,315),(0,316),(0,317),(0,318),(1,282)]),
([u10,u5,u0,u1,u2,u3,u4],[(u10,u0,u3),(u5,u0,u4)],[0,1,4,5,7],[]),
([u13,u10,u0,u1,u2,u3],[(u10,u0,u3),(u13,u0,u4)],[0,1,2,3,4],[(0,17),(0,289),(0,297),(0,319),(0,320),(0,321),(0,322),(1,283)]),
([u10,u0,u11,u1,u2,u3,u4],[(u10,u0,u3),(u11,u1,u2)],[0,1,2,7],[(0,298),(0,305),(0,323),(0,324),(0,325)]),
([u10,u0,u1,u2,u37,u3,u4],[(u10,u0,u3),(u37,u1,u2)],[3,4,7],[(0,306),(1,326)]),
([u10,u47,u0,u1,u2,u3,u4],[(u10,u0,u3),(u47,u1,u2)],[2,4,6,7],[(0,307),(0,328),(0,329),(1,327)]),
([u10,u22,u0,u1,u2,u3,u4],[(u10,u0,u3),(u22,u1,u2)],[3,4,7],[(0,308),(0,328),(0,330)]),
([u10,u0,u17,u1,u2,u4],[(u10,u0,u3),(u17,u1,u3)],[0,2,3,4,5,7],[(0,31),(0,116),(0,315),(0,319),(0,331),(1,291),(1,298)]),
([u10,u8,u0,u1,u2,u4],[(u10,u0,u3),(u8,u1,u3)],[0,2,3,4,5,7],[(0,292),(0,316),(0,320)]),
([u10,u0,u24,u1,u2,u3,u4],[(u10,u0,u3),(u24,u1,u4)],[1,5,7],[(0,309),(0,332)]),
([u10,u31,u0,u1,u2,u3,u4],[(u10,u0,u3),(u31,u1,u4)],[1,3,4,5,7],[(0,310),(0,333)]),
([u10,u0,u1,u9,u2,u4],[(u10,u0,u3),(u9,u2,u3)],[0,2,4,7],[(0,271),(0,299),(0,303),(0,317),(0,321),(0,334),(0,335)]),
([u10,u19,u0,u1,u2,u4],[(u10,u0,u3),(u19,u2,u3)],[0,2,4,7],[(0,293),(0,318),(0,322),(0,329),(0,336)]),
([u10,u0,u1,u33,u2,u3,u4],[(u10,u0,u3),(u33,u2,u4)],[1,2,7],[(0,311),(0,337)]),
([u10,u43,u0,u1,u2,u3,u4],[(u10,u0,u3),(u43,u2,u4)],[1,4,5,7],[(0,312),(1,338)]),
([u80,u0,u1,u2,u3,u4],[(u27,u0,u3),(u80,u27,u1)],[0,1,2,3,4,5,6],[(0,339),(0,340),(0,341)]),
([u0,u1,u2,0xf5f0f5f0,u3,u4],[(u27,u0,u3),(0xf5f0f5f0,u27,u2)],[0,1,2,3,4,5,6],[(0,342),(0,343)]),
([u0,u69,u1,u2,u3],[(u27,u0,u3),(u69,u27,u4)],[0,1,4,5],[(0,344),(0,345),(0,347),(1,346)]),
([u35,u0,u17,u1,u2,u3,u4],[(u35,u0,u2),(u17,u1,u3)],[0,1,2,3,4],[(0,349),(0,350),(0,351),(0,352),(1,305),(1,339),(1,342),(1,344),(1,348)]),
([u35,u0,u1,u2,u3,u45,u4],[(u35,u0,u2),(u45,u1,u3)],[0,1,3],[(0,351),(0,354),(1,306),(1,345),(1,353)]),
([u8,u35,u0,u1,u2,u3,u4],[(u35,u0,u2),(u8,u1,u3)],[0,1,4,7],[(0,346),(0,355),(0,356),(0,357),(1,307)]),
([u22,u27,u0,u1,u2,u3,u4],[(u27,u0,u3),(u22,u1,u2)],[0,1,3,4],[(0,308),(0,340),(0,347),(1,356),(1,358),(1,359)]),
([u35,u0,u24,u1,u2,u3,u4],[(u35,u0,u2),(u24,u1,u4)],[0,1,2,5],[(0,360),(0,361),(1,309)]),
([u31,u35,u0,u1,u2,u3,u4],[(u35,u0,u2),(u31,u1,u4)],[0,1,3,5],[(0,362),(1,310)]),
([u35,u0,u1,u3,u6,u4],[(u35,u0,u2),(u6,u2,u3)],[0,2,4],[(0,352),(0,357),(1,223),(1,341),(1,363)]),
([u35,u0,u1,u2,u32,u3,u4],[(u35,u0,u2),(u32,u3,u4)],[0,1,2,4,5],[(0,365),(1,311),(1,364)]),
([u23,u35,u0,u1,u2,u3,u4],[(u35,u0,u2),(u23,u3,u4)],[0,1,5],[(0,366),(1,312)]),
([u5,u0,u1,u64,u2,u3],[(u5,u0,u4),(u64,u5,u1)],[0,1,2,3,4,5],[(0,33),(0,45),(0,367),(0,368),(0,369),(0,370),(0,371),(1,367),(1,368),(1,369),(1,370),(1,371)]),
([u44,u5,u0,u1,u2,u3],[(u5,u0,u4),(u44,u5,u1)],[0,1,2,3,4,5],[(0,34),(0,35),(0,46),(0,117),(0,142),(0,372),(0,373),(0,374),(0,375),(1,372),(1,373),(1,374),(1,375)]),
([u5,u0,u1,u2,u41,u3],[(u5,u0,u4),(u41,u5,u2)],[0,1,2,3,4,5],[(0,36),(0,143),(0,201),(0,367),(0,377),(0,378),(0,380),(0,381),(0,382),(1,313),(1,373),(1,376),(1,379)]),
([u70,u5,u0,u1,u2,u3],[(u5,u0,u4),(u70,u5,u2)],[0,1,2,3,4,5],[(0,37),(0,144),(0,385),(0,386),(1,314),(1,383),(1,384)]),
([u5,u0,u11,u1,u2,u3],[(u5,u0,u4),(u11,u1,u2)],[0,1,2,3,4,5],[(0,38),(0,39),(0,47),(0,118),(0,145),(0,387),(0,388),(0,392),(1,315),(1,389),(1,390),(1,391)]),
([u5,u0,u1,u2,u37,u3],[(u5,u0,u4),(u37,u1,u2)],[0,1,2,3,4,5],[(0,374),(0,385),(0,393),(0,394),(0,395),(0,396),(1,376),(1,390)]),
([u8,u5,u0,u1,u2,u3],[(u5,u0,u4),(u8,u1,u3)],[0,1,2,3,4,5],[(0,16),(0,40),(0,146),(0,202),(0,316),(0,368),(0,373),(0,375),(0,397),(0,399),(0,400),(0,401),(0,402),(0,403),(1,398)]),
([u22,u5,u0,u1,u2,u3],[(u5,u0,u4),(u22,u1,u2)],[0,1,2,3,4,5],[(0,41),(0,48),(0,377),(0,404),(0,407),(1,401),(1,405),(1,406),(1,408),(1,409)]),
([u5,u0,u1,u9,u2,u3],[(u5,u0,u4),(u9,u2,u3)],[0,1,2,3,4,5],[(0,42),(0,147),(0,317),(0,410),(0,411),(0,412),(0,413),(0,414),(1,317)]),
([u5,u0,u1,u2,u3,u6],[(u5,u0,u4),(u6,u2,u3)],[0,1,2,3,4,5],[(0,43),(0,148),(0,296),(0,379),(0,381),(0,386),(0,392),(0,400),(0,402),(0,414),(0,415),(0,416),(0,417),(0,418),(0,419),(0,420),(1,379),(1,386),(1,392),(1,402)]),
([u19,u5,u0,u1,u2,u3],[(u5,u0,u4),(u19,u2,u3)],[0,1,2,3,4,5],[(0,44),(0,149),(0,203),(0,318),(0,380),(0,421),(0,424),(1,403),(1,422),(1,423)]),
([u44,u0,u1,u2,u3,u4],[(u5,u0,u4),(u44,u5,u1)],[0,1,2,3,4,5,6,7],[(0,24),(0,119),(0,425),(0,426),(1,425),(1,426)]),
([u0,u1,u2,u41,u3,u4],[(u5,u0,u4),(u41,u5,u2)],[0,1,2,3,4,5,6,7],[(0,204),(0,427),(0,428),(0,429)]),
([u5,u0,u11,u1,u2,u3,u4],[(u5,u0,u4),(u11,u1,u2)],[1,2,5],[(0,49),(0,430)]),
([u5,u0,u1,u2,u37,u3,u4],[(u5,u0,u4),(u37,u1,u2)],[0,1,2,3,5,6],[(0,425),(0,431),(0,432)]),
([u8,u5,u0,u1,u2,u3,u4],[(u5,u0,u4),(u8,u1,u3)],[1,3,4,5,7],[(0,426),(0,433),(0,434)]),
([u22,u5,u0,u1,u2,u3,u4],[(u5,u0,u4),(u22,u1,u2)],[0,1,2,3,5],[(0,50),(0,427),(0,435),(0,437),(1,434),(1,436),(1,438)]),
([u5,u0,u1,u9,u2,u3,u4],[(u5,u0,u4),(u9,u2,u3)],[0,1,2,5],[(0,439),(0,440),(0,441)]),
([u5,u0,u1,u2,u3,u6,u4],[(u5,u0,u4),(u6,u2,u3)],[0,1,2,4,5,6,7],[(0,441),(0,442),(0,443)]),
([u19,u5,u0,u1,u2,u3,u4],[(u5,u0,u4),(u19,u2,u3)],[1,2,5],[(0,429),(0,444),(0,445)]),
([u5,u0,u1,u2,u3],[(u13,u0,u4),(u5,u13,u0)],[0,1,5],[(0,51),(0,390),(0,424),(0,446),(0,447),(0,448),(0,449),(0,450),(1,390),(1,446),(1,447),(1,448),(1,450)]),
([u13,u0,u11,u1,u2,u3],[(u13,u0,u4),(u11,u1,u2)],[0,1,2,3,4],[(0,52),(0,120),(0,446),(0,451),(0,455),(1,319),(1,452),(1,453),(1,454)]),
([u13,u0,u1,u2,u37,u3],[(u13,u0,u4),(u37,u1,u2)],[0,1,2,3,4],[(0,447),(0,456),(0,457),(1,453)]),
([u13,u8,u0,u1,u2,u3],[(u13,u0,u4),(u8,u1,u3)],[0,1,2,3,4],[(0,17),(0,205),(0,320),(0,390),(0,459),(0,460),(0,461),(0,462),(0,463),(1,458)]),
([u13,u22,u0,u1,u2,u3],[(u13,u0,u4),(u22,u1,u2)],[0,1,2,3,4],[(0,53),(0,448),(0,465),(1,461),(1,464),(1,466),(1,467)]),
([u13,u0,u1,u9,u2,u3],[(u13,u0,u4),(u9,u2,u3)],[0,1,2,3,4],[(0,321),(0,449),(0,468),(0,469),(0,470),(1,321)]),
([u13,u0,u1,u2,u3,u6],[(u13,u0,u4),(u6,u2,u3)],[0,1,2,3,4],[(0,297),(0,424),(0,455),(0,460),(0,462),(0,470),(0,471),(0,472),(1,455),(1,462)]),
([u13,u19,u0,u1,u2,u3],[(u13,u0,u4),(u19,u2,u3)],[0,1,2,3,4],[(0,206),(0,322),(0,450),(0,475),(1,463),(1,473),(1,474)]),
([0x8888cccc,u0,u1,u2,u3,u4],[(u28,u0,u4),(0x8888cccc,u28,u1)],[0,1,2,4,6,7],[(0,476),(0,477),(1,476),(1,477)]),
([u0,u1,u2,0xf5f5f0f0,u3,u4],[(u28,u0,u4),(0xf5f5f0f0,u28,u2)],[0,1,3,4,6,7],[(0,478),(0,479),(1,480)]),
([u28,u0,u11,u1,u2,u3,u4],[(u28,u0,u4),(u11,u1,u2)],[0,1,2,3,5],[(0,55),(0,446),(0,476),(0,478),(0,481)]),
([u28,u0,u1,u2,u37,u3,u4],[(u28,u0,u4),(u37,u1,u2)],[0,1,3],[(0,447),(0,482),(0,483)]),
([u8,u28,u0,u1,u2,u3,u4],[(u28,u0,u4),(u8,u1,u3)],[0,1,4,7],[(0,390),(0,484),(0,485)]),
([u22,u28,u0,u1,u2,u3,u4],[(u28,u0,u4),(u22,u1,u2)],[0,1,3],[(0,56),(0,448),(0,477),(0,486),(0,488),(1,485),(1,487),(1,489)]),
([u28,u0,u1,u9,u2,u3,u4],[(u28,u0,u4),(u9,u2,u3)],[0,1,2,4],[(0,449),(0,480),(0,490),(0,491),(0,492),(1,480)]),
([u28,u0,u1,u2,u3,u6,u4],[(u28,u0,u4),(u6,u2,u3)],[0,1,6],[(0,424),(0,492),(0,493),(0,494)]),
([u19,u28,u0,u1,u2,u3,u4],[(u28,u0,u4),(u19,u2,u3)],[0,1,2,4,7],[(0,450),(0,495),(0,496)]),
([u51,u0,u1,u2,u3,u4],[(u17,u1,u3),(u51,u0,u17)],[0,1,2,3,4,5,6,7],[(0,0),(0,150),(0,248),(0,389),(0,452),(0,497),(0,498),(1,15),(1,324)]),
([u8,u0,u1,u2,u3,u4],[(u17,u1,u3),(u8,u17,u1)],[0,1,2,3,4,5,6,7],[(0,390),(0,453),(1,14)]),
([u0,u1,u2,u78,u3,u4],[(u17,u1,u3),(u78,u17,u2)],[0,1,2,3,4,5,6],[(0,349),(0,391),(0,454),(0,499),(0,500),(0,501)]),
([u56,u0,u1,u2,u3],[(u17,u1,u3),(u56,u17,u4)],[1,3,4,5],[(0,59),(0,151),(0,209),(0,250),(0,350),(0,503),(1,325),(1,502),(1,504)]),
([u0,u11,u17,u1,u2,u3,u4],[(u11,u1,u2),(u17,u1,u3)],[1,2,3,4],[(0,500),(0,501),(0,503),(0,505),(1,500),(1,503)]),
([u8,u0,u11,u1,u2,u3,u4],[(u11,u1,u2),(u8,u1,u3)],[1,2,3,4,6,7],[(0,504),(0,506),(0,507)]),
([u0,u11,u24,u1,u2,u3,u4],[(u11,u1,u2),(u24,u1,u4)],[1,2,5],[(0,508)]),
([u0,u11,u1,u3,u6,u4],[(u11,u1,u2),(u6,u2,u3)],[0,2,3,4,5,6],[(0,57),(0,121),(0,251),(0,298),(0,392),(0,455),(0,505),(0,507),(0,509),(1,352),(1,510)]),
([u23,u0,u17,u1,u2,u4],[(u17,u1,u3),(u23,u3,u4)],[1,3,4,5,7],[(0,58),(0,122),(1,511),(1,512)]),
([u0,u11,u1,u2,u32,u3,u4],[(u11,u1,u2),(u32,u3,u4)],[1,2,3,4,5],[(0,514),(0,515),(1,513)]),
([u23,u0,u11,u1,u2,u3,u4],[(u11,u1,u2),(u23,u3,u4)],[1,2,5],[(0,516)]),
([u62,u0,u1,u2,u3,u4],[(u37,u1,u2),(u62,u0,u37)],[0,1,2,3,4,5,6,7],[(0,394),(0,395),(0,432),(0,456),(0,483),(1,212),(1,354)]),
([0xfc00fc,u0,u1,u2,u3,u4],[(u37,u1,u2),(0xfc00fc,u37,u3)],[0,1,2,3,5,6,7],[(0,213),(0,396),(0,457),(0,518),(1,517)]),
([u0,u1,u33,u2,u3,u45,u4],[(u45,u1,u3),(u33,u2,u4)],[1,2,3,5],[(1,518),(1,519),(1,520)]),
([u23,u0,u1,u2,u37,u3,u4],[(u37,u1,u2),(u23,u3,u4)],[1,2,3,4,5,6,7],[(1,521),(1,522)]),
([u8,u0,0xaaeeaaee,u1,u2,u3,u4],[(u8,u1,u3),(0xaaeeaaee,u8,u0)],[0,1,3,4,7],[(0,523),(0,524),(1,14)]),
([u92,u0,u1,u2,u3,u4],[(u47,u1,u2),(u92,u47,u0)],[0,1,2,3,4,5,6,7],[(0,18),(0,152),(0,398),(0,458)]),
([u8,0xaa22aa22,u0,u1,u2,u3,u4],[(u8,u1,u3),(0xaa22aa22,u8,u0)],[0,3,4,7],[(0,525)]),
([u0,u1,u2,u65,u3,u4],[(u8,u1,u3),(u65,u8,u2)],[0,1,2,3,4,5,6,7],[(0,215),(0,399),(0,459),(0,506),(0,526)]),
([u8,u0,u1,u2,u65,u3,u4],[(u8,u1,u3),(u65,u8,u2)],[2,3,4,6,7],[(0,527)]),
([0xc000c,u0,u1,u2,u3,u4],[(u8,u1,u3),(0xc000c,u8,u2)],[0,1,5,6,7],[(0,400),(0,460),(0,501),(0,528)]),
([u8,u0,u1,0xf030f030,u2,u3,u4],[(u8,u1,u3),(0xf030f030,u8,u2)],[2,3,4,6,7],[(0,529)]),
([u8,u0,u1,u2,u3,0xff330000,u4],[(u8,u1,u3),(0xff330000,u8,u4)],[1,3,5],[(0,530)]),
([u8,u47,u0,u1,u2,u3,u4],[(u8,u1,u3),(u47,u1,u2)],[2,3,4,6,7],[(0,531)]),
([u8,u20,u0,u2,u4],[(u8,u1,u3),(u20,u1,u3)],[1,3,7],[(0,216),(0,258),(0,356),(0,401),(0,434),(0,461),(0,485),(0,524),(0,525),(0,527),(0,529),(0,530),(0,532),(0,533),(0,534),(0,535),(1,328)]),
([u8,u0,u24,u1,u2,u3,u4],[(u8,u1,u3),(u24,u1,u4)],[1,3,4,5,7],[]),
([u8,u0,u1,u2,u6,u4],[(u8,u1,u3),(u6,u2,u3)],[0,2,3,4,5,7],[(0,259),(0,357),(0,402),(0,462),(0,507),(0,531),(0,536)]),
([u8,u34,u0,u1,u2,u4],[(u8,u1,u3),(u34,u2,u3)],[0,2,3,4,5,7],[(0,217),(0,403),(0,463),(0,537),(0,538),(1,329)]),
([u8,u0,u1,u33,u2,u3,u4],[(u8,u1,u3),(u33,u2,u4)],[1,2,4,7],[(0,534),(0,539)]),
([u8,u43,u0,u1,u2,u3,u4],[(u8,u1,u3),(u43,u2,u4)],[1,3,4,5,7],[(0,535),(0,541),(1,540)]),
([u8,u0,u1,u2,u32,u4],[(u8,u1,u3),(u32,u3,u4)],[1,3,4,5],[(0,542),(0,543),(0,544)]),
([u8,u23,u0,u1,u2,u4],[(u8,u1,u3),(u23,u3,u4)],[1,3,4,5],[(0,545),(0,546)]),
([u76,u0,u1,u2,u3,u4],[(u20,u1,u3),(u76,u20,u0)],[0,1,2,3,4,5,6],[(0,405),(0,406),(0,436),(0,464),(0,487)]),
([u0,u1,u2,u67,u4],[(u22,u1,u2),(u67,u22,u3)],[1,2,3,7],[(0,407),(0,437),(0,465),(0,488),(0,549),(1,547),(1,548)]),
([u0,u1,u2,u53,u3,u4],[(u20,u1,u3),(u53,u20,u2)],[0,1,2,3,4,5,6],[(0,219),(0,359),(0,408),(0,466),(0,550),(0,551)]),
([u0,u52,u1,u3,u4],[(u20,u1,u3),(u52,u20,u2)],[1,2,3,4],[(0,61),(0,409),(0,438),(0,467),(0,489)]),
([u22,u0,u1,u2,u32,u3,u4],[(u22,u1,u2),(u32,u3,u4)],[3,4],[(0,553),(1,534),(1,551),(1,552)]),
([u23,u22,u0,u1,u2,u3,u4],[(u22,u1,u2),(u23,u3,u4)],[1,2,3,4,5,7],[(0,554),(0,555),(1,535)]),
([0x2222aaaa,u0,u1,u2,u3,u4],[(u24,u1,u4),(0x2222aaaa,u0,u24)],[0,1,2,3,4,5,6,7],[(0,23),(0,153)]),
([u0,u1,u2,u95,u3,u4],[(u24,u1,u4),(u95,u24,u2)],[0,1,3,4,5,6,7],[(0,361),(0,508),(0,556),(1,557)]),
([u0,u24,u1,u9,u2,u3,u4],[(u24,u1,u4),(u9,u2,u3)],[1,2,4,5],[(0,557),(0,558),(0,559),(1,557)]),
([u0,u24,u1,u2,u3,u6,u4],[(u24,u1,u4),(u6,u2,u3)],[1,3,5,6],[(0,559),(0,560),(0,561)]),
([u19,u0,u24,u1,u2,u3,u4],[(u24,u1,u4),(u19,u2,u3)],[1,2,4,5,7],[(0,562),(0,563)]),
([0x8888aaaa,u0,u1,u2,u3,u4],[(u31,u1,u4),(0x8888aaaa,u31,u0)],[0,1,2,3,4,5,6,7],[]),
([u0,u1,u2,0xf3f3f0f0,u3,u4],[(u31,u1,u4),(0xf3f3f0f0,u31,u2)],[0,1,3,4,5,6,7],[(0,222),(0,564),(0,565)]),
([u31,u0,u1,u9,u2,u3,u4],[(u31,u1,u4),(u9,u2,u3)],[1,2,3,5],[(0,566),(0,567)]),
([u31,u0,u1,u2,u3,u6,u4],[(u31,u1,u4),(u6,u2,u3)],[1,2,3,4,5,6,7],[(0,567),(0,568),(0,569)]),
([u19,u31,u0,u1,u2,u3,u4],[(u31,u1,u4),(u19,u2,u3)],[1,2,3,5],[(0,565),(0,570),(0,571)]),
([u61,u0,u1,u2,u3,u4],[(u9,u2,u3),(u61,u0,u9)],[0,1,2,3,4,5],[(0,63),(0,91),(0,124),(0,411),(0,412),(0,440),(0,468),(0,491),(0,572)]),
([u59,u0,u1,u2,u3,u4],[(u9,u2,u3),(u59,u1,u9)],[0,1,2,3,4,5],[(0,63),(0,335),(0,413),(0,469),(0,573),(0,574),(1,335)]),
([u0,u1,u9,u6,u4],[(u9,u2,u3),(u6,u2,u3)],[0,1,2,6],[(0,64),(0,93),(0,125),(0,155),(0,299),(0,414),(0,441),(0,470),(0,492),(0,559),(0,567),(0,574),(0,575),(0,576),(0,577),(0,578),(0,579),(0,580),(0,581),(0,582)]),
([u18,u0,u1,u2,u3,u4],[(u6,u2,u3),(u18,u0,u6)],[0,1,2,3,4,5,6,7],[(0,65),(0,67),(0,157),(0,165),(0,270),(0,416),(0,417),(0,443),(0,471),(0,494),(0,509),(0,536),(0,575),(0,583),(1,165),(1,270),(1,509),(1,536)]),
([u18,u0,u1,u2,u3,u6,u4],[(u6,u2,u3),(u18,u0,u6)],[0,2,4,6,7],[(0,418),(0,576)]),
([u73,u0,u1,u2,u3,u6,u4],[(u6,u2,u3),(u73,u0,u6)],[0,1,6],[(0,177),(0,419),(0,577),(0,584)]),
([u0,u42,u1,u2,u3,u4],[(u6,u2,u3),(u42,u1,u6)],[0,1,2,3,4,5,6,7],[(0,65),(0,68),(0,127),(0,420),(0,472),(0,561),(0,569),(0,585),(0,586),(0,587)]),
([u0,u42,u1,u2,u3,u6,u4],[(u6,u2,u3),(u42,u1,u6)],[1,2,3,4,6,7],[(0,578),(0,588)]),
([u93,u0,u1,u2,u3,u6,u4],[(u6,u2,u3),(u93,u1,u6)],[2,3,4,6,7],[(0,501),(0,579)]),
([u0,u1,u2,u3,0xfff00000,u6,u4],[(u6,u2,u3),(0xfff00000,u6,u4)],[1,5],[(0,582)]),
([u96,u0,u1,u2,u3,u4],[(u34,u3,u2),(u96,u34,u0)],[0,1,2,3,4,5,6],[(0,70),(0,422),(0,473),(0,538),(1,589)]),
([u0,u84,u1,u2,u3,u4],[(u34,u3,u2),(u84,u34,u1)],[0,1,2,3,4,5,6],[(0,70),(0,71),(0,129),(0,224),(0,423),(0,474),(1,336),(1,590)]),
([u0,u1,u2,u3,u6,u4],[(u19,u2,u3),(u6,u19,u3)],[0,1,2,3,4,5,6,7],[(0,177),(0,424),(0,475),(0,501)]),
([u19,u34,u0,u1,u4],[(u19,u2,u3),(u34,u2,u3)],[1,2,4],[(0,72),(0,96),(0,130),(0,159),(0,445),(0,496),(0,563),(0,571),(0,580)]),
([0xaaaaaa,u0,u1,u2,u3,u4],[(u32,u3,u4),(0xaaaaaa,u0,u32)],[0,1,2,3,4,5,6],[(0,74),(0,543),(1,591)]),
([u74,u0,u1,u2,u3,u4],[(u32,u3,u4),(u74,u1,u32)],[0,1,2,3,4,5,6],[(0,74),(0,97),(0,161),(0,514),(0,553),(1,592)]),
([u0,u1,u2,u3,u79,u4],[(u32,u3,u4),(u79,u32,u2)],[0,1,2,3,4,5,6],[(0,365),(0,515),(0,544),(0,593),(0,594)]),
([0xa0a0aaaa,u0,u1,u2,u3,u4],[(u43,u2,u4),(0xa0a0aaaa,u43,u0)],[0,1,2,3,4,5,6,7],[(0,76),(0,511),(1,545),(1,595)]),
([u0,u86,u1,u2,u3,u4],[(u43,u2,u4),(u86,u43,u1)],[0,1,2,3,4,5,6,7],[(0,76),(0,77),(0,133),(0,521),(0,541),(1,596)]),
([u0,u1,u2,u77,u3,u4],[(u23,u3,u4),(u77,u23,u2)],[0,1,2,3,5,6,7],[(0,227),(0,546),(0,555),(0,597),(0,598),(1,512)])
]
def c5_3_L7 : Array W5Node := Array.mk [
([u7,u0,u1,u2,u3,u4],[(u7,u0,u1)],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,8),(1,9),(1,16),(1,17),(1,18),(1,19),(1,23),(1,24),(1,25)]),
([u0,u1,u25,u2,u3,u4],[(u25,u0,u1)],[0,1,2,3,4,5],[(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(1,26),(1,27),(1,28),(1,32),(1,33),(1,34)]),
([u21,u0,u1,u2,u3,u4],[(u21,u0,u1)],[0,1,2,3,4,5],[(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,46),(0,47),(0,48),(1,36),(1,38),(1,39),(1,43),(1,46),(1,47),(1,48)]),
([u16,u0,u1,u2,u3,u4],[(u16,u0,u1)],[0,1,2,3,4,5],[(0,35),(0,37),(0,49),(0,50),(0,51),(0,52),(0,53),(0,54),(0,55),(0,56),(0,57),(0,58),(0,59),(0,60),(1,49),(1,53),(1,54),(1,58),(1,59),(1,60)]),
([u12,u0,u1,u2,u3,u4],[(u12,u0,u2)],[0,1,2,3,4,5],[(0,8),(0,38),(0,63),(0,66),(0,67),(0,68),(0,69),(0,70),(0,71),(0,73),(0,74),(0,75),(0,77),(0,78),(0,80),(0,81),(1,61),(1,62),(1,64),(1,65),(1,72),(1,76),(1,79)]),
([u0,u1,u2,u14,u3,u4],[(u14,u0,u2)],[0,1,2,3,4,5,6],[(0,66),(0,82),(0,83),(0,84),(0,86),(0,87),(0,89),(0,90),(0,92),(0,94),(0,95),(0,96),(0,98),(1,61),(1,85),(1,88),(1,91),(1,93),(1,97)]),
([u10,u0,u1,u2,u3,u4],[(u10,u0,u3)],[0,1,2,3,4,5,7],[(0,3),(0,9),(0,39),(0,68),(0,99),(0,101),(0,102),(0,103),(0,104),(0,105),(0,106),(0,107),(0,108),(0,109),(0,110),(0,111),(0,112),(0,113),(0,114),(0,115),(0,116),(0,117),(0,118),(0,119),(0,120),(0,121),(0,122),(0,123),(1,100)]),
([u35,u0,u1,u2,u3,u4],[(u35,u0,u2)],[0,1,2,3,4,5],[(0,127),(0,128),(0,129),(0,131),(0,132),(0,133),(0,134),(0,135),(1,108),(1,124),(1,125),(1,126),(1,130)]),
([u5,u0,u1,u2,u3],[(u5,u0,u4)],[0,1,5],[(0,10),(0,11),(0,40),(0,51),(0,69),(0,109),(0,136),(0,137),(0,138),(0,139),(0,140),(0,141),(0,142),(0,143),(0,144),(0,145),(0,146),(1,69),(1,109),(1,138),(1,139),(1,140),(1,141),(1,142),(1,143),(1,146)]),
([u5,u0,u1,u2,u3,u4],[(u5,u0,u4)],[0,1,2,3,4,5],[(0,12),(0,13),(0,41),(0,52),(0,70),(0,110),(0,147),(0,148),(0,149),(0,150),(0,151),(0,152),(0,153),(0,154),(0,155),(1,70),(1,110),(1,148),(1,149),(1,150),(1,151),(1,152),(1,155)]),
([u13,u0,u1,u2,u3],[(u13,u0,u4)],[0,1],[(0,14),(0,42),(0,71),(0,111),(0,156),(0,157),(0,158),(0,159),(0,160),(0,161),(0,162),(0,163),(1,71),(1,111),(1,157),(1,158),(1,159),(1,160),(1,163)]),
([u28,u0,u1,u2,u3,u4],[(u28,u0,u4)],[0,1,2,3,4],[(0,15),(0,156),(0,164),(0,165),(0,166),(0,167),(0,168),(0,169),(0,170),(0,171),(0,172),(1,165),(1,166),(1,167),(1,168),(1,169),(1,172)]),
([u0,u11,u1,u2,u3,u4],[(u11,u1,u2)],[0,1,2,3,4,5],[(0,16),(0,17),(0,43),(0,53),(0,85),(0,112),(0,140),(0,149),(0,157),(0,166),(0,177),(0,178),(0,179),(0,180),(0,182),(0,183),(1,73),(1,116),(1,127),(1,173),(1,174),(1,175),(1,176),(1,181)]),
([u0,u1,u2,u37,u3,u4],[(u37,u1,u2)],[0,1,2,3,4,5,6],[(0,113),(0,141),(0,150),(0,158),(0,167),(0,184),(0,185),(0,187),(1,74),(1,86),(1,128),(1,174),(1,186)]),
([u8,u0,u1,u2,u3,u4],[(u8,u1,u3)],[0,1,2,3,4,5,7],[(0,3),(0,18),(0,54),(0,72),(0,75),(0,87),(0,117),(0,129),(0,142),(0,151),(0,159),(0,168),(0,178),(0,188),(0,190),(0,191),(0,192),(0,193),(0,194),(0,195),(0,196),(0,197),(0,198),(0,199),(0,200),(0,201),(0,202),(0,203),(0,204),(1,114),(1,189)]),
([u22,u0,u1,u2,u3,u4],[(u22,u1,u2)],[0,1,2,3,4,5],[(0,19),(0,76),(0,88),(0,115),(0,130),(0,143),(0,152),(0,160),(0,169),(0,206),(0,209),(0,210),(1,197),(1,205),(1,207),(1,208)]),
([u0,u24,u1,u2,u3,u4],[(u24,u1,u4)],[0,1,2,3,4,5],[(0,20),(0,55),(0,77),(0,89),(0,118),(0,131),(0,179),(0,198),(0,211),(0,212),(0,213),(0,214),(0,215),(1,77),(1,89),(1,118),(1,131),(1,179),(1,198),(1,212),(1,215)]),
([u31,u0,u1,u2,u3,u4],[(u31,u1,u4)],[0,1,2,3,4,5],[(0,78),(0,90),(0,119),(0,132),(0,216),(0,217),(0,218),(0,219),(0,220),(1,78),(1,90),(1,119),(1,132),(1,217),(1,220)]),
([u0,u1,u9,u2,u3,u4],[(u9,u2,u3)],[0,1,2,3,4,5],[(0,21),(0,30),(0,44),(0,56),(0,120),(0,144),(0,153),(0,161),(0,170),(0,213),(0,218),(0,221),(0,222),(0,223),(1,120)]),
([u0,u1,u2,u3,u6,u4],[(u6,u2,u3)],[0,1,2,3,4,5,6,7],[(0,22),(0,31),(0,45),(0,57),(0,91),(0,104),(0,133),(0,145),(0,154),(0,162),(0,171),(0,180),(0,193),(0,199),(0,214),(0,219),(0,223),(0,224),(0,225),(0,226),(0,227),(0,228),(0,229),(0,230),(1,91),(1,133),(1,180),(1,199)]),
([u19,u0,u1,u2,u3,u4],[(u19,u2,u3)],[0,1,2,3,4,5,7],[(0,23),(0,32),(0,46),(0,58),(0,79),(0,92),(0,121),(0,146),(0,155),(0,163),(0,172),(0,215),(0,220),(0,233),(0,234),(1,200),(1,231),(1,232)]),
([u0,u1,u33,u2,u3,u4],[(u33,u2,u4)],[0,1,2,3,4,5],[(0,24),(0,33),(0,47),(0,59),(0,97),(0,122),(0,186),(0,201),(1,80),(1,134),(1,182),(1,203),(1,209),(1,235),(1,236),(1,237)]),
([u23,u0,u1,u2,u3,u4],[(u23,u3,u4)],[0,1,2,3,4,5,7],[(0,25),(0,34),(0,48),(0,60),(0,81),(0,98),(0,135),(0,181),(0,183),(0,187),(0,204),(0,210),(0,240),(1,123),(1,202),(1,238),(1,239)])
]
def c5_3_L8 : Array W5Node := Array.mk [
([u0,u1,u2,u3,u4],[],[1],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(1,4),(1,5),(1,6),(1,7),(1,12),(1,13),(1,14),(1,15),(1,20),(1,21),(1,22)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_2_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 2 c5_3_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_2 : ∀ i < c5_3_L2.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 2 c5_3_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_3_L2.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_3_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_3_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 3 c5_3_L3 c5_3_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_3_1 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 3 c5_3_L3 c5_3_L2 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_3_2 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 3 c5_3_L3 c5_3_L2 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_3_3 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 3 c5_3_L3 c5_3_L2 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_3_4 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 3 c5_3_L3 c5_3_L2 64 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_3 : ∀ i < c5_3_L3.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 3 c5_3_L3 c5_3_L2 i = true := by
  intro i hi
  have hsz : c5_3_L3.size = 78 := by decide +kernel
  have hi' : i < 78 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_3_chk_3_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_3_chk_3_1 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_3_chk_3_2 i (by omega) (by omega)
  ·
    by_cases h : i < 64
    ·
      exact checkBlockW5_at c5_3_chk_3_3 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_3_chk_3_4 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_1 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_2 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_3 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_4 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_5 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_6 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_7 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_8 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_9 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_10 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_11 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_12 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_13 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_14 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_15 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_16 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_17 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_18 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_19 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 304 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_4 : ∀ i < c5_3_L4.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 c5_3_L3 i = true := by
  intro i hi
  have hsz : c5_3_L4.size = 305 := by decide +kernel
  have hi' : i < 305 := hsz ▸ hi
  by_cases h : i < 160
  ·
    by_cases h : i < 80
    ·
      by_cases h : i < 48
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW5_at c5_3_chk_4_0 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_4_1 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_2 i (by omega) (by omega)
      ·
        by_cases h : i < 64
        ·
          exact checkBlockW5_at c5_3_chk_4_3 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_4 i (by omega) (by omega)
    ·
      by_cases h : i < 128
      ·
        by_cases h : i < 112
        ·
          by_cases h : i < 96
          ·
            exact checkBlockW5_at c5_3_chk_4_5 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_4_6 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_7 i (by omega) (by omega)
      ·
        by_cases h : i < 144
        ·
          exact checkBlockW5_at c5_3_chk_4_8 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_9 i (by omega) (by omega)
  ·
    by_cases h : i < 240
    ·
      by_cases h : i < 208
      ·
        by_cases h : i < 192
        ·
          by_cases h : i < 176
          ·
            exact checkBlockW5_at c5_3_chk_4_10 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_4_11 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_12 i (by omega) (by omega)
      ·
        by_cases h : i < 224
        ·
          exact checkBlockW5_at c5_3_chk_4_13 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_14 i (by omega) (by omega)
    ·
      by_cases h : i < 288
      ·
        by_cases h : i < 272
        ·
          by_cases h : i < 256
          ·
            exact checkBlockW5_at c5_3_chk_4_15 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_4_16 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_17 i (by omega) (by omega)
      ·
        by_cases h : i < 304
        ·
          exact checkBlockW5_at c5_3_chk_4_18 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_4_19 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_1 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_2 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_3 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_4 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_5 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_6 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_7 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_8 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_9 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_10 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_11 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_12 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_13 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_14 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_15 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_16 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_17 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_18 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_19 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_20 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_21 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_22 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_23 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_24 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_25 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_26 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_27 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_28 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_29 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_30 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_31 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_32 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 512 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_33 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 528 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_34 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 544 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_35 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 560 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_36 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 576 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_37 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 592 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_5 : ∀ i < c5_3_L5.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 i = true := by
  intro i hi
  have hsz : c5_3_L5.size = 599 := by decide +kernel
  have hi' : i < 599 := hsz ▸ hi
  by_cases h : i < 304
  ·
    by_cases h : i < 160
    ·
      by_cases h : i < 80
      ·
        by_cases h : i < 48
        ·
          by_cases h : i < 32
          ·
            by_cases h : i < 16
            ·
              exact checkBlockW5_at c5_3_chk_5_0 i (by omega) (by omega)
            ·
              exact checkBlockW5_at c5_3_chk_5_1 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_2 i (by omega) (by omega)
        ·
          by_cases h : i < 64
          ·
            exact checkBlockW5_at c5_3_chk_5_3 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_4 i (by omega) (by omega)
      ·
        by_cases h : i < 128
        ·
          by_cases h : i < 112
          ·
            by_cases h : i < 96
            ·
              exact checkBlockW5_at c5_3_chk_5_5 i (by omega) (by omega)
            ·
              exact checkBlockW5_at c5_3_chk_5_6 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_7 i (by omega) (by omega)
        ·
          by_cases h : i < 144
          ·
            exact checkBlockW5_at c5_3_chk_5_8 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_9 i (by omega) (by omega)
    ·
      by_cases h : i < 240
      ·
        by_cases h : i < 208
        ·
          by_cases h : i < 192
          ·
            by_cases h : i < 176
            ·
              exact checkBlockW5_at c5_3_chk_5_10 i (by omega) (by omega)
            ·
              exact checkBlockW5_at c5_3_chk_5_11 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_12 i (by omega) (by omega)
        ·
          by_cases h : i < 224
          ·
            exact checkBlockW5_at c5_3_chk_5_13 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_14 i (by omega) (by omega)
      ·
        by_cases h : i < 272
        ·
          by_cases h : i < 256
          ·
            exact checkBlockW5_at c5_3_chk_5_15 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_16 i (by omega) (by omega)
        ·
          by_cases h : i < 288
          ·
            exact checkBlockW5_at c5_3_chk_5_17 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_18 i (by omega) (by omega)
  ·
    by_cases h : i < 464
    ·
      by_cases h : i < 384
      ·
        by_cases h : i < 352
        ·
          by_cases h : i < 336
          ·
            by_cases h : i < 320
            ·
              exact checkBlockW5_at c5_3_chk_5_19 i (by omega) (by omega)
            ·
              exact checkBlockW5_at c5_3_chk_5_20 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_21 i (by omega) (by omega)
        ·
          by_cases h : i < 368
          ·
            exact checkBlockW5_at c5_3_chk_5_22 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_23 i (by omega) (by omega)
      ·
        by_cases h : i < 432
        ·
          by_cases h : i < 416
          ·
            by_cases h : i < 400
            ·
              exact checkBlockW5_at c5_3_chk_5_24 i (by omega) (by omega)
            ·
              exact checkBlockW5_at c5_3_chk_5_25 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_26 i (by omega) (by omega)
        ·
          by_cases h : i < 448
          ·
            exact checkBlockW5_at c5_3_chk_5_27 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_28 i (by omega) (by omega)
    ·
      by_cases h : i < 544
      ·
        by_cases h : i < 512
        ·
          by_cases h : i < 496
          ·
            by_cases h : i < 480
            ·
              exact checkBlockW5_at c5_3_chk_5_29 i (by omega) (by omega)
            ·
              exact checkBlockW5_at c5_3_chk_5_30 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_31 i (by omega) (by omega)
        ·
          by_cases h : i < 528
          ·
            exact checkBlockW5_at c5_3_chk_5_32 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_33 i (by omega) (by omega)
      ·
        by_cases h : i < 576
        ·
          by_cases h : i < 560
          ·
            exact checkBlockW5_at c5_3_chk_5_34 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_35 i (by omega) (by omega)
        ·
          by_cases h : i < 592
          ·
            exact checkBlockW5_at c5_3_chk_5_36 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_3_chk_5_37 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_1 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_2 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_3 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_4 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_5 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_6 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_7 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_8 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_9 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_10 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_11 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_12 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_13 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_14 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_15 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 240 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_6 : ∀ i < c5_3_L6.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 i = true := by
  intro i hi
  have hsz : c5_3_L6.size = 241 := by decide +kernel
  have hi' : i < 241 := hsz ▸ hi
  by_cases h : i < 128
  ·
    by_cases h : i < 64
    ·
      by_cases h : i < 32
      ·
        by_cases h : i < 16
        ·
          exact checkBlockW5_at c5_3_chk_6_0 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_1 i (by omega) (by omega)
      ·
        by_cases h : i < 48
        ·
          exact checkBlockW5_at c5_3_chk_6_2 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_3 i (by omega) (by omega)
    ·
      by_cases h : i < 96
      ·
        by_cases h : i < 80
        ·
          exact checkBlockW5_at c5_3_chk_6_4 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_5 i (by omega) (by omega)
      ·
        by_cases h : i < 112
        ·
          exact checkBlockW5_at c5_3_chk_6_6 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_7 i (by omega) (by omega)
  ·
    by_cases h : i < 192
    ·
      by_cases h : i < 160
      ·
        by_cases h : i < 144
        ·
          exact checkBlockW5_at c5_3_chk_6_8 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_9 i (by omega) (by omega)
      ·
        by_cases h : i < 176
        ·
          exact checkBlockW5_at c5_3_chk_6_10 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_11 i (by omega) (by omega)
    ·
      by_cases h : i < 224
      ·
        by_cases h : i < 208
        ·
          exact checkBlockW5_at c5_3_chk_6_12 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_13 i (by omega) (by omega)
      ·
        by_cases h : i < 240
        ·
          exact checkBlockW5_at c5_3_chk_6_14 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_3_chk_6_15 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_7_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 7 c5_3_L7 c5_3_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_7_1 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 7 c5_3_L7 c5_3_L6 16 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_7 : ∀ i < c5_3_L7.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 7 c5_3_L7 c5_3_L6 i = true := by
  intro i hi
  have hsz : c5_3_L7.size = 23 := by decide +kernel
  have hi' : i < 23 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_3_chk_7_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_3_chk_7_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_8_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 8 c5_3_L8 c5_3_L7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_8 : ∀ i < c5_3_L8.size, checkNodeW5 c5_3_goal 2 c5_3_pow 8 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 8 c5_3_L8 c5_3_L7 i = true := by
  intro i hi
  have hsz : c5_3_L8.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_3_chk_8_0 i (Nat.zero_le _) (by omega)
theorem c5_3_L2_sound : ∀ i < c5_3_L2.size, ¬ live (basicOps 32) c5_3_goal 2 (c5_3_L2[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound (fun j hj => by simp at hj) c5_3_chk_2
theorem c5_3_L3_sound : ∀ i < c5_3_L3.size, ¬ live (basicOps 32) c5_3_goal 3 (c5_3_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L2_sound c5_3_chk_3
theorem c5_3_L4_sound : ∀ i < c5_3_L4.size, ¬ live (basicOps 32) c5_3_goal 4 (c5_3_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L3_sound c5_3_chk_4
theorem c5_3_L5_sound : ∀ i < c5_3_L5.size, ¬ live (basicOps 32) c5_3_goal 5 (c5_3_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L4_sound c5_3_chk_5
theorem c5_3_L6_sound : ∀ i < c5_3_L6.size, ¬ live (basicOps 32) c5_3_goal 6 (c5_3_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L5_sound c5_3_chk_6
theorem c5_3_L7_sound : ∀ i < c5_3_L7.size, ¬ live (basicOps 32) c5_3_goal 7 (c5_3_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L6_sound c5_3_chk_7
theorem c5_3_L8_sound : ∀ i < c5_3_L8.size, ¬ live (basicOps 32) c5_3_goal 8 (c5_3_L8[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L7_sound c5_3_chk_8
set_option maxRecDepth 100000 in
theorem c5_3_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_3_goal ws) = [rows5] := by decide +kernel
theorem c5_3_top_match : sameSet (rows5.map (actB 32 (c5_3_pow[0]?.getD []))) (c5_3_L8[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_3_no_build : ¬ build (basicOps 32) c5_3_goal 8 rows5.toFinset :=
  no_build_of_top c5_3_G_valid (by decide) c5_3_sublists c5_3_top_match (c5_3_L8_sound 0 (by decide))

def c5_4_goal : BitVec 32 := 0xeee8eaa0
def c5_4_idxs4 : List ℕ := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]
set_option maxRecDepth 100000 in
theorem c5_4_no_build : ¬ build (basicOps 32) c5_4_goal 7 rows5.toFinset :=
  no_build5_of_proj4 6 b4_0_goal (by decide) b4_0_no_build c5_4_goal c5_4_idxs4 1 12 14 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_5_goal : BitVec 32 := 0xfeeeeee0
def c5_5_idxs4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_5_no_build : ¬ build (basicOps 32) c5_5_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_1_goal (by decide) b4_1_no_build c5_5_goal c5_5_idxs4 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def nrmM64 (m : BitVec 64) (b0 : ℕ) (u : BitVec 64) : BitVec 64 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM64 (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 64) :
    projS 32 idxs (nrmM64 m b0 u) = projS 32 idxs u := by
  unfold nrmM64
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 32 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 32 idxs m hm (~~~u), projS_not 32 (by decide) idxs hlen hlt u]

abbrev W6Node := List (BitVec 64) × List (BitVec 64 × BitVec 64 × BitVec 64) × List ℕ × List (ℕ × ℕ)

def checkReplay64 (m : BitVec 64) (b0 : ℕ) (bank : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → Bool
  | [], targets => targets.all (fun t => nrmM64 m b0 t == 0 || bank.contains (nrmM64 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 64 a b).contains v &&
    checkReplay64 m b0 (v :: bank) rest targets

theorem checkReplay64_sound (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 32)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay64 m b0 bank steps targets = true →
      build (basicOps 32) g k (nonZeroImg (projS 32 idxs) targets.toFinset) →
      build (basicOps 32) g (k + steps.length) (nonZeroImg (projS 32 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 32 := projS 32 idxs
  have hn : 0 < 32 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay64, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM64 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM64 m b0 t, hmem, projS_nrmM64 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay64, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 32 (f a) (f b) := projS_ops 32 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 32 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 32 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 32 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 32 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed64 (stock needed : List (BitVec 64)) (u : BitVec 64) : List (BitVec 64) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded64 (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM64 m b0 w
    let needed' := if needed.contains pw then addNeed64 stock (addNeed64 stock needed (nrmM64 m b0 a)) (nrmM64 m b0 b) else needed
    buildNeeded64 m b0 stock rest needed'

def buildSteps64 (m : BitVec 64) (b0 : ℕ) (needed : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64 × BitVec 64 × BitVec 64)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM64 m b0 w
    let pa := nrmM64 m b0 a
    let pb := nrmM64 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 64 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps64 m b0 needed rest (pw :: bank)
    else
      buildSteps64 m b0 needed rest bank

def checkCofClose64 (lb fuel : ℕ) (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM64 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeed64 stock acc (nrmM64 m b0 u)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeeded64 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildSteps64 m b0 needed hist stock
        Nat.blt (steps.length + rem) lb && checkReplay64 m b0 stock steps nxt
      else false
    else false
  else false

theorem checkCofClose64_sound_aux (goal6 : BitVec 64) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 64)) (g : BitVec 32) (hgnz : g ≠ 0)
    (hg : projS 32 idxs goal6 = g)
    (hstock : stock.all (fun w => rows5.contains (projS 32 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 32) g (lb - 1) rows5.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose64 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose64 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 32) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM64 m b0 u == 0)).length ≤ zCount (projS 32 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM64 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM64 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay64_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 32 idxs) stock.toFinset ⊆ rows5.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW6 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose64 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW6 (goal6 : BitVec 64) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (a b : BitVec 64) (r : List (BitVec 64)) : Bool :=
  (ops 64 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 64 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 64 jumps6 goal6 (w :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 64 jumps6 goal6 (w :: a :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 64 jumps6 goal6 (w :: b :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 64 jumps6 goal6 (w :: a :: b :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW6 (goal6 : BitVec 64) (gsize : ℕ) (g6_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cur prev : Array W6Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal6) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW6 goal6 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW6 (goal6 : BitVec 64) (gsize : ℕ) (g6_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cur prev : Array W6Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW6_at {goal6 : BitVec 64} {gsize ncf k start m : ℕ} {g6_pow : Array (List ℕ)}
    {cfLBs cfB0s : Array ℕ} {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (h : checkBlockW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW6, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W6 {goal6 : BitVec 64} {gsize ncf k i : ℕ}
    {g6_idx g6_pow : Array (List ℕ)} {g6_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 64 gsize g6_idx g6_pow g6_inv goal6) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose64 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 64) goal6 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW6 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 64) goal6 (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (g6_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[g]?.getD []))).toFinset.image
        (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 64 (g6_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal6 ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 64} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 64 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 64) goal6 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 64 jumps6 goal6 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW6 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 64 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW6 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact hcof c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 64 a b ▸ hz)

theorem level_sound_W6 {goal6 : BitVec 64} {gsize ncf k : ℕ}
    {g6_idx g6_pow : Array (List ℕ)} {g6_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 64 gsize g6_idx g6_pow g6_inv goal6) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose64 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 64) goal6 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W6 hk hi hvalid hcof hprev (hblk i hi)

theorem projS_nrmM64_16 (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 64) :
    projS 16 idxs (nrmM64 m b0 u) = projS 16 idxs u := by
  unfold nrmM64
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 16 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 16 idxs m hm (~~~u), projS_not 16 (by decide) idxs hlen hlt u]

theorem checkReplay64_16_sound (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 16)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay64 m b0 bank steps targets = true →
      build (basicOps 16) g k (nonZeroImg (projS 16 idxs) targets.toFinset) →
      build (basicOps 16) g (k + steps.length) (nonZeroImg (projS 16 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 16 := projS 16 idxs
  have hn : 0 < 16 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay64, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM64_16 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM64 m b0 t, hmem, projS_nrmM64_16 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay64, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 16 (f a) (f b) := projS_ops 16 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 16 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 16 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 16 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 16 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

theorem checkCofClose64_16_sound_aux (goal6 : BitVec 64) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 64)) (g : BitVec 16) (hgnz : g ≠ 0)
    (hg : projS 16 idxs goal6 = g)
    (hstock : stock.all (fun w => rows4.contains (projS 16 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 16) g (lb - 1) rows4.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose64 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose64 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 16) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM64 m b0 u == 0)).length ≤ zCount (projS 16 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM64 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM64_16 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay64_16_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 16 idxs) stock.toFinset ⊆ rows4.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def v0 : BitVec 64 := 0xcccccccccccccccc
def v1 : BitVec 64 := 0xffff0000ffff0000
def v2 : BitVec 64 := 0xff00ff00ff00ff00
def v3 : BitVec 64 := 0xf0f0f0f0f0f0f0f0
def v4 : BitVec 64 := 0xffffffff00000000
def v5 : BitVec 64 := 0xaaaaaaaaaaaaaaaa
def v6 : BitVec 64 := 0xffffff00ffffff00
def v7 : BitVec 64 := 0xf0f00000f0f0
def v8 : BitVec 64 := 0x3030303030303030
def v9 : BitVec 64 := 0xffccffccffccffcc
def v10 : BitVec 64 := 0x303000003030
def v11 : BitVec 64 := 0x3333330033333300
def v12 : BitVec 64 := 0xffffccccffffcccc
def v13 : BitVec 64 := 0xffffffccffffffcc
def v14 : BitVec 64 := 0xccccfcfcccccfcfc
def v15 : BitVec 64 := 0xf0000000f0
def v16 : BitVec 64 := 0xf0f0f000f0f0f000
def v17 : BitVec 64 := 0xf0c0f0c0f0c0f0c0
def v18 : BitVec 64 := 0xcccccc00cccccc00
def v19 : BitVec 64 := 0xffcc0000ffcc
def v20 : BitVec 64 := 0x3000000030
def v21 : BitVec 64 := 0xf000f000f000f0
def v22 : BitVec 64 := 0xff00fff0ff00fff0
def v23 : BitVec 64 := 0xffff3030ffff3030
def v24 : BitVec 64 := 0xf0f0c0c0f0f0c0c0
def v25 : BitVec 64 := 0xff30ff30ff30ff30
def v26 : BitVec 64 := 0xc0c00000c0c0
def v27 : BitVec 64 := 0xffff00f0ffff00f0
def v28 : BitVec 64 := 0xc0c0c0c0c0c0c0c0
def v29 : BitVec 64 := 0xcc000000cc
def v30 : BitVec 64 := 0x3030300030303000
def v31 : BitVec 64 := 0xffffff30ffffff30
def v32 : BitVec 64 := 0xffccfffcffccfffc
def v33 : BitVec 64 := 0xcccccccc
def v34 : BitVec 64 := 0xccccccfcccccccfc
def v35 : BitVec 64 := 0xff00cc00ff00cc
def v36 : BitVec 64 := 0xcccc0c0ccccc0c0c
def v37 : BitVec 64 := 0xcc00cc00cc00cc
def v38 : BitVec 64 := 0xffffffffcccccccc
def v39 : BitVec 64 := 0xf0c00000f0c0
def v40 : BitVec 64 := 0xf0f0f0c0f0f0f0c0
def v41 : BitVec 64 := 0xffffffff33333300
def v42 : BitVec 64 := 0x30003000300030
def v43 : BitVec 64 := 0xccccfcfc
def v44 : BitVec 64 := 0xf000f030f000f030
def v45 : BitVec 64 := 0xffff0030ffff0030
def v46 : BitVec 64 := 0xff00ff30ff00ff30
def v47 : BitVec 64 := 0x3300333033003330
def v48 : BitVec 64 := 0xf0300000f030
def v49 : BitVec 64 := 0xffc0ffc0ffc0ffc0
def v50 : BitVec 64 := 0xfcfcfcccfcfcfccc
def v51 : BitVec 64 := 0xccccccff00000000
def v52 : BitVec 64 := 0xffffffc0ffffffc0
def v53 : BitVec 64 := 0xc0c0c0f0c0c0c0f0
def v54 : BitVec 64 := 0xff300000ff30
def v55 : BitVec 64 := 0x333333cc333333cc
def v56 : BitVec 64 := 0xffffc0c0ffffc0c0
def v57 : BitVec 64 := 0xccfcccfcccfcccfc
def v58 : BitVec 64 := 0xfffffffff0f0f000
def v59 : BitVec 64 := 0xff00ff00ffccffcc
def v60 : BitVec 64 := 0xccfc0000ccfc
def v61 : BitVec 64 := 0xf030f030f030f030
def v62 : BitVec 64 := 0xcccc0000cccc
def v63 : BitVec 64 := 0xffc00000ffc0
def v64 : BitVec 64 := 0xff000000ffcc
def v65 : BitVec 64 := 0xfffff0c0fffff0c0
def v66 : BitVec 64 := 0xff000000cc
def v67 : BitVec 64 := 0xffff0000cccc
def v68 : BitVec 64 := 0xffffff00ffffffcc
def v69 : BitVec 64 := 0xcfcfcf00cfcfcf00
def v70 : BitVec 64 := 0xfffff030fffff030
def v71 : BitVec 64 := 0xf0f03030f0f03030
def v72 : BitVec 64 := 0xffff00ccffff00cc
def v73 : BitVec 64 := 0xff00ffccff00ffcc
def v74 : BitVec 64 := 0xff0fcc0cff0fcc0c
def v75 : BitVec 64 := 0xf000f0c0f000f0c0
def v76 : BitVec 64 := 0xcc0ccc0ccc0ccc0c
def v77 : BitVec 64 := 0xffff00ffffff00cc
def v78 : BitVec 64 := 0xffff0000ffffcccc
def v79 : BitVec 64 := 0xf0f0f030f0f0f030
def v80 : BitVec 64 := 0xc0c0c000c0c0c000
def v81 : BitVec 64 := 0xf0c0f000f0c0f000
def v82 : BitVec 64 := 0xfcccfcfcfcccfcfc
def v83 : BitVec 64 := 0xcc3ccc3ccc3ccc3c
def v84 : BitVec 64 := 0xf0f00030f0f00030
def v85 : BitVec 64 := 0xc000c000c000c0
def v86 : BitVec 64 := 0xff00ffc0ff00ffc0
def v87 : BitVec 64 := 0xffccff0cffccff0c
def v88 : BitVec 64 := 0x303030f0303030f0
def v89 : BitVec 64 := 0xfff0ffc0fff0ffc0
def v90 : BitVec 64 := 0xff00ffffff00ffcc
def v91 : BitVec 64 := 0xffffccfcffffccfc
def v92 : BitVec 64 := 0xc0000000c0
def v93 : BitVec 64 := 0xfff0ff30fff0ff30
def v94 : BitVec 64 := 0xf0f3f000f0f3f00
def v95 : BitVec 64 := 0xffffffff30303000
def v96 : BitVec 64 := 0xffcc0f0cffcc0f0c
def v97 : BitVec 64 := 0xf0f000c0f0f000c0
def v98 : BitVec 64 := 0xcccc3c3ccccc3c3c
def v99 : BitVec 64 := 0x3f3f3f003f3f3f00
def v100 : BitVec 64 := 0xccf0fc00ccf0fc
def v101 : BitVec 64 := 0xffffff00cccccc00
def v102 : BitVec 64 := 0xffffff0033333300
def v103 : BitVec 64 := 0xffffffffffffff00
def v104 : BitVec 64 := 0xffffffffff00ff00

def g6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55,40,41,42,43,44,45,46,47,56,57,58,59,60,61,62,63]
def g6_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0,g6_s1]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0,g6_p1]
def g6_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_G_valid : (List.range 2).all (symValid 64 2 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel

def g6_m0 : BitVec 64 := 0xff00ff00ff00ff

def g6_st0 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]

def g6_ix0 : List ℕ := [0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,32,33,34,35,48,49,50,51,36,37,38,39,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_0 : g6_ix0.length = 32 ∧ (∀ idx ∈ g6_ix0, idx < 64) ∧ (∀ idx ∈ g6_ix0, g6_m0.getLsbD idx = true) ∧ projS 32 g6_ix0 goal6 = c5_0_goal ∧ g6_st0.all (fun w => rows5.contains (projS 32 g6_ix0 w)) = true := by decide +kernel

def g6_m1 : BitVec 64 := 0x3333333333333333

def g6_st1 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]

def g6_ix1 : List ℕ := [0,1,8,9,16,17,24,25,4,5,12,13,20,21,28,29,32,33,40,41,48,49,56,57,36,37,44,45,52,53,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_1 : g6_ix1.length = 32 ∧ (∀ idx ∈ g6_ix1, idx < 64) ∧ (∀ idx ∈ g6_ix1, g6_m1.getLsbD idx = true) ∧ projS 32 g6_ix1 goal6 = c5_1_goal ∧ g6_st1.all (fun w => rows5.contains (projS 32 g6_ix1 w)) = true := by decide +kernel

def g6_m2 : BitVec 64 := 0xffff0000ffff

def g6_st2 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]

def g6_ix2 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,32,33,34,35,40,41,42,43,36,37,38,39,44,45,46,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_2 : g6_ix2.length = 32 ∧ (∀ idx ∈ g6_ix2, idx < 64) ∧ (∀ idx ∈ g6_ix2, g6_m2.getLsbD idx = true) ∧ projS 32 g6_ix2 goal6 = c5_0_goal ∧ g6_st2.all (fun w => rows5.contains (projS 32 g6_ix2 w)) = true := by decide +kernel

def g6_m3 : BitVec 64 := 0xf0f0f0f0f0f0f0f0

def g6_st3 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000]

def g6_ix3 : List ℕ := [4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,36,37,38,39,44,45,46,47,52,53,54,55,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_3 : g6_ix3.length = 32 ∧ (∀ idx ∈ g6_ix3, idx < 64) ∧ (∀ idx ∈ g6_ix3, g6_m3.getLsbD idx = true) ∧ projS 32 g6_ix3 goal6 = c5_2_goal ∧ g6_st3.all (fun w => rows5.contains (projS 32 g6_ix3 w)) = true := by decide +kernel

def g6_m4 : BitVec 64 := 0x5555555555555555

def g6_st4 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]

def g6_ix4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_4 : g6_ix4.length = 32 ∧ (∀ idx ∈ g6_ix4, idx < 64) ∧ (∀ idx ∈ g6_ix4, g6_m4.getLsbD idx = true) ∧ projS 32 g6_ix4 goal6 = c5_3_goal ∧ g6_st4.all (fun w => rows5.contains (projS 32 g6_ix4 w)) = true := by decide +kernel

def g6_m5 : BitVec 64 := 0xf0f0f0f0

def g6_st5 : List (BitVec 64) := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]

def g6_ix5 : List ℕ := [4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]

set_option maxRecDepth 100000 in

theorem g6_cspec_5 : g6_ix5.length = 16 ∧ (∀ idx ∈ g6_ix5, idx < 64) ∧ (∀ idx ∈ g6_ix5, g6_m5.getLsbD idx = true) ∧ projS 16 g6_ix5 goal6 = b4_0_goal ∧ g6_st5.all (fun w => rows4.contains (projS 16 g6_ix5 w)) = true := by decide +kernel

def g6_m6 : BitVec 64 := 0xffffffff

def g6_st6 : List (BitVec 64) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def g6_ix6 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]

set_option maxRecDepth 100000 in

theorem g6_cspec_6 : g6_ix6.length = 32 ∧ (∀ idx ∈ g6_ix6, idx < 64) ∧ (∀ idx ∈ g6_ix6, g6_m6.getLsbD idx = true) ∧ projS 32 g6_ix6 goal6 = c5_4_goal ∧ g6_st6.all (fun w => rows5.contains (projS 32 g6_ix6 w)) = true := by decide +kernel

def g6_m7 : BitVec 64 := 0xffffffff00000000

def g6_st7 : List (BitVec 64) := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]

def g6_ix7 : List ℕ := [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_7 : g6_ix7.length = 32 ∧ (∀ idx ∈ g6_ix7, idx < 64) ∧ (∀ idx ∈ g6_ix7, g6_m7.getLsbD idx = true) ∧ projS 32 g6_ix7 goal6 = c5_5_goal ∧ g6_st7.all (fun w => rows5.contains (projS 32 g6_ix7 w)) = true := by decide +kernel

def g6_m8 : BitVec 64 := 0x3333333300000000

def g6_st8 : List (BitVec 64) := [0x2222222200000000,0x3030303000000000,0x3300330000000000,0x3333000000000000]

def g6_ix8 : List ℕ := [32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_8 : g6_ix8.length = 16 ∧ (∀ idx ∈ g6_ix8, idx < 64) ∧ (∀ idx ∈ g6_ix8, g6_m8.getLsbD idx = true) ∧ projS 16 g6_ix8 goal6 = b4_1_goal ∧ g6_st8.all (fun w => rows4.contains (projS 16 g6_ix8 w)) = true := by decide +kernel

def g6_cfMasks : Array (BitVec 64) := Array.mk [g6_m0,g6_m1,g6_m2,g6_m3,g6_m4,g6_m5,g6_m6,g6_m7,g6_m8]

def g6_cfB0s : Array ℕ := Array.mk [0,0,0,4,0,4,0,32,32]

def g6_cfStocks : Array (List (BitVec 64)) := Array.mk [g6_st0,g6_st1,g6_st2,g6_st3,g6_st4,g6_st5,g6_st6,g6_st7,g6_st8]

def g6_cfLBs : Array ℕ := Array.mk [8,7,8,8,9,7,8,7,6]

theorem g6_cof_sound (c fuel : ℕ) (hc : c < 9) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) (hnd : nxt.Nodup) (hchk : checkCofClose64 (g6_cfLBs[c]?.getD 0) fuel (g6_cfMasks[c]?.getD 0) (g6_cfB0s[c]?.getD 0) (g6_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose64_sound_aux goal6 8 g6_ix0 g6_cspec_0.1 g6_cspec_0.2.1 g6_m0 g6_cspec_0.2.2.1 0 g6_st0 c5_0_goal (by decide) g6_cspec_0.2.2.2.1 g6_cspec_0.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_sound_aux goal6 7 g6_ix1 g6_cspec_1.1 g6_cspec_1.2.1 g6_m1 g6_cspec_1.2.2.1 0 g6_st1 c5_1_goal (by decide) g6_cspec_1.2.2.2.1 g6_cspec_1.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_sound_aux goal6 8 g6_ix2 g6_cspec_2.1 g6_cspec_2.2.1 g6_m2 g6_cspec_2.2.2.1 0 g6_st2 c5_0_goal (by decide) g6_cspec_2.2.2.2.1 g6_cspec_2.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_sound_aux goal6 8 g6_ix3 g6_cspec_3.1 g6_cspec_3.2.1 g6_m3 g6_cspec_3.2.2.1 4 g6_st3 c5_2_goal (by decide) g6_cspec_3.2.2.2.1 g6_cspec_3.2.2.2.2 c5_2_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_sound_aux goal6 9 g6_ix4 g6_cspec_4.1 g6_cspec_4.2.1 g6_m4 g6_cspec_4.2.2.1 0 g6_st4 c5_3_goal (by decide) g6_cspec_4.2.2.2.1 g6_cspec_4.2.2.2.2 c5_3_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_16_sound_aux goal6 7 g6_ix5 g6_cspec_5.1 g6_cspec_5.2.1 g6_m5 g6_cspec_5.2.2.1 4 g6_st5 b4_0_goal (by decide) g6_cspec_5.2.2.2.1 g6_cspec_5.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose64_sound_aux goal6 8 g6_ix6 g6_cspec_6.1 g6_cspec_6.2.1 g6_m6 g6_cspec_6.2.2.1 0 g6_st6 c5_4_goal (by decide) g6_cspec_6.2.2.2.1 g6_cspec_6.2.2.2.2 c5_4_no_build fuel hist nxt hnd hchk
  | 7 => exact checkCofClose64_sound_aux goal6 7 g6_ix7 g6_cspec_7.1 g6_cspec_7.2.1 g6_m7 g6_cspec_7.2.2.1 32 g6_st7 c5_5_goal (by decide) g6_cspec_7.2.2.2.1 g6_cspec_7.2.2.2.2 c5_5_no_build fuel hist nxt hnd hchk
  | 8 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix8 g6_cspec_8.1 g6_cspec_8.2.1 g6_m8 g6_cspec_8.2.2.1 32 g6_st8 b4_1_goal (by decide) g6_cspec_8.2.2.2.1 g6_cspec_8.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | c + 9 => omega

def g6_L4 : Array W6Node := Array.mk [
([0xf0f3ff00f0f3ff0,v5,v0,v2,v4],[],[],[])
]

def g6_L5 : Array W6Node := Array.mk [
([v63,0xff00c000ff00c0,v5,v0,v3,v4],[],[],[]),
([v5,v0,v44,v49,v1,v4],[],[],[]),
([v5,v0,v17,v1,v31,v4],[],[],[]),
([v43,v5,v14,v3,v2,v23],[],[],[]),
([v5,v14,v24,v2,v23,v4],[],[],[]),
([v54,v5,v0,v17,v1,v4],[],[],[]),
([v54,0xff003000ff0030,v5,v0,v3,v4],[],[],[]),
([v5,v0,v17,v45,v6,v4],[],[],[]),
([v5,v0,v17,v46,v1,v4],[],[],[]),
([v5,v34,v3,v2,v45,v4],[],[],[]),
([v5,v0,v40,v2,v45,v4],[],[],[]),
([v5,v0,v3,v46,v45,v4],[],[],[]),
([v10,v5,v0,v17,v6,v4],[],[],[]),
([v5,v0,0xcfcfff30cfcfff30,v3,v2,v4],[],[],[]),
([v5,0xcccccc30cccccc30,v3,v2,v1,v4],[],[],[]),
([v11,v5,v3,v2,v45,v4],[],[],[]),
([v5,v0,v44,v89,v1,v4],[],[],[]),
([v5,v0,v17,v93,v1,v4],[],[],[]),
([v5,v0,v44,v24,v6,v4],[],[],[]),
([v5,v0,v14,v17,v6,v4],[],[],[]),
([v7,v5,v18,v17,v6,v4],[],[],[]),
([v7,v11,v5,v17,v6,v4],[],[],[]),
([v7,v5,v0,v81,v6,v4],[],[],[]),
([v7,0xf3f0f000f3f0f00,v5,v0,v6,v4],[],[],[]),
([v15,v94,v5,v0,v2,v4],[],[],[(0,0)]),
([v5,v0,v17,v27,v6,v4],[],[],[]),
([v5,v0,v3,v74,v6,v4],[],[],[]),
([0xf0c0f3c0f0c0f3c,v5,v0,v2,v1,v4],[],[],[]),
([v5,0xccccfc00ccccfc00,v3,v2,v12,v4],[],[],[]),
([0x30fffc0030fffc,v5,v0,v3,v6,v4],[],[],[]),
([v60,0x3333003033330030,v5,v3,v2,v4],[],[],[]),
([0x33f0000033f000,v5,v0,v3,v6,v4],[],[],[]),
([v5,v0,v3,0xff00ccc0ff00ccc0,v6,v4],[],[],[]),
([v5,v3,v82,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v35,v2,v12),(v44,v35,v3),(v82,v0,v44)],[0],[]),
([v19,v11,v5,v3,v2,v41],[],[],[]),
([v19,v11,v5,v51,v3,v2],[],[],[]),
([v19,v35,v11,v5,v3,v4],[],[],[]),
([v5,v0,v75,v93,v1,v4],[],[],[]),
([v5,v0,v3,v90,v77,v4],[],[],[]),
([v64,0xff000000ff00cc,v5,v0,v3,v4],[],[],[]),
([v7,0xf0fcf000f0fcf00,v5,v0,v2,v4],[],[],[]),
([v5,v83,v3,v1,v6,v4],[],[],[]),
([v5,v14,v3,v2,0xffff3330ffff3330,v4],[],[],[]),
([v47,v5,v14,v3,v6,v4],[],[],[]),
([v5,v0,v3,v2,0xffccfffc33000300,v1],[],[],[]),
([v7,v94,v5,v0,v2,v4],[],[],[]),
([v5,v76,v17,v25,v1,v4],[],[],[]),
([v5,v14,v3,v2,v23,v4],[],[],[]),
([v5,v83,v3,v25,v1,v4],[],[],[]),
([v5,v0,v3,0xff00cfc0ff00cfc0,v6,v4],[],[],[]),
([v5,v0,v81,v22,v1,v4],[],[],[]),
([0x3333cc3c3333cc3c,v5,v3,v2,v1,v4],[],[],[]),
([v5,v0,v16,v2,v27,v58],[],[],[]),
([v5,v0,v16,v22,v27,v4],[],[],[]),
([v5,0xcccccc3ccccccc3c,v3,v2,v1,v4],[],[],[]),
([v7,v55,v5,v3,v2,v4],[(v7,v3,v1),(v6,v2,v1),(v18,v0,v6),(v13,v0,v6),(v55,v18,v13)],[0],[]),
([0xf0fffc00f0fffc,v5,v0,v3,v6,v4],[],[],[]),
([v5,v0,v3,0xff000f0cff000f0c,v6,v4],[],[],[]),
([v19,v11,v5,v3,v2,v4],[],[],[]),
([0x33cc000033cc,v55,v5,v3,v2,v4],[(v6,v1,v2),(v18,v0,v6),(v13,v0,v6),(v55,v18,v13),(0x33cc000033cc,v55,v1)],[0],[]),
([v19,v55,v5,v3,v2,v4],[(v6,v1,v2),(v18,v0,v6),(v13,v0,v6),(v55,v18,v13),(v19,v1,v13)],[0],[]),
([v19,v35,v5,v18,v3,v4],[(v6,v1,v2),(v18,v0,v6),(v13,v0,v6),(v19,v1,v13),(v35,v2,v13)],[0],[]),
([v55,v5,v51,v3,v2,v1],[(v6,v2,v1),(v29,v0,v6),(v11,v0,v6),(v55,v29,v11),(v51,v11,v4)],[0],[]),
([0xfccc0000fccc,v11,v5,v3,v2,v4],[],[],[]),
([v5,v0,v16,v2,0xffffc0f0ffffc0f0,v4],[],[],[]),
([0xeaeaeaaaeaeaeaaa,v3,v50,v2,v1,v4],[],[],[]),
([0x3c3c3ccc3c3c3ccc,v5,v3,v2,v1,v4],[],[],[]),
([v5,v0,0xcfcfcfffc0c0c000,v3,v2,v1],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L6 : Array W6Node := Array.mk [
([v11,v5,v3,v2,v56,v6,v4],[(v28,v0,v3),(v56,v28,v1),(v6,v1,v2),(v11,v0,v6)],[1],[]),
([v63,v5,v0,v3,v49,v6,v4],[(v28,v0,v3),(v49,v28,v2),(v6,v2,v1),(v63,v1,v49)],[2],[]),
([v11,v5,v3,v2,v1,v52,v4],[(v28,v0,v3),(v49,v28,v2),(v52,v49,v1),(v11,v0,v52)],[3],[]),
([v63,v5,v0,v3,v2,v52,v4],[(v28,v0,v3),(v56,v28,v1),(v52,v56,v2),(v63,v1,v52)],[4],[(0,0)]),
([v11,v5,v3,v2,v49,v1,v4],[],[],[]),
([v63,v5,v0,v3,v2,v56,v4],[(v28,v0,v3),(v56,v28,v1),(v52,v56,v2),(v63,v1,v52)],[4],[(0,0),(1,1)]),
([v63,v5,v0,v3,v2,v6,v4],[(v28,v0,v3),(v6,v1,v2),(v52,v28,v6),(v63,v1,v52)],[0,4],[]),
([v11,v5,v3,0xf3f3f3c0f3f3f3c0,v2,v1,v4],[],[],[]),
([v5,v0,v17,v25,v1,v4],[],[],[]),
([v5,v0,v17,v25,v9,v1,v4],[],[],[]),
([v5,v0,v3,v2,v12,v31,v4],[(v8,v0,v3),(v23,v8,v1),(v12,v0,v1),(v31,v2,v23)],[0,1],[(1,2)]),
([v54,v5,v0,v3,v9,v1,v4],[],[],[]),
([v5,v0,v17,v2,v1,v23,v4],[],[],[]),
([v5,v0,v3,v2,0xff30cc00ff30cc00,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v12,v0,v1),(0xff30cc00ff30cc00,v25,v12)],[0],[]),
([v5,v14,v3,v2,v23,v4],[(v8,v0,v3),(v23,v8,v1),(v10,v1,v23),(v14,v10,v0)],[5],[(0,3)]),
([v10,v5,v14,v3,v2,v23,v4],[],[],[(0,4)]),
([v5,v0,v14,v3,v2,v23,v4],[],[],[]),
([v10,v5,v0,v24,v2,v23,v4],[],[],[(0,4)]),
([v10,v5,v0,v3,v2,v31,v4],[(v8,v0,v3),(v23,v8,v1),(v10,v1,v23),(v31,v2,v23)],[0],[(1,2)]),
([v10,0xff003000ff0030,v5,v0,v3,v2,v4],[],[],[(1,5)]),
([v5,v18,v3,v2,v1,v31,v4],[(v8,v0,v3),(v25,v8,v2),(v31,v25,v1),(v18,v0,v31)],[3],[]),
([v54,v5,v0,v3,v2,v31,v4],[(v8,v0,v3),(v23,v8,v1),(v31,v23,v2),(v54,v1,v31)],[4],[(0,6)]),
([v54,v5,v0,v3,v2,v23,v4],[(v8,v0,v3),(v23,v8,v1),(v31,v23,v2),(v54,v1,v31)],[4],[(0,6)]),
([v5,v0,0xccccfffcccccfffc,v3,v2,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v54,v25,v1),(0xccccfffcccccfffc,v54,v0)],[6,7],[]),
([v8,v5,v14,v3,v2,v23,v4],[],[],[]),
([v8,v5,v0,v17,v25,v1,v4],[],[],[]),
([v5,v0,v3,v2,0xff30cf00ff30cf00,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v10,v8,v1),(0xff30cf00ff30cf00,v10,v25)],[0],[]),
([v5,v0,v69,v3,v2,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v31,v25,v1),(v69,v8,v31)],[0,2],[]),
([v10,v5,v14,v24,v2,v1,v4],[],[],[(0,4)]),
([v43,v10,v5,v14,v3,v2,v1],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0),(v43,v14,v4)],[4],[(0,3)]),
([v10,v5,v14,v3,v2,v6,v4],[],[],[]),
([v5,v0,v3,v2,v32,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0),(v32,v14,v2)],[2,6,7],[]),
([v60,v5,v0,v3,v2,v1,v4],[],[],[]),
([v5,v0,v14,v3,v2,v6,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0),(v6,v2,v1)],[0],[]),
([v5,v0,v14,v24,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0),(v24,v10,v3)],[6],[]),
([v5,v0,v17,v2,v1,v45,v4],[],[],[(0,7)]),
([v20,v5,v0,v17,v2,v1,v4],[(v8,v0,v3),(v42,v8,v2),(v17,v42,v3),(v20,v42,v1)],[2],[]),
([v10,v5,v0,v24,v2,v6,v4],[],[],[(1,2),(1,7)]),
([v5,v0,v3,v2,v45,v12,v4],[(v8,v0,v3),(v42,v8,v2),(v45,v42,v1),(v12,v0,v1)],[2,4],[(1,8)]),
([v20,v5,v0,v3,v2,v45,v4],[(v8,v0,v3),(v42,v8,v2),(v45,v42,v1),(v20,v1,v45)],[4],[(0,9),(0,10),(0,11)]),
([v10,v5,v0,v3,v46,v6,v4],[(v8,v0,v3),(v10,v8,v1),(v46,v10,v2),(v6,v2,v1)],[0],[(1,7)]),
([v20,v5,v34,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v34,v20,v0)],[4],[(0,9),(1,9)]),
([v5,v0,v34,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v34,v20,v0)],[6,7],[]),
([v20,v5,v0,v40,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v40,v20,v3)],[4],[(0,10)]),
([v10,v5,v34,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v34,v20,v0)],[4],[(1,9)]),
([v10,v5,v0,v40,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v40,v20,v3)],[4],[]),
([v10,v5,v0,v3,v2,v45,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v45,v20,v1)],[4],[(0,11),(1,8)]),
([v10,v5,v0,v17,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v9,v0,v2),(v17,v3,v9)],[2],[(0,12)]),
([v10,v5,v0,v3,v9,v6,v4],[(v8,v0,v3),(v10,v8,v1),(v9,v0,v2),(v6,v2,v1)],[0],[(0,12)]),
([v10,v5,v18,v3,v2,v6,v4],[],[],[]),
([v10,v11,v5,v3,v2,v6,v4],[],[],[]),
([v43,v8,v5,v14,v3,v2,v1],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0),(v43,v14,v4)],[3,4,6],[(0,3)]),
([v8,v5,v14,v3,v2,v6,v4],[],[],[]),
([v8,v5,v14,v24,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0),(v24,v10,v3)],[3,6],[(0,4)]),
([v8,v5,v0,v17,v1,v6,v4],[],[],[(0,12)]),
([v30,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v30,v20,v8)],[6,7],[]),
([v8,v5,v34,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v34,v20,v0)],[3,4,6],[]),
([v8,v5,v0,v40,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2),(v40,v20,v3)],[3,4],[]),
([v10,v42,v5,v0,v3,v6,v4],[(v8,v0,v3),(v10,v8,v1),(v42,v8,v2),(v6,v2,v1)],[0,2],[(0,12),(1,12)]),
([v10,v5,v0,v69,v3,v2,v4],[(v8,v0,v3),(v10,v8,v1),(v6,v2,v1),(v69,v8,v6)],[2,3],[(0,13)]),
([v5,v0,v69,v3,v2,v12,v4],[(v8,v0,v3),(v12,v0,v1),(v6,v1,v2),(v69,v8,v6)],[2,3],[]),
([v8,v11,v5,v3,v2,v1,v4],[(v8,v0,v3),(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[3,6],[]),
([0x3030fffc3030fffc,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v9,v0,v2),(v19,v9,v1),(0x3030fffc3030fffc,v19,v8)],[0],[]),
([v30,v5,v3,v50,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6),(v50,v30,v0)],[4],[]),
([v5,v0,v3,v50,v2,v1,v4],[],[],[]),
([v30,v5,v53,v0,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6),(v53,v30,v3)],[4],[]),
([v30,v5,v0,v3,v2,v1,v95],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6),(v95,v30,v4)],[6],[]),
([v20,v5,v0,v3,v2,v1,v4],[],[],[]),
([v8,v5,v3,v50,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6),(v50,v30,v0)],[3,4],[]),
([v8,v5,v53,v0,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6),(v53,v30,v3)],[3,4],[]),
([v11,v5,v3,v2,v1,v31,v4],[(v8,v0,v3),(v6,v2,v1),(v31,v8,v6),(v11,v0,v6)],[0],[(0,14)]),
([v54,v5,v0,v3,v2,v6,v4],[(v8,v0,v3),(v6,v1,v2),(v31,v8,v6),(v54,v1,v31)],[0,4],[]),
([v5,v0,v3,v2,v45,v6,v4],[(v8,v0,v3),(v6,v1,v2),(v20,v8,v6),(v45,v20,v1)],[0,4],[(0,15)]),
([v5,v0,v3,v2,v1,v31,v4],[(v8,v0,v3),(v6,v2,v1),(v20,v8,v6),(v31,v20,v6)],[3],[]),
([v20,v5,v18,v3,v2,v1,v4],[],[],[(0,14)]),
([v20,v11,v5,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v20,v8,v6),(v11,v0,v6)],[3],[(0,15),(1,15)]),
([v8,v11,v5,v53,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v11,v0,v6),(v53,v11,v3)],[3,5],[]),
([v8,v11,v5,v3,v2,v1,v41],[(v8,v0,v3),(v6,v2,v1),(v11,v0,v6),(v41,v11,v4)],[3,6],[]),
([0xf0c3f0c0f0c3f0c,v5,v0,v3,v2,v1,v4],[(v12,v0,v1),(v9,v0,v2),(v24,v3,v12),(0xf0c3f0c0f0c3f0c,v24,v9)],[0],[]),
([v5,v0,v17,v3,v12,v6,v4],[(v9,v0,v2),(v12,v0,v1),(v17,v3,v9),(v6,v2,v1)],[0,3],[(0,12)]),
([v11,v5,v3,v9,v12,v6,v4],[(v9,v0,v2),(v12,v0,v1),(v6,v2,v1),(v11,v0,v6)],[0,1,2,6],[]),
([v19,v35,v5,v0,v3,v4],[(v12,v0,v1),(v9,v0,v2),(v19,v1,v9),(v35,v2,v12)],[4],[]),
([v19,v35,v5,v0,v3,v9,v4],[],[],[]),
([0x3330330033303300,v5,v0,v3,v2,v1,v4],[(v12,v0,v1),(v24,v3,v12),(v89,v24,v2),(0x3330330033303300,v0,v89)],[6,7],[]),
([v39,v5,v0,v3,v2,v65,v4],[(v9,v0,v2),(v17,v3,v9),(v65,v17,v1),(v39,v1,v65)],[4],[(1,16)]),
([v7,v5,v0,v17,v2,v65,v4],[(v9,v0,v2),(v17,v3,v9),(v65,v17,v1),(v7,v3,v1)],[2],[]),
([v39,v5,v0,v84,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v39,v17,v1),(v84,v39,v3)],[4],[(1,16)]),
([v5,v0,v44,v24,v2,v1,v4],[(v12,v0,v1),(v24,v3,v12),(0xf000c000f000c0,v24,v2),(v44,0xf000c000f000c0,v3)],[4],[(0,18),(1,17)]),
([v39,v5,v0,v17,v3,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v39,v17,v1),(v6,v2,v1)],[2],[(1,18)]),
([v5,v0,v14,v17,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v7,v3,v1),(v14,v7,v0)],[6],[(0,19)]),
([v7,v5,v0,v17,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v7,v3,v1),(v6,v2,v1)],[2,4],[(0,12),(0,19),(0,20),(0,21),(0,22),(0,23)]),
([v5,v18,v17,v3,v1,v6,v4],[],[],[(0,20)]),
([v11,v5,v17,v3,v1,v6,v4],[],[],[(0,21)]),
([v5,v0,v81,v3,v1,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v6,v2,v1),(v81,v17,v6)],[0],[(0,22)]),
([v94,v5,v0,v3,v2,v6,v4],[(v12,v0,v1),(v24,v3,v12),(v6,v1,v2),(v94,v24,v6)],[0],[(0,24),(1,23)]),
([v15,v5,v0,v17,v1,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v6,v2,v1),(v15,v3,v6)],[2],[(0,25),(1,24)]),
([v5,v14,v24,v2,v1,v12,v4],[],[],[]),
([v19,v5,v0,v3,v2,v65,v4],[(v9,v0,v2),(v17,v3,v9),(v65,v17,v1),(v19,v9,v1)],[4],[(1,16)]),
([v5,v0,v3,v2,v74,v1,v4],[],[],[(0,26)]),
([v39,v5,v0,v3,v9,v6,v4],[],[],[(1,26)]),
([v5,v0,v17,v2,v32,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v7,v3,v1),(v32,v7,v9)],[6],[(0,27)]),
([v7,v5,v0,v17,v9,v6,v4],[],[],[]),
([v19,v5,v0,v17,v3,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v6,v2,v1),(v19,v9,v1)],[2],[(1,18)]),
([v11,v5,v17,v3,v2,v1,v4],[],[],[]),
([0xf0f3f0c0f0f3f0c,v5,v0,v3,v2,v1,v4],[(v12,v0,v1),(v24,v3,v12),(v13,v12,v2),(0xf0f3f0c0f0f3f0c,v24,v13)],[0],[]),
([v43,v5,v14,v3,v2,v1,v12],[(v12,v0,v1),(v10,v3,v12),(v14,v10,v0),(v43,v14,v4)],[2,4],[]),
([v5,v14,v3,v2,v12,v6,v4],[],[],[(0,28)]),
([v5,v14,v3,v2,v23,v12,v4],[(v12,v0,v1),(v10,v3,v12),(v14,v10,v0),(v23,v10,v1)],[2,3],[(0,4)]),
([v5,v0,v3,v46,v12,v6,v4],[(v12,v0,v1),(v10,v3,v12),(v46,v10,v2),(v6,v2,v1)],[0],[(1,7)]),
([v5,v0,v3,v2,v45,v13,v4],[(v9,v0,v2),(v42,v3,v9),(v45,v42,v1),(v13,v1,v9)],[4],[(0,10),(0,15)]),
([v5,v34,v3,v2,v9,v1,v4],[(v9,v0,v2),(v42,v3,v9),(v20,v42,v1),(v34,v20,v0)],[0,4],[]),
([v10,v35,v5,v0,v3,v6,v4],[],[],[(1,29)]),
([v10,v11,v5,v3,v2,v1,v4],[(v12,v0,v1),(v10,v3,v12),(v13,v2,v12),(v11,v0,v13)],[3],[(1,15)]),
([0x30fffc0030fffc,v5,v0,v3,v2,v1,v4],[],[],[(0,29)]),
([v60,v5,v0,v3,v2,v12,v4],[(v12,v0,v1),(v21,v3,v2),(v57,v21,v0),(v60,v57,v1)],[2,4],[]),
([v5,v0,v14,v3,v9,v6,v4],[(v9,v0,v2),(v7,v3,v1),(v14,v7,v0),(v6,v2,v1)],[0],[(0,19)]),
([v7,v5,v0,v84,v2,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v39,v7,v9),(v84,v39,v3)],[3,4],[]),
([v7,v5,v0,v3,v2,v65,v4],[(v9,v0,v2),(v7,v3,v1),(v39,v7,v9),(v65,v39,v1)],[3,4],[]),
([v47,v5,v0,v3,v2,v1,v4],[],[],[]),
([v47,v5,v3,v2,v32,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9),(v47,v0,v32)],[4],[(1,30)]),
([v60,v5,v0,v3,v2,v91,v4],[(v12,v0,v1),(v21,v3,v2),(v91,v21,v12),(v60,v1,v91)],[4],[(0,30)]),
([0xffccfffc,v5,v0,v3,v2,v32,v1],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9),(0xffccfffc,v32,v4)],[2,6],[]),
([v7,v5,v0,v3,v32,v6,v4],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9),(v6,v2,v1)],[2],[(1,26)]),
([v47,v5,v3,v2,v9,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9),(v47,v0,v32)],[0,4],[]),
([v39,v5,v0,v3,v2,v1,v4],[],[],[]),
([v7,v5,v0,v40,v2,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v20,v7,v9),(v40,v20,v3)],[3,4],[]),
([v7,v5,v0,v3,v2,v45,v4],[(v9,v0,v2),(v7,v3,v1),(v20,v7,v9),(v45,v20,v1)],[3,4],[]),
([v5,v0,v3,v74,v6,v4],[(v12,v0,v1),(v21,v3,v2),(v74,v21,v12),(v6,v2,v1)],[2,3,4],[(1,31)]),
([v7,v5,v0,v3,v96,v6,v4],[(v9,v0,v2),(v7,v3,v1),(v96,v7,v9),(v6,v2,v1)],[2],[]),
([v5,v0,v3,v74,v12,v6,v4],[],[],[]),
([v7,v5,v18,v3,v9,v6,v4],[(v9,v0,v2),(v7,v3,v1),(v6,v2,v1),(v18,v0,v6)],[3],[(0,20)]),
([v7,v11,v5,v3,v9,v6,v4],[],[],[(0,21)]),
([v7,v5,v0,v16,v9,v6,v4],[(v9,v0,v2),(v7,v3,v1),(v6,v2,v1),(v16,v3,v6)],[2],[]),
([0x330033cc330033cc,v5,v3,v9,v1,v6,v4],[(v9,v0,v2),(v6,v2,v1),(v18,v0,v6),(0x330033cc330033cc,v18,v9)],[0,2],[]),
([v11,v5,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v18,v0,v6),(v11,v18,v6)],[4],[]),
([v5,v18,v16,v3,v2,v12,v4],[(v12,v0,v1),(v6,v1,v2),(v18,v0,v6),(v16,v3,v6)],[6,8],[]),
([v15,v5,v18,v3,v2,v12,v4],[],[],[]),
([v19,v5,v18,v3,v9,v6,v4],[(v9,v0,v2),(v6,v2,v1),(v18,v0,v6),(v19,v1,v9)],[2,4],[]),
([v11,v5,v3,v2,v12,v6,v41],[(v12,v0,v1),(v6,v1,v2),(v11,v0,v6),(v41,v11,v4)],[1],[]),
([v11,v5,v51,v3,v2,v12,v6],[(v12,v0,v1),(v6,v1,v2),(v11,v0,v6),(v51,v11,v4)],[1,2],[]),
([v19,v11,v5,v3,v9,v6,v4],[(v9,v0,v2),(v6,v2,v1),(v11,v0,v6),(v19,v1,v9)],[2],[]),
([v5,v34,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v15,v3,v6),(v34,v15,v0)],[1],[]),
([v5,v0,v3,v22,v12,v6,v4],[],[],[(0,32),(1,25)]),
([v5,v0,v3,v2,v91,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v15,v3,v6),(v91,v15,v12)],[0],[]),
([v5,v0,v44,v3,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v35,v2,v12),(v44,v35,v3)],[0],[(0,18),(0,33)]),
([v5,v53,v0,v3,v2,v1,v4],[],[],[]),
([v11,v5,v0,v51,v3,v2,v1],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13),(v51,v11,v4)],[7],[]),
([v11,v5,v3,v2,v1,v13,v41],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13),(v41,v11,v4)],[4],[(0,34),(1,34)]),
([v11,v5,v51,v3,v2,v1,v13],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13),(v51,v11,v4)],[4],[(0,35),(1,35)]),
([v11,v5,v40,v3,v2,v1,v4],[],[],[]),
([v19,v11,v5,v3,v2,v4],[],[],[(0,34),(0,35)]),
([v19,v11,v5,v3,v2,v13,v4],[],[],[(0,36)]),
([v19,v11,v5,v0,v3,v2,v4],[],[],[]),
([v5,v34,v3,v2,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v20,v3,v13),(v34,v20,v0)],[4],[]),
([v19,v35,v5,v0,v3,v13,v4],[],[],[(0,36)]),
([v11,v5,v3,v2,v9,v1,v41],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13),(v41,v11,v4)],[0,4],[(0,34)]),
([v11,v5,v51,v3,v2,v9,v1],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13),(v51,v11,v4)],[0,4],[(0,35)]),
([v19,v11,v5,v3,v2,v9,v4],[],[],[]),
([v19,v11,v5,v3,v2,v12,v4],[(v12,v0,v1),(v13,v12,v2),(v11,v0,v13),(v19,v1,v13)],[0,2],[(0,36)]),
([v5,v0,v3,v82,v2,v1,v4],[(v12,v0,v1),(v35,v12,v2),(v44,v35,v3),(v82,v0,v44)],[2,6,7],[]),
([v5,v3,v82,v2,v1,v12,v4],[(v12,v0,v1),(v35,v12,v2),(v44,v35,v3),(v82,v0,v44)],[0,2],[(0,33)]),
([v5,v0,v3,v2,v12,v70,v4],[(v12,v0,v1),(v35,v12,v2),(v44,v35,v3),(v70,v44,v1)],[0,1],[(1,17)]),
([v48,v5,v0,v3,v2,v70,v4],[(v37,v0,v2),(v61,v37,v3),(v70,v61,v1),(v48,v1,v70)],[4],[(1,37)]),
([v48,v5,v0,v97,v2,v1,v4],[(v37,v0,v2),(v61,v37,v3),(v48,v61,v1),(v97,v48,v3)],[4],[(1,37)]),
([v5,v0,v75,v71,v2,v1,v4],[(v62,v0,v1),(v71,v62,v3),(0xf0003000f00030,v71,v2),(v75,0xf0003000f00030,v3)],[1,4],[]),
([v5,v0,v3,v2,v72,v70,v4],[(v37,v0,v2),(v72,v37,v1),(v48,v3,v72),(v70,v48,v1)],[4],[(1,37)]),
([v7,v5,v0,v97,v2,v1,v4],[(v37,v0,v2),(v7,v3,v1),(v48,v37,v7),(v97,v48,v3)],[3,4],[]),
([v7,v5,v0,v3,v2,v70,v4],[(v37,v0,v2),(v7,v3,v1),(v48,v37,v7),(v70,v48,v1)],[3,4],[]),
([v66,v5,v0,v3,v2,v77,v4],[(v38,v0,v4),(v6,v1,v2),(v66,v6,v38),(v77,v66,v1)],[4],[(0,38)]),
([v5,v0,v3,v2,v77,v6,v4],[(v38,v0,v4),(v6,v1,v2),(v66,v6,v38),(v77,v66,v1)],[0,4],[]),
([v67,v5,v0,v3,v2,v77,v4],[(v38,v0,v4),(v67,v1,v38),(v66,v67,v2),(v77,v66,v1)],[4],[(0,38)]),
([v64,v5,v0,v3,v59,v6,v4],[(v33,v0,v4),(v59,v33,v2),(v6,v2,v1),(v64,v1,v59)],[2],[]),
([v64,v5,v0,v3,v2,v68,v4],[(v33,v0,v4),(v78,v33,v1),(v68,v78,v2),(v64,v1,v68)],[4],[(0,39)]),
([v64,v5,v0,v3,v2,v78,v4],[(v33,v0,v4),(v78,v33,v1),(v68,v78,v2),(v64,v1,v68)],[4,7],[(0,39)]),
([v64,v5,v0,v3,v2,v6,v4],[(v33,v0,v4),(v6,v1,v2),(v68,v33,v6),(v64,v1,v68)],[0,4],[]),
([v10,v5,v14,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v10,v26,v7),(v14,v10,v0)],[3,4],[]),
([v5,v0,v3,v2,v46,v1,v4],[],[],[]),
([v10,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v26,v7,v0),(v10,v26,v7),(v6,v2,v1)],[0],[]),
([v7,v5,v14,v71,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v71,v26,v3),(v14,v7,v0)],[1,3],[]),
([v7,v5,v0,v71,v2,v6,v4],[],[],[(0,40)]),
([v15,v5,v0,v3,v2,0xffff00c0ffff00c0,v4],[(v21,v3,v2),(v85,v21,v0),(0xffff00c0ffff00c0,v85,v1),(v15,v21,v1)],[1,4],[]),
([v7,v5,v0,v3,v86,v6,v4],[(v7,v3,v1),(v26,v7,v0),(v86,v26,v2),(v6,v2,v1)],[0],[]),
([v7,v5,v0,v3,v2,v52,v4],[(v7,v3,v1),(v26,v7,v0),(v86,v26,v2),(v52,v86,v1)],[3],[]),
([v7,v5,v14,v3,v2,v56,v4],[(v7,v3,v1),(v26,v7,v0),(v56,v26,v1),(v14,v7,v0)],[1],[]),
([v5,v0,v3,v2,v22,v56,v4],[],[],[]),
([v15,v5,v0,v3,v2,v56,v4],[(v7,v3,v1),(v26,v7,v0),(v56,v26,v1),(v15,v7,v2)],[0,1],[]),
([v7,0xff00c000ff00c0,v5,v0,v3,v2,v4],[],[],[]),
([v5,v83,v3,v2,v1,v4],[(v21,v3,v2),(v85,v21,v0),(v57,v21,v0),(v83,v85,v57)],[0,3],[(0,41)]),
([v5,v83,v57,v3,v2,v1,v4],[(v21,v3,v2),(v85,v21,v0),(v57,v21,v0),(v83,v85,v57)],[5,8],[]),
([v26,v5,v14,v3,v2,v6,v4],[],[],[(1,41)]),
([v7,v5,v98,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v14,v7,v0),(v98,v26,v14)],[3],[]),
([v5,v0,v3,0xff003f30ff003f30,v2,v1,v4],[],[],[]),
([v26,v5,v34,v3,v2,v1,v4],[],[],[]),
([v47,v5,v14,v3,v2,v1,v4],[(v7,v3,v1),(v14,v7,v0),(v32,v14,v2),(v47,v0,v32)],[4],[(0,42),(0,43),(1,30)]),
([v43,v5,v0,v3,v2,v32,v1],[(v7,v3,v1),(v14,v7,v0),(v32,v14,v2),(v43,v14,v4)],[2],[(0,44)]),
([v5,v0,v14,v3,v32,v6,v4],[(v7,v3,v1),(v14,v7,v0),(v32,v14,v2),(v6,v2,v1)],[0,2],[(0,43)]),
([v43,0xcc00fc00cc00fc,v5,v0,v3,v2,v1],[],[],[]),
([v43,v5,v0,v14,v3,v2,v6],[(v7,v3,v1),(v14,v7,v0),(v43,v14,v4),(v6,v2,v1)],[0],[]),
([v5,v0,0xccccfc00ccccfc00,v3,v2,v6,v4],[(v7,v3,v1),(v14,v7,v0),(v6,v2,v1),(0xccccfc00ccccfc00,v14,v6)],[0],[]),
([v7,v5,v14,v24,v2,v1,v4],[],[],[]),
([v7,v5,v14,v3,v2,v23,v4],[],[],[]),
([v60,v5,v0,v3,v2,v27,v4],[(v21,v3,v2),(v57,v21,v0),(v27,v21,v1),(v60,v57,v1)],[4],[(0,30)]),
([v43,v5,v0,v3,v2,v22,v1],[],[],[]),
([v5,v0,v14,v3,v22,v6,v4],[(v7,v3,v1),(v14,v7,v0),(v22,v7,v2),(v6,v2,v1)],[0],[(0,43)]),
([v5,v0,0xccccfc0cccccfc0c,v3,v2,v1,v4],[],[],[]),
([v43,v15,v5,v0,v3,v2,v1],[],[],[]),
([v43,v7,v5,v0,v3,v2,v6],[(v7,v3,v1),(v14,v7,v0),(v43,v14,v4),(v6,v2,v1)],[0,3],[]),
([v7,v5,v36,v24,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v24,v10,v3),(v36,v7,v0)],[3],[]),
([v5,v0,v17,v2,v1,v27,v4],[],[],[(0,25)]),
([v15,v5,v0,v17,v2,v1,v4],[(v21,v3,v2),(v42,v21,v0),(v17,v42,v3),(v15,v21,v1)],[2],[]),
([v7,v5,v0,v24,v2,v6,v4],[],[],[(0,45),(1,25)]),
([v7,v5,v0,v24,v2,v23,v4],[(v7,v3,v1),(v10,v7,v0),(v24,v10,v3),(v23,v10,v1)],[3],[(0,4),(1,46)]),
([v10,v5,v36,v24,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v24,v10,v3),(v36,v7,v0)],[3],[(1,46)]),
([v15,v5,v0,v3,v2,v45,v4],[(v21,v3,v2),(v42,v21,v0),(v45,v42,v1),(v15,v21,v1)],[4],[(0,9)]),
([v7,v5,v0,v3,v46,v6,v4],[(v7,v3,v1),(v10,v7,v0),(v46,v10,v2),(v6,v2,v1)],[0],[]),
([v7,v5,v0,v3,v2,v31,v4],[(v7,v3,v1),(v10,v7,v0),(v46,v10,v2),(v31,v46,v1)],[3],[]),
([v7,v5,v36,v3,v2,v23,v4],[(v7,v3,v1),(v10,v7,v0),(v23,v10,v1),(v36,v7,v0)],[2],[(0,47)]),
([v7,0xff003000ff0030,v5,v0,v3,v2,v4],[],[],[]),
([v10,v5,v36,v3,v2,v23,v4],[(v7,v3,v1),(v10,v7,v0),(v23,v10,v1),(v36,v7,v0)],[3],[(1,46),(1,48)]),
([v10,v5,v98,v3,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v36,v7,v0),(v98,v10,v36)],[3],[(1,48)]),
([v10,v5,v36,v3,v2,v6,v4],[(v7,v3,v1),(v10,v7,v0),(v36,v7,v0),(v6,v2,v1)],[3],[(1,41)]),
([v5,v0,v3,0xff00cfc0ff00cfc0,v2,v1,v4],[],[],[(0,49)]),
([v10,v5,v0,v3,v22,v6,v4],[],[],[(0,49),(1,25)]),
([v5,v0,v3,v2,v27,0xffffcc0cffffcc0c,v4],[(v21,v3,v2),(v76,v21,v0),(v27,v21,v1),(0xffffcc0cffffcc0c,v76,v1)],[1,4],[(1,50)]),
([v47,v5,v36,v3,v2,v1,v4],[],[],[]),
([v5,0xcc0cccfccc0cccfc,v0,v3,v2,v1,v4],[(v21,v3,v2),(v76,v21,v0),(v15,v21,v1),(0xcc0cccfccc0cccfc,v15,v76)],[6,7],[]),
([v7,v5,v0,v81,v2,v1,v4],[(v7,v3,v1),(v36,v7,v0),(v87,v36,v2),(v81,v3,v87)],[2],[(0,22)]),
([v7,v5,v0,v3,v87,v6,v4],[(v7,v3,v1),(v36,v7,v0),(v87,v36,v2),(v6,v2,v1)],[0,3],[(0,22)]),
([v5,v0,v3,v2,v22,0xffffccc0ffffccc0,v4],[],[],[]),
([v5,0xcc00ccc0cc00ccc0,v3,v2,v32,v1,v4],[],[],[(1,51)]),
([0xffccfffc,v5,v0,v3,v2,v22,v1],[],[],[]),
([0xcc0c0000cc0c,0x3333003033330030,v5,v3,v2,v1,v4],[],[],[(0,51)]),
([v5,v0,v16,v2,v27,v4],[(v21,v3,v2),(v27,v21,v1),(v15,v1,v27),(v16,v15,v3)],[5],[(0,52)]),
([v15,v5,v0,v16,v2,v27,v4],[],[],[(0,53)]),
([v5,v0,v3,v22,v27,v4],[(v21,v3,v2),(v27,v21,v1),(v15,v1,v27),(v22,v15,v2)],[4],[]),
([v15,v5,v0,v3,v22,v27,v4],[],[],[(0,53)]),
([v7,v5,v0,v16,v22,v1,v4],[],[],[]),
([v7,v5,v0,v3,v22,v27,v4],[],[],[]),
([v7,v5,v0,v3,v2,0xffff3330ffff3330,v4],[(v7,v3,v1),(v22,v7,v2),(v47,v0,v22),(0xffff3330ffff3330,v47,v1)],[3],[(0,42)]),
([v7,v47,v5,v0,v3,v6,v4],[(v7,v3,v1),(v22,v7,v2),(v47,v0,v22),(v6,v2,v1)],[0],[(0,43)]),
([v7,v5,v0,v16,v22,v6,v4],[(v7,v3,v1),(v22,v7,v2),(v6,v2,v1),(v16,v3,v6)],[3],[]),
([v15,v5,v0,v79,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v92,v15,v0),(v79,v92,v3)],[1,4],[]),
([v92,v5,v34,v3,v2,v1,v4],[],[],[(0,54)]),
([0xccccccfc,v5,v0,v34,v3,v2,v1],[(v7,v3,v1),(v15,v7,v2),(v34,v15,v0),(0xccccccfc,v34,v4)],[6],[]),
([0xccccccfc,v15,v5,v0,v3,v2,v1],[],[],[]),
([v15,v5,v0,v40,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v20,v15,v0),(v40,v20,v3)],[4],[]),
([v20,v5,0xcccccc0ccccccc0c,v3,v2,v1,v4],[],[],[(0,54)]),
([v15,v5,v0,v16,v2,v1,v58],[(v7,v3,v1),(v15,v7,v2),(v16,v15,v3),(v58,v16,v4)],[4],[(0,52)]),
([v7,v5,v0,v16,v2,v1,v58],[(v7,v3,v1),(v15,v7,v2),(v16,v15,v3),(v58,v16,v4)],[3,4],[]),
([v7,v5,v0,v16,v2,v27,v4],[(v7,v3,v1),(v15,v7,v2),(v16,v15,v3),(v27,v15,v1)],[0,3],[(0,53)]),
([v5,v0,0xccccfcf0ccccfcf0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v18,v0,v6),(0xccccfcf0ccccfcf0,v7,v18)],[0],[]),
([v7,v5,v18,v3,v2,v13,v4],[(v7,v3,v1),(v6,v2,v1),(v18,v0,v6),(v13,v0,v6)],[0],[(0,55)]),
([v39,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v13,v0,v6),(v39,v7,v13)],[0,3],[]),
([v7,v5,v0,v40,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v13,v0,v6),(v40,v3,v13)],[3],[]),
([v7,v35,v5,v0,v3,v6,v4],[],[],[(1,56)]),
([v48,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v29,v0,v6),(v48,v29,v7)],[0,3],[]),
([v7,v5,v0,v79,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v29,v0,v6),(v79,v29,v3)],[3],[]),
([v7,v5,v0,v3,v73,v6,v4],[],[],[(0,57)]),
([v29,v7,v11,v5,v3,v2,v4],[(v7,v3,v1),(v6,v2,v1),(v29,v0,v6),(v11,v0,v6)],[0],[(0,55)]),
([v7,v5,v0,v3,v2,v6,v41],[(v7,v3,v1),(v6,v2,v1),(v11,v0,v6),(v41,v11,v4)],[0,3],[]),
([v7,v5,v0,v16,v2,v6,v58],[(v7,v3,v1),(v6,v2,v1),(v16,v3,v6),(v58,v16,v4)],[3],[]),
([0x30f0000030f0,v5,v0,v3,v2,v6,v4],[(v6,v1,v2),(v18,v0,v6),(v88,v18,v3),(0x30f0000030f0,v88,v1)],[0,3],[]),
([v88,v5,v0,v16,v2,v1,v4],[(v6,v2,v1),(v18,v0,v6),(v88,v18,v3),(v16,v3,v6)],[1,4,8],[]),
([v11,v5,v3,v2,v1,v13,v4],[(v6,v2,v1),(v18,v0,v6),(v11,v18,v6),(v13,v0,v6)],[4],[(0,58),(1,58)]),
([v55,v5,v3,v2,v1,v4],[(v6,v2,v1),(v18,v0,v6),(v13,v0,v6),(v55,v18,v13)],[0,2,4],[(0,55),(0,59),(1,55),(1,59)]),
([v55,v5,v3,v2,v1,v13,v4],[(v6,v2,v1),(v18,v0,v6),(v13,v0,v6),(v55,v18,v13)],[0],[(0,60),(1,60)]),
([v5,v18,v40,v3,v2,v1,v4],[],[],[]),
([v19,v5,v18,v3,v2,v13,v4],[(v6,v1,v2),(v18,v0,v6),(v13,v0,v6),(v19,v1,v13)],[0],[(0,60),(0,61)]),
([v55,v5,v3,v2,v1,v6,v4],[(v6,v2,v1),(v18,v0,v6),(v13,v0,v6),(v55,v18,v13)],[0,2],[]),
([v19,v5,v18,v3,v2,v6,v4],[(v6,v1,v2),(v18,v0,v6),(v13,v0,v6),(v19,v1,v13)],[2],[(0,58)]),
([v5,v18,v3,v50,v2,v1,v4],[],[],[]),
([v5,v0,0xccccccf0ccccccf0,v3,v2,v1,v4],[(v6,v2,v1),(v18,v0,v6),(v15,v3,v6),(0xccccccf0ccccccf0,v15,v18)],[3,6,7],[]),
([v19,v11,v5,v3,v2,v6,v4],[],[],[]),
([0xf0f0fcc0f0f0fcc,v5,v0,v3,v2,v1,v4],[],[],[]),
([v5,v0,v44,v3,v1,v6,v4],[(v6,v2,v1),(v13,v0,v6),(v35,v2,v13),(v44,v35,v3)],[0],[]),
([v19,v35,v5,v0,v3,v6,v4],[(v6,v1,v2),(v13,v0,v6),(v19,v1,v13),(v35,v2,v13)],[0],[(0,36),(0,61)]),
([v11,v5,v79,v3,v2,v1,v4],[],[],[]),
([v11,v5,v3,v2,v72,v6,v4],[(v6,v1,v2),(v29,v0,v6),(v72,v29,v1),(v11,v0,v6)],[1,2],[]),
([v5,v0,v75,v3,v1,v6,v4],[(v6,v2,v1),(v29,v0,v6),(v73,v29,v2),(v75,v3,v73)],[0],[]),
([v5,v0,v40,v3,v2,v1,v4],[],[],[]),
([v11,v55,v5,v3,v2,v1,v4],[(v6,v2,v1),(v29,v0,v6),(v11,v0,v6),(v55,v29,v11)],[0,2,8],[(0,62)]),
([v29,v11,v5,v51,v3,v2,v1],[(v6,v2,v1),(v29,v0,v6),(v11,v0,v6),(v51,v11,v4)],[0],[(0,62)]),
([v5,v0,0xf0f0f0ccf0f0f0cc,v3,v2,v1,v4],[],[],[]),
([v29,v5,v34,v3,v2,v1,v4],[],[],[(0,14)]),
([v11,v5,v3,v50,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v30,v11,v3),(v50,v30,v0)],[4],[(0,63),(1,63)]),
([v30,v5,v0,v3,v2,v1,v41],[(v6,v2,v1),(v11,v0,v6),(v30,v11,v3),(v41,v11,v4)],[5],[]),
([v5,v53,v0,v3,v2,v1,v41],[],[],[]),
([v5,v0,v51,v3,v2,v1,v13],[],[],[]),
([v5,v0,v3,v2,0xffffc0f0ffffc0f0,v6,v4],[(v6,v1,v2),(v11,v0,v6),(v53,v11,v3),(0xffffc0f0ffffc0f0,v53,v1)],[0],[(0,64)]),
([v5,v53,v0,v16,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v53,v11,v3),(v16,v3,v6)],[4],[(0,64)]),
([v5,v0,v16,v3,v2,v1,v41],[(v6,v2,v1),(v11,v0,v6),(v41,v11,v4),(v16,v3,v6)],[5,7],[]),
([v15,v5,v0,v3,v2,v1,v41],[],[],[]),
([0x333333f0333333f0,v5,v0,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v15,v3,v6),(0x333333f0333333f0,v15,v11)],[3],[]),
([v0,0xeaeaeaaaeaeaeaaa,v16,v3,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6),(v80,v0,v16),(0xeaeaeaaaeaeaeaaa,v5,v80)],[1,5,8],[(0,65)]),
([v5,v0,v16,v3,v2,v1,0xffffffffc0c0c000],[(v6,v2,v1),(v16,v3,v6),(v80,v0,v16),(0xffffffffc0c0c000,v80,v4)],[6,7],[]),
([v5,v80,v3,v50,v2,v1,v4],[],[],[(0,65),(0,66)]),
([v5,v0,v3,v50,v2,v1,v58],[],[],[]),
([0xc0c0ccc0c0c0ccc,v30,v5,v3,v2,v1,v4],[],[],[(0,66)]),
([v5,v0,v16,v3,v2,v1,v95],[(v6,v2,v1),(v16,v3,v6),(v30,v0,v16),(v95,v30,v4)],[6,7],[]),
([v30,v5,v0,v3,v2,v1,v58],[],[],[(0,67)]),
([0xfccc0000fccc,v5,v0,v3,v2,v6,v4],[(v6,v1,v2),(v16,v3,v6),(v50,v0,v16),(0xfccc0000fccc,v50,v1)],[0,3],[(0,63)]),
([v5,v0,v16,v2,v27,v6,v4],[],[],[]),
([v47,v5,v0,v3,v1,v6,v4],[(v6,v2,v1),(v15,v3,v6),(v22,v15,v2),(v47,v0,v22)],[0,2],[]),
([v5,v0,v3,v22,v27,v6,v4],[(v6,v1,v2),(v15,v3,v6),(v27,v15,v1),(v22,v15,v2)],[0,3],[(0,53)])
]

set_option maxRecDepth 100000 in

def g6_L7 : Array W6Node := Array.mk [
([v5,v0,v3,v2,v56,v6,v4],[(v28,v0,v3),(v56,v28,v1),(v6,v1,v2)],[0,1,2,3,4,7],[(0,0),(1,1)]),
([v5,v0,v3,v2,v1,v52,v4],[(v28,v0,v3),(v49,v28,v2),(v52,v49,v1)],[0,1,2,3,4,6,7],[(0,2),(0,3),(1,3)]),
([v5,v0,v3,v2,v49,v1,v52,v4],[(v28,v0,v3),(v49,v28,v2),(v52,v49,v1)],[2,3],[(0,3),(0,4),(1,5)]),
([v63,v5,v0,v3,v2,v1,v4],[(v28,v0,v3),(v49,v28,v2),(v63,v49,v1)],[0,1,2,3,4,6,7],[(0,3)]),
([v63,v5,v0,v3,v2,v49,v1,v4],[(v28,v0,v3),(v49,v28,v2),(v63,v49,v1)],[0,1,2],[(0,1),(0,3)]),
([v5,v0,v3,v2,v1,v6,v52,v4],[(v28,v0,v3),(v6,v2,v1),(v52,v28,v6)],[0,1,3],[(0,2),(0,6),(1,6)]),
([v99,v5,v0,v3,v2,v1,v4],[(v28,v0,v3),(v6,v2,v1),(v99,v28,v6)],[0,1,2,3,4,6,7],[]),
([v99,v5,v0,v3,v2,v1,v6,v4],[(v28,v0,v3),(v6,v2,v1),(v99,v28,v6)],[0,1,2],[]),
([v11,v5,v28,v3,v2,v1,v4],[(v28,v0,v3),(v6,v2,v1),(v11,v0,v6)],[0,1,2,3,4,5,6,8],[(0,7)]),
([v11,v5,v28,v3,v2,v1,v6,v4],[(v28,v0,v3),(v6,v2,v1),(v11,v0,v6)],[0,1,6],[(0,0),(0,2),(1,0)]),
([v5,v0,v3,v2,v23,v12,v4],[(v8,v0,v3),(v23,v8,v1),(v12,v0,v1)],[2,3,4],[(0,10),(1,8),(1,9),(1,11)]),
([v5,v0,v3,v2,v25,v1,v12,v4],[(v8,v0,v3),(v25,v8,v2),(v12,v0,v1)],[2,3],[(0,10),(0,13),(1,12)]),
([v10,v5,v0,v3,v2,v23,v4],[(v8,v0,v3),(v23,v8,v1),(v10,v1,v23)],[3,4],[(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(1,8)]),
([v5,v0,v3,v2,v1,v31,v4],[(v8,v0,v3),(v25,v8,v2),(v31,v25,v1)],[0,1,2,3,4,6,7],[(0,10),(0,20),(0,21),(1,10),(1,21)]),
([v5,v0,v3,v2,v25,v1,v31,v4],[(v8,v0,v3),(v25,v8,v2),(v31,v25,v1)],[1,2,3],[(0,21),(1,18),(1,22)]),
([v54,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v54,v25,v1)],[0,2,3,4,6,7],[(0,11),(0,21),(0,23)]),
([v54,v5,v0,v3,v2,v25,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v54,v25,v1)],[2],[(0,21),(1,19)]),
([v10,v8,v5,v0,v3,v2,v23,v4],[(v8,v0,v3),(v23,v8,v1),(v10,v8,v1)],[2,3,4],[(0,24),(1,25)]),
([v5,v0,v3,v2,v25,v1,v23,v4],[(v8,v0,v3),(v25,v8,v2),(v23,v8,v1)],[0,2],[(0,22),(1,22)]),
([v10,v5,v0,v3,v2,v25,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v10,v8,v1)],[2],[(0,18),(0,26),(1,12)]),
([v8,v5,v0,v3,v2,v23,v12,v4],[(v8,v0,v3),(v23,v8,v1),(v12,v0,v1)],[2,3,4],[(1,25)]),
([v8,v5,v0,v3,v2,v1,v31,v4],[(v8,v0,v3),(v25,v8,v2),(v31,v25,v1)],[0,1,2,3],[(0,18),(0,27),(1,18)]),
([v54,v8,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v25,v8,v2),(v54,v25,v1)],[0,2,3],[(0,22),(1,19)]),
([v10,v5,v14,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0)],[2,3,4,5],[(0,14),(0,15),(0,28),(0,29),(0,30)]),
([v5,v0,v14,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0)],[0,2,3,4,5,6,7,8],[(0,31),(0,33),(1,32)]),
([v10,v5,v0,v14,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0)],[6,8],[(0,16),(0,34)]),
([v10,v5,v0,v24,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v24,v10,v3)],[2,4,6],[(0,17),(0,28),(0,34),(0,37),(1,8),(1,35),(1,36)]),
([v5,v0,v3,v2,v46,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v46,v10,v2)],[0,2,3,4,5,6,7],[(0,31),(1,38),(1,39)]),
([v10,v5,v0,v3,v2,v46,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v46,v10,v2)],[0],[(0,18),(0,40),(1,35),(1,39)]),
([v20,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2)],[0,2,3,4,6,7],[(0,39),(0,41),(0,42),(0,43),(1,39)]),
([v20,v10,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2)],[0],[(0,44),(0,45),(0,46),(1,36),(1,39)]),
([v10,v5,v0,v3,v2,v9,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v9,v0,v2)],[0,3],[(0,31),(0,47),(0,48),(1,38)]),
([v10,v5,v0,v3,v2,v6,v4],[(v8,v0,v3),(v10,v8,v1),(v6,v2,v1)],[0,2,3,4],[(0,18),(0,30),(0,33),(0,37),(0,40),(0,48),(0,49),(0,50)]),
([v8,v5,v14,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0)],[1,2,3,4,5,6],[(0,14),(0,24),(0,51),(0,52)]),
([v10,v8,v5,v14,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0)],[2,3,4,6],[(0,15),(0,24),(0,53)]),
([v8,v5,v0,v14,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v14,v10,v0)],[1,2,3,4,6,7],[(0,16)]),
([v8,v5,v0,v17,v2,v1,v4],[(v8,v0,v3),(v42,v8,v2),(v17,v42,v3)],[0,3,4,6],[(0,12),(0,25),(0,47),(0,54)]),
([v10,v8,v5,v0,v24,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v24,v10,v3)],[2,3,4],[(0,17),(0,53),(1,25)]),
([v8,v5,v0,v3,v2,v46,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v46,v10,v2)],[0,2,3],[(1,46)]),
([v20,v8,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v20,v10,v2)],[3],[(0,55),(0,56),(0,57)]),
([v10,v42,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1),(v42,v8,v2)],[0,2],[(0,46),(0,47),(0,58),(1,46),(1,47)]),
([v10,v8,v5,v0,v3,v2,v6,v4],[(v8,v0,v3),(v10,v8,v1),(v6,v2,v1)],[0,2,3],[(0,18),(0,52),(0,58),(0,59),(1,54)]),
([v8,v5,v0,v17,v2,v9,v1,v4],[(v8,v0,v3),(v9,v0,v2),(v17,v3,v9)],[0,3,4],[(0,9)]),
([v8,v5,v0,v3,v2,v12,v6,v4],[(v8,v0,v3),(v12,v0,v1),(v6,v1,v2)],[0,1,2,3],[(0,10),(0,60),(1,48),(1,54)]),
([v8,v5,v0,v3,v2,v1,v13,v4],[(v8,v0,v3),(v9,v0,v2),(v13,v9,v1)],[3],[(0,55),(0,57),(0,61)]),
([v19,v8,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v9,v0,v2),(v19,v9,v1)],[0,3],[(0,62)]),
([v30,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6)],[0,2,3,4,5,6,7],[(0,63),(0,64),(0,65),(0,66)]),
([v30,v8,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6)],[3,6,7],[(0,67),(0,68),(0,69)]),
([v30,v5,v0,v3,v2,v1,v6,v4],[(v8,v0,v3),(v6,v2,v1),(v30,v8,v6)],[0,2,6,7],[(0,27)]),
([v5,v0,v3,v2,v1,v6,v31,v4],[(v8,v0,v3),(v6,v2,v1),(v31,v8,v6)],[0,3],[(0,20),(0,67),(0,70),(0,71),(1,71)]),
([v20,v5,v0,v3,v2,v1,v6,v4],[(v8,v0,v3),(v6,v2,v1),(v20,v8,v6)],[0],[(0,72),(0,73),(0,74),(0,75),(1,72)]),
([v5,v0,v69,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v69,v8,v6)],[0,1,2,3,4,6,7],[(0,60),(1,60)]),
([v8,v5,v0,v69,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v69,v8,v6)],[0,2,3],[(0,59),(0,73),(1,59)]),
([v5,v0,v69,v3,v2,v1,v6,v4],[(v8,v0,v3),(v6,v2,v1),(v69,v8,v6)],[0,2],[(0,55)]),
([v8,v5,v18,v3,v2,v1,v6,v4],[(v8,v0,v3),(v6,v2,v1),(v18,v0,v6)],[0],[(0,20),(0,49),(0,61),(0,74),(1,49)]),
([v8,v11,v5,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v11,v0,v6)],[0,1,2,3,4,5,6],[(0,75),(0,76),(0,77)]),
([v8,v11,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v6,v2,v1),(v11,v0,v6)],[1,3,6,7],[(0,67),(0,69)]),
([v8,v11,v5,v3,v2,v1,v6,v4],[(v8,v0,v3),(v6,v2,v1),(v11,v0,v6)],[0,1,3,6],[(0,50),(0,70),(0,75),(1,50)]),
([v5,v0,v17,v3,v2,v1,v12,v4],[(v9,v0,v2),(v12,v0,v1),(v17,v3,v9)],[0,2,3],[(0,47),(0,79),(1,78)]),
([v5,v0,v3,v9,v12,v6,v4],[(v9,v0,v2),(v12,v0,v1),(v6,v2,v1)],[0,1,2,3,4,6],[(0,48),(0,79),(0,80),(1,48),(1,79)]),
([v19,v5,v0,v3,v2,v12,v4],[(v12,v0,v1),(v9,v0,v2),(v19,v1,v9)],[0,2,4],[(0,81),(1,82)]),
([v19,v5,v0,v3,v2,v9,v12,v4],[(v12,v0,v1),(v9,v0,v2),(v19,v1,v9)],[0,1,2,4],[(0,82)]),
([v5,v0,v3,v2,v89,v1,v4],[(v12,v0,v1),(v24,v3,v12),(v89,v24,v2)],[0,2,3,4,6,7],[(0,83),(1,84)]),
([v5,v0,v17,v3,v2,v1,v65,v4],[(v9,v0,v2),(v17,v3,v9),(v65,v17,v1)],[2,3],[(0,36),(0,84),(0,85)]),
([v39,v5,v0,v3,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v39,v17,v1)],[0,1,2,3,4,6,7],[(0,84),(0,86)]),
([v39,v5,v0,v17,v3,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v39,v17,v1)],[2],[(0,84),(0,88),(1,87)]),
([v7,v5,v0,v17,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v7,v3,v1)],[0,2,3,4,6],[(0,36),(0,47),(0,85),(0,89),(0,90)]),
([v5,v0,v17,v3,v1,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v6,v2,v1)],[0,2,3,4,6],[(0,54),(0,79),(0,88),(0,90),(0,91),(0,92),(0,93),(0,95),(1,37),(1,94)]),
([v10,v5,v0,v24,v2,v1,v12,v4],[(v12,v0,v1),(v24,v3,v12),(v10,v24,v3)],[2,3,4],[(0,96),(1,9)]),
([v5,v0,v3,v2,v9,v1,v65,v4],[(v9,v0,v2),(v17,v3,v9),(v65,v17,v1)],[0,2,3],[(0,97)]),
([v39,v5,v0,v3,v2,v9,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v39,v17,v1)],[0],[(0,99),(1,98)]),
([v7,v5,v0,v17,v2,v9,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v7,v3,v1)],[0,2,3],[(0,36),(0,100),(0,101)]),
([v5,v0,v17,v3,v9,v1,v6,v4],[(v9,v0,v2),(v17,v3,v9),(v6,v2,v1)],[1,2,3],[(0,99),(0,101),(0,102),(1,37)]),
([v5,v0,v17,v3,v2,v1,v13,v4],[(v9,v0,v2),(v17,v3,v9),(v13,v9,v1)],[3],[(0,36),(0,103),(1,104)]),
([v19,v5,v0,v17,v3,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9),(v19,v9,v1)],[0,2,3],[(0,97),(0,102),(1,87)]),
([v5,v14,v3,v2,v1,v12,v4],[(v12,v0,v1),(v10,v3,v12),(v14,v10,v0)],[1,2,3,4,5],[(0,96),(0,105),(0,106)]),
([v10,v5,v14,v3,v2,v1,v12,v4],[(v12,v0,v1),(v10,v3,v12),(v14,v10,v0)],[2,3,4],[(0,28),(0,96),(0,107)]),
([v5,v0,v14,v3,v2,v1,v12,v4],[(v12,v0,v1),(v10,v3,v12),(v14,v10,v0)],[1,2,3,4,6,7],[(0,34)]),
([v5,v0,v3,v2,v46,v1,v12,v4],[(v12,v0,v1),(v10,v3,v12),(v46,v10,v2)],[0,2,3],[(0,10),(0,108),(1,35),(1,109)]),
([v20,v5,v0,v3,v2,v9,v1,v4],[(v9,v0,v2),(v42,v3,v9),(v20,v42,v1)],[0,3],[(0,31),(0,36),(0,110),(1,38)]),
([v10,v5,v0,v3,v2,v23,v12,v4],[(v12,v0,v1),(v10,v3,v12),(v23,v10,v1)],[2,3,4],[(0,17),(0,107),(1,9)]),
([v10,v5,v0,v3,v2,v12,v6,v4],[(v12,v0,v1),(v10,v3,v12),(v6,v2,v1)],[0,1,3],[(0,10),(0,37),(0,106),(0,108),(0,111)]),
([v10,v5,v0,v3,v2,v1,v13,v4],[(v12,v0,v1),(v10,v3,v12),(v13,v2,v12)],[0,3],[(0,45),(0,112),(1,109)]),
([v10,v35,v5,v0,v3,v2,v1,v4],[(v12,v0,v1),(v10,v3,v12),(v35,v2,v12)],[0],[(0,111),(1,113)]),
([v5,v0,v14,v3,v2,v9,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v14,v7,v0)],[0,3,6,7],[(0,67),(0,89),(0,115),(1,114)]),
([v39,v7,v5,v0,v3,v2,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v39,v7,v9)],[3],[(0,67),(0,116),(0,117)]),
([v5,v0,v3,v2,v32,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9)],[0,2,3,4,5,6,7],[(0,118),(0,119),(0,121),(1,120)]),
([v7,v5,v0,v3,v2,v32,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9)],[2,3,6,7],[(0,122),(1,98)]),
([v5,v0,v3,v2,v9,v32,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v32,v7,v9)],[0,2,3,6,7],[(0,67),(0,100),(0,123),(1,114)]),
([v20,v7,v5,v0,v3,v2,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v20,v7,v9)],[3],[(0,124),(0,125),(0,126)]),
([v5,v0,v3,v2,v74,v1,v4],[(v12,v0,v1),(v21,v3,v2),(v74,v21,v12)],[0,1,2,3,4,6,7],[(0,127)]),
([v7,v5,v0,v3,v2,v96,v1,v4],[(v9,v0,v2),(v7,v3,v1),(v96,v7,v9)],[2,3],[(0,31),(0,128)]),
([v5,v0,v3,v2,v74,v1,v12,v4],[(v12,v0,v1),(v21,v3,v2),(v74,v21,v12)],[2],[(0,129),(1,124)]),
([v7,v5,v0,v3,v9,v6,v4],[(v9,v0,v2),(v7,v3,v1),(v6,v2,v1)],[0,2,3,4],[(0,48),(0,90),(0,99),(0,101),(0,115),(0,122),(0,128),(0,130),(0,131),(0,132),(1,127),(1,129)]),
([v5,v18,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v18,v0,v6)],[0,1,2,3,4,6,8],[(0,49),(0,134),(0,135),(0,136),(1,91),(1,130),(1,133),(1,137)]),
([v11,v5,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v11,v0,v6)],[0,1,2,4],[(0,50),(0,138),(0,139),(1,92),(1,131),(1,140)]),
([v11,v5,v0,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v11,v0,v6)],[0,1,2,6,8],[(0,80)]),
([v5,v0,v16,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v16,v3,v6)],[0,2,3,6,8],[(0,135),(1,132)]),
([v15,v5,v0,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2),(v15,v3,v6)],[0,1,3],[(0,136),(0,141),(0,142),(0,143),(1,95)]),
([v19,v5,v0,v3,v9,v6,v4],[(v9,v0,v2),(v6,v2,v1),(v19,v1,v9)],[0,2,4],[(0,99),(0,102),(0,137),(0,140),(1,111),(1,144)]),
([v11,v5,v0,v3,v2,v1,v4],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[0,1,2,3,4,6,7,8],[(0,55),(0,61),(0,145),(0,146)]),
([v11,v5,v3,v2,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[0,2,4],[(0,75),(0,147),(0,148),(0,149),(0,150),(0,151),(1,150),(1,151)]),
([v11,v5,v0,v3,v2,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[6,8],[(0,152),(1,152)]),
([v5,v0,v40,v3,v2,v1,v4],[(v9,v0,v2),(v13,v9,v1),(v40,v3,v13)],[0,2,3,4,6,7],[(0,43),(0,55),(0,57)]),
([v5,v0,v40,v3,v2,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v40,v3,v13)],[3],[(0,43),(0,149)]),
([v20,v5,v0,v3,v2,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v20,v3,v13)],[3],[(0,43),(0,75),(0,109),(0,153),(1,109)]),
([v19,v5,v0,v3,v2,v13,v4],[(v12,v0,v1),(v13,v12,v2),(v19,v1,v13)],[0,4],[(0,81),(0,150),(0,151),(0,152),(0,154)]),
([v11,v5,v3,v2,v9,v1,v4],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[0,1,2,4],[(0,103),(0,150),(0,155),(0,156),(0,157),(1,112)]),
([v11,v5,v0,v3,v2,v9,v1,v4],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[0,1,2,4,6,7],[(0,152)]),
([v11,v5,v3,v2,v9,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v11,v0,v13)],[0,2,4],[(0,151),(0,157),(1,158)]),
([v5,v0,v40,v3,v2,v9,v1,v4],[(v9,v0,v2),(v13,v9,v1),(v40,v3,v13)],[0,2,3],[(1,45)]),
([v19,v5,v0,v3,v2,v12,v13,v4],[(v12,v0,v1),(v13,v12,v2),(v19,v1,v13)],[0,2,4],[(0,154),(0,158),(1,82)]),
([v19,v5,v0,v3,v2,v9,v13,v4],[(v9,v0,v2),(v13,v9,v1),(v19,v9,v1)],[0,2,4],[(0,82),(0,157)]),
([v39,v19,v5,v0,v3,v2,v1,v4],[(v9,v0,v2),(v19,v9,v1),(v39,v19,v3)],[3],[(0,86),(0,97)]),
([v5,v0,v44,v3,v2,v1,v4],[(v12,v0,v1),(v35,v12,v2),(v44,v35,v3)],[0,1,2,3,4,6,7],[(0,159),(1,86)]),
([v19,v5,v0,v84,v3,v2,v1,v4],[(v9,v0,v2),(v19,v9,v1),(v84,v19,v3)],[3],[(0,86)]),
([v5,v0,v44,v3,v2,v1,v12,v4],[(v12,v0,v1),(v35,v12,v2),(v44,v35,v3)],[0,2,3],[(0,87),(0,144),(0,160),(0,161)]),
([v5,v0,v3,v2,v93,v1,v4],[(v62,v0,v1),(v71,v62,v3),(v93,v71,v2)],[0,1,2,3,4,6,7],[(1,162)]),
([v5,v0,v61,v3,v2,v1,v70,v4],[(v37,v0,v2),(v61,v37,v3),(v70,v61,v1)],[2],[(0,162)]),
([v48,v5,v0,v3,v2,v1,v4],[(v37,v0,v2),(v61,v37,v3),(v48,v61,v1)],[0,1,2,3,4,6,7],[(0,162),(0,163)]),
([v48,v5,v0,v61,v3,v2,v1,v4],[(v37,v0,v2),(v61,v37,v3),(v48,v61,v1)],[2],[(0,162),(1,164)]),
([v5,v0,v75,v3,v2,v1,v4],[(v62,v0,v1),(v73,v62,v2),(v75,v3,v73)],[0,1,2,3,4,6,7],[(1,163)]),
([v5,v0,v75,v3,v2,v73,v1,v4],[(v62,v0,v1),(v73,v62,v2),(v75,v3,v73)],[3],[(1,163)]),
([v48,v5,v0,v3,v2,v1,v72,v4],[(v37,v0,v2),(v72,v37,v1),(v48,v3,v72)],[3],[(0,163),(0,165)]),
([v100,v5,v0,v3,v2,v1,v4],[(v37,v0,v2),(v7,v3,v1),(v100,v37,v7)],[0,1,2,3,4,6,7],[]),
([v7,v100,v5,v0,v3,v2,v1,v4],[(v37,v0,v2),(v7,v3,v1),(v100,v37,v7)],[1,3],[]),
([v48,v7,v5,v0,v3,v2,v1,v4],[(v37,v0,v2),(v7,v3,v1),(v48,v37,v7)],[1,3],[(0,166),(0,167)]),
([v5,v0,v3,v2,v1,v101,v4],[(v38,v0,v4),(v6,v2,v1),(v101,v6,v38)],[0,1,2,3,4,5,6,8],[]),
([v5,v0,v3,v2,v1,v101,v6,v4],[(v38,v0,v4),(v6,v2,v1),(v101,v6,v38)],[0,7],[]),
([v66,v5,v0,v3,v2,v1,v4],[(v38,v0,v4),(v6,v2,v1),(v66,v6,v38)],[0,1,2,3,4,5,6,8],[(0,168),(1,168)]),
([v66,v5,v0,v3,v2,v1,v6,v4],[(v38,v0,v4),(v6,v2,v1),(v66,v6,v38)],[0,7],[(0,169),(1,169)]),
([v5,v0,v3,v2,v90,v1,v4],[(v38,v0,v4),(v67,v1,v38),(v90,v67,v2)],[0,1,2,3,4,5,6,8],[(1,168)]),
([v67,v5,v0,v3,v2,v90,v1,v4],[(v38,v0,v4),(v67,v1,v38),(v90,v67,v2)],[0],[(1,168)]),
([v66,v67,v5,v0,v3,v2,v1,v4],[(v38,v0,v4),(v67,v1,v38),(v66,v67,v2)],[0],[(0,170),(1,168)]),
([v5,v0,v3,v2,v78,v6,v4],[(v33,v0,v4),(v78,v33,v1),(v6,v1,v2)],[0,1,2,4,5,6],[(1,171)]),
([v5,v0,v3,v2,v1,v68,v4],[(v33,v0,v4),(v59,v33,v2),(v68,v59,v1)],[0,1,2,3,4,5,6],[(0,172),(1,172)]),
([v5,v0,v3,v2,v59,v1,v68,v4],[(v33,v0,v4),(v59,v33,v2),(v68,v59,v1)],[2],[(0,172),(1,173)]),
([v64,v5,v0,v3,v2,v1,v4],[(v33,v0,v4),(v59,v33,v2),(v64,v59,v1)],[0,1,2,3,4,5,6],[(0,172)]),
([v64,v5,v0,v3,v2,v59,v1,v4],[(v33,v0,v4),(v59,v33,v2),(v64,v59,v1)],[0,1,2],[(0,171),(0,172)]),
([v5,v0,v3,v2,v1,v6,v68,v4],[(v33,v0,v4),(v6,v2,v1),(v68,v33,v6)],[0,1],[(0,174),(1,174)]),
([v5,v0,v3,v2,v1,v102,v4],[(v33,v0,v4),(v6,v2,v1),(v102,v33,v6)],[0,1,2,3,4,5,6,7],[]),
([v5,v0,v3,v2,v1,v102,v6,v4],[(v33,v0,v4),(v6,v2,v1),(v102,v33,v6)],[0,1,2,6,7],[]),
([v10,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v10,v26,v7)],[0,1,2,3,4,6,7],[(0,67),(0,175),(0,176),(0,177)]),
([v10,v7,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v10,v26,v7)],[1,2,3,4],[(0,175)]),
([v7,v5,v0,v71,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v71,v26,v3)],[1,2,3,4],[(0,178),(0,179)]),
([v7,v5,v0,v3,v2,v86,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v86,v26,v2)],[0,3],[(0,67),(0,181),(0,182),(1,180)]),
([v7,v5,v0,v3,v2,v56,v4],[(v7,v3,v1),(v26,v7,v0),(v56,v26,v1)],[1,2,3,4,5],[(0,182),(0,183),(0,184),(0,185),(0,186)]),
([v26,v5,v14,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v14,v7,v0)],[1,2,3,4,5,8],[(0,189),(1,187),(1,188)]),
([v26,v7,v5,v14,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v14,v7,v0)],[1,3],[(0,175),(0,178),(0,183),(0,190)]),
([v26,v5,v0,v3,v2,v22,v1,v4],[],[],[(0,184),(0,191)]),
([v15,v26,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0),(v15,v7,v2)],[0,1],[(0,67),(0,185),(0,192),(1,180)]),
([v26,v7,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v26,v7,v0),(v6,v2,v1)],[0,3],[(0,177),(0,179),(0,181),(0,182),(0,189)]),
([v5,v0,v14,v3,v2,v32,v1,v4],[(v7,v3,v1),(v14,v7,v0),(v32,v14,v2)],[0,2,3,5,6,8],[(0,193),(0,194),(0,195),(1,120)]),
([v60,v5,v0,v3,v2,v1,v4],[(v21,v3,v2),(v57,v21,v0),(v60,v57,v1)],[0,2,3,4,6,7],[(0,67),(0,114),(0,120)]),
([v60,v5,v0,v57,v3,v2,v1,v4],[(v21,v3,v2),(v57,v21,v0),(v60,v57,v1)],[2,5],[(0,120),(1,196)]),
([v43,v5,v0,v14,v3,v2,v1],[(v7,v3,v1),(v14,v7,v0),(v43,v14,v4)],[0,2,3,4,6,8],[(0,29),(0,194),(0,196),(0,197)]),
([v5,v0,v14,v3,v2,v6,v4],[(v7,v3,v1),(v14,v7,v0),(v6,v2,v1)],[0,2,3,4,5],[(0,30),(0,115),(0,177),(0,195),(0,197),(0,198)]),
([v10,v7,v5,v14,v3,v2,v1,v4],[(v7,v3,v1),(v14,v7,v0),(v10,v7,v0)],[1,3,4],[(0,199),(0,200)]),
([v5,v0,v14,v3,v2,v22,v1,v4],[(v7,v3,v1),(v14,v7,v0),(v22,v7,v2)],[0,1,3,6],[(0,193),(0,202),(0,203),(1,201)]),
([v15,v5,v0,v14,v3,v2,v1,v4],[(v7,v3,v1),(v14,v7,v0),(v15,v7,v2)],[6],[(0,204),(0,205)]),
([v60,v21,v5,v0,v3,v2,v1,v4],[(v21,v3,v2),(v57,v21,v0),(v60,v57,v1)],[1,2,3],[(0,201)]),
([v43,v7,v5,v0,v3,v2,v1],[(v7,v3,v1),(v14,v7,v0),(v43,v14,v4)],[0,1,2,3,4,6,7,8],[(0,202),(0,205),(0,206)]),
([v43,v7,v5,v0,v14,v3,v2,v1],[(v7,v3,v1),(v14,v7,v0),(v43,v14,v4)],[1,3,6,8],[(0,29)]),
([v7,v5,v0,v14,v3,v2,v6,v4],[(v7,v3,v1),(v14,v7,v0),(v6,v2,v1)],[0,3,6],[(0,30),(0,122),(0,189),(0,203),(0,206)]),
([v7,v5,v0,v14,v3,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v14,v10,v0)],[1,3,4,6,7],[]),
([v7,v5,v0,v24,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v24,v10,v3)],[2,3,4,6],[(0,34),(0,199),(0,207),(0,210),(1,208),(1,209)]),
([v10,v7,v5,v0,v24,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v24,v10,v3)],[3,4],[(0,28),(0,199),(0,211),(0,212)]),
([v7,v5,v0,v3,v2,v46,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v46,v10,v2)],[0,1,3],[(0,214),(0,215),(1,213)]),
([v7,v5,v0,v3,v2,v23,v4],[(v7,v3,v1),(v10,v7,v0),(v23,v10,v1)],[2,3,4],[(0,14),(0,16),(0,200),(0,215),(0,216),(0,217)]),
([v10,v7,v5,v0,v3,v2,v23,v4],[(v7,v3,v1),(v10,v7,v0),(v23,v10,v1)],[3,4],[(0,15),(0,200),(0,211),(0,218)]),
([v10,v5,v36,v3,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v36,v7,v0)],[1,2,3,4],[(0,212),(0,218),(0,219),(0,220),(1,187)]),
([v10,v7,v5,v36,v3,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v36,v7,v0)],[1,2,3],[(0,175),(0,190),(0,207),(0,216)]),
([v10,v5,v0,v3,v2,v22,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v22,v7,v2)],[3],[(0,221),(0,222),(1,208)]),
([v15,v10,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0),(v15,v7,v2)],[0,1],[(0,44),(1,209),(1,213)]),
([v10,v7,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v10,v7,v0),(v6,v2,v1)],[0,3],[(0,30),(0,210),(0,214),(0,215),(0,220),(0,222)]),
([v5,v76,v0,v3,v2,v1,v27,v4],[(v21,v3,v2),(v76,v21,v0),(v27,v21,v1)],[1,2],[(0,223),(1,31),(1,224)]),
([v15,v5,v76,v0,v3,v2,v1,v4],[],[],[(0,225)]),
([v7,v5,v0,v3,v2,v87,v1,v4],[(v7,v3,v1),(v36,v7,v0),(v87,v36,v2)],[0,3],[(0,31),(0,226),(0,227),(1,223)]),
([v7,v5,v36,v0,v3,v2,v6,v4],[(v7,v3,v1),(v36,v7,v0),(v6,v2,v1)],[0,3],[(0,33),(0,220),(0,227)]),
([v5,0xcc00ccc0cc00ccc0,v0,v3,v2,v22,v1,v4],[(v7,v3,v1),(v22,v7,v2),(0xcc00ccc0cc00ccc0,v0,v22)],[0,1],[(0,118),(0,228),(0,229)]),
([v5,v0,v3,v2,v22,v32,v1,v4],[(v7,v3,v1),(v22,v7,v2),(v32,v0,v22)],[1,2,3,6],[(0,119),(0,229),(0,230),(1,201)]),
([0xcc0c0000cc0c,v5,v0,v3,v2,v1,v27,v4],[(v21,v3,v2),(v27,v21,v1),(0xcc0c0000cc0c,v0,v27)],[1],[(0,223),(0,231),(1,31)]),
([v47,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v22,v7,v2),(v47,v0,v22)],[0,2,3,4,6,7],[(0,31),(0,119)]),
([v47,v5,v0,v3,v2,v22,v1,v4],[(v7,v3,v1),(v22,v7,v2),(v47,v0,v22)],[1],[(0,119),(1,231)]),
([v15,v5,v0,v3,v2,v27,v4],[(v21,v3,v2),(v27,v21,v1),(v15,v1,v27)],[0,3,4,7],[(0,232),(0,233),(0,234),(0,235)]),
([v15,v7,v5,v0,v3,v22,v1,v4],[(v7,v3,v1),(v22,v7,v2),(v15,v7,v2)],[0,3,4],[(0,236),(0,237)]),
([v7,v47,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v22,v7,v2),(v47,v0,v22)],[0,1,3],[(0,193),(0,224),(0,238),(0,239)]),
([v7,v5,v0,v3,v22,v6,v4],[(v7,v3,v1),(v22,v7,v2),(v6,v2,v1)],[0,2,3,4],[(0,122),(0,203),(0,222),(0,239),(0,240)]),
([v92,v15,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v92,v15,v0)],[1],[(0,67),(0,180),(0,241),(0,242),(1,180)]),
([v5,v0,v34,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v34,v15,v0)],[0,2,3,4,5,6,7],[(0,41),(0,67),(0,243)]),
([v15,v5,v0,v34,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v34,v15,v0)],[1,6],[(0,41),(0,242),(0,244)]),
([v20,v15,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v20,v15,v0)],[1],[(0,41),(0,213),(0,245),(0,246),(1,213)]),
([v15,v5,0xcccccc0ccccccc0c,v0,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(0xcccccc0ccccccc0c,v15,v0)],[1],[(0,42),(0,246)]),
([v15,v5,v0,v16,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v16,v15,v3)],[0,2,4,5],[(0,232),(0,233),(0,247),(1,233)]),
([v7,v5,v0,v34,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v34,v15,v0)],[0,1,3,6,7],[(0,44),(0,192)]),
([v7,v5,v0,v16,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v16,v15,v3)],[0,3,4,5],[(0,236),(0,248)]),
([v15,v7,v5,v0,v16,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2),(v16,v15,v3)],[0,3,4],[(0,236),(0,249),(1,233)]),
([v7,v5,v0,v3,v2,v27,v4],[(v7,v3,v1),(v15,v7,v2),(v27,v15,v1)],[0,2,3,4,5],[(0,234),(0,237)]),
([v15,v7,v5,v0,v3,v2,v27,v4],[(v7,v3,v1),(v15,v7,v2),(v27,v15,v1)],[0,3,4],[(0,235),(0,237),(0,249)]),
([v7,v5,v18,v0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v18,v0,v6)],[0,2,3],[(0,49),(0,130),(0,250),(0,251)]),
([v7,v5,v0,v3,v2,v6,v13,v4],[(v7,v3,v1),(v6,v2,v1),(v13,v0,v6)],[0,3],[(0,251),(0,252),(0,253),(0,254)]),
([v29,v7,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v29,v0,v6)],[0,3],[(0,255),(0,256),(0,257),(0,258)]),
([v7,v11,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v11,v0,v6)],[0,2,3,6],[(0,50),(0,131),(0,258),(0,259)]),
([v7,v5,v0,v16,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1),(v16,v3,v6)],[0,2,3,4,5],[(0,132),(0,240),(0,260)]),
([v88,v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v18,v0,v6),(v88,v18,v3)],[0,2,3],[(0,55),(0,261),(0,262),(1,261)]),
([v11,v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v18,v0,v6),(v11,v18,v6)],[0,1,2,4,6,7],[(0,134),(0,263),(1,134)]),
([v5,v18,v3,v2,v1,v13,v4],[(v6,v2,v1),(v18,v0,v6),(v13,v0,v6)],[0,1,2,4],[(0,74),(0,251),(0,264),(0,265),(0,266),(0,267),(1,251),(1,267)]),
([v5,v18,v3,v2,v1,v6,v13,v4],[(v6,v2,v1),(v18,v0,v6),(v13,v0,v6)],[0,1,2],[(0,263),(0,268),(0,269),(1,269)]),
([v5,v18,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v18,v0,v6),(v16,v3,v6)],[0,1,2,3,6,8],[(0,55),(0,135),(0,262),(0,270),(1,135)]),
([v15,v5,v18,v0,v3,v2,v1,v4],[(v6,v2,v1),(v18,v0,v6),(v15,v3,v6)],[0,1,2],[(0,74),(0,136),(0,271),(1,136)]),
([v11,v5,v3,v2,v1,v6,v13,v4],[(v6,v2,v1),(v13,v0,v6),(v11,v0,v6)],[0,1,4],[(0,272),(1,272)]),
([v5,v0,v16,v3,v2,v1,v13,v4],[(v6,v2,v1),(v13,v0,v6),(v16,v3,v6)],[6,8],[(0,273)]),
([v15,v5,v0,v3,v2,v1,v13,v4],[(v6,v2,v1),(v13,v0,v6),(v15,v3,v6)],[1,3],[(0,153),(0,245)]),
([v5,v0,v40,v3,v2,v1,v6,v4],[(v6,v2,v1),(v13,v0,v6),(v40,v3,v13)],[0,1,3],[(0,149),(0,245),(0,252),(0,253),(0,266),(1,252),(1,253)]),
([v19,v5,v0,v3,v2,v6,v4],[(v6,v1,v2),(v13,v0,v6),(v19,v1,v13)],[0,2,4],[(0,150),(0,152),(0,252),(0,269),(0,272),(1,254),(1,274)]),
([v19,v5,v0,v3,v2,v6,v13,v4],[(v6,v1,v2),(v13,v0,v6),(v19,v1,v13)],[0,4],[(0,151),(0,267),(0,272),(0,275)]),
([v5,v0,v79,v3,v2,v1,v6,v4],[(v6,v2,v1),(v29,v0,v6),(v79,v29,v3)],[0,1,3],[(0,67),(0,241),(0,255),(0,256),(0,276),(1,255),(1,256)]),
([v5,v0,v3,v2,v72,v6,v4],[(v6,v1,v2),(v29,v0,v6),(v72,v29,v1)],[0,1,2,4],[(0,255),(0,277),(1,257),(1,278)]),
([v5,v0,v3,v2,v1,v13,v4],[(v6,v2,v1),(v29,v0,v6),(v13,v29,v6)],[0,1,2,3,4,6,7],[(0,67),(0,263),(0,279)]),
([v5,v0,v3,v2,v1,v6,v13,v4],[(v6,v2,v1),(v29,v0,v6),(v13,v29,v6)],[0,1,2,4],[(0,263)]),
([v29,v11,v5,v3,v2,v1,v4],[(v6,v2,v1),(v29,v0,v6),(v11,v0,v6)],[0,1,2,4,8],[(0,258),(0,264),(0,276),(0,280),(0,281),(1,258)]),
([v29,v11,v5,v3,v2,v1,v6,v4],[(v6,v2,v1),(v29,v0,v6),(v11,v0,v6)],[0,1,2],[(0,263),(0,268),(0,277),(1,277)]),
([v29,v5,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v29,v0,v6),(v16,v3,v6)],[6,8],[(0,282)]),
([v29,v15,v5,v0,v3,v2,v1,v4],[(v6,v2,v1),(v29,v0,v6),(v15,v3,v6)],[1,3],[(0,67),(0,241),(0,283)]),
([v30,v11,v5,v0,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v30,v11,v3)],[3,5,6,8],[(0,65),(0,284),(0,285)]),
([v5,v53,v0,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v53,v11,v3)],[0,2,3,4,6,7],[(0,65),(0,67),(0,69)]),
([v11,v5,v53,v0,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v53,v11,v3)],[3,5],[(0,65),(0,75),(0,76),(0,286)]),
([v11,v5,v0,v3,v2,v1,v41],[(v6,v2,v1),(v11,v0,v6),(v41,v11,v4)],[0,2,3,4,6,8],[(0,77),(0,147),(0,285),(0,286)]),
([v11,v5,v0,v51,v3,v2,v1],[(v6,v2,v1),(v11,v0,v6),(v51,v11,v4)],[0,2,3,4,5,6,7,8],[(0,148),(0,287)]),
([v5,v53,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v11,v0,v6),(v53,v11,v3)],[0,1,2,3],[(0,288),(0,289),(1,288)]),
([v5,v0,v3,v2,v1,v6,v41],[(v6,v2,v1),(v11,v0,v6),(v41,v11,v4)],[0,1,2,3,4,6,7,8],[(0,259),(0,290),(0,291),(1,259)]),
([v11,v5,v0,v3,v2,v1,v6,v41],[(v6,v2,v1),(v11,v0,v6),(v41,v11,v4)],[0,1,2,6,8],[(0,138),(0,147),(1,138)]),
([v11,v5,v0,v51,v3,v2,v1,v6],[(v6,v2,v1),(v11,v0,v6),(v51,v11,v4)],[0,1,2,7],[(0,139),(0,148),(0,281),(1,139)]),
([v11,v5,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v16,v3,v6)],[1,3,6,8],[(0,284),(0,289),(0,290)]),
([v15,v11,v5,v0,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6),(v15,v3,v6)],[1,6],[(0,75),(0,291),(0,292)]),
([v5,v80,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6),(v80,v0,v16)],[0,1,2,4,5,6,8],[(0,55),(0,262),(0,293),(0,294),(0,295)]),
([v5,v0,v3,v50,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6),(v50,v0,v16)],[0,2,3,4,6,7],[(0,55),(0,63)]),
([v5,v0,v16,v3,v50,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6),(v50,v0,v16)],[1,5],[(0,63),(0,295),(0,296)]),
([0xc0c0ccc0c0c0ccc,v5,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6),(0xc0c0ccc0c0c0ccc,v0,v16)],[1,5,8],[(0,64),(0,297)]),
([v30,v5,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6),(v30,v0,v16)],[1,5,6],[(0,63),(0,289),(0,297),(0,298),(0,299)]),
([v5,v0,v16,v3,v2,v1,v58],[(v6,v2,v1),(v16,v3,v6),(v58,v16,v4)],[0,2,3,4,6,8],[(0,247),(0,296),(0,299)]),
([v5,v0,v3,v50,v2,v1,v6,v4],[(v6,v2,v1),(v16,v3,v6),(v50,v0,v16)],[0,1,3],[(0,270),(0,284),(0,300),(1,300)]),
([v15,v5,v0,v16,v2,v1,v6,v4],[(v6,v2,v1),(v16,v3,v6),(v15,v16,v3)],[0,3,4],[(0,301),(1,301)]),
([v5,v0,v3,v2,v1,v6,v58],[(v6,v2,v1),(v16,v3,v6),(v58,v16,v4)],[0,2,3,4,6,7,8],[]),
([v5,v0,v16,v3,v2,v1,v6,v58],[(v6,v2,v1),(v16,v3,v6),(v58,v16,v4)],[0,2,3,6],[(0,247),(0,260),(1,260)]),
([v5,v0,v34,v3,v2,v1,v6,v4],[(v6,v2,v1),(v15,v3,v6),(v34,v15,v0)],[0,1,2,3,6,7],[(0,141),(0,143),(0,153),(0,283),(1,141),(1,143)]),
([v5,v0,v3,v2,v27,v6,v4],[(v6,v1,v2),(v15,v3,v6),(v27,v15,v1)],[0,2,3,4,5],[(0,143),(0,232),(0,301),(1,142),(1,302)]),
([v15,v5,v0,v3,v2,v27,v6,v4],[(v6,v1,v2),(v15,v3,v6),(v27,v15,v1)],[0,3,4],[(0,233),(0,301),(0,303)]),
([0xffff0000ff00,v5,v0,v3,v2,v6,v4],[(v6,v1,v2),(v103,v6,v4),(0xffff0000ff00,v1,v103)],[0,2,3,4,5,6,7,8],[])
]

def g6_L8 : Array W6Node := Array.mk [
([v5,v0,v3,v2,v49,v1,v4],[(v28,v0,v3),(v49,v28,v2)],[0,1,2,3,4,5,6,7],[(0,1),(0,2),(0,3),(0,4),(1,0)]),
([v5,v28,v0,v3,v2,v1,v6,v4],[(v28,v0,v3),(v6,v2,v1)],[0,1,2,3,4,6,7],[(0,0),(0,1),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)]),
([v5,v0,v3,v2,v25,v1,v4],[(v8,v0,v3),(v25,v8,v2)],[0,1,2,3,4,5,6,7],[(0,11),(0,13),(0,14),(0,15),(0,16),(1,10),(1,12)]),
([v8,v5,v0,v3,v2,v25,v1,v4],[(v8,v0,v3),(v25,v8,v2)],[0,1,2,3,4,5,6,7],[(0,18),(0,19),(0,21),(0,22),(1,12),(1,17),(1,20)]),
([v10,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1)],[0,1,2,3,4,5,6,7],[(0,12),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32)]),
([v10,v8,v5,v0,v3,v2,v1,v4],[(v8,v0,v3),(v10,v8,v1)],[0,1,2,3,4,5,6,7],[(0,12),(0,17),(0,19),(0,33),(0,34),(0,35),(0,37),(0,38),(0,39),(0,40),(0,41),(1,36)]),
([v8,v5,v0,v3,v2,v9,v1,v4],[(v8,v0,v3),(v9,v0,v2)],[0,1,2,3,4,6,7],[(0,31),(0,36),(0,42),(0,44),(0,45),(1,10),(1,11),(1,20),(1,43)]),
([v8,v5,v0,v3,v2,v1,v6,v4],[(v8,v0,v3),(v6,v2,v1)],[0,1,2,3,4,6,7],[(0,13),(0,21),(0,29),(0,32),(0,39),(0,41),(0,43),(0,44),(0,46),(0,47),(0,48),(0,49),(0,50),(0,51),(0,52),(0,53),(0,54),(0,55),(0,56),(0,57),(1,32),(1,41),(1,43)]),
([v5,v0,v3,v2,v9,v1,v12,v4],[(v9,v0,v2),(v12,v0,v1)],[0,1,2,3,4,6,7],[(0,31),(0,58),(0,59),(0,60),(0,61),(1,31),(1,58),(1,60),(1,61)]),
([v5,v0,v17,v3,v2,v1,v4],[(v9,v0,v2),(v17,v3,v9)],[0,1,2,3,4,5,6,7],[(0,36),(0,58),(0,63),(0,64),(0,65),(0,66),(0,67),(1,26),(1,62)]),
([v5,v0,v17,v3,v2,v9,v1,v4],[(v9,v0,v2),(v17,v3,v9)],[0,1,2,3,4,5,6,7],[(0,42),(0,69),(0,70),(0,71),(0,72),(0,73),(0,74),(1,26),(1,68)]),
([v10,v5,v0,v3,v2,v1,v12,v4],[(v12,v0,v1),(v10,v3,v12)],[0,1,2,3,4,5,6,7],[(0,10),(0,26),(0,68),(0,75),(0,76),(0,77),(0,78),(0,80),(0,81),(0,82),(0,83),(1,79)]),
([v7,v5,v0,v3,v2,v9,v1,v4],[(v9,v0,v2),(v7,v3,v1)],[0,1,2,3,4,6,7],[(0,29),(0,31),(0,64),(0,66),(0,70),(0,71),(0,79),(0,84),(0,85),(0,86),(0,87),(0,88),(0,89),(0,91),(0,93),(1,90),(1,92)]),
([v5,v0,v3,v2,v12,v6,v4],[(v12,v0,v1),(v6,v1,v2)],[0,1,2,3,4,5,6,8],[(0,32),(0,43),(0,59),(0,81),(0,94),(0,95),(0,96),(0,97),(0,98),(1,67),(1,72),(1,93),(1,99)]),
([v5,v0,v3,v2,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1)],[0,1,2,3,4,5,6,7,8],[(0,29),(0,44),(0,100),(0,101),(0,102),(0,103),(0,104),(0,105),(0,106),(1,106)]),
([v5,v0,v3,v2,v9,v1,v13,v4],[(v9,v0,v2),(v13,v9,v1)],[0,1,2,3,4,6,7,8],[(0,73),(0,79),(0,106),(0,107),(0,108),(0,109),(0,110),(0,112),(1,60),(1,82),(1,111)]),
([v19,v5,v0,v3,v2,v1,v4],[(v9,v0,v2),(v19,v9,v1)],[0,1,2,3,4,5,6,7,8],[(0,45),(0,60),(0,64),(0,106),(0,113),(0,115),(1,114)]),
([v19,v5,v0,v3,v2,v9,v1,v4],[(v9,v0,v2),(v19,v9,v1)],[0,1,2,3,4,6,7,8],[(0,61),(0,70),(0,74),(0,99),(0,106),(0,112),(1,83),(1,116)]),
([v5,v0,v61,v3,v2,v1,v4],[(v37,v0,v2),(v61,v37,v3)],[0,1,2,3,4,5,6,7],[(0,118),(0,119),(0,120),(1,117)]),
([v5,v0,v3,v2,v73,v1,v4],[(v62,v0,v1),(v73,v62,v2)],[0,1,2,3,4,5,6,7,8],[(0,121),(0,122),(1,119),(1,123)]),
([v62,v21,v5,v0,v3,v2,v1,v4],[(v62,v0,v1),(v21,v3,v2)],[0,1,2,3,4,6,7],[(1,119),(1,124),(1,125),(1,126)]),
([v5,v0,v3,v2,v1,v6,v4,v38],[(v38,v0,v4),(v6,v2,v1)],[0,1,2,3,4,5,6,7,8],[(0,127),(0,128),(0,129),(0,130)]),
([v67,v5,v0,v3,v2,v1,v4],[(v38,v0,v4),(v67,v1,v38)],[0,1,2,3,4,5,6,7,8],[(0,129),(0,131),(0,132),(0,133)]),
([v5,v0,v3,v2,v59,v1,v4],[(v33,v0,v4),(v59,v33,v2)],[0,1,2,3,4,5,6],[(0,135),(0,136),(0,137),(0,138),(1,134)]),
([v33,v5,v0,v3,v2,v1,v6,v4],[(v33,v0,v4),(v6,v2,v1)],[0,1,2,3,4,5,6,7],[(0,134),(0,135),(0,139),(0,140),(0,141),(1,134)]),
([v26,v7,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v26,v7,v0)],[0,1,2,3,4,5,6,7],[(0,142),(0,143),(0,144),(0,145),(0,146),(0,147),(0,148),(0,149),(0,150),(0,151)]),
([v5,v0,v14,v3,v2,v1,v4],[(v7,v3,v1),(v14,v7,v0)],[0,1,2,3,4,5,6,7],[(0,23),(0,25),(0,84),(0,86),(0,142),(0,152),(0,155),(0,156),(1,153),(1,154)]),
([v7,v5,v0,v14,v3,v2,v1,v4],[(v7,v3,v1),(v14,v7,v0)],[0,1,2,3,4,5,6,7],[(0,23),(0,25),(0,87),(0,143),(0,147),(0,148),(0,157),(0,158),(0,159),(0,161),(0,162),(0,163),(1,160)]),
([v10,v7,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v10,v7,v0)],[0,1,2,3,4,5,6,7],[(0,23),(0,25),(0,89),(0,157),(0,164),(0,165),(0,166),(0,167),(0,168),(0,169),(0,170),(0,171),(0,172),(0,173),(0,174)]),
([v7,v5,v36,v0,v3,v2,v1,v4],[(v7,v3,v1),(v36,v7,v0)],[0,1,2,3,4,5,6,7],[(0,24),(0,164),(0,170),(0,171),(0,177),(0,178),(1,175),(1,176)]),
([v5,v0,v3,v2,v22,v1,v4],[(v7,v3,v1),(v22,v7,v2)],[0,1,2,3,4,5,6,7],[(0,86),(0,179),(0,180),(0,182),(0,183),(1,181),(1,184)]),
([v7,v5,v0,v3,v2,v22,v1,v4],[(v7,v3,v1),(v22,v7,v2)],[0,1,2,3,4,5,6,7],[(0,87),(0,149),(0,158),(0,172),(0,185),(0,186),(0,187),(1,175),(1,184)]),
([v15,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2)],[0,1,2,3,4,5,6,7],[(0,29),(0,184),(0,188),(0,189),(0,190),(0,191),(0,192),(0,193),(1,184)]),
([v15,v7,v5,v0,v3,v2,v1,v4],[(v7,v3,v1),(v15,v7,v2)],[0,1,2,3,4,5,6,7],[(0,89),(0,150),(0,159),(0,173),(0,185),(0,194),(0,195),(0,196),(0,197),(0,198),(1,176),(1,184)]),
([v7,v5,v0,v3,v2,v6,v4],[(v7,v3,v1),(v6,v2,v1)],[0,2,3,4,5,6],[(0,32),(0,93),(0,151),(0,156),(0,163),(0,174),(0,178),(0,187),(0,199),(0,200),(0,201),(0,202),(0,203)]),
([v5,v18,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v18,v0,v6)],[0,1,2,3,4,6,7,8],[(0,54),(0,94),(0,100),(0,199),(0,204),(0,205),(0,206),(0,207),(0,208),(0,209),(1,94),(1,199)]),
([v5,v0,v3,v2,v1,v6,v13,v4],[(v6,v2,v1),(v13,v0,v6)],[0,1,2,3,4,6,7,8],[(0,50),(0,101),(0,102),(0,200),(0,205),(0,206),(0,207),(0,210),(0,211),(0,212),(0,213),(0,214),(0,215),(1,200),(1,214),(1,215)]),
([v29,v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v29,v0,v6)],[0,1,2,3,4,6,7,8],[(0,201),(0,216),(0,217),(0,218),(0,219),(0,220),(0,221),(0,222),(0,223),(1,201),(1,217)]),
([v11,v5,v0,v3,v2,v1,v4],[(v6,v2,v1),(v11,v0,v6)],[0,1,2,3,4,5,6,7,8],[(0,8),(0,46),(0,55),(0,56),(0,101),(0,102),(0,218),(0,224),(0,225),(0,226),(0,227),(0,228)]),
([v11,v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v11,v0,v6)],[0,1,2,3,4,6,7,8],[(0,9),(0,48),(0,57),(0,95),(0,96),(0,101),(0,102),(0,202),(0,210),(0,219),(0,220),(0,221),(0,229),(0,230),(0,231),(0,232),(0,233),(0,234),(1,95),(1,96),(1,202)]),
([v5,v0,v16,v3,v2,v1,v4],[(v6,v2,v1),(v16,v3,v6)],[0,1,2,3,4,5,6,7],[(0,46),(0,193),(0,235),(0,236),(0,237),(0,238),(0,239),(0,240)]),
([v5,v0,v16,v3,v2,v1,v6,v4],[(v6,v2,v1),(v16,v3,v6)],[0,1,2,3,4,5,6,7],[(0,48),(0,97),(0,193),(0,203),(0,208),(0,211),(0,222),(0,233),(0,241),(0,242),(0,243),(0,244),(1,97),(1,203)]),
([v15,v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(v15,v3,v6)],[0,1,2,3,4,5,6,7],[(0,50),(0,98),(0,193),(0,209),(0,212),(0,223),(0,234),(0,242),(0,245),(0,246),(0,247),(1,98),(1,246),(1,247)]),
([v5,v0,v3,v2,v1,v6,v4,v103],[(v6,v2,v1),(v103,v6,v4)],[0,1,2,3,4,5,6,7,8],[(0,248),(1,248)]),
([0xffffff00,v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1),(0xffffff00,v6,v4)],[0,1,2,3,4,5,6,7,8],[]),
([0xffff0000ff00,v5,v0,v3,v2,v1,v4],[(v104,v2,v4),(0xffff0000ff00,v1,v104)],[0,1,2,3,4,5,6,7,8],[])
]

def g6_L9 : Array W6Node := Array.mk [
([v5,v28,v0,v3,v2,v1,v4],[(v28,v0,v3)],[0,1,2,3,4,5,6,7],[(0,0),(0,1),(1,0)]),
([v8,v5,v0,v3,v2,v1,v4],[(v8,v0,v3)],[0,1,2,3,4,5,6,7],[(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6)]),
([v5,v0,v3,v2,v9,v1,v4],[(v9,v0,v2)],[0,1,2,3,4,5,6,7,8],[(0,6),(0,8),(0,9),(0,10),(0,12),(0,14),(0,15),(0,16),(0,17),(1,4),(1,11),(1,13)]),
([v62,v5,v0,v3,v2,v1,v4],[(v62,v0,v1)],[0,1,2,3,4,5,6,7,8],[(0,19),(0,20),(1,18)]),
([v5,v0,v3,v2,v1,v4,v38],[(v38,v0,v4)],[0,1,2,3,4,5,6,7,8],[(0,21),(0,22),(1,22)]),
([v33,v5,v0,v3,v2,v1,v4],[(v33,v0,v4)],[0,1,2,3,4,5,6,7],[(0,23),(0,24),(1,23)]),
([v7,v5,v0,v3,v2,v1,v4],[(v7,v3,v1)],[0,1,2,3,4,5,6,7],[(0,4),(0,12),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(1,20)]),
([v5,v0,v3,v2,v1,v6,v4],[(v6,v2,v1)],[0,1,2,3,4,5,6,7],[(0,1),(0,7),(0,13),(0,14),(0,21),(0,24),(0,32),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(1,13),(1,34)]),
([v5,v0,v3,v2,v1,v4,v104],[(v104,v2,v4)],[0,1,2,3,4,5,6,7,8],[(0,45)])
]

def g6_L10 : Array W6Node := Array.mk [
([v5,v0,v3,v2,v1,v4],[],[0,2,3,4,5,6],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3),(1,6),(1,8)])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 (Array.mk []) i = true := by
  intro i hi
  have hsz : g6_L4.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_4_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_1 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_2 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_3 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_4 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 64 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 i = true := by
  intro i hi
  have hsz : g6_L5.size = 68 := by decide +kernel
  have hi' : i < 68 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW6_at g6_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_1 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_5_2 i (by omega) (by omega)
  ·
    by_cases h : i < 64
    ·
      exact checkBlockW6_at g6_chk_5_3 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_5_4 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_1 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_2 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_3 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_4 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_5 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_6 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_7 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_8 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_9 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_10 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_11 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_12 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_13 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_14 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_15 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_16 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_17 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_18 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : g6_L6.size = 304 := by decide +kernel
  have hi' : i < 304 := hsz ▸ hi
  by_cases h : i < 160
  ·
    by_cases h : i < 80
    ·
      by_cases h : i < 48
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW6_at g6_chk_6_0 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_1 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_2 i (by omega) (by omega)
      ·
        by_cases h : i < 64
        ·
          exact checkBlockW6_at g6_chk_6_3 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_4 i (by omega) (by omega)
    ·
      by_cases h : i < 128
      ·
        by_cases h : i < 112
        ·
          by_cases h : i < 96
          ·
            exact checkBlockW6_at g6_chk_6_5 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_6 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_7 i (by omega) (by omega)
      ·
        by_cases h : i < 144
        ·
          exact checkBlockW6_at g6_chk_6_8 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_9 i (by omega) (by omega)
  ·
    by_cases h : i < 240
    ·
      by_cases h : i < 208
      ·
        by_cases h : i < 192
        ·
          by_cases h : i < 176
          ·
            exact checkBlockW6_at g6_chk_6_10 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_11 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_12 i (by omega) (by omega)
      ·
        by_cases h : i < 224
        ·
          exact checkBlockW6_at g6_chk_6_13 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_14 i (by omega) (by omega)
    ·
      by_cases h : i < 272
      ·
        by_cases h : i < 256
        ·
          exact checkBlockW6_at g6_chk_6_15 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_16 i (by omega) (by omega)
      ·
        by_cases h : i < 288
        ·
          exact checkBlockW6_at g6_chk_6_17 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_18 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_1 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_2 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_3 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_4 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_5 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_6 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_7 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_8 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_9 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_10 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_11 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_12 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_13 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_14 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_15 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 240 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 i = true := by
  intro i hi
  have hsz : g6_L7.size = 249 := by decide +kernel
  have hi' : i < 249 := hsz ▸ hi
  by_cases h : i < 128
  ·
    by_cases h : i < 64
    ·
      by_cases h : i < 32
      ·
        by_cases h : i < 16
        ·
          exact checkBlockW6_at g6_chk_7_0 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_1 i (by omega) (by omega)
      ·
        by_cases h : i < 48
        ·
          exact checkBlockW6_at g6_chk_7_2 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_3 i (by omega) (by omega)
    ·
      by_cases h : i < 96
      ·
        by_cases h : i < 80
        ·
          exact checkBlockW6_at g6_chk_7_4 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_5 i (by omega) (by omega)
      ·
        by_cases h : i < 112
        ·
          exact checkBlockW6_at g6_chk_7_6 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_7 i (by omega) (by omega)
  ·
    by_cases h : i < 192
    ·
      by_cases h : i < 160
      ·
        by_cases h : i < 144
        ·
          exact checkBlockW6_at g6_chk_7_8 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_9 i (by omega) (by omega)
      ·
        by_cases h : i < 176
        ·
          exact checkBlockW6_at g6_chk_7_10 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_11 i (by omega) (by omega)
    ·
      by_cases h : i < 224
      ·
        by_cases h : i < 208
        ·
          exact checkBlockW6_at g6_chk_7_12 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_13 i (by omega) (by omega)
      ·
        by_cases h : i < 240
        ·
          exact checkBlockW6_at g6_chk_7_14 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_15 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_1 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_2 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 32 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 i = true := by
  intro i hi
  have hsz : g6_L8.size = 46 := by decide +kernel
  have hi' : i < 46 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW6_at g6_chk_8_0 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_8_1 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_8_2 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_9 : ∀ i < g6_L9.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 i = true := by
  intro i hi
  have hsz : g6_L9.size = 9 := by decide +kernel
  exact checkBlockW6_at g6_chk_9_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_10_0 : checkBlockW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_10 : ∀ i < g6_L10.size, checkNodeW6 goal6 2 g6_pow 9 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 i = true := by
  intro i hi
  have hsz : g6_L10.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_10_0 i (Nat.zero_le _) (by omega)

theorem g6_L4_sound : ∀ i < g6_L4.size, ¬ live (basicOps 64) goal6 4 (g6_L4[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound (fun j hj => by simp at hj) g6_chk_4

theorem g6_L5_sound : ∀ i < g6_L5.size, ¬ live (basicOps 64) goal6 5 (g6_L5[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L4_sound g6_chk_5

theorem g6_L6_sound : ∀ i < g6_L6.size, ¬ live (basicOps 64) goal6 6 (g6_L6[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L5_sound g6_chk_6

theorem g6_L7_sound : ∀ i < g6_L7.size, ¬ live (basicOps 64) goal6 7 (g6_L7[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L6_sound g6_chk_7

theorem g6_L8_sound : ∀ i < g6_L8.size, ¬ live (basicOps 64) goal6 8 (g6_L8[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L7_sound g6_chk_8

theorem g6_L9_sound : ∀ i < g6_L9.size, ¬ live (basicOps 64) goal6 9 (g6_L9[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L8_sound g6_chk_9

theorem g6_L10_sound : ∀ i < g6_L10.size, ¬ live (basicOps 64) goal6 10 (g6_L10[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L9_sound g6_chk_10

set_option maxRecDepth 100000 in

theorem g6_sublists : rows6.sublists.filter (fun ws => cover 64 jumps6 goal6 ws) = [rows6] := by decide +kernel

theorem g6_top_match : sameSet (rows6.map (actB 64 (g6_pow[0]?.getD []))) (g6_L10[0]?.getD ([], [], [], [])).1 = true := by decide +kernel

theorem g6_no_build : ¬ build (basicOps 64) goal6 10 rows6.toFinset :=

  no_build_of_top g6_G_valid (by decide) g6_sublists g6_top_match (g6_L10_sound 0 (by decide))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W6 := BitVec 64
abbrev basicOps6 (a b : W6) : Finset W6 := (ops 64 a b).toFinset

def holds (av : Finset W6) (z : W6) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W6} {z a : W6} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W6} {z : W6} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W6) (z : W6) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps6 a b, holds (insert w av) z

theorem reachable_not {av : Finset W6} {z : W6} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset W6} {x y : W6} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W6) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W6) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y); rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W6) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64); rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W6) (hw : w ∈ basicOps6 a b) (z : W6) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps6, ops] : a &&& b ∈ basicOps6 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps6, ops] : a &&& ~~~b ∈ basicOps6 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps6, ops] : b &&& ~~~a ∈ basicOps6 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps6, ops] : a ||| b ∈ basicOps6 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W6} {x y : W6} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit6 (k : Fin 64) (z : W6) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit6 (w : List W6) (i : ℕ) (k : Fin 64) :
    (w.map (bit6 k)).getD i false = bit6 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit6]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W6) (g : Gate) : W6 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W6) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit6 k)) g = (w ++ [action w g]).map (bit6 k) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W6)[k.val] = false := by simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit6, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit6, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W6} {w : List W6} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

theorem gate_reach (w : List W6) (av : Finset W6) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W6, x ||| (0 : W6) = x from fun x => BitVec.or_zero,
    show ∀ x : W6, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W6) (av : Finset W6) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit6 k))).getD out false = bit6 k goal6) :
    ∃ t, (t = goal6 ∨ t = ~~~goal6) ∧ build basicOps6 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal6 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil, read_bit6, bit6] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal6 ≠ 0) zero)
    · exact False.elim ((by decide : goal6 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W6 => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit6 k))).getD out false = bit6 k goal6 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W6) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def F (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277071584 * 2 ^ 32 + 4209699456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem sample6_ok : ∀ k : Fin 64, F (fun i => (rows6.getD i.val 0)[k.val]) = goal6[k.val] := by decide +kernel

def idxs64 : List ℕ := List.range 64
theorem idxs64_spec : idxs64.length = 64 ∧ ∀ idx ∈ idxs64, idx < 64 := by decide
theorem projS64_goal6 : projS 64 idxs64 goal6 = goal6 := by decide +kernel
theorem projS64_rows6_sub : rows6.all (fun w => projS 64 idxs64 w == 0 || rows6.contains (projS 64 idxs64 w)) = true := by decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows6, holds rows6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (rows6.map (bit6 k))).getD o false = bit6 k goal6 := by
    let x (i : Fin 6) : Bool := bit6 k (rows6.getD i.val 0)
    have same : List.ofFn x = rows6.map (bit6 k) := by
      apply List.ext_getElem
      · simp [rows6]
      · intro i hi hj
        have hlt : i < rows6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows6.map (bit6 k)) = bit6 k goal6
    rw [← same, he]
    exact sample6_ok k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows6 rows6.toFinset init evaluate
  obtain ⟨s, hs, hl⟩ := compress (build_mono_k low run)
  have hpt : projS 64 idxs64 t = goal6 := by
    rcases ht with rfl | rfl
    · exact projS64_goal6
    · rw [projS_not 64 (by decide) idxs64 idxs64_spec.1 idxs64_spec.2]; exact projS64_goal6
  have hb64 := live_restrict (by decide : 0 < 64) idxs64 idxs64_spec.1 idxs64_spec.2
    (fun a b z hz => List.mem_toFinset.mp hz) hpt (by decide : goal6 ≠ 0) hl
  have hsub64 : nonZeroImg (projS 64 idxs64) s ⊆ rows6.toFinset := by
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu
    obtain ⟨hne, v, hv, rfl⟩ := hu
    have h1 := List.all_eq_true.mp projS64_rows6_sub v (List.mem_toFinset.mp (hs hv))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact g6_no_build (build_mono_k (Nat.sub_le _ _) (build_mono_av hsub64 hb64))

def wg : List Gate := [
  ⟨.and, [5, 1]⟩,
  ⟨.or, [4, 3]⟩,
  ⟨.and, [5, 0]⟩,
  ⟨.or, [6, 0]⟩,
  ⟨.and, [4, 3]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.or, [10, 1]⟩,
  ⟨.and, [7, 9]⟩,
  ⟨.or, [8, 12]⟩,
  ⟨.and, [14, 2]⟩,
  ⟨.or, [15, 13]⟩,
  ⟨.and, [16, 11]⟩
]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_41514_aux

open PEqualNP.Outside.L_meta_41514_aux in
theorem PEqualNP.Outside.L_meta_41514 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209699456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4209699456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsz, hev⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, legal g := fun g hg => by
      have hf := hfan g hg
      refine ⟨?_, hf.2⟩
      simpa using hf.1
    have hb := bound C.gates C.output hleg hev
    have hclen : C.gates.length ≤ s := hsz
    have hl : (⟨wg, 17⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 12 := rfl
    exact ⟨⟨wg, 17⟩, wfits, by omega, weval⟩
  · refine ⟨C, fun g hg => ⟨?_, (hfan g hg).2⟩, hsz, hev⟩
    have hf := (hfan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
    rcases hf with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
