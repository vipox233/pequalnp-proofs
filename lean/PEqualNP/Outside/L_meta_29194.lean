import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29194.Leaf10732.Src

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

theorem bit_dif {n : ℕ} {w : BitVec n} {d i : ℕ} (hi : i < n) :
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

theorem checkBlockP_merge {n gsize k start a b : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h1 : checkBlockP n jumps goal gsize G_pow k cur prev start a = true)
    (h2 : checkBlockP n jumps goal gsize G_pow k cur prev (start + a) b = true) :
    checkBlockP n jumps goal gsize G_pow k cur prev start (a + b) = true := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h2 ⊢
    exact ⟨by simpa [Nat.add_assoc] using h2.1, ih h2.2⟩

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
    (hblk : checkBlockP n jumps goal gsize G_pow k cur prev 0 cur.size = true) :
    ∀ i < cur.size, ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset :=
  fun i hi => node_sound_P hk hi hvalid hprev (checkBlockP_at hblk i (Nat.zero_le _) (by simpa using hi))

theorem no_build_of_root {n gsize k rg : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {rows root_ws : List (BitVec n)}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hrg : rg < gsize)
    (hsub : rows.sublists.filter (fun ws => cover n jumps goal ws) = [rows])
    (hmatch : sameSet (rows.map (actB n (G_pow[rg]?.getD []))) root_ws = true)
    (hdead : ¬ live (basicOps n) goal k root_ws.toFinset) :
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

def jumps5 : List ℕ := [1, 2, 4, 8, 16]
def jumps6 : List ℕ := [1, 2, 4, 8, 16, 32]


def p4h_goal : BitVec 32 := 0xfffeeea0
def p4h_rows : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def p4h_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def p4h_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648]
def p4h_s1 : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31]
def p4h_p1 : List ℕ := [1, 256, 16, 4096, 4, 1024, 64, 16384, 2, 512, 32, 8192, 8, 2048, 128, 32768, 65536, 16777216, 1048576, 268435456, 262144, 67108864, 4194304, 1073741824, 131072, 33554432, 2097152, 536870912, 524288, 134217728, 8388608, 2147483648]
def p4h_idx : Array (List ℕ) := Array.mk [p4h_s0, p4h_s1]
def p4h_pow : Array (List ℕ) := Array.mk [p4h_p0, p4h_p1]
def p4h_inv : Array ℕ := Array.mk [0, 1]
theorem p4h_G_valid : (List.range 2).all (symValid 32 2 p4h_idx p4h_pow p4h_inv p4h_goal) = true := by decide +kernel
def p4h_L2 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xeeaeeeae,0xfff0fff0,0xffff0000],[]),
  ([0xeeeeeeaa,0xfff0fff0,0xffff0000],[])
]
def p4h_L3 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xeeeeeeee,0xffaaffaa,0xfff0fff0,0xffff0000],[]),
  ([0xcccccccc,0xeeaaeeaa,0xfff0fff0,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffffcc00],[]),
  ([0xaaaaaaaa,0xcc0ccc0c,0xfff0fff0,0xffff0000],[(0,0)]),
  ([0xaaaaaaaa,0xcccccc00,0xfff0fff0,0xffff0000],[(0,1)]),
  ([0xf000f0,0xeeaeeeae,0xff00ff00,0xffff0000],[(0,0)]),
  ([0x44f444f4,0xaaaaaaaa,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xffb0ffb0,0xffff0000],[(1,0)]),
  ([0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xffffcc00],[]),
  ([0x33cc33cc,0xaaaaaaaa,0xf0f0f0f0,0xffff0000],[]),
  ([0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffaa00],[]),
  ([0x55aa55aa,0xcccccccc,0xf0f0f0f0,0xffff0000],[]),
  ([0xaaaaaaaa,0xf0f0f0f0,0xffcccccc,0xffffff00],[]),
  ([0xcccccccc,0xf0f0f0f0,0xffaaaaaa,0xffffff00],[]),
  ([0xffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfff0ffa0,0xffff0000],[(1,1)]),
  ([0xaaaaaaaa,0xf0f0f0f0,0xffccff00,0xffffcccc],[]),
  ([0xf0ff0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00],[])
]
def p4h_L4 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xeeeeeeee,0xff00ff00,0xfff0fff0,0xffff0000],[(0,0)]),
  ([0xf000f0,0xaaaaaaaa,0xeeeeeeee,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xffaaffaa,0xfff0fff0,0xffff0000],[(0,0)]),
  ([0xaa00aa,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xa0a0a0a0,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,1),(1,2)]),
  ([0xcc00cc,0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffff0000],[]),
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffff0000],[(0,3)]),
  ([0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffff0000,0xffffff00],[(0,4)]),
  ([0xaaaa,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000],[]),
  ([0xf000f0,0xf000f00,0xaaaaaaaa,0xcccccccc,0xffff0000],[]),
  ([0xf000f0,0xaaaaaaaa,0xccfcccfc,0xff00ff00,0xffff0000],[]),
  ([0xf000f0,0xaaaaaaaa,0xcc0ccc0c,0xff00ff00,0xffff0000],[(0,3),(0,5)]),
  ([0xf000f0,0x44444444,0xaaaaaaaa,0xff00ff00,0xffff0000],[(0,6)]),
  ([0xaaaaaaaa,0xcccccccc,0xf4f4f4f4,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xb0b0b0b0,0xcccccccc,0xff00ff00,0xffff0000],[(0,7),(1,3)]),
  ([0xaaaaaaaa,0xcccccccc,0xfcf0fcf0,0xff00ff00,0xffff0000],[]),
  ([0x30f030f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffa0ffa0,0xffff0000],[(1,1)]),
  ([0x22aa22aa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffa0a0],[(1,2),(1,8)]),
  ([0x33ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[]),
  ([0xa0a0a0a0,0xcccccccc,0xfafafafa,0xff00ff00,0xffff0000],[(1,8),(1,9)]),
  ([0xaaaaaaaa,0xcccccccc,0xf3f0f3f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xc0f0c0f0,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xcc00cc,0x33003300,0xaaaaaaaa,0xf0f0f0f0,0xffff0000],[(0,9)]),
  ([0xaaaaaaaa,0xcccccccc,0xfaf0faf0,0xff00ff00,0xffff0000],[]),
  ([0x44cc44cc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaa00],[(0,10)]),
  ([0x55ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[]),
  ([0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffff0000],[(0,10),(0,11)]),
  ([0xaaaaaaaa,0xcccccccc,0xf5f0f5f0,0xff00ff00,0xffff0000],[]),
  ([0xa0f0a0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaa00aa,0x55005500,0xcccccccc,0xf0f0f0f0,0xffff0000],[(0,11)]),
  ([0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0f0f0,0xffff0000],[]),
  ([0xf0f0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfafaf0f0,0xff00ff00,0xffff0000],[(1,12)]),
  ([0xcccccc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaff00,0xffff0000],[(1,13)]),
  ([0xaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa],[(1,12),(1,13),(1,14)]),
  ([0xaaaaaaaa,0xcccccc00,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,4),(1,15)]),
  ([0xf0f0a0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0fff0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccc4444,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaa,0x55550000,0xcccccccc,0xf0f0f0f0,0xff00ff00],[(1,14)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff30ff30,0xffff0000],[]),
  ([0xa2a2a2a2,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xc0c0c0c,0x30303030,0xaaaaaaaa,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfff0ff00,0xffff0000],[]),
  ([0xf00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfcfcf0f0,0xff00ff00,0xffff0000],[]),
  ([0xc0ccccc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffccff00,0xffff0000],[(0,16)]),
  ([0xa0aaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccc0000,0xf0f0f0f0,0xff00ff00,0xffffcccc],[(0,16),(1,17)]),
  ([0xcccc,0x33330000,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00],[(1,17)])
]
def p4h_L5 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,0)]),
  ([0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000],[(0,0),(0,1),(0,3),(0,6),(0,7),(0,8),(1,2),(1,4),(1,5),(1,9)]),
  ([0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,7)]),
  ([0xf000f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,10),(0,11)]),
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[(0,2),(0,7),(0,10),(0,12),(0,13),(0,14)]),
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,7),(0,11),(1,15),(1,16)]),
  ([0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,5),(0,19),(0,21),(0,23),(1,17),(1,18),(1,20),(1,22)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000],[(0,23)]),
  ([0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,24),(1,25),(1,26)]),
  ([0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,6),(0,26)]),
  ([0xaa00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,27),(0,28),(0,29),(0,30),(0,31),(1,27),(1,28)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000],[(0,3),(0,31),(1,3)]),
  ([0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,4),(0,34),(1,32),(1,33)]),
  ([0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,37),(0,39),(0,41),(1,35),(1,36),(1,38),(1,40)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffaaaa],[(0,41),(0,43),(1,8),(1,42)]),
  ([0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,9),(0,45),(0,46),(1,44)]),
  ([0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,46)]),
  ([0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000],[]),
  ([0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,48),(0,49),(1,47)]),
  ([0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,52),(0,54),(0,56),(1,50),(1,51),(1,53),(1,55)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffcccc],[(0,56)]),
  ([0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,57)]),
  ([0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,57)])
]
def p4h_L6 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,12),(1,13),(1,14),(1,15),(1,16),(1,19),(1,20),(1,21),(1,22),(1,23)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_2_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 2 p4h_L2 (Array.mk []) 0 2 = true := by decide +kernel
theorem p4h_chk_2 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 2 p4h_L2 (Array.mk []) 0 2 = true := p4h_chk_2_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_3_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 3 p4h_L3 p4h_L2 0 18 = true := by decide +kernel
theorem p4h_chk_3 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 3 p4h_L3 p4h_L2 0 18 = true := p4h_chk_3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_4_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 4 p4h_L4 p4h_L3 0 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_4_40 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 4 p4h_L4 p4h_L3 40 18 = true := by decide +kernel
theorem p4h_chk_4 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 4 p4h_L4 p4h_L3 0 58 = true := (checkBlockP_merge p4h_chk_4_0 p4h_chk_4_40)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_5_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 5 p4h_L5 p4h_L4 0 24 = true := by decide +kernel
theorem p4h_chk_5 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 5 p4h_L5 p4h_L4 0 24 = true := p4h_chk_5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_6_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 6 p4h_L6 p4h_L5 0 1 = true := by decide +kernel
theorem p4h_chk_6 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 6 p4h_L6 p4h_L5 0 1 = true := p4h_chk_6_0
theorem p4h_L2_sound : ∀ i < p4h_L2.size, ¬ live (basicOps 32) p4h_goal 2 (p4h_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid (fun j hj => by simp at hj) p4h_chk_2
theorem p4h_L3_sound : ∀ i < p4h_L3.size, ¬ live (basicOps 32) p4h_goal 3 (p4h_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L2_sound p4h_chk_3
theorem p4h_L4_sound : ∀ i < p4h_L4.size, ¬ live (basicOps 32) p4h_goal 4 (p4h_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L3_sound p4h_chk_4
theorem p4h_L5_sound : ∀ i < p4h_L5.size, ¬ live (basicOps 32) p4h_goal 5 (p4h_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L4_sound p4h_chk_5
theorem p4h_L6_sound : ∀ i < p4h_L6.size, ¬ live (basicOps 32) p4h_goal 6 (p4h_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L5_sound p4h_chk_6
theorem p4h_sublists : p4h_rows.sublists.filter (fun ws => cover 32 jumps5 p4h_goal ws) = [p4h_rows] := by decide +kernel
theorem p4h_top_match : sameSet (p4h_rows.map (actB 32 (p4h_pow[0]?.getD []))) (p4h_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem p4h_no_build : ¬ build (basicOps 32) p4h_goal 6 p4h_rows.toFinset :=
  no_build_of_root p4h_G_valid (by decide) p4h_sublists p4h_top_match (p4h_L6_sound 0 (by decide))


def c5_goal : BitVec 32 := 0xfefceea0
def c5_rows : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def c5_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def c5_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648]
def c5_s1 : List ℕ := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 2, 3, 18, 19, 10, 11, 26, 27, 6, 7, 22, 23, 14, 15, 30, 31]
def c5_p1 : List ℕ := [1, 2, 65536, 131072, 256, 512, 16777216, 33554432, 16, 32, 1048576, 2097152, 4096, 8192, 268435456, 536870912, 4, 8, 262144, 524288, 1024, 2048, 67108864, 134217728, 64, 128, 4194304, 8388608, 16384, 32768, 1073741824, 2147483648]
def c5_s2 : List ℕ := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 4, 6, 5, 7, 20, 22, 21, 23, 12, 14, 13, 15, 28, 30, 29, 31]
def c5_p2 : List ℕ := [1, 4, 2, 8, 65536, 262144, 131072, 524288, 256, 1024, 512, 2048, 16777216, 67108864, 33554432, 134217728, 16, 64, 32, 128, 1048576, 4194304, 2097152, 8388608, 4096, 16384, 8192, 32768, 268435456, 1073741824, 536870912, 2147483648]
def c5_s3 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31]
def c5_p3 : List ℕ := [1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576, 4194304, 16777216, 67108864, 268435456, 1073741824, 2, 8, 32, 128, 512, 2048, 8192, 32768, 131072, 524288, 2097152, 8388608, 33554432, 134217728, 536870912, 2147483648]
def c5_s4 : List ℕ := [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 8, 12, 10, 14, 9, 13, 11, 15, 24, 28, 26, 30, 25, 29, 27, 31]
def c5_p4 : List ℕ := [1, 16, 4, 64, 2, 32, 8, 128, 65536, 1048576, 262144, 4194304, 131072, 2097152, 524288, 8388608, 256, 4096, 1024, 16384, 512, 8192, 2048, 32768, 16777216, 268435456, 67108864, 1073741824, 33554432, 536870912, 134217728, 2147483648]
def c5_s5 : List ℕ := [0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31]
def c5_p5 : List ℕ := [1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 2, 32, 512, 8192, 131072, 2097152, 33554432, 536870912, 4, 64, 1024, 16384, 262144, 4194304, 67108864, 1073741824, 8, 128, 2048, 32768, 524288, 8388608, 134217728, 2147483648]
def c5_s6 : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31]
def c5_p6 : List ℕ := [1, 256, 16, 4096, 4, 1024, 64, 16384, 2, 512, 32, 8192, 8, 2048, 128, 32768, 65536, 16777216, 1048576, 268435456, 262144, 67108864, 4194304, 1073741824, 131072, 33554432, 2097152, 536870912, 524288, 134217728, 8388608, 2147483648]
def c5_s7 : List ℕ := [0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31]
def c5_p7 : List ℕ := [1, 256, 65536, 16777216, 2, 512, 131072, 33554432, 4, 1024, 262144, 67108864, 8, 2048, 524288, 134217728, 16, 4096, 1048576, 268435456, 32, 8192, 2097152, 536870912, 64, 16384, 4194304, 1073741824, 128, 32768, 8388608, 2147483648]
def c5_s8 : List ℕ := [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23, 8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31]
def c5_p8 : List ℕ := [1, 65536, 2, 131072, 4, 262144, 8, 524288, 16, 1048576, 32, 2097152, 64, 4194304, 128, 8388608, 256, 16777216, 512, 33554432, 1024, 67108864, 2048, 134217728, 4096, 268435456, 8192, 536870912, 16384, 1073741824, 32768, 2147483648]
def c5_s9 : List ℕ := [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31]
def c5_p9 : List ℕ := [1, 65536, 256, 16777216, 16, 1048576, 4096, 268435456, 4, 262144, 1024, 67108864, 64, 4194304, 16384, 1073741824, 2, 131072, 512, 33554432, 32, 2097152, 8192, 536870912, 8, 524288, 2048, 134217728, 128, 8388608, 32768, 2147483648]
def c5_idx : Array (List ℕ) := Array.mk [c5_s0, c5_s1, c5_s2, c5_s3, c5_s4, c5_s5, c5_s6, c5_s7, c5_s8, c5_s9]
def c5_pow : Array (List ℕ) := Array.mk [c5_p0, c5_p1, c5_p2, c5_p3, c5_p4, c5_p5, c5_p6, c5_p7, c5_p8, c5_p9]
def c5_inv : Array ℕ := Array.mk [0, 1, 2, 8, 4, 7, 6, 5, 3, 9]
theorem c5_G_valid : (List.range 10).all (symValid 32 10 c5_idx c5_pow c5_inv c5_goal) = true := by decide +kernel
def c5_L3 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0],[]),
  ([0xf0ff0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00],[])
]
def c5_L4 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaa0aaa0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0f00],[]),
  ([0xa2a2a2a2,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaa,0x55550000,0xcccccccc,0xf0f0f0f0,0xff00ff00],[(8,0)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaa00],[]),
  ([0xf00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffa0a0],[]),
  ([0xa0aaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xa0a0a0a0,0xcccccccc,0xfafafafa,0xff00ff00,0xffff0000],[(5,1)]),
  ([0xcccc,0x33330000,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00],[(7,1)])
]
def c5_L5 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(4,1),(6,0)]),
  ([0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,4),(2,3),(7,2)]),
  ([0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,7),(0,9),(1,5),(4,7),(5,6),(5,8),(9,8)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000],[(0,9)]),
  ([0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,10)])
]
def c5_L6 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5),(4,2),(4,5),(5,0),(5,1),(5,2),(5,5),(6,2),(6,5),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,2),(9,5)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_3_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 3 c5_L3 (Array.mk []) 0 2 = true := by decide +kernel
theorem c5_chk_3 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 3 c5_L3 (Array.mk []) 0 2 = true := c5_chk_3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_4_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 4 c5_L4 c5_L3 0 11 = true := by decide +kernel
theorem c5_chk_4 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 4 c5_L4 c5_L3 0 11 = true := c5_chk_4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_5_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 5 c5_L5 c5_L4 0 6 = true := by decide +kernel
theorem c5_chk_5 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 5 c5_L5 c5_L4 0 6 = true := c5_chk_5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_6_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 6 c5_L6 c5_L5 0 1 = true := by decide +kernel
theorem c5_chk_6 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 6 c5_L6 c5_L5 0 1 = true := c5_chk_6_0
theorem c5_L3_sound : ∀ i < c5_L3.size, ¬ live (basicOps 32) c5_goal 3 (c5_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid (fun j hj => by simp at hj) c5_chk_3
theorem c5_L4_sound : ∀ i < c5_L4.size, ¬ live (basicOps 32) c5_goal 4 (c5_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid c5_L3_sound c5_chk_4
theorem c5_L5_sound : ∀ i < c5_L5.size, ¬ live (basicOps 32) c5_goal 5 (c5_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid c5_L4_sound c5_chk_5
theorem c5_L6_sound : ∀ i < c5_L6.size, ¬ live (basicOps 32) c5_goal 6 (c5_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid c5_L5_sound c5_chk_6
theorem c5_sublists : c5_rows.sublists.filter (fun ws => cover 32 jumps5 c5_goal ws) = [c5_rows] := by decide +kernel
theorem c5_top_match : sameSet (c5_rows.map (actB 32 (c5_pow[0]?.getD []))) (c5_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem c5_no_build : ¬ build (basicOps 32) c5_goal 6 c5_rows.toFinset :=
  no_build_of_root c5_G_valid (by decide) c5_sublists c5_top_match (c5_L6_sound 0 (by decide))


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

theorem nrm_zero (n : ℕ) : nrm n 0 = 0 := by
  unfold nrm; simp

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


abbrev W5Node := List (BitVec 64) × List (BitVec 64 × BitVec 64 × BitVec 64) × List ℕ × List (ℕ × ℕ)

def checkReplay (m : BitVec 64) (bank : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → Bool
  | [], targets => targets.all (fun t => (t &&& m) == 0 || bank.contains (t &&& m))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 64 a b).contains v &&
    checkReplay m (v :: bank) rest targets

theorem checkReplay_sound (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (g : BitVec 32)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay m bank steps targets = true →
      build (basicOps 32) g k (nonZeroImg (projS 32 idxs) targets.toFinset) →
      build (basicOps 32) g (k + steps.length) (nonZeroImg (projS 32 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 32 := projS 32 idxs
  have hn : 0 < 32 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_mask 32 idxs m hm t, h0, projS_zero]
    · exact ⟨hne, t &&& m, hmem, projS_mask 32 idxs m hm t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
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

def addNeed (stock needed : List (BitVec 64)) (u : BitVec 64) : List (BitVec 64) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded (m : BitVec 64) (stock : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := w &&& m
    let needed' := if needed.contains pw then addNeed stock (addNeed stock needed (a &&& m)) (b &&& m) else needed
    buildNeeded m stock rest needed'

def buildSteps (m : BitVec 64) (needed : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64 × BitVec 64 × BitVec 64)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := w &&& m
    let pa := a &&& m
    let pb := b &&& m
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 64 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps m needed rest (pw :: bank)
    else
      buildSteps m needed rest bank

def checkCofClose (fuel : ℕ) (m : BitVec 64) (stock : List (BitVec 64))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  let flat := (nxt.filter (fun u => (u &&& m) == 0)).length
  let rem := fuel - flat
  if Nat.blt rem 7 then
    let start := nxt.foldl (fun acc u => addNeed stock acc (u &&& m)) []
    if Nat.blt (start.length + rem) 7 then
      let needed := buildNeeded m stock hist.reverse start
      if Nat.blt (needed.length + rem) 7 then
        let steps := buildSteps m needed hist stock
        Nat.blt (steps.length + rem) 7 && checkReplay m stock steps nxt
      else false
    else false
  else false

def w5_goal : BitVec 64 := 0xfffffffefefceea0
def w5_rows : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def w5_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def w5_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 68719476736, 137438953472, 274877906944, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 70368744177664, 140737488355328, 281474976710656, 562949953421312, 1125899906842624, 2251799813685248, 4503599627370496, 9007199254740992, 18014398509481984, 36028797018963968, 72057594037927936, 144115188075855872, 288230376151711744, 576460752303423488, 1152921504606846976, 2305843009213693952, 4611686018427387904, 9223372036854775808]
def w5_s1 : List ℕ := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 2, 3, 18, 19, 10, 11, 26, 27, 6, 7, 22, 23, 14, 15, 30, 31, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61, 34, 35, 50, 51, 42, 43, 58, 59, 38, 39, 54, 55, 46, 47, 62, 63]
def w5_p1 : List ℕ := [1, 2, 65536, 131072, 256, 512, 16777216, 33554432, 16, 32, 1048576, 2097152, 4096, 8192, 268435456, 536870912, 4, 8, 262144, 524288, 1024, 2048, 67108864, 134217728, 64, 128, 4194304, 8388608, 16384, 32768, 1073741824, 2147483648, 4294967296, 8589934592, 281474976710656, 562949953421312, 1099511627776, 2199023255552, 72057594037927936, 144115188075855872, 68719476736, 137438953472, 4503599627370496, 9007199254740992, 17592186044416, 35184372088832, 1152921504606846976, 2305843009213693952, 17179869184, 34359738368, 1125899906842624, 2251799813685248, 4398046511104, 8796093022208, 288230376151711744, 576460752303423488, 274877906944, 549755813888, 18014398509481984, 36028797018963968, 70368744177664, 140737488355328, 4611686018427387904, 9223372036854775808]
def w5_s2 : List ℕ := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 4, 6, 5, 7, 20, 22, 21, 23, 12, 14, 13, 15, 28, 30, 29, 31, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59, 36, 38, 37, 39, 52, 54, 53, 55, 44, 46, 45, 47, 60, 62, 61, 63]
def w5_p2 : List ℕ := [1, 4, 2, 8, 65536, 262144, 131072, 524288, 256, 1024, 512, 2048, 16777216, 67108864, 33554432, 134217728, 16, 64, 32, 128, 1048576, 4194304, 2097152, 8388608, 4096, 16384, 8192, 32768, 268435456, 1073741824, 536870912, 2147483648, 4294967296, 17179869184, 8589934592, 34359738368, 281474976710656, 1125899906842624, 562949953421312, 2251799813685248, 1099511627776, 4398046511104, 2199023255552, 8796093022208, 72057594037927936, 288230376151711744, 144115188075855872, 576460752303423488, 68719476736, 274877906944, 137438953472, 549755813888, 4503599627370496, 18014398509481984, 9007199254740992, 36028797018963968, 17592186044416, 70368744177664, 35184372088832, 140737488355328, 1152921504606846976, 4611686018427387904, 2305843009213693952, 9223372036854775808]
def w5_s3 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63]
def w5_p3 : List ℕ := [1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576, 4194304, 16777216, 67108864, 268435456, 1073741824, 2, 8, 32, 128, 512, 2048, 8192, 32768, 131072, 524288, 2097152, 8388608, 33554432, 134217728, 536870912, 2147483648, 4294967296, 17179869184, 68719476736, 274877906944, 1099511627776, 4398046511104, 17592186044416, 70368744177664, 281474976710656, 1125899906842624, 4503599627370496, 18014398509481984, 72057594037927936, 288230376151711744, 1152921504606846976, 4611686018427387904, 8589934592, 34359738368, 137438953472, 549755813888, 2199023255552, 8796093022208, 35184372088832, 140737488355328, 562949953421312, 2251799813685248, 9007199254740992, 36028797018963968, 144115188075855872, 576460752303423488, 2305843009213693952, 9223372036854775808]
def w5_s4 : List ℕ := [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 8, 12, 10, 14, 9, 13, 11, 15, 24, 28, 26, 30, 25, 29, 27, 31, 32, 36, 34, 38, 33, 37, 35, 39, 48, 52, 50, 54, 49, 53, 51, 55, 40, 44, 42, 46, 41, 45, 43, 47, 56, 60, 58, 62, 57, 61, 59, 63]
def w5_p4 : List ℕ := [1, 16, 4, 64, 2, 32, 8, 128, 65536, 1048576, 262144, 4194304, 131072, 2097152, 524288, 8388608, 256, 4096, 1024, 16384, 512, 8192, 2048, 32768, 16777216, 268435456, 67108864, 1073741824, 33554432, 536870912, 134217728, 2147483648, 4294967296, 68719476736, 17179869184, 274877906944, 8589934592, 137438953472, 34359738368, 549755813888, 281474976710656, 4503599627370496, 1125899906842624, 18014398509481984, 562949953421312, 9007199254740992, 2251799813685248, 36028797018963968, 1099511627776, 17592186044416, 4398046511104, 70368744177664, 2199023255552, 35184372088832, 8796093022208, 140737488355328, 72057594037927936, 1152921504606846976, 288230376151711744, 4611686018427387904, 144115188075855872, 2305843009213693952, 576460752303423488, 9223372036854775808]
def w5_s5 : List ℕ := [0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31, 32, 36, 40, 44, 48, 52, 56, 60, 33, 37, 41, 45, 49, 53, 57, 61, 34, 38, 42, 46, 50, 54, 58, 62, 35, 39, 43, 47, 51, 55, 59, 63]
def w5_p5 : List ℕ := [1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 2, 32, 512, 8192, 131072, 2097152, 33554432, 536870912, 4, 64, 1024, 16384, 262144, 4194304, 67108864, 1073741824, 8, 128, 2048, 32768, 524288, 8388608, 134217728, 2147483648, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976, 8589934592, 137438953472, 2199023255552, 35184372088832, 562949953421312, 9007199254740992, 144115188075855872, 2305843009213693952, 17179869184, 274877906944, 4398046511104, 70368744177664, 1125899906842624, 18014398509481984, 288230376151711744, 4611686018427387904, 34359738368, 549755813888, 8796093022208, 140737488355328, 2251799813685248, 36028797018963968, 576460752303423488, 9223372036854775808]
def w5_s6 : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31, 32, 40, 36, 44, 34, 42, 38, 46, 33, 41, 37, 45, 35, 43, 39, 47, 48, 56, 52, 60, 50, 58, 54, 62, 49, 57, 53, 61, 51, 59, 55, 63]
def w5_p6 : List ℕ := [1, 256, 16, 4096, 4, 1024, 64, 16384, 2, 512, 32, 8192, 8, 2048, 128, 32768, 65536, 16777216, 1048576, 268435456, 262144, 67108864, 4194304, 1073741824, 131072, 33554432, 2097152, 536870912, 524288, 134217728, 8388608, 2147483648, 4294967296, 1099511627776, 68719476736, 17592186044416, 17179869184, 4398046511104, 274877906944, 70368744177664, 8589934592, 2199023255552, 137438953472, 35184372088832, 34359738368, 8796093022208, 549755813888, 140737488355328, 281474976710656, 72057594037927936, 4503599627370496, 1152921504606846976, 1125899906842624, 288230376151711744, 18014398509481984, 4611686018427387904, 562949953421312, 144115188075855872, 9007199254740992, 2305843009213693952, 2251799813685248, 576460752303423488, 36028797018963968, 9223372036854775808]
def w5_s7 : List ℕ := [0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31, 32, 40, 48, 56, 33, 41, 49, 57, 34, 42, 50, 58, 35, 43, 51, 59, 36, 44, 52, 60, 37, 45, 53, 61, 38, 46, 54, 62, 39, 47, 55, 63]
def w5_p7 : List ℕ := [1, 256, 65536, 16777216, 2, 512, 131072, 33554432, 4, 1024, 262144, 67108864, 8, 2048, 524288, 134217728, 16, 4096, 1048576, 268435456, 32, 8192, 2097152, 536870912, 64, 16384, 4194304, 1073741824, 128, 32768, 8388608, 2147483648, 4294967296, 1099511627776, 281474976710656, 72057594037927936, 8589934592, 2199023255552, 562949953421312, 144115188075855872, 17179869184, 4398046511104, 1125899906842624, 288230376151711744, 34359738368, 8796093022208, 2251799813685248, 576460752303423488, 68719476736, 17592186044416, 4503599627370496, 1152921504606846976, 137438953472, 35184372088832, 9007199254740992, 2305843009213693952, 274877906944, 70368744177664, 18014398509481984, 4611686018427387904, 549755813888, 140737488355328, 36028797018963968, 9223372036854775808]
def w5_s8 : List ℕ := [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23, 8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31, 32, 48, 33, 49, 34, 50, 35, 51, 36, 52, 37, 53, 38, 54, 39, 55, 40, 56, 41, 57, 42, 58, 43, 59, 44, 60, 45, 61, 46, 62, 47, 63]
def w5_p8 : List ℕ := [1, 65536, 2, 131072, 4, 262144, 8, 524288, 16, 1048576, 32, 2097152, 64, 4194304, 128, 8388608, 256, 16777216, 512, 33554432, 1024, 67108864, 2048, 134217728, 4096, 268435456, 8192, 536870912, 16384, 1073741824, 32768, 2147483648, 4294967296, 281474976710656, 8589934592, 562949953421312, 17179869184, 1125899906842624, 34359738368, 2251799813685248, 68719476736, 4503599627370496, 137438953472, 9007199254740992, 274877906944, 18014398509481984, 549755813888, 36028797018963968, 1099511627776, 72057594037927936, 2199023255552, 144115188075855872, 4398046511104, 288230376151711744, 8796093022208, 576460752303423488, 17592186044416, 1152921504606846976, 35184372088832, 2305843009213693952, 70368744177664, 4611686018427387904, 140737488355328, 9223372036854775808]
def w5_s9 : List ℕ := [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31, 32, 48, 40, 56, 36, 52, 44, 60, 34, 50, 42, 58, 38, 54, 46, 62, 33, 49, 41, 57, 37, 53, 45, 61, 35, 51, 43, 59, 39, 55, 47, 63]
def w5_p9 : List ℕ := [1, 65536, 256, 16777216, 16, 1048576, 4096, 268435456, 4, 262144, 1024, 67108864, 64, 4194304, 16384, 1073741824, 2, 131072, 512, 33554432, 32, 2097152, 8192, 536870912, 8, 524288, 2048, 134217728, 128, 8388608, 32768, 2147483648, 4294967296, 281474976710656, 1099511627776, 72057594037927936, 68719476736, 4503599627370496, 17592186044416, 1152921504606846976, 17179869184, 1125899906842624, 4398046511104, 288230376151711744, 274877906944, 18014398509481984, 70368744177664, 4611686018427387904, 8589934592, 562949953421312, 2199023255552, 144115188075855872, 137438953472, 9007199254740992, 35184372088832, 2305843009213693952, 34359738368, 2251799813685248, 8796093022208, 576460752303423488, 549755813888, 36028797018963968, 140737488355328, 9223372036854775808]
def w5_idx : Array (List ℕ) := Array.mk [w5_s0, w5_s1, w5_s2, w5_s3, w5_s4, w5_s5, w5_s6, w5_s7, w5_s8, w5_s9]
def w5_pow : Array (List ℕ) := Array.mk [w5_p0, w5_p1, w5_p2, w5_p3, w5_p4, w5_p5, w5_p6, w5_p7, w5_p8, w5_p9]
def w5_inv : Array ℕ := Array.mk [0, 1, 2, 8, 4, 7, 6, 5, 3, 9]
theorem w5_G_valid : (List.range 10).all (symValid 64 10 w5_idx w5_pow w5_inv w5_goal) = true := by decide +kernel
def cfMask0 : BitVec 64 := 0x5555555555555555
def cfStock0 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def cfIdx0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62]
def cfMask1 : BitVec 64 := 0x3333333333333333
def cfStock1 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def cfIdx1 : List ℕ := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61]
def cfMask2 : BitVec 64 := 0xf0f0f0f0f0f0f0f
def cfStock2 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def cfIdx2 : List ℕ := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59]
def cfMask3 : BitVec 64 := 0xff00ff00ff00ff
def cfStock3 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def cfIdx3 : List ℕ := [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 32, 36, 34, 38, 33, 37, 35, 39, 48, 52, 50, 54, 49, 53, 51, 55]
def cfMask4 : BitVec 64 := 0xffff0000ffff
def cfStock4 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def cfIdx4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
def cfMask5 : BitVec 64 := 0xffffffff
def cfStock5 : List (BitVec 64) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def cfIdx5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def cfMasks : Array (BitVec 64) := Array.mk [cfMask0, cfMask1, cfMask2, cfMask3, cfMask4, cfMask5]
def cfStocks : Array (List (BitVec 64)) := Array.mk [cfStock0, cfStock1, cfStock2, cfStock3, cfStock4, cfStock5]

theorem cf_specs :
    (cfIdx0.length = 32 ∧ (∀ idx ∈ cfIdx0, idx < 64) ∧ (∀ idx ∈ cfIdx0, cfMask0.getLsbD idx = true) ∧ projS 32 cfIdx0 w5_goal = p4h_goal ∧ cfStock0.all (fun w => p4h_rows.contains (projS 32 cfIdx0 w)) = true) ∧
    (cfIdx1.length = 32 ∧ (∀ idx ∈ cfIdx1, idx < 64) ∧ (∀ idx ∈ cfIdx1, cfMask1.getLsbD idx = true) ∧ projS 32 cfIdx1 w5_goal = p4h_goal ∧ cfStock1.all (fun w => p4h_rows.contains (projS 32 cfIdx1 w)) = true) ∧
    (cfIdx2.length = 32 ∧ (∀ idx ∈ cfIdx2, idx < 64) ∧ (∀ idx ∈ cfIdx2, cfMask2.getLsbD idx = true) ∧ projS 32 cfIdx2 w5_goal = p4h_goal ∧ cfStock2.all (fun w => p4h_rows.contains (projS 32 cfIdx2 w)) = true) ∧
    (cfIdx3.length = 32 ∧ (∀ idx ∈ cfIdx3, idx < 64) ∧ (∀ idx ∈ cfIdx3, cfMask3.getLsbD idx = true) ∧ projS 32 cfIdx3 w5_goal = p4h_goal ∧ cfStock3.all (fun w => p4h_rows.contains (projS 32 cfIdx3 w)) = true) ∧
    (cfIdx4.length = 32 ∧ (∀ idx ∈ cfIdx4, idx < 64) ∧ (∀ idx ∈ cfIdx4, cfMask4.getLsbD idx = true) ∧ projS 32 cfIdx4 w5_goal = p4h_goal ∧ cfStock4.all (fun w => p4h_rows.contains (projS 32 cfIdx4 w)) = true) ∧
    (cfIdx5.length = 32 ∧ (∀ idx ∈ cfIdx5, idx < 64) ∧ (∀ idx ∈ cfIdx5, cfMask5.getLsbD idx = true) ∧ projS 32 cfIdx5 w5_goal = c5_goal  ∧ cfStock5.all (fun w => c5_rows.contains  (projS 32 cfIdx5 w)) = true) := by
  decide +kernel

theorem checkCofClose_sound_aux (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true)
    (stock : List (BitVec 64)) (g : BitVec 32) (hgnz : g ≠ 0) (rows : List (BitVec 32))
    (hg : projS 32 idxs w5_goal = g)
    (hstock : stock.all (fun w => rows.contains (projS 32 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 32) g 6 rows.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose fuel m stock hist nxt = true) :
    ¬ live (basicOps 64) w5_goal fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 32) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => (u &&& m) == 0)).length ≤ zCount (projS 32 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => (u &&& m) == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_mask 32 idxs m hm u, hu.2, projS_zero]
        have hrep := checkReplay_sound idxs hlen hlt m hm g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 32 idxs) stock.toFinset ⊆ rows.toFinset := by
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

theorem checkCofClose_sound (c fuel : ℕ) (hc : c < 6)
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup)
    (hchk : checkCofClose fuel (cfMasks[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true) :
    ¬ live (basicOps 64) w5_goal fuel nxt.toFinset := by
  have hp4_nz : p4h_goal ≠ 0 := by decide
  have hc5_nz : c5_goal ≠ 0 := by decide
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cf_specs
  match c with
  | 0 => exact checkCofClose_sound_aux cfIdx0 h0.1 h0.2.1 cfMask0 h0.2.2.1 cfStock0 p4h_goal hp4_nz p4h_rows h0.2.2.2.1 h0.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose_sound_aux cfIdx1 h1.1 h1.2.1 cfMask1 h1.2.2.1 cfStock1 p4h_goal hp4_nz p4h_rows h1.2.2.2.1 h1.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose_sound_aux cfIdx2 h2.1 h2.2.1 cfMask2 h2.2.2.1 cfStock2 p4h_goal hp4_nz p4h_rows h2.2.2.2.1 h2.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose_sound_aux cfIdx3 h3.1 h3.2.1 cfMask3 h3.2.2.1 cfStock3 p4h_goal hp4_nz p4h_rows h3.2.2.2.1 h3.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose_sound_aux cfIdx4 h4.1 h4.2.1 cfMask4 h4.2.2.1 cfStock4 p4h_goal hp4_nz p4h_rows h4.2.2.2.1 h4.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose_sound_aux cfIdx5 h5.1 h5.2.1 cfMask5 h5.2.2.1 cfStock5 c5_goal  hc5_nz c5_rows  h5.2.2.2.1 h5.2.2.2.2 c5_no_build  fuel hist nxt hnd hchk
  | c + 6 => omega

def checkChildW5 (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose (k - 1) (cfMasks[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW5 (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (a b : BitVec 64) (r : List (BitVec 64)) : Bool :=
  (ops 64 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 64 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 64 jumps6 w5_goal (w :: r) || checkChildW5 k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 64 jumps6 w5_goal (w :: a :: r) || checkChildW5 k cfs targets h' (w :: a :: r)) &&
       (!cover 64 jumps6 w5_goal (w :: b :: r) || checkChildW5 k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 64 jumps6 w5_goal (w :: a :: b :: r) || checkChildW5 k cfs targets h' (w :: a :: b :: r))

def checkNodeW5 (k : ℕ) (cur prev : Array W5Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains w5_goal) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c 6) &&
    hs.all (fun p => Nat.blt p.1 10 && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (w5_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW5 k extra cfs targets hist a b r)

def checkBlockW5 (k : ℕ) (cur prev : Array W5Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW5 k cur prev (start + m) && checkBlockW5 k cur prev start m

theorem checkBlockW5_at {k start m : ℕ} {cur prev : Array W5Node}
    (h : checkBlockW5 k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW5 k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem checkBlockW5_merge {k start a b : ℕ} {cur prev : Array W5Node}
    (h1 : checkBlockW5 k cur prev start a = true)
    (h2 : checkBlockW5 k cur prev (start + a) b = true) :
    checkBlockW5 k cur prev start (a + b) = true := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h2 ⊢
    exact ⟨by simpa [Nat.add_assoc] using h2.1, ih h2.2⟩

theorem node_sound_W5 {k i : ℕ} {cur prev : Array W5Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) w5_goal (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW5 k cur prev i = true) :
    ¬ live (basicOps 64) w5_goal k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW5 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (w5_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 64) w5_goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec w5_G_valid g hg).1
    have hinv_g := (actB_spec w5_G_valid (w5_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 64 (w5_pow[w5_inv[g]?.getD 0]?.getD [])) (actB_inj w5_G_valid _ hinv_lt)
      hinv_g (actB_ops w5_G_valid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 64 (w5_pow[g]?.getD []))).toFinset.image
        (actB 64 (w5_pow[w5_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left w5_G_valid g hg v]
      · intro hu; exact ⟨actB 64 (w5_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left w5_G_valid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : w5_goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
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
      have htail : live (basicOps 64) w5_goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 64 jumps6 w5_goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW5 at hstep
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
      have close (hc : checkChildW5 k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW5 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact checkCofClose_sound c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
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

theorem level_sound_W5 {k : ℕ} {cur prev : Array W5Node}
    (hk : 0 < k)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) w5_goal (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW5 k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 64) w5_goal k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W5 hk hi hprev (hblk i hi)


def w5_L4 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xfcfcfc00fcfcfc00,0xfff0fff0fff0fff0,0xffffccccffffcccc,0xffffffff00000000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfcfc00fcfcfc00,0xfcfcfcfcfcfcfcfc,0xffffff00ffffff00)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffff00cccccc00,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffff00cccccc00,0xffffff00ffffff00,0xffffffffcccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffffff0fcfcfcf0,0xffffffffffff0000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffff00cccccc00,0xffffff00ffffff00,0xffffffffcccccccc),(0xfffffff0fcfcfcf0,0xffffff00cccccc00,0xf0f0f0f0f0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[])
]
def w5_L5 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfc,0xfff0fff0fff0fff0,0xffffccccffffcccc,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc)],[1, 2],[(0,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffff00ffffff00,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfca8a8fcfca8a8,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xfcfca8a8fcfca8a8,0xfcfcfcfcfcfcfcfc,0xffffaaaaffffaaaa)],[],[(6,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xfffffffff0f0f0f0,0xffffffffffffaaaa],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfc0000,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfcfcfcfcfcfc0000,0xfcfcfcfcfcfcfcfc,0xffffffffffff0000)],[4],[(1,1)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0aaa0fff0aaa0,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfff0aaa0fff0aaa0,0xfff0fff0fff0fff0,0xffffaaaaffffaaaa)],[],[(2,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffffff0fffffff0,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfffffff0fffffff0,0xffff0000ffff0000,0xfff0fff0fff0fff0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 5],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffffafafffffafa,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffafafffffafa,0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[5],[]),
  ([0xeeee0000eeee,0x5555444455554444,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee),(0x5555444455554444,0xaaaaaaaaaaaaaaaa,0xffffeeeeffffeeee)],[],[]),
  ([0xeeee0000eeee,0x3333222233332222,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee),(0x3333222233332222,0xcccccccccccccccc,0xffffeeeeffffeeee)],[1],[]),
  ([0xffff0000fefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfefefefefefefefe,0xfcfcfcfcfcfcfcfc,0xaaaaaaaaaaaaaaaa),(0xfffffffffefefefe,0xfefefefefefefefe,0xffffffff00000000),(0xffff0000fefe,0xffff0000ffff0000,0xfffffffffefefefe)],[],[]),
  ([0xfafa0000fafa,0x5555505055555050,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa),(0x5555505055555050,0xaaaaaaaaaaaaaaaa,0xfffffafafffffafa)],[],[]),
  ([0xfafa0000fafa,0xf0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa),(0xf0f0a0a0f0f0a0a,0xf0f0f0f0f0f0f0f0,0xfffffafafffffafa)],[],[]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xfffffffffffffcfc,0xfffffcfcfffffcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffffffcfc)],[],[]),
  ([0xfcfc0000fcfc,0xf0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xf0f0a0a0f0f0a0a,0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaa)],[],[]),
  ([0xffff0000aaaa,0x5555555555550000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa),(0x5555555555550000,0xaaaaaaaaaaaaaaaa,0xffffffffffffaaaa)],[],[]),
  ([0xeeeeeeee,0x3333333322222222,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000),(0x3333333322222222,0xcccccccccccccccc,0xffffffffeeeeeeee),(0xeeeeeeee,0xffffffff00000000,0xffffffffeeeeeeee)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccaa88ffccaa88,0xffffff00ffffff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffccaa88ffccaa88,0xffffaaaaffffaaaa,0xffccffccffccffcc),(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0302ffff0302,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0x302030203020302,0xfcfcfcfcfcfcfcfc,0xffaaffaaffaaffaa),(0xffff0302ffff0302,0x302030203020302,0xffff0000ffff0000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaacccc8888,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffaaaacccc8888,0xffffaaaaffffaaaa,0xffffffffcccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaf0f0a0a0,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffaaaaf0f0a0a0,0xffffaaaaffffaaaa,0xfffffffff0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffeeeeffffee00,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xeeeeeeeeee00ee00,0xeeeeeeeeeeeeeeee,0xffffffffff00ff00),(0xffffeeeeffffee00,0xeeeeeeeeee00ee00,0xffff0000ffff0000)],[],[(7,2)]),
  ([0xffaa0000ffaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xffffffffff00ff00],[(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)],[0],[]),
  ([0xfafa0000fafa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[],[]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[],[]),
  ([0xffff0000cccc,0x3333333333330000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc),(0x3333333333330000,0xcccccccccccccccc,0xffffffffffffcccc)],[],[]),
  ([0xfafafafa,0xf0f0f0f0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000),(0xf0f0f0f0a0a0a0a,0xf0f0f0f0f0f0f0f0,0xfffffffffafafafa),(0xfafafafa,0xffffffff00000000,0xfffffffffafafafa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccf0f0c0c0,0xffffffffffff0000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffccccf0f0c0c0,0xffffccccffffcccc,0xfffffffff0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xdddd0000dcdc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0x5555555550505050,0xaaaaaaaaaaaaaaaa,0xfffffffff0f0f0f0),(0xdddddddddcdcdcdc,0x5555555550505050,0xcccccccccccccccc),(0xdddd0000dcdc,0xdddddddddcdcdcdc,0xffff0000ffff0000)],[],[])
]
def w5_L6 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa)],[0, 1],[(4,0)]),
  ([0xfafa0000fafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffff00ffffff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[(0,1)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)],[0, 1],[(0,2),(6,0)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfcfcfcfcfcfcfcfc)],[4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000,0xffffffffffff0000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[(0,4),(1,1),(2,3)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffffff0fffffff0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfffffff0fffffff0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0)],[0, 2],[]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0, 2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000,0xffffffffffffff00],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffff00,0xffffff00ffffff00,0xffffffff00000000)],[1],[(6,3)]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[3],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xfffffffffffff0f0],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfffffffffffff0f0,0xfffff0f0fffff0f0,0xffffffff00000000)],[0],[]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa)],[0, 2],[(0,5),(2,0)]),
  ([0xeeee0000eeee,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[1, 4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[(0,6)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xffffffffffffff00],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffff00,0xffffff00ffffff00,0xffffffff00000000)],[0, 1],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[],[]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffeeeeffffeeee,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffeeeeffffeeee,0xcccccccccccccccc,0xffffaaaaffffaaaa)],[1, 5],[(7,7)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[5],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[1],[(7,6),(7,7)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffafafffffafa,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffafafffffafa,0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaa)],[5],[(0,8)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfcfcfcfcfcfcfcfc)],[5],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[],[(0,8),(6,1)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffaaffffffaa,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffaaffffffaa,0xff00ff00ff00ff00,0xffffaaaaffffaaaa)],[0, 5],[]),
  ([0xeeee0000eeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[0, 4],[]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[1],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[5],[]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffeeeeffffeeee,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee)],[0, 1],[(0,9),(0,10)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffaaffffffaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xffffffaaffffffaa,0xffffaaaaffffaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffffffaaffffffaa)],[0],[(3,9),(9,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffefffefffefffe,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0),(0xfffefffefffefffe,0xfefefefefefefefe,0xff00ff00ff00ff00)],[],[]),
  ([0xfefe0000fefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfefefefefefefefe,0xfcfcfcfcfcfcfcfc,0xaaaaaaaaaaaaaaaa),(0xfefe0000fefe,0xfefefefefefefefe,0xffff0000ffff0000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffefefefe],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0),(0xfffffffffefefefe,0xfefefefefefefefe,0xffffffff00000000)],[3, 4],[(0,11),(4,11)]),
  ([0xfefefefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0),(0xfefefefe,0xfefefefefefefefe,0xffffffff00000000)],[],[]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee)],[0],[(0,10)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xffffffaaffffffaa,0xffffaaaaffffaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffffffaaffffffaa)],[0],[(3,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xaafeaafeaafeaafe,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xfc00fc00fc00fc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00),(0xaafeaafeaafeaafe,0xfc00fc00fc00fc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xe0e00000e0e,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xe0e00000e0e,0xeeee0000eeee,0xf0f0f0f0f0f0f0f0)],[0, 1],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaafffaaaaafffa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xfff00000fff0,0xfff0fff0fff0fff0,0xffff0000ffff0000),(0xaaaafffaaaaafffa,0xfff00000fff0,0xaaaaaaaaaaaaaaaa)],[3],[]),
  ([0xee000000ee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xee000000ee,0xeeee0000eeee,0xff00ff00ff00ff00)],[0],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000eeee],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xffffffff0000eeee,0xeeee0000eeee,0xffffffff00000000)],[],[]),
  ([0xeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xeeee,0xeeee0000eeee,0xffffffff00000000)],[0],[]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffafafffffafa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa)],[0],[(0,12),(0,13)]),
  ([0xffee0000ffee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00),(0xffee0000ffee,0xffff0000ffff0000,0xffeeffeeffeeffee)],[],[]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffcfcfffffcfc,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfffffcfcfffffcfc)],[0],[(2,13),(7,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffcfcfffffcfc,0xffffffff00000000,0xffffffffffff0000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[5],[(2,8),(7,8)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffeeffee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00),(0xffffffffffeeffee,0xffeeffeeffeeffee,0xffffffff00000000)],[],[(4,14)]),
  ([0xffeeffee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00),(0xffeeffee,0xffeeffeeffeeffee,0xffffffff00000000)],[],[]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa)],[0],[(0,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaafefeaaaafefe,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xaaaafefeaaaafefe,0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000fcfc],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffffff0000fcfc,0xfcfc0000fcfc,0xffffffff00000000)],[5],[]),
  ([0xfcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xfcfc,0xfcfc0000fcfc,0xffffffff00000000)],[],[]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000)],[0],[(0,15)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffffaaaa],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa)],[0],[(0,16),(1,17)]),
  ([0xffff0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000),(0xffff0000eeee,0xffff0000ffff0000,0xffffffffeeeeeeee)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xfffffffffff0fff0],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfffffffffff0fff0,0xfff0fff0fff0fff0,0xffffffff00000000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)],[0],[(4,3),(5,3)]),
  ([0xaaaaaaaaaaa0aaa0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffff0fff0],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfffffffffff0fff0,0xfff0fff0fff0fff0,0xffffffff00000000),(0xaaaaaaaaaaa0aaa0,0xaaaaaaaaaaaaaaaa,0xfffffffffff0fff0)],[],[(8,14)]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[],[]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[],[]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xfffffffffcfcfcfc],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[4],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffeeeeeeee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000),(0xeeeeeeee,0xffffffff00000000,0xffffffffeeeeeeee)],[0],[(0,17),(2,17)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa)],[0],[(1,17)]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaafefefefe,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xaaaaaaaafefefefe,0xfcfcfcfc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaafffafffa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfff0fff0,0xfff0fff0fff0fff0,0xffffffff00000000),(0xaaaaaaaafffafffa,0xfff0fff0,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeee0eee0eee0eee0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xeee0eee0eee0eee0,0xeeeeeeeeeeeeeeee,0xfff0fff0fff0fff0)],[0, 3],[(1,5),(8,2)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[3],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeee0e0eeeee0e0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xeeeee0e0eeeee0e0,0xeeeeeeeeeeeeeeee,0xfffff0f0fffff0f0)],[],[(8,18)]),
  ([0xfa000000fa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfa000000fa,0xffffff00ffffff00,0xfafafafafafafafa)],[1],[(1,19)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[0],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeee0e0e0e0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xeeeeeeeee0e0e0e0,0xeeeeeeeeeeeeeeee,0xfffffffff0f0f0f0)],[0, 5],[(8,20)]),
  ([0xff000000aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xff000000aa,0xffffff00ffffff00,0xffffffffaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeee00ee00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xeeeeeeeeee00ee00,0xeeeeeeeeeeeeeeee,0xffffffffff00ff00)],[0, 1, 2, 3, 4, 5],[(0,22),(1,21),(2,22),(3,4),(4,4),(8,21)]),
  ([0xff000000cc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xff000000cc,0xffffff00ffffff00,0xffffffffcccccccc)],[],[]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0],[(0,23)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 4, 5],[(0,3),(0,7),(0,8),(2,3),(2,8),(4,23),(7,24),(7,25),(9,24),(9,25)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000,0xffffffffcccccccc],[(0xffffccccffffcccc,0xcccccccccccccccc,0xffff0000ffff0000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[1, 4],[]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[5],[(0,24)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[],[(2,8),(5,1),(7,3)]),
  ([0xfafa0000fafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[],[(0,24)]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[],[(0,25)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[2, 5],[]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffeeeeffffeeee,0xaaaaaaaaaaaaaaaa,0xffffccccffffcccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee)],[0, 1, 4],[(0,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaafaaaffaafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xff00f000ff00f0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0),(0xaaffaafaaaffaafa,0xff00f000ff00f0,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xf0a00000f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xf0a00000f0a,0xffaa0000ffaa,0xf0f0f0f0f0f0f0f0)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000ffaa],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xffffffff0000ffaa,0xffaa0000ffaa,0xffffffff00000000)],[],[]),
  ([0xffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xffaa,0xffaa0000ffaa,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfac8fac8fac8fac8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xfac8fac8fac8fac8,0xfafafafafafafafa,0xffccffccffccffcc)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafac8c8c8c8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xfafafafac8c8c8c8,0xfafafafafafafafa,0xffffffffcccccccc)],[5],[]),
  ([0xf0f00000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xf0f00000f00,0xfffff0f0fffff0f0,0xffffffffff00ff00)],[],[]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xffffccccffffcccc,0xf0f0f0f0f0f0f0f0),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfffffcfcfffffcfc)],[0, 1],[(2,13)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xfffffafafffffafa,0xfffff0f0fffff0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa)],[0, 2],[(0,12)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaeeaaffaaee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffccccffffcccc,0xcccccccccccccccc,0xffff0000ffff0000),(0xff00cc00ff00cc,0xffffccccffffcccc,0xff00ff00ff00ff00),(0xaaffaaeeaaffaaee,0xff00cc00ff00cc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffeeaaaaffee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffcc0000ffcc,0xffccffccffccffcc,0xffff0000ffff0000),(0xaaaaffeeaaaaffee,0xffcc0000ffcc,0xaaaaaaaaaaaaaaaa)],[3],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000fafa],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000),(0xffffffff0000fafa,0xfafa0000fafa,0xffffffff00000000)],[],[]),
  ([0xfafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000),(0xfafa,0xfafa0000fafa,0xffffffff00000000)],[],[]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffffcccc],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc)],[0],[(0,26),(2,27)]),
  ([0xffff0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffffffffffaaffaa,0xffaaffaaffaaffaa,0xffffffff00000000),(0xffff0000ffaa,0xffff0000ffff0000,0xffffffffffaaffaa)],[],[]),
  ([0xffff0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000),(0xffff0000fafa,0xffff0000ffff0000,0xfffffffffafafafa)],[],[]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffffafafafa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000),(0xfafafafa,0xffffffff00000000,0xfffffffffafafafa)],[0],[(0,27),(4,27)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc)],[0, 1],[(2,27)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffffeeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffccccffffcccc,0xcccccccccccccccc,0xffff0000ffff0000),(0xffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xaaaaaaaaffffeeee,0xffffcccc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffeeffee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffccffcc,0xffccffccffccffcc,0xffffffff00000000),(0xaaaaaaaaffeeffee,0xffccffcc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafa00fa00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xfafafafafa00fa00,0xfafafafafafafafa,0xffffffffff00ff00)],[0, 5],[(8,28)]),
  ([0xf0f00000a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xf0f00000a0a,0xfffff0f0fffff0f0,0xffffffffaaaaaaaa)],[],[]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffffffaaaa,0xaaaaaaaaaaaaaaaa,0xffffffffffff0000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa)],[0],[(0,16)]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xfffffffffcfcfcfc,0xf0f0f0f0f0f0f0f0,0xffffffffcccccccc),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[1],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffffffffeeeeeeee,0xcccccccccccccccc,0xffffffffaaaaaaaa),(0xeeeeeeee,0xffffffff00000000,0xffffffffeeeeeeee)],[0],[(0,17)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaffaaffaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xff00ff00ff0000,0xff00ff00ff00ff00,0xffffffffffff0000),(0xaaffaaffaaffaaaa,0xff00ff00ff0000,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaffaafaaafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xff00ff00f000f0,0xff00ff00ff00ff00,0xfffffffff0f0f0f0),(0xaaffaaffaafaaafa,0xff00ff00f000f0,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffff0000ff00,0xffff0000ffff0000,0xffffffffff00ff00),(0xaaaaffffaaaaffaa,0xffff0000ff00,0xaaaaaaaaaaaaaaaa)],[3],[]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[2],[(0,25)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[5],[]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffffffcccc,0xcccccccccccccccc,0xffffffffffff0000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc)],[0],[(0,26)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfffffffffafafafa,0xf0f0f0f0f0f0f0f0,0xffffffffaaaaaaaa),(0xfafafafa,0xffffffff00000000,0xfffffffffafafafa)],[0],[(0,27)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaaeeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc),(0xaaaaffffaaaaeeee,0xffff0000cccc,0xaaaaaaaaaaaaaaaa)],[3],[(3,29)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaffaaeeaaee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xff00ff00cc00cc,0xff00ff00ff00ff00,0xffffffffcccccccc),(0xaaffaaffaaeeaaee,0xff00ff00cc00cc,0xaaaaaaaaaaaaaaaa)],[0],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaafafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffff0000f0f0,0xffff0000ffff0000,0xfffffffff0f0f0f0),(0xaaaaffffaaaafafa,0xffff0000f0f0,0xaaaaaaaaaaaaaaaa)],[],[])
]
def w5_L7 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0)],[0, 1, 2, 3, 4],[(0,3),(0,6),(0,10),(1,9),(2,4),(2,5),(4,7),(6,8),(7,11),(8,0),(8,2),(9,1)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00)],[0, 1, 2, 3, 4],[(0,0),(0,6),(0,12),(0,16),(1,15),(1,17),(3,13),(4,14),(5,15),(5,17),(6,0),(6,6),(6,16),(8,12),(8,14),(9,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[0, 1, 3, 4, 5],[(0,10),(0,16),(0,19),(0,21),(0,22),(0,24),(0,26),(1,20),(1,29),(2,23),(3,27),(3,28),(5,25),(6,2),(6,14),(9,18)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0)],[0, 1, 2, 3, 4, 5],[(0,32),(0,33),(0,34),(0,35),(1,26),(1,31),(2,19),(2,30),(4,32),(4,33),(5,6),(8,19),(8,30),(9,6)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0)],[0, 2],[(1,37),(2,30),(8,36)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000)],[0, 1, 2, 3, 4, 5],[(0,15),(0,20),(0,27),(0,30),(0,39),(0,41),(0,42),(0,43),(4,38),(6,40)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000)],[0, 1, 4],[(0,13),(0,30)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffeeffeeffeeffee,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00)],[0, 1, 2, 3, 4, 5],[(0,32),(0,45),(0,48),(0,49),(1,22),(1,44),(2,32),(2,45),(4,46),(4,47),(8,22),(8,44)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffeeffeeffeeffee,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00)],[3],[(1,50),(4,46),(8,50)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000)],[0, 1, 2, 3, 4, 5],[(0,23),(0,46),(0,51),(0,52),(0,53),(0,54),(4,41),(6,23),(6,51),(6,54),(8,41)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000)],[1, 2, 4],[(0,4),(0,46),(6,4)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffeeeeeeee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,34),(0,48),(0,56),(0,62),(1,55),(2,34),(2,56),(4,59),(4,60),(4,61),(6,57),(6,58),(7,8),(7,16),(8,55),(9,8),(9,16)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffeeeeeeee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[3, 5],[(0,62),(1,63),(4,64),(8,63)]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,9),(0,17),(0,43),(0,62),(2,9),(2,17),(2,43),(3,65),(4,53),(4,65),(6,66)]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[0, 1, 5],[(0,29),(0,62),(2,29)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)],[0, 1, 2, 3],[(0,32),(0,67),(1,6),(1,12),(2,41),(4,54),(5,6),(7,41),(8,3),(8,54)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000)],[0, 1, 2],[(0,39),(0,69),(1,0),(4,32),(7,68),(7,70),(8,0),(9,68)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[0, 1, 2],[(0,34),(0,72),(1,16),(2,19),(2,43),(5,14),(7,73),(8,21),(8,71)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 3, 5],[(0,48),(0,74),(1,10),(1,24),(3,5),(4,5),(4,47),(4,53),(6,57),(7,75),(8,10),(8,24)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000,0xffffffffffff0000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[1, 4, 5],[(0,8),(0,19),(0,47),(0,80),(1,78),(2,79),(2,83),(3,81),(3,82),(6,5),(6,22),(7,77),(8,76)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfefefefefefefefe,0xcccccccccccccccc,0xfafafafafafafafa)],[0, 1, 2],[(1,31),(2,84),(8,84)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0, 1, 2, 3, 4, 5],[(0,7),(0,31),(0,76),(0,86),(0,87),(0,88),(4,85),(6,7),(6,76),(6,86),(8,85)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0, 3, 4],[(0,31)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00)],[0, 1],[(0,32),(0,89),(1,86),(5,86)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[0, 1],[(0,34),(0,90),(1,26),(1,88),(5,91)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xfffafffafffafffa,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffafffafffafffa,0xfafafafafafafafa,0xff00ff00ff00ff00)],[0, 3],[(4,44),(5,93),(8,92)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000)],[0, 1, 2, 3, 4, 5],[(0,44),(0,68),(0,70),(0,79),(0,81),(0,96),(0,97),(6,95),(7,86),(8,94)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000)],[0, 2, 4],[(0,1),(0,44)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffafafafa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,34),(0,100),(0,101),(1,48),(1,99),(2,98),(4,100),(5,10),(7,48),(8,98),(9,10)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffafafafa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 5],[(0,101),(2,102),(8,102)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,11),(0,97),(0,101),(1,88),(2,103),(3,104),(4,11),(4,97),(6,104)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 2, 5],[(0,83),(0,101),(4,83)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 2, 3],[(0,105),(2,8),(3,2),(4,22),(4,97),(5,106),(7,48),(8,80)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa,0xffffffffeeeeeeee],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffffffffeeeeeeee,0xcccccccccccccccc,0xffffffffaaaaaaaa)],[0, 1, 3],[(0,109),(1,55),(3,108),(8,107)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[0, 1, 2, 3, 4, 5],[(0,28),(0,55),(0,73),(0,82),(0,106),(0,113),(4,111),(6,112),(7,91),(8,110)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[0, 4, 5],[(0,18),(0,55)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xfffffffff0f0f0f0],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[0, 2, 5],[(0,57),(0,113),(2,21),(2,114),(4,57),(4,113),(5,24),(5,77),(5,80),(8,21),(8,114),(9,24),(9,80)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa,0xfffffffffafafafa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfffffffffafafafa,0xf0f0f0f0f0f0f0f0,0xffffffffaaaaaaaa)],[0, 2],[(0,116),(2,98),(8,115)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[0, 1, 2, 3, 4, 5],[(0,25),(0,71),(0,75),(0,98),(0,117),(2,106),(4,118),(6,119),(8,73)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[1, 4, 5],[(0,78),(0,98),(0,114)])
]
def w5_L8 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)],[0, 1, 2, 3, 4, 5],[(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(1,0),(1,1),(1,2),(2,3),(2,4),(2,5),(2,6),(2,15),(2,17),(4,9),(4,10),(8,0),(8,1),(8,2)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0)],[0, 1, 2, 3, 4, 5],[(0,3),(0,20),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(1,7),(1,21),(1,22),(2,19),(4,23),(4,25),(4,26),(4,27),(4,32),(5,0),(5,16),(7,7),(8,19),(9,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,11),(0,28),(0,33),(0,34),(0,35),(0,36),(0,37),(1,11),(1,28),(1,33),(1,34),(1,35),(1,36),(1,37),(2,24),(2,38),(2,39),(3,38),(3,39),(4,17),(5,17),(6,32),(7,18),(7,32),(8,2),(8,19),(9,2),(9,19)])
]
def w5_L9 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[],[0, 1, 2, 3, 4, 5],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(6,2),(7,0),(7,1),(8,0),(8,1)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_4_0 : checkBlockW5 4 w5_L4 (Array.mk []) 0 3 = true := by decide +kernel
theorem w5_chk_4 : ∀ i < w5_L4.size, checkNodeW5 4 w5_L4 (Array.mk []) i = true :=
  fun i hi => checkBlockW5_at w5_chk_4_0 i (Nat.zero_le _) (by simpa [w5_L4] using hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_5_0 : checkBlockW5 5 w5_L5 w5_L4 0 30 = true := by decide +kernel
theorem w5_chk_5 : ∀ i < w5_L5.size, checkNodeW5 5 w5_L5 w5_L4 i = true :=
  fun i hi => checkBlockW5_at w5_chk_5_0 i (Nat.zero_le _) (by simpa [w5_L5] using hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_0 : checkBlockW5 6 w5_L6 w5_L5 0 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_30 : checkBlockW5 6 w5_L6 w5_L5 30 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_60 : checkBlockW5 6 w5_L6 w5_L5 60 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_90 : checkBlockW5 6 w5_L6 w5_L5 90 30 = true := by decide +kernel
theorem w5_chk_6 : ∀ i < w5_L6.size, checkNodeW5 6 w5_L6 w5_L5 i = true := by
  intro i hi
  have hsz : i < 120 := by simpa [w5_L6] using hi
  by_cases h0 : i < 30
  · exact checkBlockW5_at w5_chk_6_0 i (by omega) (by omega)
  ·
    by_cases h1 : i < 60
    · exact checkBlockW5_at w5_chk_6_30 i (by omega) (by omega)
    ·
      by_cases h2 : i < 90
      · exact checkBlockW5_at w5_chk_6_60 i (by omega) (by omega)
      ·
        exact checkBlockW5_at w5_chk_6_90 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_7_0 : checkBlockW5 7 w5_L7 w5_L6 0 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_7_30 : checkBlockW5 7 w5_L7 w5_L6 30 10 = true := by decide +kernel
theorem w5_chk_7 : ∀ i < w5_L7.size, checkNodeW5 7 w5_L7 w5_L6 i = true := by
  intro i hi
  have hsz : i < 40 := by simpa [w5_L7] using hi
  by_cases h0 : i < 30
  · exact checkBlockW5_at w5_chk_7_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at w5_chk_7_30 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_8_0 : checkBlockW5 8 w5_L8 w5_L7 0 3 = true := by decide +kernel
theorem w5_chk_8 : ∀ i < w5_L8.size, checkNodeW5 8 w5_L8 w5_L7 i = true :=
  fun i hi => checkBlockW5_at w5_chk_8_0 i (Nat.zero_le _) (by simpa [w5_L8] using hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_9_0 : checkBlockW5 9 w5_L9 w5_L8 0 1 = true := by decide +kernel
theorem w5_chk_9 : ∀ i < w5_L9.size, checkNodeW5 9 w5_L9 w5_L8 i = true :=
  fun i hi => checkBlockW5_at w5_chk_9_0 i (Nat.zero_le _) (by simpa [w5_L9] using hi)

theorem w5_L4_sound : ∀ i < w5_L4.size, ¬ live (basicOps 64) w5_goal 4 (w5_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) (fun j hj => by simp at hj) w5_chk_4
theorem w5_L5_sound : ∀ i < w5_L5.size, ¬ live (basicOps 64) w5_goal 5 (w5_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L4_sound w5_chk_5
theorem w5_L6_sound : ∀ i < w5_L6.size, ¬ live (basicOps 64) w5_goal 6 (w5_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L5_sound w5_chk_6
theorem w5_L7_sound : ∀ i < w5_L7.size, ¬ live (basicOps 64) w5_goal 7 (w5_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L6_sound w5_chk_7
theorem w5_L8_sound : ∀ i < w5_L8.size, ¬ live (basicOps 64) w5_goal 8 (w5_L8[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L7_sound w5_chk_8
theorem w5_L9_sound : ∀ i < w5_L9.size, ¬ live (basicOps 64) w5_goal 9 (w5_L9[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L8_sound w5_chk_9

theorem w5_sublists : w5_rows.sublists.filter (fun ws => cover 64 jumps6 w5_goal ws) = [w5_rows] := by decide +kernel
theorem w5_top_match : sameSet (w5_rows.map (actB 64 (w5_pow[0]?.getD []))) (w5_L9[0]?.getD ([], [], [], [])).1 = true := by decide +kernel

theorem w5_no_build : ¬ build (basicOps 64) w5_goal 9 w5_rows.toFinset :=
  no_build_of_root w5_G_valid (by decide) w5_sublists w5_top_match (w5_L9_sound 0 (by decide))


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W7 := BitVec 128
abbrev basicOps7 (a b : W7) : Finset W7 := (ops 128 a b).toFinset

def holds (av : Finset W7) (z : W7) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W7} {z a : W7} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W7} {z : W7} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W7) (z : W7) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps7 a b, holds (insert w av) z

theorem reachable_not {av : Finset W7} {z : W7} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset W7} {x y : W7} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W7) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W7) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y); rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W7) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128); rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W7) (hw : w ∈ basicOps7 a b) (z : W7) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps7, ops] : a &&& b ∈ basicOps7 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps7, ops] : a &&& ~~~b ∈ basicOps7 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps7, ops] : b &&& ~~~a ∈ basicOps7 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps7, ops] : a ||| b ∈ basicOps7 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W7} {x y : W7} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit7 (k : Fin 128) (z : W7) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit7 (w : List W7) (i : ℕ) (k : Fin 128) :
    (w.map (bit7 k)).getD i false = bit7 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit7]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W7) (g : Gate) : W7 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W7) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit7 k)) g = (w ++ [action w g]).map (bit7 k) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W7)[k.val] = false := by simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit7, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit7, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W7} {w : List W7} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

theorem gate_reach (w : List W7) (av : Finset W7) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W7, x ||| (0 : W7) = x from fun x => BitVec.or_zero,
    show ∀ x : W7, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

def goal7 : W7 := 0xfffffffefffffffefffffffefefceea0
def rows7 : List W7 := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def idx76 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W7) (av : Finset W7) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit7 k))).getD out false = bit7 k goal7) :
    ∃ t, (t = goal7 ∨ t = ~~~goal7) ∧ build basicOps7 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal7 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil, read_bit7, bit7] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal7 ≠ 0) zero)
    · exact False.elim ((by decide : goal7 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W7 => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit7 k))).getD out false = bit7 k goal7 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W7) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
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

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)

theorem sample7_ok : ∀ k : Fin 128, F (fun i => (rows7.getD i.val 0)[k.val]) = goal7[k.val] := by decide +kernel
theorem idx76_spec : idx76.length = 64 ∧ ∀ idx ∈ idx76, idx < 128 := by decide
theorem projS76_goal7 : projS 64 idx76 goal7 = w5_goal := by decide +kernel
theorem projS76_x5 : projS 64 idx76 (rows7.getD 5 0) = 0 := by decide +kernel
theorem projS76_rows7_sub : rows7.all (fun w => projS 64 idx76 w == 0 || w5_rows.contains (projS 64 idx76 w)) = true := by decide +kernel
theorem x5_ess_only : rows7.all (fun w => w == rows7.getD 5 0 || w.getLsbD 1 == w.getLsbD 33) = true := by decide +kernel
theorem goal7_diff_1_33 : goal7.getLsbD 1 ≠ goal7.getLsbD 33 := by decide

theorem ops7_diff133 (a b z : W7) (hz : z ∈ basicOps7 a b)
    (hd : z.getLsbD 1 ≠ z.getLsbD 33) : a.getLsbD 1 ≠ a.getLsbD 33 ∨ b.getLsbD 1 ≠ b.getLsbD 33 := by
  simp only [basicOps7, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      show (1 : ℕ) < 128 by decide, show (33 : ℕ) < 128 by decide, decide_true, Bool.true_and, ha, hb]

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows7, holds rows7.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (rows7.map (bit7 k))).getD o false = bit7 k goal7 := by
    let x (i : Fin 7) : Bool := bit7 k (rows7.getD i.val 0)
    have same : List.ofFn x = rows7.map (bit7 k) := by
      apply List.ext_getElem
      · simp [rows7]
      · intro i hi hj
        have hlt : i < rows7.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows7.map (bit7 k)) = bit7 k goal7
    rw [← same, he]
    exact sample7_ok k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows7 rows7.toFinset init evaluate
  obtain ⟨s, hs, hl⟩ := compress (build_mono_k low run)
  have hdt : t.getLsbD 1 ≠ t.getLsbD 33 := by
    rcases ht with rfl | rfl
    · exact goal7_diff_1_33
    · intro h
      have hgd := goal7_diff_1_33
      simp only [BitVec.getLsbD_not, show (1 : ℕ) < 128 by decide, show (33 : ℕ) < 128 by decide,
        decide_true, Bool.true_and] at h
      cases h1 : goal7.getLsbD 1 <;> cases h2 : goal7.getLsbD 33 <;>
        simp only [h1, h2, Bool.not_true, Bool.not_false] at h hgd <;>
        first | exact Bool.noConfusion h | exact hgd rfl
  obtain ⟨w, hw, hdw⟩ := live_separates (fun u : W7 => u.getLsbD 1 ≠ u.getLsbD 33) hdt ops7_diff133 hl
  have hw_eq : w = rows7.getD 5 0 := by
    have h1 := List.all_eq_true.mp x5_ess_only w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    exact h1.resolve_right hdw
  have hx5_mem : rows7.getD 5 0 ∈ s.filter (fun u => projS 64 idx76 u = 0) :=
    Finset.mem_filter.mpr ⟨hw_eq ▸ hw, projS76_x5⟩
  have hzc_pos : 1 ≤ zCount (projS 64 idx76) s := Finset.one_le_card.mpr ⟨_, hx5_mem⟩
  have hpt : projS 64 idx76 t = w5_goal := by
    rcases ht with rfl | rfl
    · exact projS76_goal7
    · rw [projS_not 64 (by decide) idx76 idx76_spec.1 idx76_spec.2]; exact projS76_goal7
  have hw5_nz : w5_goal ≠ 0 := by decide
  have hb64 := live_restrict (by decide : 0 < 64) idx76 idx76_spec.1 idx76_spec.2
    (fun a b z hz => List.mem_toFinset.mp hz) hpt hw5_nz hl
  have hsub64 : nonZeroImg (projS 64 idx76) s ⊆ w5_rows.toFinset := by
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu
    obtain ⟨hne, v, hv, rfl⟩ := hu
    have h1 := List.all_eq_true.mp projS76_rows7_sub v (List.mem_toFinset.mp (hs hv))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact w5_no_build (build_mono_k (by omega) (build_mono_av hsub64 hb64))
end PEqualNP.Outside.L_meta_29194.Leaf10732.Src

namespace PEqualNP.Outside.L_meta_29194.Leaf10732.Wire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def paid (g : Gate) : Bool := match g.op with | .not => false | _ => true

def addr {n : ℕ} (m : ℕ) (σ : Fin n → Fin m) (i : ℕ) :=
  if hi : i < n then (σ ⟨i,hi⟩).val else m + (i-n)

def rename (p : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map p⟩
def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem get_rename {n m : ℕ} (σ : Fin n → Fin m) (a b t : List Bool)
    (ha : a.length = n) (hb : b.length = m)
    (h : ∀ j : Fin n, a.getD j.val false = b.getD (σ j).val false) (i : ℕ) :
    (a++t).getD i false = (b++t).getD (addr m σ i) false := by
  by_cases hi : i < n
  · have hi' : i < a.length := ha.symm ▸ hi
    have hk : (σ ⟨i,hi⟩).val < b.length := hb.symm ▸ (σ ⟨i,hi⟩).isLt
    simpa only [addr,dif_pos hi,List.getD_eq_getElem?_getD,List.getElem?_append_left hi',
      List.getElem?_append_left hk] using h ⟨i,hi⟩
  · have hi' : a.length ≤ i := by omega
    have hk : b.length ≤ m+(i-n) := by omega
    simp only [addr,dif_neg hi,List.getD_eq_getElem?_getD,List.getElem?_append_right hi',
      List.getElem?_append_right hk,ha,hb,Nat.add_sub_cancel_left]

theorem simulate {n m : ℕ} (σ : Fin n → Fin m) (a b : List Bool)
    (ha : a.length = n) (hb : b.length = m)
    (h : ∀ j : Fin n, a.getD j.val false = b.getD (σ j).val false)
    (gs : List Gate) (t : List Bool) :
    ∃ z : List Bool, gs.foldl step (a++t) = a++z ∧
      (gs.map (rename (addr m σ))).foldl step (b++t) = b++z := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => (a++t).getD i false))
    have he : (rename (addr m σ) g).op.eval
        ((rename (addr m σ) g).inputs.map (fun i => (b++t).getD i false)) = v := by
      simp only [v,rename,List.map_map,Function.comp_def,get_rename σ a b t ha hb h]
    obtain ⟨z,haz,hbz⟩ := ih (t ++ [v])
    refine ⟨z,?_,?_⟩
    · simpa [step,List.append_assoc,v] using haz
    · simp only [List.map_cons,List.foldl_cons,step,he,List.append_assoc]
      exact hbz

def orGate {m : ℕ} (u v : Fin m) : Gate := ⟨.or,[u.val,v.val]⟩
def expand {n m : ℕ} (σ : Fin n → Fin (m+1)) (u v : Fin m) (C : Circuit) : Circuit :=
  ⟨orGate u v :: C.gates.map (rename (addr (m+1) σ)), addr (m+1) σ C.output⟩

def pull {n m : ℕ} (σ : Fin n → Fin (m+1)) (u v : Fin m) (x : Fin m → Bool) (j : Fin n) :=
  if h : (σ j).val < m then x ⟨(σ j).val,h⟩ else x u || x v

theorem eval_expand {n m : ℕ} (σ : Fin n → Fin (m+1)) (u v : Fin m) (C : Circuit)
    (x : Fin m → Bool) :
    (expand σ u v C).eval (List.ofFn x) = C.eval (List.ofFn (pull σ u v x)) := by
  let a := List.ofFn (pull σ u v x)
  let b := List.ofFn x ++ [x u || x v]
  have ha : a.length = n := by simp [a]
  have hb : b.length = m+1 := by simp [b]
  have hw (j : Fin n) : a.getD j.val false = b.getD (σ j).val false := by
    by_cases hj : (σ j).val < m
    · have ht : (σ j).val < (List.ofFn x).length := by simpa using hj
      simp [a,b,pull,hj,List.getD_eq_getElem?_getD,List.getElem?_append_left ht]
    · have hh : (σ j).val = m := by have := (σ j).isLt; omega
      simp [a,b,pull,hj,hh,List.getD_eq_getElem?_getD,List.getElem?_append_right]
  obtain ⟨z,haz,hbz⟩ := simulate σ a b ha hb hw C.gates []
  simp only [List.append_nil] at haz hbz
  have he : step (List.ofFn x) (orGate u v) = b := by
    simp [step,orGate,GateOp.eval,b,List.getD_eq_getElem?_getD]
  change ((C.gates.map (rename (addr (m+1) σ))).foldl step (step (List.ofFn x) (orGate u v))).getD _ false =
    (C.gates.foldl step a).getD _ false
  rw [he,haz,hbz]; exact (get_rename σ a b z ha hb hw C.output).symm

theorem fit_expand {n m : ℕ} (σ : Fin n → Fin (m+1)) (u v : Fin m) (C : Circuit)
   (hf : FanInTwo C) : FanInTwo (expand σ u v C) := by
  intro g hg
  change g ∈ _ :: _ at hg
  rcases List.mem_cons.mp hg with he | hm
  · subst g; simp [orGate]
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    simpa [rename] using hf q hq

theorem cost_expand {n m : ℕ} (σ : Fin n → Fin (m+1)) (u v : Fin m) (C : Circuit) :
    (expand σ u v C).gates.countP paid = C.gates.countP paid+1 := by
  change (orGate u v :: C.gates.map (rename (addr (m+1) σ))).countP paid = _
  rw [List.countP_cons_of_pos (by rfl : paid (orGate u v)),List.countP_map]
  rfl

end PEqualNP.Outside.L_meta_29194.Leaf10732.Wire

namespace PEqualNP.Outside.L_meta_29194.Leaf10732
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def graph6 (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 4) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)
def coords : Fin 6 → Fin 8 := ![0, 1, 2, 3, 4, 7]
theorem lower (C : Circuit) (hf : FanInTwo C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph6 x) :
      10 ≤ C.gates.countP Wire.paid := by
  let D := Wire.expand coords (5 : Fin 7) (6 : Fin 7) C
  have hD : FanInTwo D := Wire.fit_expand _ _ _ _ hf
  have iden : ∀ x : Fin 7 → Bool, graph6 (Wire.pull coords (5 : Fin 7) (6 : Fin 7) x) = Src.F x := by decide +kernel
  have eq : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x) = Src.F x := fun x =>
    (Wire.eval_expand _ _ _ _ _).trans ((hc _).trans (iden x))
  have toll : D.gates.countP Wire.paid = C.gates.countP Wire.paid + 1 := Wire.cost_expand _ _ _ _
  have legal : ∀ g ∈ D.gates, Src.legal g := by
    simpa only [FanInTwo,Src.legal,Set.mem_insert_iff,Set.mem_singleton_iff] using hD
  have low := Src.bound D.gates D.output legal eq
  have he : Src.binaryCost D.gates = D.gates.countP Wire.paid := by
    rw [List.countP_eq_length_filter]
    rfl
  rw [he,toll] at low
  omega
end PEqualNP.Outside.L_meta_29194.Leaf10732

namespace PEqualNP.Outside.L_meta_29194
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace RecCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rcStep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) : List Gate × List (Bool ⊕ ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (out, env ++ [Sum.inl true])
    | i :: _ =>
      match env.getD i (Sum.inl false) with
      | Sum.inl b => (out, env ++ [Sum.inl (!b)])
      | Sum.inr w' => (out ++ [{ op := GateOp.not, inputs := [w'] }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.and =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) then
      (out, env ++ [Sum.inl false])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl true])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.and, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.or =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) then
      (out, env ++ [Sum.inl true])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl false])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.or, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | _ => (out, env ++ [Sum.inl false])

def rcCircuit (nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (gs : List Gate) (o : ℕ) : List Gate × ℕ :=
  let res := gs.foldl (rcStep nOut) ([], env0)
  match res.2.getD o (Sum.inl false) with
  | Sum.inr w' => (res.1, w')
  | Sum.inl false => (res.1, nOut + res.1.length)
  | Sum.inl true => (res.1 ++ [{ op := GateOp.not, inputs := [] }], nOut + res.1.length)

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t; omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]; omega

lemma rcStep_env_len (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (rcStep nOut st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]
    cases g.inputs with
    | nil => simp
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) <;> simp
  · simp [rcStep, h]
  · simp [rcStep, h]

lemma rcStep_legal (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, legal g') (hg : legal g) :
    ∀ g' ∈ (rcStep nOut st g).1, legal g' := by
  rcases st with ⟨out, env⟩
  dsimp only at h1 ⊢
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    cases g.inputs with
    | nil => exact h1
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => exact h1
      | inr w' =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · exact ⟨by simp, by simp⟩

lemma rcFold_legal (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ))
    (h1 : ∀ g' ∈ st.1, legal g') (hM : ∀ g ∈ gs, legal g) :
    ∀ g' ∈ (gs.foldl (rcStep nOut) st).1, legal g' := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rcStep nOut st g) (rcStep_legal nOut st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma binaryCost_append_one (gs : List Gate) (g : Gate) :
    binaryCost (gs ++ [g]) = binaryCost gs + (if isBinary g then 1 else 0) := by
  unfold binaryCost
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isBinary g <;> simp

lemma rcStep_binCost_le (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    binaryCost (rcStep nOut st g).1 ≤ binaryCost st.1 + (if isBinary g then 1 else 0) := by
  rcases st with ⟨out, env⟩
  dsimp only
  cases h : g.op
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases g.inputs with
    | nil => dsimp only; exact le_refl _
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => dsimp only; exact le_refl _
      | inr w' => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp [rcStep, h, isBinary]
  · simp [rcStep, h, isBinary]

lemma rcFold_binCost_le (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ)) :
    binaryCost (gs.foldl (rcStep nOut) st).1 ≤ binaryCost st.1 + binaryCost gs := by
  induction gs generalizing st with
  | nil => simp [binaryCost]
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    omega

lemma rcFold_eval_inv (nOut : ℕ) (gs : List Gate) (ys : List Bool) (hyl : ys.length = nOut)
    (hM : ∀ g ∈ gs, legal g) (ws : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i (Sum.inl false) with
      | Sum.inl b => ws.getD i false = b
      | Sum.inr w' => w' < nOut + st.1.length ∧ ws.getD i false = (st.1.foldl step ys).getD w' false) :
    let ws' := gs.foldl step ws
    let st' := gs.foldl (rcStep nOut) st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i (Sum.inl false) with
      | Sum.inl b => ws'.getD i false = b
      | Sum.inr w' => w' < nOut + st'.1.length ∧ ws'.getD i false = (st'.1.foldl step ys).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (step ws g).length = env.length + 1 := by simp [step, hlen_ws]
    have hget_old : ∀ i < env.length, (step ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (step ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (step ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (step ws g).length = (rcStep nOut (out, env) g).2.length ∧
        ∀ i, match (rcStep nOut (out, env) g).2.getD i (Sum.inl false) with
          | Sum.inl b => (step ws g).getD i false = b
          | Sum.inr w' => w' < nOut + (rcStep nOut (out, env) g).1.length ∧
              (step ws g).getD i false = ((rcStep nOut (out, env) g).1.foldl step ys).getD w' false := by
      constructor
      · rw [rcStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl step ys) = step (out.foldl step ys) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + out.length ∧ (step ws g).getD i false = (out.foldl step ys).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]; exact hinv i
        have hkeep_old_app : ∀ (x : Bool ⊕ ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + (out ++ [gnew]).length ∧
                (step ws g).getD i false = ((out ++ [gnew]).foldl step ys).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i (Sum.inl false) with
          | inl b => rw [hm] at hk; exact hk
          | inr w' =>
            rw [hm] at hk; dsimp only at hk
            have hw' : w' < nOut + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
            have hlen_w : (step (out.foldl step ys) gnew).length = nOut + out.length + 1 := by simp [step, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl step ys).length),
                List.getD_eq_getElem _ _ (by omega : w' < (step (out.foldl step ys) gnew).length)]
            simp [step, List.getElem_append_left (by omega : w' < (out.foldl step ys).length)]
        have hkeep_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none),
            w' < nOut + out.length := by
          intro w' hw'
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
          have hij := hinv j
          cases hm : env.getD j (Sum.inl false) with
          | inl b => rw [hm] at hj; cases hj
          | inr w0 =>
            rw [hm] at hj hij; dsimp only at hij
            cases hj; exact hij.1
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl false) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl false), hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjf⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjf hj'; dsimp only at hj'
                  cases b with
                  | false => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                  | true => simp at hjf
                | inr w' => rw [hm] at hjf; simp at hjf
              · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
          · have hand_eq : (g.inputs.map fun j => ws.getD j false).all id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).all id := by
              have hnof : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl false := by
                intro j hj heqf
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqf]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl false) →
                  (l.map fun j => ws.getD j false).all id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).all id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnf
                  have ha := hnf a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnf j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | false => exact absurd hm ha
                    | true =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia, Bool.true_and, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnof
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hand_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl true) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop]; simpa [GateOp.eval] using hand_eq
                · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl true), hget_last, hop]
                simp only [GateOp.eval, List.any_eq_true, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjt⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjt hj'; dsimp only at hj'
                  cases b with
                  | true => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hj'⟩
                  | false => simp at hjt
                | inr w' => rw [hm] at hjt; simp at hjt
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          · have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).any id := by
              have hnot : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl true := by
                intro j hj heqt
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqt]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl true) →
                  (l.map fun j => ws.getD j false).any id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).any id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnt
                  have ha := hnt a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | true => exact absurd hm ha
                    | false =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnot
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl false) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl false), hget_last, hop]; simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          cases hgi : g.inputs with
          | nil =>
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop, hgi]; rfl
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          | cons j rest_i =>
            dsimp only
            cases hm : env.getD j (Sum.inl false) with
            | inl b =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl (!b)) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl (!b)), hget_last, hop, hgi]; simpa [GateOp.eval] using hj'
                · rw [hkeep_hi (Sum.inl (!b)) i (by omega)]; exact hget_hi i (by omega)
            | inr w' =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (Sum.inr (nOut + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hgi, hfold_app]
                  have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                  simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hj'.2
                · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step ws g) (rcStep nOut (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma rcFold_inr_agree (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = st.2.length) (hylen : wy.length = st.2.length)
    (heq_cost : binaryCost (gs.foldl (rcStep nOut) st).1 = binaryCost st.1 + binaryCost gs)
    (hagree : ∀ i w', st.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false) :
    ∀ i w', (gs.foldl (rcStep nOut) st).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false := by
  induction gs generalizing wx wy st with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons] at heq_cost ⊢
    have hg := hM g List.mem_cons_self
    have h1 := rcFold_binCost_le nOut rest (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hstep_cost : binaryCost (rcStep nOut st g).1 = binaryCost st.1 + (if isBinary g then 1 else 0) := by omega
    have hrest_cost : binaryCost (rest.foldl (rcStep nOut) (rcStep nOut st g)).1 =
        binaryCost (rcStep nOut st g).1 + binaryCost rest := by omega
    rcases st with ⟨out, env⟩
    dsimp only at hxlen hylen hagree hstep_cost
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step wx g) (step wy g)
      (rcStep nOut (out, env) g) (by rw [rcStep_env_len]; simp [step, hxlen])
      (by rw [rcStep_env_len]; simp [step, hylen]) hrest_cost ?_
    have hget_old_x : ∀ i < env.length, (step wx g).getD i false = wx.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < env.length, (step wy g).getD i false = wy.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : (step wx g).getD env.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : (step wy g).getD env.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hall_inr_of_len2 :
        (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 →
        ∀ j ∈ g.inputs, ∃ w0, env.getD j (Sum.inl false) = Sum.inr w0 := by
      intro hl2 j hj
      cases hm : env.getD j (Sum.inl false) with
      | inr w0 => exact ⟨w0, rfl⟩
      | inl b =>
        exfalso
        have hlt := list_filterMap_len_lt (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
          g.inputs j hj (by rw [hm])
        have hcap := hg.2
        omega
    have hstep_env_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
        (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x i hi => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
      simp [List.getElem_append_left hi]
    have hstep_env_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
        (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
      List.getD_eq_default _ _ (by simp; omega)
    have hstep_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    intro i w' hiw'
    by_cases hi : i < env.length
    · have h1 : (rcStep nOut (out, env) g).2.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
        cases h : g.op
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; cases g.inputs with
          | nil => exact hstep_env_old _ i hi
          | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
      rw [h1] at hiw'
      rw [hget_old_x i hi, hget_old_y i hi]
      exact hagree i w' hiw'
    · by_cases heq : i = env.length
      · subst heq
        rw [hget_last_x, hget_last_y]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop] at hiw'
          cases hgi : g.inputs with
          | nil =>
            rw [hgi] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
          | cons j rest_i =>
            rw [hgi] at hiw'; dsimp only at hiw'
            cases hm : env.getD j (Sum.inl false) with
            | inl b => rw [hm] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
            | inr w0 =>
              rw [hop]
              simp only [GateOp.eval, List.map_cons, List.headD_cons, hagree j w0 hm]
      · exfalso
        have hlen_st : (rcStep nOut (out, env) g).2.length = env.length + 1 := rcStep_env_len nOut (out, env) g
        rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'

lemma rcCircuit_props (nIn nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (hlen0 : env0.length = nIn)
    (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g) :
    let res := rcCircuit nOut env0 gs o
    (∀ g ∈ res.1, legal g) ∧
    binaryCost res.1 ≤ binaryCost gs ∧
    (∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      Circuit.eval ⟨res.1, res.2⟩ ys = Circuit.eval ⟨gs, o⟩ xs) := by
  dsimp only [rcCircuit]
  have hfold_leg := rcFold_legal nOut gs ([], env0) (by intro g h; cases h) hM
  have hfold_bc : binaryCost (gs.foldl (rcStep nOut) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le nOut gs ([], env0); simpa [binaryCost] using this
  have hcore_eval : ∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      ∀ i, match (gs.foldl (rcStep nOut) ([], env0)).2.getD i (Sum.inl false) with
        | Sum.inl b => (gs.foldl step xs).getD i false = b
        | Sum.inr w' => w' < nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length ∧
            (gs.foldl step xs).getD i false = ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD w' false := by
    intro xs ys hxl hyl hinit
    have hinit' : ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut + (([] : List Gate), env0).1.length ∧ xs.getD i false = ((([] : List Gate), env0).1.foldl step ys).getD w' false := by
      intro i
      by_cases hi : i < nIn
      · simpa using hinit i hi
      · dsimp only
        rw [List.getD_eq_default _ _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
    exact (rcFold_eval_inv nOut gs ys hyl hM xs ([], env0) (by simp [hlen0, hxl]) hinit').2
  cases hm : (gs.foldl (rcStep nOut) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    refine ⟨hfold_leg, hfold_bc, ?_⟩
    intro xs ys hxl hyl hinit
    have h := hcore_eval xs ys hxl hyl hinit o
    rw [hm] at h; exact h.2.symm
  | inl b =>
    cases b with
    | false =>
      refine ⟨hfold_leg, hfold_bc, ?_⟩
      intro xs ys hxl hyl hinit
      have h := hcore_eval xs ys hxl hyl hinit o
      rw [hm] at h
      change ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
        (gs.foldl step xs).getD o false
      rw [h, List.getD_eq_default _ _ (by rw [wfold_len, hyl])]
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with h | rfl
        · exact hfold_leg g h
        · exact ⟨by simp, by decide⟩
      · rw [binaryCost_append_one]; simp [isBinary]; exact hfold_bc
      · intro xs ys hxl hyl hinit
        have h := hcore_eval xs ys hxl hyl hinit o
        rw [hm] at h
        change (((gs.foldl (rcStep nOut) ([], env0)).1 ++ [({ op := GateOp.not, inputs := [] } : Gate)]).foldl step ys).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
          (gs.foldl step xs).getD o false
        rw [h, List.foldl_append]
        change (step ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys) ({ op := GateOp.not, inputs := [] } : Gate)).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false = true
        have hlen : ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).length =
            nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length := by rw [wfold_len, hyl]
        rw [← hlen, List.getD_eq_getElem _ _ (by simp [step])]
        simp [step, GateOp.eval]


lemma rcCircuit_binCost_lt (n k : ℕ) (hk : k < n) (val : Bool) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = n) (hx2l : x2.length = n)
    (hagree_xy : ∀ i < n, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = n) (hz2l : z2.length = n)
    (hz1k : z1.getD k false = val) (hz2k : z2.getD k false = val)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl val else Sum.inr i.val
    binaryCost (rcCircuit n env0 gs o).1 + 1 ≤ binaryCost gs := by
  intro env0
  have hle_fold : binaryCost (gs.foldl (rcStep n) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le n gs ([], env0); simpa [binaryCost] using this
  have hbc_rc : binaryCost (rcCircuit n env0 gs o).1 = binaryCost (gs.foldl (rcStep n) ([], env0)).1 := by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep n) ([], env0)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  rw [hbc_rc]
  by_contra hlt
  have hzero : binaryCost ([] : List Gate) = 0 := rfl
  have heq_cost : binaryCost (gs.foldl (rcStep n) ([], env0)).1 = binaryCost ([] : List Gate) + binaryCost gs := by
    rw [hzero, Nat.zero_add]; omega
  cases hm : (gs.foldl (rcStep n) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    have hinit : ∀ i w0, (([] : List Gate), env0).2.getD i (Sum.inl false) = Sum.inr w0 → x1.getD i false = x2.getD i false := by
      intro i w0 hiw
      by_cases hi : i < n
      · dsimp only at hiw
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])] at hiw
        change (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) = Sum.inr w0 at hiw
        rw [List.getElem_ofFn] at hiw
        by_cases hik : i = k
        · simp [hik] at hiw
        · exact hagree_xy i hi hik
      · dsimp only at hiw
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)] at hiw; cases hiw
    have hsame := rcFold_inr_agree n gs hM x1 x2 ([], env0) (by simp [env0, hx1l]) (by simp [env0, hx2l])
      heq_cost hinit o w' hm
    exact hdiff_xy hsame
  | inl b =>
    have hinit_z : ∀ (z : List Bool), z.length = n → z.getD k false = val →
        ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < n + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
      intro z hzl hzk i
      by_cases hi : i < n
      · dsimp only
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
        change match (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < n + 0 ∧ z.getD i false = z.getD w' false
        rw [List.getElem_ofFn]
        by_cases hik : i = k
        · subst hik; simp only [ite_true]; exact hzk
        · simp [hik, hi]
      · dsimp only
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)]
        exact List.getD_eq_default z false (by omega)
    have hz1 := (rcFold_eval_inv n gs z1 hz1l hM z1 ([], env0) (by simp [env0, hz1l]) (hinit_z z1 hz1l hz1k)).2 o
    have hz2 := (rcFold_eval_inv n gs z2 hz2l hM z2 ([], env0) (by simp [env0, hz2l]) (hinit_z z2 hz2l hz2k)).2 o
    rw [hm] at hz1 hz2
    dsimp only at hz1 hz2
    exact hdiff_zz (hz1.trans hz2.symm)

lemma rcStep_env_old_getD (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (i : ℕ) (hi : i < st.2.length) :
    (rcStep nOut st g).2.getD i (Sum.inl false) = st.2.getD i (Sum.inl false) := by
  rcases st with ⟨out, env⟩
  dsimp only at hi ⊢
  have h1 : ∀ x : Bool ⊕ ℕ, (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
    simp [List.getElem_append_left hi]
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · exact h1 _
    · cases g.inputs.filterMap _ with | nil => exact h1 _ | cons a t => cases t <;> exact h1 _
  · simp only [rcStep, h]; split_ifs
    · exact h1 _
    · cases g.inputs.filterMap _ with | nil => exact h1 _ | cons a t => cases t <;> exact h1 _
  · simp only [rcStep, h]; cases g.inputs with
    | nil => exact h1 _
    | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact h1 _
  · simp only [rcStep, h]; exact h1 _
  · simp only [rcStep, h]; exact h1 _

lemma rcStep_bin_keep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', st.2.getD j (Sum.inl false) = Sum.inr w') :
    binaryCost (rcStep nOut st g).1 = binaryCost st.1 + 1 ∧
    ∃ w', (rcStep nOut st g).2.getD st.2.length (Sum.inl false) = Sum.inr w' := by
  rcases st with ⟨out, env⟩
  dsimp only at h2 ⊢
  obtain ⟨hl2, hall⟩ := h2
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [hins] at hl2
  · simp [hins] at hl2
  · obtain ⟨wa, hwa⟩ := hall a (by simp [hins])
    obtain ⟨wb, hwb⟩ := hall b (by simp [hins])
    rcases hop with hop | hop
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, hwa, hwb, Bool.or_false, Bool.false_eq_true, ite_false,
        List.filterMap_cons, List.filterMap_nil]
      refine ⟨by rw [binaryCost_append_one]; simp [isBinary], nOut + out.length, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, hwa, hwb, Bool.or_false, Bool.false_eq_true, ite_false,
        List.filterMap_cons, List.filterMap_nil]
      refine ⟨by rw [binaryCost_append_one]; simp [isBinary], nOut + out.length, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
  · simp [hins] at hl2

lemma rcStep_bin_drop (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hcap : g.inputs.length ≤ 2)
    (hnot2 : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', st.2.getD j (Sum.inl false) = Sum.inr w')) :
    binaryCost (rcStep nOut st g).1 = binaryCost st.1 := by
  rcases st with ⟨out, env⟩
  dsimp only at hnot2 ⊢
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with hop | hop <;> simp [rcStep, hop, hins]
  · rcases hop with hop | hop
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, Bool.or_false,
        List.filterMap_cons, List.filterMap_nil]
      cases env.getD a (Sum.inl false) with
      | inl bb => cases bb <;> rfl
      | inr wa => rfl
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, Bool.or_false,
        List.filterMap_cons, List.filterMap_nil]
      cases env.getD a (Sum.inl false) with
      | inl bb => cases bb <;> rfl
      | inr wa => rfl
  · have hex : ∃ j ∈ ([a, b] : List ℕ), ∀ w', env.getD j (Sum.inl false) ≠ Sum.inr w' := by
      by_contra hno
      apply hnot2
      refine ⟨by simp [hins], ?_⟩
      intro j hj
      rw [hins] at hj
      by_contra hno2
      exact hno ⟨j, hj, fun w' hw' => hno2 ⟨w', hw'⟩⟩
    obtain ⟨j, hj, hnj⟩ := hex
    have hflt : (([a, b] : List ℕ).filterMap fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length < 2 := by
      apply list_filterMap_len_lt _ [a, b] j hj
      cases hm : env.getD j (Sum.inl false) with
      | inl _ => rfl
      | inr w' => exact absurd hm (hnj w')
    rcases hop with hop | hop
    · simp only [rcStep, hop, hins]
      split_ifs
      · rfl
      · cases hf : ([a, b] : List ℕ).filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
        | nil => rfl
        | cons u t =>
          cases t with
          | nil => rfl
          | cons v t2 => rw [hf] at hflt; simp at hflt
    · simp only [rcStep, hop, hins]
      split_ifs
      · rfl
      · cases hf : ([a, b] : List ℕ).filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
        | nil => rfl
        | cons u t =>
          cases t with
          | nil => rfl
          | cons v t2 => rw [hf] at hflt; simp at hflt
  · simp [hins] at hcap

lemma rcStep_bin_inr_no_kill (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w' : ℕ) (hinr : (rcStep nOut st g).2.getD st.2.length (Sum.inl false) = Sum.inr w') :
    ∀ j ∈ g.inputs, ∀ b, st.2.getD j (Sum.inl false) = Sum.inl b →
      (g.op = GateOp.and → b = true) ∧ (g.op = GateOp.or → b = false) := by
  rcases st with ⟨out, env⟩
  dsimp only at hinr ⊢
  intro j hj b hjb
  rcases hop with hop | hop
  · refine ⟨(fun _ => ?_), (fun h => by rw [hop] at h; cases h)⟩
    cases b with
    | true => rfl
    | false =>
      exfalso
      have hany : g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) = true :=
        List.any_eq_true.mpr ⟨j, hj, by rw [hjb]⟩
      simp only [rcStep, hop, hany, ite_true] at hinr
      rw [List.getD_eq_getElem _ _ (by simp)] at hinr
      simp at hinr
  · refine ⟨(fun h => by rw [hop] at h; cases h), (fun _ => ?_)⟩
    cases b with
    | false => rfl
    | true =>
      exfalso
      have hany : g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) = true :=
        List.any_eq_true.mpr ⟨j, hj, by rw [hjb]⟩
      simp only [rcStep, hop, hany, ite_true] at hinr
      rw [List.getD_eq_getElem _ _ (by simp)] at hinr
      simp at hinr

lemma rcFold_two_elim_contra (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (stF stT : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = stF.2.length) (hylen : wy.length = stF.2.length)
    (hlenFT : stT.2.length = stF.2.length)
    (hshape : ∀ i, (∃ b, stF.2.getD i (Sum.inl false) = Sum.inl b) ↔
                   (∃ b, stT.2.getD i (Sum.inl false) = Sum.inl b))
    (hagreeF : ∀ i w', stF.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false)
    (hagreeT : ∀ i w', stT.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false)
    (hsameInl : ∀ i b, stF.2.getD i (Sum.inl false) = Sum.inl b →
                       stT.2.getD i (Sum.inl false) = Sum.inl b →
                       wx.getD i false = b ∧ wy.getD i false = b)
    (hcostF : binaryCost (gs.foldl (rcStep nOut) stF).1 + 1 = binaryCost stF.1 + binaryCost gs)
    (hcostT : binaryCost (gs.foldl (rcStep nOut) stT).1 + 1 = binaryCost stT.1 + binaryCost gs) :
    (∀ i w', (gs.foldl (rcStep nOut) stF).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false) ∨
    (∀ i w', (gs.foldl (rcStep nOut) stT).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false) := by
  induction gs generalizing wx wy stF stT with
  | nil =>
    simp [binaryCost] at hcostF
  | cons g rest ih =>
    simp only [List.foldl_cons] at hcostF hcostT ⊢
    have hg := hM g List.mem_cons_self
    have hMrest : ∀ g' ∈ rest, legal g' := fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')
    have hbc_cons : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hshape_inr : ∀ i, (∃ w', stF.2.getD i (Sum.inl false) = Sum.inr w') ↔
                           (∃ w', stT.2.getD i (Sum.inl false) = Sum.inr w') := by
      intro i
      cases hF : stF.2.getD i (Sum.inl false) <;> cases hT : stT.2.getD i (Sum.inl false)
      · simp
      · exfalso; obtain ⟨b, hb⟩ := (hshape i).mp ⟨_, hF⟩; rw [hT] at hb; cases hb
      · exfalso; obtain ⟨b, hb⟩ := (hshape i).mpr ⟨_, hT⟩; rw [hF] at hb; cases hb
      · simp
    set stF' := rcStep nOut stF g with hstF'
    set stT' := rcStep nOut stT g with hstT'
    set wx' := step wx g with hwx'
    set wy' := step wy g with hwy'
    have hlenF' : stF'.2.length = stF.2.length + 1 := rcStep_env_len nOut stF g
    have hlenT' : stT'.2.length = stF.2.length + 1 := by rw [rcStep_env_len, hlenFT]
    have hxlen' : wx'.length = stF'.2.length := by rw [hwx', hlenF']; simp [step, hxlen]
    have hylen' : wy'.length = stF'.2.length := by rw [hwy', hlenF']; simp [step, hylen]
    have hget_old_x : ∀ i < stF.2.length, wx'.getD i false = wx.getD i false := fun i hi => by
      rw [hwx', List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < stF.2.length, wy'.getD i false = wy.getD i false := fun i hi => by
      rw [hwy', List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : wx'.getD stF.2.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [hwx', ← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : wy'.getD stF.2.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [hwy', ← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hrc_oldF : ∀ i < stF.2.length, stF'.2.getD i (Sum.inl false) = stF.2.getD i (Sum.inl false) :=
      rcStep_env_old_getD nOut stF g
    have hrc_oldT : ∀ i < stF.2.length, stT'.2.getD i (Sum.inl false) = stT.2.getD i (Sum.inl false) := fun i hi =>
      rcStep_env_old_getD nOut stT g i (by omega)
    have hle_restF := rcFold_binCost_le nOut rest stF'
    have hle_restT := rcFold_binCost_le nOut rest stT'
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
    rcases hop with hop | hop | hop
    · have hbin : isBinary g = true := by simp [isBinary, hop]
      by_cases h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stF.2.getD j (Sum.inl false) = Sum.inr w'
      · have h2T : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w' :=
          ⟨h2.1, fun j hj => (hshape_inr j).mp (h2.2 j hj)⟩
        obtain ⟨hcF, wF, hwF⟩ := rcStep_bin_keep nOut stF g (Or.inl hop) h2
        obtain ⟨hcT, wT, hwT⟩ := rcStep_bin_keep nOut stT g (Or.inl hop) h2T
        have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
          rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
          intro j hj; obtain ⟨w0, hw0⟩ := h2.2 j hj; exact hagreeF j w0 hw0
        apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
        · intro i
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF, ← hlenFT, hwT]; simp
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i b hF hT
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
            rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF] at hF; cases hF
            · rw [List.getD_eq_default _ _ (by omega)] at hF
              cases hF
              exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
        · simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        · simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
      · have hnot2T : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w') :=
          fun h2T => h2 ⟨h2T.1, fun j hj => (hshape_inr j).mpr (h2T.2 j hj)⟩
        have hcF := rcStep_bin_drop nOut stF g (Or.inl hop) hg.2 h2
        have hcT := rcStep_bin_drop nOut stT g (Or.inl hop) hg.2 hnot2T
        have hrestF : binaryCost (rest.foldl (rcStep nOut) stF').1 = binaryCost stF'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        have hrestT : binaryCost (rest.foldl (rcStep nOut) stT').1 = binaryCost stT'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
        cases hlastF : stF'.2.getD stF.2.length (Sum.inl false) with
        | inl bf =>
          left
          refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
          intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hlastF] at hiw'; cases hiw'
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        | inr wF =>
          cases hlastT : stT'.2.getD stF.2.length (Sum.inl false) with
          | inl bt =>
            right
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stT' (by omega) (by omega) hrestT ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; rw [hlastT] at hiw'; cases hiw'
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
          | inr wT =>
            left
            have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
              rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
              intro j hj
              cases hjF : stF.2.getD j (Sum.inl false) with
              | inr w0 => exact hagreeF j w0 hjF
              | inl bF =>
                obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
                have hbF : bF = true := (rcStep_bin_inr_no_kill nOut stF g (Or.inl hop) wF hlastF j hj bF hjF).1 hop
                have hbT : bT = true := (rcStep_bin_inr_no_kill nOut stT g (Or.inl hop) wT (by rw [hlenFT]; exact hlastT) j hj bT hjT).1 hop
                subst hbF; subst hbT
                have hxy := hsameInl j true hjF hjT
                exact hxy.1.trans hxy.2.symm
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; exact hlast_eq
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
    · have hbin : isBinary g = true := by simp [isBinary, hop]
      by_cases h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stF.2.getD j (Sum.inl false) = Sum.inr w'
      · have h2T : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w' :=
          ⟨h2.1, fun j hj => (hshape_inr j).mp (h2.2 j hj)⟩
        obtain ⟨hcF, wF, hwF⟩ := rcStep_bin_keep nOut stF g (Or.inr hop) h2
        obtain ⟨hcT, wT, hwT⟩ := rcStep_bin_keep nOut stT g (Or.inr hop) h2T
        have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
          rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
          intro j hj; obtain ⟨w0, hw0⟩ := h2.2 j hj; exact hagreeF j w0 hw0
        apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
        · intro i
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF, ← hlenFT, hwT]; simp
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i b hF hT
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
            rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF] at hF; cases hF
            · rw [List.getD_eq_default _ _ (by omega)] at hF
              cases hF
              exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
        · simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        · simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
      · have hnot2T : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w') :=
          fun h2T => h2 ⟨h2T.1, fun j hj => (hshape_inr j).mpr (h2T.2 j hj)⟩
        have hcF := rcStep_bin_drop nOut stF g (Or.inr hop) hg.2 h2
        have hcT := rcStep_bin_drop nOut stT g (Or.inr hop) hg.2 hnot2T
        have hrestF : binaryCost (rest.foldl (rcStep nOut) stF').1 = binaryCost stF'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        have hrestT : binaryCost (rest.foldl (rcStep nOut) stT').1 = binaryCost stT'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
        cases hlastF : stF'.2.getD stF.2.length (Sum.inl false) with
        | inl bf =>
          left
          refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
          intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hlastF] at hiw'; cases hiw'
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        | inr wF =>
          cases hlastT : stT'.2.getD stF.2.length (Sum.inl false) with
          | inl bt =>
            right
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stT' (by omega) (by omega) hrestT ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; rw [hlastT] at hiw'; cases hiw'
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
          | inr wT =>
            left
            have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
              rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
              intro j hj
              cases hjF : stF.2.getD j (Sum.inl false) with
              | inr w0 => exact hagreeF j w0 hjF
              | inl bF =>
                obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
                have hbF : bF = false := (rcStep_bin_inr_no_kill nOut stF g (Or.inr hop) wF hlastF j hj bF hjF).2 hop
                have hbT : bT = false := (rcStep_bin_inr_no_kill nOut stT g (Or.inr hop) wT (by rw [hlenFT]; exact hlastT) j hj bT hjT).2 hop
                subst hbF; subst hbT
                have hxy := hsameInl j false hjF hjT
                exact hxy.1.trans hxy.2.symm
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; exact hlast_eq
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
    · have hbin : isBinary g = false := by simp [isBinary, hop]
      have hcF : binaryCost stF'.1 = binaryCost stF.1 := by
        rw [hstF']
        simp only [rcStep, hop]
        cases g.inputs with
        | nil => rfl
        | cons j _ =>
          dsimp only
          cases stF.2.getD j (Sum.inl false) with
          | inl _ => rfl
          | inr _ => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
      have hcT : binaryCost stT'.1 = binaryCost stT.1 := by
        rw [hstT']
        simp only [rcStep, hop]
        cases g.inputs with
        | nil => rfl
        | cons j _ =>
          dsimp only
          cases stT.2.getD j (Sum.inl false) with
          | inl _ => rfl
          | inr _ => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
      have hlast_cases :
          ((∃ b, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl b) ↔
           (∃ b, stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl b)) ∧
          ((∃ w', stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr w') →
            wx'.getD stF.2.length false = wy'.getD stF.2.length false) ∧
          (∀ b, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl b →
                stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl b →
                wx'.getD stF.2.length false = b ∧ wy'.getD stF.2.length false = b) := by
        cases hgi : g.inputs with
        | nil =>
          have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl true := by
            rw [hstF']; simp only [rcStep, hop, hgi]
            rw [List.getD_eq_getElem _ _ (by simp)]; simp
          have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl true := by
            rw [hstT']; simp only [rcStep, hop, hgi]
            rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
          rw [hlF, hlT]
          refine ⟨(by simp), (fun ⟨_, h⟩ => by cases h), (fun b hb _ => ?_)⟩
          cases hb
          rw [hget_last_x, hget_last_y, hop, hgi]
          exact ⟨rfl, rfl⟩
        | cons j _ =>
          cases hjF : stF.2.getD j (Sum.inl false) with
          | inl bF =>
            obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
            have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl (!bF) := by
              rw [hstF']; simp only [rcStep, hop, hgi, hjF]
              rw [List.getD_eq_getElem _ _ (by simp)]; simp
            have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl (!bT) := by
              rw [hstT']; simp only [rcStep, hop, hgi, hjT]
              rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
            rw [hlF, hlT]
            refine ⟨(by simp), (fun ⟨_, h⟩ => by cases h), (fun b hbF hbT => ?_)⟩
            have he1 : (!bF) = b := Sum.inl.inj hbF
            have he2 : (!bT) = b := Sum.inl.inj hbT
            have hbt : bF = bT := by
              have he : (!bF) = (!bT) := he1.trans he2.symm
              cases bF <;> cases bT <;> first | rfl | cases he
            subst hbt
            have hxy := hsameInl j bF hjF hjT
            rw [hget_last_x, hget_last_y, hop, hgi]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, hxy.1, hxy.2, he1, and_self]
          | inr wF =>
            obtain ⟨wT, hjT⟩ := (hshape_inr j).mp ⟨wF, hjF⟩
            have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr (nOut + stF.1.length) := by
              rw [hstF']; simp only [rcStep, hop, hgi, hjF]
              rw [List.getD_eq_getElem _ _ (by simp)]; simp
            have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inr (nOut + stT.1.length) := by
              rw [hstT']; simp only [rcStep, hop, hgi, hjT]
              rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
            rw [hlF, hlT]
            refine ⟨(by simp), (fun _ => ?_), (fun _ h _ => by cases h)⟩
            rw [hget_last_x, hget_last_y, hop, hgi]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, hagreeF j wF hjF]
      apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
      · intro i
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.1
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · intro i w' hiw'
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.2.1 ⟨w', hiw'⟩
          · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
      · intro i w' hiw'
        by_cases hi : i < stF.2.length
        · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
        · by_cases heq : i = stF.2.length
          · subst heq
            have hF_inr : ∃ w0, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr w0 := by
              cases hF : stF'.2.getD stF.2.length (Sum.inl false) with
              | inr w0 => exact ⟨w0, rfl⟩
              | inl b0 =>
                exfalso; obtain ⟨b1, hb1⟩ := hlast_cases.1.mp ⟨b0, hF⟩
                rw [hiw'] at hb1; cases hb1
            exact hlast_cases.2.1 hF_inr
          · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
      · intro i b hF hT
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
          rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.2.2 b hF hT
          · rw [List.getD_eq_default _ _ (by omega)] at hF
            cases hF
            exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
      · simp only [hbc_cons, hbin, Bool.false_eq_true, ite_false, Nat.add_zero] at hcostF; omega
      · simp only [hbc_cons, hbin, Bool.false_eq_true, ite_false, Nat.add_zero] at hcostT; omega

lemma rcCircuit_binCost_two_elim (n k : ℕ) (hk : k < n) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = n) (hx2l : x2.length = n)
    (hagree_xy : ∀ i < n, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = n) (hz2l : z2.length = n)
    (hz1k : z1.getD k false = false) (hz2k : z2.getD k false = false)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2)
    (w1 w2 : List Bool) (hw1l : w1.length = n) (hw2l : w2.length = n)
    (hw1k : w1.getD k false = true) (hw2k : w2.getD k false = true)
    (hdiff_ww : Circuit.eval ⟨gs, o⟩ w1 ≠ Circuit.eval ⟨gs, o⟩ w2) :
    ∃ val : Bool,
      let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl val else Sum.inr i.val
      binaryCost (rcCircuit n env0 gs o).1 + 2 ≤ binaryCost gs := by
  let envF : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl false else Sum.inr i.val
  let envT : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl true else Sum.inr i.val
  have hltF : binaryCost (rcCircuit n envF gs o).1 + 1 ≤ binaryCost gs :=
    rcCircuit_binCost_lt n k hk false gs o hM x1 x2 hx1l hx2l hagree_xy hdiff_xy z1 z2 hz1l hz2l hz1k hz2k hdiff_zz
  have hltT : binaryCost (rcCircuit n envT gs o).1 + 1 ≤ binaryCost gs :=
    rcCircuit_binCost_lt n k hk true gs o hM x1 x2 hx1l hx2l hagree_xy hdiff_xy w1 w2 hw1l hw2l hw1k hw2k hdiff_ww
  by_cases h2F : binaryCost (rcCircuit n envF gs o).1 + 2 ≤ binaryCost gs
  · exact ⟨false, h2F⟩
  by_cases h2T : binaryCost (rcCircuit n envT gs o).1 + 2 ≤ binaryCost gs
  · exact ⟨true, h2T⟩
  exfalso
  have hbc_rc : ∀ env : List (Bool ⊕ ℕ),
      binaryCost (rcCircuit n env gs o).1 = binaryCost (gs.foldl (rcStep n) ([], env)).1 := fun env => by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep n) ([], env)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  have hcostF : binaryCost (gs.foldl (rcStep n) ([], envF)).1 + 1 = binaryCost ([] : List Gate) + binaryCost gs := by
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    rw [← hbc_rc envF, h0, Nat.zero_add]; omega
  have hcostT : binaryCost (gs.foldl (rcStep n) ([], envT)).1 + 1 = binaryCost ([] : List Gate) + binaryCost gs := by
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    rw [← hbc_rc envT, h0, Nat.zero_add]; omega
  have henv_at : ∀ (val : Bool) (i : ℕ),
      (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val).getD i (Sum.inl false) =
        if i < n then (if i = k then Sum.inl val else Sum.inr i) else Sum.inl false := fun val i => by
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]; simp [hi]
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]
  have hcontra := rcFold_two_elim_contra n gs hM x1 x2 ([], envF) ([], envT)
    (by simp [envF, hx1l]) (by simp [envF, hx2l]) (by simp [envF, envT])
    (by intro i; dsimp only; rw [henv_at false i, henv_at true i]; split_ifs <;> simp)
    (by intro i w' hiw'; dsimp only at hiw'; rw [henv_at false i] at hiw'
        by_cases hi : i < n
        · simp only [hi, ite_true] at hiw'
          by_cases hik : i = k
          · simp [hik] at hiw'
          · exact hagree_xy i hi hik
        · simp [hi] at hiw')
    (by intro i w' hiw'; dsimp only at hiw'; rw [henv_at true i] at hiw'
        by_cases hi : i < n
        · simp only [hi, ite_true] at hiw'
          by_cases hik : i = k
          · simp [hik] at hiw'
          · exact hagree_xy i hi hik
        · simp [hi] at hiw')
    (by intro i b hF hT; dsimp only at hF hT; rw [henv_at false i] at hF; rw [henv_at true i] at hT
        by_cases hi : i < n
        · simp only [hi, ite_true] at hF hT
          by_cases hik : i = k
          · simp only [hik, ite_true] at hF hT; cases hF; cases hT
          · simp [hik] at hF
        · simp only [hi, ite_false] at hF; cases hF
          exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩)
    hcostF hcostT
  have hinit_val : ∀ (val : Bool) (z : List Bool), z.length = n → z.getD k false = val →
      ∀ i, match (([] : List Gate), List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val).2.getD i (Sum.inl false) with
        | Sum.inl b0 => z.getD i false = b0
        | Sum.inr w' => w' < n + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
    intro val z hzl hzk i
    dsimp only; rw [henv_at val i]
    by_cases hi : i < n
    · simp only [hi, ite_true]
      by_cases hik : i = k
      · subst hik; simp only [ite_true]; exact hzk
      · simp [hik, hi]
    · simp only [hi, ite_false]
      exact List.getD_eq_default z false (by omega)
  rcases hcontra with hF_ag | hT_ag
  · cases hm : (gs.foldl (rcStep n) ([], envF)).2.getD o (Sum.inl false) with
    | inr w' => exact hdiff_xy (hF_ag o w' hm)
    | inl b =>
      have hz1 := (rcFold_eval_inv n gs z1 hz1l hM z1 ([], envF) (by simp [envF, hz1l]) (hinit_val false z1 hz1l hz1k)).2 o
      have hz2 := (rcFold_eval_inv n gs z2 hz2l hM z2 ([], envF) (by simp [envF, hz2l]) (hinit_val false z2 hz2l hz2k)).2 o
      rw [hm] at hz1 hz2; dsimp only at hz1 hz2
      exact hdiff_zz (hz1.trans hz2.symm)
  · cases hm : (gs.foldl (rcStep n) ([], envT)).2.getD o (Sum.inl false) with
    | inr w' => exact hdiff_xy (hT_ag o w' hm)
    | inl b =>
      have hw1 := (rcFold_eval_inv n gs w1 hw1l hM w1 ([], envT) (by simp [envT, hw1l]) (hinit_val true w1 hw1l hw1k)).2 o
      have hw2 := (rcFold_eval_inv n gs w2 hw2l hM w2 ([], envT) (by simp [envT, hw2l]) (hinit_val true w2 hw2l hw2k)).2 o
      rw [hm] at hw1 hw2; dsimp only at hw1 hw2
      exact hdiff_ww (hw1.trans hw2.symm)



lemma val_read {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]

def pinEnv (p : Fin 8) (v : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin 8 => if i.val=p.val then Sum.inl v else Sum.inr i.val

lemma pin_eval (p : Fin 8) (v : Bool) (gs : List Gate) (o : ℕ) (hg : ∀ z ∈ gs, legal z) (x : Fin 8 → Bool) :
    let c := rcCircuit 8 (pinEnv p v) gs o
    Circuit.eval ⟨c.1,c.2⟩ (List.ofFn x) = Circuit.eval ⟨gs,o⟩ (List.ofFn (Function.update x p v)) := by
  intro c
  have hp := rcCircuit_props 8 8 (pinEnv p v) (by simp [pinEnv]) gs o hg
  apply hp.2.2 _ _ (by simp) (by simp)
  intro i hi
  unfold pinEnv
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]
  by_cases hh : i = p.val
  · subst i
    simp only [ite_true]
    rw [val_read, Function.update_self]
  · simp only [hh, ite_false]
    refine ⟨hi, ?_⟩
    rw [val_read (Function.update x p v) ⟨i,hi⟩,val_read x ⟨i,hi⟩]
    exact Function.update_of_ne (fun e => hh (congrArg Fin.val e)) _ _

lemma map_eval {n : ℕ} (π : Fin 8 → Fin n) (gs : List Gate) (o : ℕ) (hg : ∀ z ∈ gs, legal z) (x : Fin n → Bool) :
    let e : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => Sum.inr (π i).val
    let c := rcCircuit n e gs o
    Circuit.eval ⟨c.1,c.2⟩ (List.ofFn x) = Circuit.eval ⟨gs,o⟩ (List.ofFn (x ∘ π)) := by
  intro e c
  have hp := rcCircuit_props 8 n e (by simp [e]) gs o hg
  apply hp.2.2 _ _ (by simp) (by simp)
  intro i hi
  rw [List.getD_eq_getElem e _ (by simpa [e] using hi)]
  dsimp only [e]
  rw [List.getElem_ofFn]
  refine ⟨(π ⟨i,hi⟩).isLt,?_⟩
  rw [val_read (x ∘ π) ⟨i,hi⟩,val_read x (π ⟨i,hi⟩)]
  rfl

def PFn := (Fin 8 → Bool) → Bool
def BL (f : PFn) (k : ℕ) := ∀ (gs : List Gate) (o : ℕ), (∀ z ∈ gs, legal z) →
  (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) → k ≤ binaryCost gs

def probe (r : ℕ) (i : Fin 8) : Bool := r.testBit i.val
def flipTest (f : PFn) (p : Fin 8) (r t : ℕ) : Prop :=
  (∀ i : Fin 8, i ≠ p → probe r i = probe t i) ∧ f (probe r) ≠ f (probe t)
def varyTest (f : PFn) (p : Fin 8) (v : Bool) (r t : ℕ) : Prop :=
  probe r p=v ∧ probe t p=v ∧ f (probe r) ≠ f (probe t)
lemma rawAgree (p : Fin 8) (r t : ℕ) (h : ∀ i : Fin 8, i ≠ p → probe r i = probe t i) :
    ∀ i < 8, i ≠ p.val → (List.ofFn (probe r)).getD i false = (List.ofFn (probe t)).getD i false := by
  intro i hi hne
  rw [val_read (probe r) ⟨i,hi⟩,val_read (probe t) ⟨i,hi⟩]
  exact h ⟨i,hi⟩ (fun e => hne (congrArg Fin.val e))
lemma rawVal (r : ℕ) (p : Fin 8) : (List.ofFn (probe r)).getD p.val false = probe r p := val_read _ _

lemma one {f g k} (p : Fin 8) (v : Bool) (r t u w : ℕ) (hd : flipTest f p r t)
    (hv : varyTest f p v u w) (eq : ∀ x, f (Function.update x p v) = g x) (child : BL g k) : BL f (k+1) := by
  intro gs o hg hc
  have sav := rcCircuit_binCost_lt 8 p.val p.isLt v gs o hg
    (List.ofFn (probe r)) (List.ofFn (probe t)) (by simp) (by simp) (rawAgree p r t hd.1)
    (by rw [hc,hc]; exact hd.2)
    (List.ofFn (probe u)) (List.ofFn (probe w)) (by simp) (by simp)
    ((rawVal u p).trans hv.1) ((rawVal w p).trans hv.2.1) (by rw [hc,hc]; exact hv.2.2)
  let c := rcCircuit 8 (pinEnv p v) gs o
  have ch := child c.1 c.2 (rcCircuit_props 8 8 (pinEnv p v) (by simp [pinEnv]) gs o hg).1
    (fun x => (pin_eval p v gs o hg x).trans ((hc _).trans (eq x)))
  change binaryCost c.1 + 1 ≤ binaryCost gs at sav
  omega

lemma two {f g₀ g₁ k} (p : Fin 8) (r t u w u' w' : ℕ) (hd : flipTest f p r t)
    (hv : varyTest f p false u w) (hw : varyTest f p true u' w')
    (e0 : ∀ x, f (Function.update x p false) = g₀ x) (e1 : ∀ x, f (Function.update x p true) = g₁ x)
    (child0 : BL g₀ k) (child1 : BL g₁ k) : BL f (k+2) := by
  intro gs o hg hc
  obtain ⟨v,sav⟩ := rcCircuit_binCost_two_elim 8 p.val p.isLt gs o hg
    (List.ofFn (probe r)) (List.ofFn (probe t)) (by simp) (by simp) (rawAgree p r t hd.1)
    (by rw [hc,hc]; exact hd.2)
    (List.ofFn (probe u)) (List.ofFn (probe w)) (by simp) (by simp)
    ((rawVal u p).trans hv.1) ((rawVal w p).trans hv.2.1) (by rw [hc,hc]; exact hv.2.2)
    (List.ofFn (probe u')) (List.ofFn (probe w')) (by simp) (by simp)
    ((rawVal u' p).trans hw.1) ((rawVal w' p).trans hw.2.1) (by rw [hc,hc]; exact hw.2.2)
  let c := rcCircuit 8 (pinEnv p v) gs o
  change binaryCost c.1 + 2 ≤ binaryCost gs at sav
  have ok := (rcCircuit_props 8 8 (pinEnv p v) (by simp [pinEnv]) gs o hg).1
  have he (x) := (pin_eval p v gs o hg x).trans (hc _)
  cases v
  · have ch := child0 _ _ ok (fun x => (he x).trans (e0 x))
    dsimp only [c] at sav
    omega
  · have ch := child1 _ _ ok (fun x => (he x).trans (e1 x))
    dsimp only [c] at sav
    omega


end RecCore
open RecCore
theorem fromLeaf10732 (gs : List Gate) (o : ℕ) (hg : ∀ z ∈ gs, RecCore.legal z)
    (hc : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Leaf10732.graph6 x) :
    10 ≤ RecCore.binaryCost gs := by
  have l := Leaf10732.lower ⟨gs,o⟩ (by simpa only [FanInTwo,RecCore.legal,Set.mem_insert_iff,Set.mem_singleton_iff] using hg) hc
  have eq : Leaf10732.Wire.paid = RecCore.isBinary := by
    funext z
    rcases z with ⟨op,is⟩
    cases op <;> rfl
  rw [eq,List.countP_eq_length_filter] at l
  exact l

def target8 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 5) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def witness : List Gate := [⟨.or, [3, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [13, 9]⟩, ⟨.and, [2, 14]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩]
theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, target8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in

def fn0 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def fn1 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def fn2 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem ln2 : BL fn2 10 := by
  intro gs o hg hc
  let π : Fin 8 → Fin 6 := ![0, 0, 1, 2, 0, 3, 4, 5]
  let env : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => Sum.inr (π i).val
  let c := rcCircuit 6 env gs o
  have props := rcCircuit_props 8 6 env (by simp [env]) gs o hg
  have e : ∀ x : Fin 6 → Bool, fn2 (x ∘ π) = Leaf10732.graph6 x := by decide +kernel
  have child := fromLeaf10732 c.1 c.2 props.1 (fun x => (map_eval π gs o hg x).trans ((hc _).trans (e x)))
  exact child.trans props.2.1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ln1 : BL fn1 11 := by
  exact one 1 false 64 66 9 0 (by unfold flipTest; decide +kernel) (by unfold varyTest; decide +kernel) (by decide +kernel) ln2

def fn3 (x : Fin 8 → Bool) : Bool := (x 1) || (x 0 && x 3) || (x 0 && x 5) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ln3 : BL fn3 11 := by
  exact one 1 false 0 2 9 0 (by unfold flipTest; decide +kernel) (by unfold varyTest; decide +kernel) (by decide +kernel) ln2
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ln0 : BL fn0 13 := by
  exact two 4 2 18 9 0 18 16 (by unfold flipTest; decide +kernel) (by unfold varyTest; decide +kernel) (by unfold varyTest; decide +kernel) (by decide +kernel) (by decide +kernel) ln1 ln3
end PEqualNP.Outside.L_meta_29194
open PEqualNP.Outside.L_meta_29194 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_29194 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have he : ∀ y : Fin 8 → Bool, target8 y = fn0 y := by decide +kernel
    have h := ln0 gates o legal (fun x => (computes x).trans ((graph_correct x).symm.trans (he x)))
    obtain ⟨g,mg,notg⟩ := hn
    have save : RecCore.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := RecCore.isBinary)).2
        ⟨g,mg,by simp [RecCore.isBinary,notg]⟩
    have sz : witness.length ≤ 14 := by decide
    exact ⟨witness, 21, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨h,le⟩ := legal g hg
    refine ⟨?_,le⟩
    rcases h with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact False.elim (hn ⟨g,hg,c⟩)
