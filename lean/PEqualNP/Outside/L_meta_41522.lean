import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41522_aux

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

def goal6 : BitVec 64 := 0xfeeeeee8eeeaece0

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

def b4_0_goal : BitVec 16 := 0xeaa8
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
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0,b4_0_s1,b4_0_s2,b4_0_s3,b4_0_s4,b4_0_s5]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0,b4_0_p1,b4_0_p2,b4_0_p3,b4_0_p4,b4_0_p5]
def b4_0_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_G_valid : (List.range 6).all (symValid 16 6 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x55aa,0xcccc,0xf0f0],[]),
([0xff0,0xaaaa,0xcccc],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
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
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(1,0),(4,1),(5,1)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,3),(1,3),(2,2),(3,2)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,4)]),
([0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[(4,4)]),
([0xaaaa,0xc0c0,0xcccc,0xf0f0,0xff00],[(0,5)]),
([0xaaaa,0xcccc,0xf0f0,0xfcfc,0xff00],[(0,5)]),
([0xcc,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,8),(1,6),(4,7)])
]
def b4_0_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5),(1,6),(2,0),(2,1),(2,3),(2,6),(3,0),(3,1),(3,3),(3,6),(4,2),(4,4),(4,5),(4,6),(5,6)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_0_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 3 b4_0_L3 b4_0_L2 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true := by
  intro i hi
  have hsz : b4_0_L3.size = 9 := by decide +kernel
  exact checkBlockP_at b4_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 4 b4_0_L4 b4_0_L3 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true := by
  intro i hi
  have hsz : b4_0_L4.size = 7 := by decide +kernel
  exact checkBlockP_at b4_0_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_5_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 5 b4_0_L5 b4_0_L4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_5 : ∀ i < b4_0_L5.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 5 b4_0_L5 b4_0_L4 i = true := by
  intro i hi
  have hsz : b4_0_L5.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_5_0 i (Nat.zero_le _) (by omega)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
theorem b4_0_L5_sound : ∀ i < b4_0_L5.size, ¬ live (basicOps 16) b4_0_goal 5 (b4_0_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L4_sound b4_0_chk_5
set_option maxRecDepth 100000 in
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L5[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 5 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L5_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xeee8
def b4_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_1_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_1_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_1_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_1_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_1_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_1_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1,b4_1_s2,b4_1_s3]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1,b4_1_p2,b4_1_p3]
def b4_1_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 4).all (symValid 16 4 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 4 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 4 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 4 b4_1_pow 3 b4_1_L3 b4_1_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 4 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 4 b4_1_pow 4 b4_1_L4 b4_1_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 4 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
  intro i hi
  have hsz : b4_1_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
set_option maxRecDepth 100000 in
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 4 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L4_sound 0 (by decide))

def b4_2_goal : BitVec 16 := 0xe888
def b4_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_2_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_2_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_2_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_2_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_2_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_2_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_2_idx : Array (List ℕ) := Array.mk [b4_2_s0,b4_2_s1,b4_2_s2,b4_2_s3]
def b4_2_pow : Array (List ℕ) := Array.mk [b4_2_p0,b4_2_p1,b4_2_p2,b4_2_p3]
def b4_2_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_G_valid : (List.range 4).all (symValid 16 4 b4_2_idx b4_2_pow b4_2_inv b4_2_goal) = true := by decide +kernel
def b4_2_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[])
]
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[]),
([0xaaaa,0xcccc,0xf000,0xf0f0],[]),
([0xf0,0xaaaa,0xcccc,0xf0f0],[(0,0)])
]
def b4_2_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_2_0 : checkBlockP 16 jumps4 b4_2_goal 4 b4_2_pow 2 b4_2_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_2 : ∀ i < b4_2_L2.size, checkNodeP 16 jumps4 b4_2_goal 4 b4_2_pow 2 b4_2_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_2_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_2_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_3_0 : checkBlockP 16 jumps4 b4_2_goal 4 b4_2_pow 3 b4_2_L3 b4_2_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_3 : ∀ i < b4_2_L3.size, checkNodeP 16 jumps4 b4_2_goal 4 b4_2_pow 3 b4_2_L3 b4_2_L2 i = true := by
  intro i hi
  have hsz : b4_2_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_2_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_4_0 : checkBlockP 16 jumps4 b4_2_goal 4 b4_2_pow 4 b4_2_L4 b4_2_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_4 : ∀ i < b4_2_L4.size, checkNodeP 16 jumps4 b4_2_goal 4 b4_2_pow 4 b4_2_L4 b4_2_L3 i = true := by
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

def b4_3_goal : BitVec 16 := 0xfeea
def b4_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_3_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_3_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_3_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_3_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_3_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_3_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_3_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_3_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_3_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_3_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0,b4_3_s1,b4_3_s2,b4_3_s3,b4_3_s4,b4_3_s5]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0,b4_3_p1,b4_3_p2,b4_3_p3,b4_3_p4,b4_3_p5]
def b4_3_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_G_valid : (List.range 6).all (symValid 16 6 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xcccc,0xfafa,0xffaa],[])
]
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_3_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_2_0 : checkBlockP 16 jumps4 b4_3_goal 6 b4_3_pow 2 b4_3_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_2 : ∀ i < b4_3_L2.size, checkNodeP 16 jumps4 b4_3_goal 6 b4_3_pow 2 b4_3_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_3_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 6 b4_3_pow 3 b4_3_L3 b4_3_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 6 b4_3_pow 3 b4_3_L3 b4_3_L2 i = true := by
  intro i hi
  have hsz : b4_3_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_4_0 : checkBlockP 16 jumps4 b4_3_goal 6 b4_3_pow 4 b4_3_L4 b4_3_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_4 : ∀ i < b4_3_L4.size, checkNodeP 16 jumps4 b4_3_goal 6 b4_3_pow 4 b4_3_L4 b4_3_L3 i = true := by
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

def b4_4_goal : BitVec 16 := 0xe8a8
def b4_4_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_4_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_4_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_4_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_4_idx : Array (List ℕ) := Array.mk [b4_4_s0,b4_4_s1]
def b4_4_pow : Array (List ℕ) := Array.mk [b4_4_p0,b4_4_p1]
def b4_4_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_G_valid : (List.range 2).all (symValid 16 2 b4_4_idx b4_4_pow b4_4_inv b4_4_goal) = true := by decide +kernel
def b4_4_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcc88,0xf0f0],[]),
([0xaaaa,0xcc0c,0xf0f0],[])
]
def b4_4_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(1,0)]),
([0x5500,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcc00,0xcccc,0xf0f0],[]),
([0xcc,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_4_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_2_0 : checkBlockP 16 jumps4 b4_4_goal 2 b4_4_pow 2 b4_4_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_2 : ∀ i < b4_4_L2.size, checkNodeP 16 jumps4 b4_4_goal 2 b4_4_pow 2 b4_4_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_4_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_4_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_3_0 : checkBlockP 16 jumps4 b4_4_goal 2 b4_4_pow 3 b4_4_L3 b4_4_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_3 : ∀ i < b4_4_L3.size, checkNodeP 16 jumps4 b4_4_goal 2 b4_4_pow 3 b4_4_L3 b4_4_L2 i = true := by
  intro i hi
  have hsz : b4_4_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_4_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_4_0 : checkBlockP 16 jumps4 b4_4_goal 2 b4_4_pow 4 b4_4_L4 b4_4_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_4 : ∀ i < b4_4_L4.size, checkNodeP 16 jumps4 b4_4_goal 2 b4_4_pow 4 b4_4_L4 b4_4_L3 i = true := by
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

def u0 : BitVec 32 := 0xf0f0f0f0
def u1 : BitVec 32 := 0xaaaaaaaa
def u2 : BitVec 32 := 0xff00ff00
def u3 : BitVec 32 := 0xffff0000
def u4 : BitVec 32 := 0xcccccccc
def u5 : BitVec 32 := 0xfff0fff0
def u6 : BitVec 32 := 0xeeeeeeee
def u7 : BitVec 32 := 0xffffff00
def u8 : BitVec 32 := 0xfafafafa
def u9 : BitVec 32 := 0xf000f000
def u10 : BitVec 32 := 0xf0f0
def u11 : BitVec 32 := 0xff000000
def u12 : BitVec 32 := 0xfffffff0
def u13 : BitVec 32 := 0x30303030
def u14 : BitVec 32 := 0xfff0
def u15 : BitVec 32 := 0xffffaaaa
def u16 : BitVec 32 := 0xffaaffaa
def u17 : BitVec 32 := 0xfffff0f0
def u18 : BitVec 32 := 0xffffcccc
def u19 : BitVec 32 := 0xffff00
def u20 : BitVec 32 := 0xff0000
def u21 : BitVec 32 := 0xfcfcfcfc
def u22 : BitVec 32 := 0xfafa
def u23 : BitVec 32 := 0xfefefefe
def u24 : BitVec 32 := 0xeeee
def u25 : BitVec 32 := 0xf0f0000
def u26 : BitVec 32 := 0x32323232
def u27 : BitVec 32 := 0xff00
def u28 : BitVec 32 := 0xffccffcc
def u29 : BitVec 32 := 0xfffff0
def u30 : BitVec 32 := 0x33303330
def u31 : BitVec 32 := 0xffff00f0
def u32 : BitVec 32 := 0x33003300
def u33 : BitVec 32 := 0xf0f0fff0
def u34 : BitVec 32 := 0xf000f0
def u35 : BitVec 32 := 0xfffafffa
def u36 : BitVec 32 := 0xf0fff0
def u37 : BitVec 32 := 0xffffeeee
def u38 : BitVec 32 := 0xfcccfccc
def u39 : BitVec 32 := 0xf0f0f00
def u40 : BitVec 32 := 0x55550000
def u41 : BitVec 32 := 0xfff00000
def u42 : BitVec 32 := 0xf0fffff0
def u43 : BitVec 32 := 0xe0e0e0e0
def u44 : BitVec 32 := 0xf000f00
def u45 : BitVec 32 := 0xaa00aa
def u46 : BitVec 32 := 0xeee0eee0
def u47 : BitVec 32 := 0xf0e0f0e0
def u48 : BitVec 32 := 0xaaaafafa
def u49 : BitVec 32 := 0xff0fff00
def u50 : BitVec 32 := 0xf0f0f000
def u51 : BitVec 32 := 0xf0fff0f0
def u52 : BitVec 32 := 0xf000f0f0
def u53 : BitVec 32 := 0xf3f0f3f0
def u54 : BitVec 32 := 0xcccc0000

def c5_0_goal : BitVec 32 := 0xfeeeeee8
def c5_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
def c5_0_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s2 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]
def c5_0_p2 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_0_s3 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
def c5_0_p3 : List ℕ := [1,2,4,8,256,512,1024,2048,65536,131072,262144,524288,16777216,33554432,67108864,134217728,16,32,64,128,4096,8192,16384,32768,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_0_s4 : List ℕ := [0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31]
def c5_0_p4 : List ℕ := [1,2,4,8,65536,131072,262144,524288,16,32,64,128,1048576,2097152,4194304,8388608,256,512,1024,2048,16777216,33554432,67108864,134217728,4096,8192,16384,32768,268435456,536870912,1073741824,2147483648]
def c5_0_s5 : List ℕ := [0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]
def c5_0_p5 : List ℕ := [1,2,4,8,65536,131072,262144,524288,256,512,1024,2048,16777216,33554432,67108864,134217728,16,32,64,128,1048576,2097152,4194304,8388608,4096,8192,16384,32768,268435456,536870912,1073741824,2147483648]
def c5_0_s6 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31]
def c5_0_p6 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768,65536,262144,131072,524288,1048576,4194304,2097152,8388608,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648]
def c5_0_s7 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]
def c5_0_p7 : List ℕ := [1,4,2,8,16,64,32,128,65536,262144,131072,524288,1048576,4194304,2097152,8388608,256,1024,512,2048,4096,16384,8192,32768,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648]
def c5_0_s8 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]
def c5_0_p8 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768,65536,262144,131072,524288,16777216,67108864,33554432,134217728,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_0_s9 : List ℕ := [0,2,1,3,8,10,9,11,16,18,17,19,24,26,25,27,4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31]
def c5_0_p9 : List ℕ := [1,4,2,8,256,1024,512,2048,65536,262144,131072,524288,16777216,67108864,33554432,134217728,16,64,32,128,4096,16384,8192,32768,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_0_s10 : List ℕ := [0,2,1,3,16,18,17,19,4,6,5,7,20,22,21,23,8,10,9,11,24,26,25,27,12,14,13,15,28,30,29,31]
def c5_0_p10 : List ℕ := [1,4,2,8,65536,262144,131072,524288,16,64,32,128,1048576,4194304,2097152,8388608,256,1024,512,2048,16777216,67108864,33554432,134217728,4096,16384,8192,32768,268435456,1073741824,536870912,2147483648]
def c5_0_s11 : List ℕ := [0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31]
def c5_0_p11 : List ℕ := [1,4,2,8,65536,262144,131072,524288,256,1024,512,2048,16777216,67108864,33554432,134217728,16,64,32,128,1048576,4194304,2097152,8388608,4096,16384,8192,32768,268435456,1073741824,536870912,2147483648]
def c5_0_idx : Array (List ℕ) := Array.mk [c5_0_s0,c5_0_s1,c5_0_s2,c5_0_s3,c5_0_s4,c5_0_s5,c5_0_s6,c5_0_s7,c5_0_s8,c5_0_s9,c5_0_s10,c5_0_s11]
def c5_0_pow : Array (List ℕ) := Array.mk [c5_0_p0,c5_0_p1,c5_0_p2,c5_0_p3,c5_0_p4,c5_0_p5,c5_0_p6,c5_0_p7,c5_0_p8,c5_0_p9,c5_0_p10,c5_0_p11]
def c5_0_inv : Array ℕ := Array.mk [0,1,2,4,3,5,6,7,8,10,9,11]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_G_valid : (List.range 12).all (symValid 32 12 c5_0_idx c5_0_pow c5_0_inv c5_0_goal) = true := by decide +kernel
def c5_0_m0 : BitVec 32 := 0xf0f0f0f
def c5_0_st0 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_0_ix0 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_0 : c5_0_ix0.length = 16 ∧ (∀ idx ∈ c5_0_ix0, idx < 32) ∧ (∀ idx ∈ c5_0_ix0, c5_0_m0.getLsbD idx = true) ∧ projS 16 c5_0_ix0 c5_0_goal = b4_1_goal ∧ c5_0_st0.all (fun w => rows4.contains (projS 16 c5_0_ix0 w)) = true := by decide +kernel
def c5_0_m1 : BitVec 32 := 0x55555555
def c5_0_st1 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_0_ix1 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_1 : c5_0_ix1.length = 16 ∧ (∀ idx ∈ c5_0_ix1, idx < 32) ∧ (∀ idx ∈ c5_0_ix1, c5_0_m1.getLsbD idx = true) ∧ projS 16 c5_0_ix1 c5_0_goal = b4_0_goal ∧ c5_0_st1.all (fun w => rows4.contains (projS 16 c5_0_ix1 w)) = true := by decide +kernel
def c5_0_m2 : BitVec 32 := 0x33333333
def c5_0_st2 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def c5_0_ix2 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_2 : c5_0_ix2.length = 16 ∧ (∀ idx ∈ c5_0_ix2, idx < 32) ∧ (∀ idx ∈ c5_0_ix2, c5_0_m2.getLsbD idx = true) ∧ projS 16 c5_0_ix2 c5_0_goal = b4_0_goal ∧ c5_0_st2.all (fun w => rows4.contains (projS 16 c5_0_ix2 w)) = true := by decide +kernel
def c5_0_m3 : BitVec 32 := 0xffff
def c5_0_st3 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_0_ix3 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_3 : c5_0_ix3.length = 16 ∧ (∀ idx ∈ c5_0_ix3, idx < 32) ∧ (∀ idx ∈ c5_0_ix3, c5_0_m3.getLsbD idx = true) ∧ projS 16 c5_0_ix3 c5_0_goal = b4_1_goal ∧ c5_0_st3.all (fun w => rows4.contains (projS 16 c5_0_ix3 w)) = true := by decide +kernel
def c5_0_m4 : BitVec 32 := 0xff00ff
def c5_0_st4 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_0_ix4 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_4 : c5_0_ix4.length = 16 ∧ (∀ idx ∈ c5_0_ix4, idx < 32) ∧ (∀ idx ∈ c5_0_ix4, c5_0_m4.getLsbD idx = true) ∧ projS 16 c5_0_ix4 c5_0_goal = b4_1_goal ∧ c5_0_st4.all (fun w => rows4.contains (projS 16 c5_0_ix4 w)) = true := by decide +kernel
def c5_0_cfMasks : Array (BitVec 32) := Array.mk [c5_0_m0,c5_0_m1,c5_0_m2,c5_0_m3,c5_0_m4]
def c5_0_cfB0s : Array ℕ := Array.mk [0,0,0,0,0]
def c5_0_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_0_st0,c5_0_st1,c5_0_st2,c5_0_st3,c5_0_st4]
def c5_0_cfLBs : Array ℕ := Array.mk [5,6,6,5,5]
theorem c5_0_cof_sound (c fuel : ℕ) (hc : c < 5) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_0_cfLBs[c]?.getD 0) fuel (c5_0_cfMasks[c]?.getD 0) (c5_0_cfB0s[c]?.getD 0) (c5_0_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_0_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix0 c5_0_cspec_0.1 c5_0_cspec_0.2.1 c5_0_m0 c5_0_cspec_0.2.2.1 0 c5_0_st0 b4_1_goal (by decide) c5_0_cspec_0.2.2.2.1 c5_0_cspec_0.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_0_goal 6 c5_0_ix1 c5_0_cspec_1.1 c5_0_cspec_1.2.1 c5_0_m1 c5_0_cspec_1.2.2.1 0 c5_0_st1 b4_0_goal (by decide) c5_0_cspec_1.2.2.2.1 c5_0_cspec_1.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_0_goal 6 c5_0_ix2 c5_0_cspec_2.1 c5_0_cspec_2.2.1 c5_0_m2 c5_0_cspec_2.2.2.1 0 c5_0_st2 b4_0_goal (by decide) c5_0_cspec_2.2.2.2.1 c5_0_cspec_2.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix3 c5_0_cspec_3.1 c5_0_cspec_3.2.1 c5_0_m3 c5_0_cspec_3.2.2.1 0 c5_0_st3 b4_1_goal (by decide) c5_0_cspec_3.2.2.2.1 c5_0_cspec_3.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix4 c5_0_cspec_4.1 c5_0_cspec_4.2.1 c5_0_m4 c5_0_cspec_4.2.2.1 0 c5_0_st4 b4_1_goal (by decide) c5_0_cspec_4.2.2.2.1 c5_0_cspec_4.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | c + 5 => omega
def c5_0_L2 : Array W5Node := Array.mk [
([u1,u38,0xffffeee0],[],[],[]),
([u1,u4,0xf00f0ff0],[],[],[])
]
def c5_0_L3 : Array W5Node := Array.mk [
([u46,u8,u28,u3],[],[],[]),
([u6,u0,0xffaacc88,u7],[],[],[]),
([u1,u4,u47,0xffffee00],[],[],[]),
([u1,u4,u0,0xffeeee00],[],[],[]),
([u1,u4,0xf0e0ffe0,u3],[],[],[]),
([u1,u4,0xf00ef00e,u3],[],[],[]),
([u1,u46,u38,u3],[],[],[(0,0)]),
([u1,u4,u9,0xffffeee0],[],[],[(0,0),(6,0)]),
([u1,u38,u18,u12],[(u18,u4,u3),(u7,u3,u2),(u9,u2,u0),(u38,u4,u9),(u12,u0,u7)],[0],[]),
([u29,u1,u4,u8],[],[],[]),
([0xffff30,u1,u4,u0],[],[],[]),
([u29,u13,u1,u4],[],[],[]),
([u1,0xaaffffaa,u4,u42],[],[],[]),
([u19,u1,u4,0xf0f3f3f0],[],[],[]),
([u19,u1,u4,0xf0a0a0f0],[],[],[]),
([0x333300,u1,u4,u42],[],[],[]),
([u19,u1,u4,0xf00000f0],[],[],[]),
([0xf0f000,u1,u4,u42],[],[],[(0,1)]),
([u1,u4,0xf00000f0,u42],[],[],[]),
([u19,u1,u4,u42],[],[],[]),
([0xff0,u1,u4,0xf00f0000],[],[],[(0,1)]),
([u29,u1,u4,u0],[],[],[]),
([u29,u1,u4,u50],[],[],[]),
([0xffff0,u1,u4,u9],[],[],[]),
([u14,0xfff0ff0,u1,u4],[(u9,u0,u2),(u5,u0,u2),(u12,u5,u3),(0xfff0ff0,u9,u12),(u14,u3,u12)],[0],[]),
([u14,u1,u4,0xf00ff000],[],[],[]),
([u14,0xfff00f0,u1,u4],[(u9,u0,u2),(u17,u0,u3),(0xfff00f0,u9,u17),(u12,0xfff00f0,u2),(u14,u3,u12)],[0],[]),
([0xffffff0,u1,u4],[],[],[]),
([u36,0xffffff0,u1,u4],[],[],[])
]
set_option maxRecDepth 100000 in
def c5_0_L4 : Array W5Node := Array.mk [
([u6,u0,u2,u15,0xfffffcfc],[(u6,u1,u4),(u15,u1,u3),(u18,u4,u3),(0xfffffcfc,u0,u18)],[1],[]),
([u22,u6,u21,u2,u3],[],[],[]),
([u6,u0,u16,u18,u7],[],[],[(0,1),(4,0)]),
([u6,u0,0xfac8fac8,u2,u3],[(u6,u4,u1),(u28,u4,u2),(u8,u1,u0),(0xfac8fac8,u8,u28)],[1,2],[(3,1)]),
([u1,u6,u0,u28,0xffffee00],[],[],[]),
([u1,u46,u0,u28,u3],[(u6,u4,u1),(u28,u4,u2),(u5,u2,u0),(u46,u6,u5)],[2],[(0,0)]),
([u48,u6,u21,u2,u3],[],[],[]),
([u1,u6,u0,u49,u18],[],[],[]),
([u1,u4,u0,0xffeeff00,u37],[],[],[(0,3),(1,2)]),
([0x1111eeee,u1,u4,u0,u2],[(u6,u1,u4),(0xeeee0000,u6,u3),(u37,u6,u3),(0x1111eeee,0xeeee0000,u37)],[1],[]),
([u1,u4,u43,0xfe00fe00,u3],[],[],[(2,2),(3,3)]),
([u26,0x54545454,u0,u2,u3],[],[],[]),
([u24,0x33332222,u1,u0,u2],[],[],[]),
([u24,u1,u4,0xf0f0e0e0,u2],[],[],[]),
([u1,u4,0xf0eef0ee,u0,u3],[],[],[]),
([u1,u4,u0,u49,u37],[(u6,u1,u4),(u37,u6,u3),(u25,u3,u0),(u49,u25,u2)],[0],[(4,4)]),
([0xfefe,u1,u4,u0,u2],[],[],[]),
([u1,u4,u47,u2,0xffee0000],[],[],[]),
([0xfefe,u1,u4,u0,0xfe00fe00],[],[],[]),
([0xfffe,u1,u4,u0,u2],[],[],[]),
([0xfefe,0xfe00fe,u1,u4,u0],[],[],[]),
([u10,u1,u4,0xf0f0fefe,u2],[],[],[(1,5)]),
([0xf0fe,u1,u4,u0,u2],[],[],[]),
([0xee,u1,u4,u0,u11],[],[],[(4,5)]),
([u24,u1,0xccccfcfc,u0,u2],[],[],[]),
([u24,u1,u4,0xf0f000f0,u2],[],[],[]),
([u1,u6,u0,0xffcccccc,u7],[],[],[(4,6)]),
([u1,u4,u0,0xffeeeeee,u7],[(u6,u1,u4),(u11,u2,u3),(0xffeeeeee,u6,u11),(u7,u2,u3)],[0],[(0,3)]),
([0xfeee,u1,u4,u0,u2],[],[],[]),
([u1,u4,u46,u9,u3],[],[],[(0,6),(0,7),(3,3),(6,6)]),
([u19,u1,u4,u6,u0],[(u6,u1,u4),(u11,u2,u3),(u7,u2,u3),(u19,u11,u7)],[1],[]),
([u1,u4,u0,u2,0xffffeee0],[],[],[(0,7)]),
([u1,0xaaaafcfc,u4,u0,u2],[],[],[]),
([u26,u1,u4,u2,u31],[],[],[]),
([u1,u4,u0,0xffaacc88,u7],[],[],[(0,1)]),
([u1,u0,u38,u18,u7],[(u18,u4,u3),(u7,u3,u2),(u9,u2,u0),(u38,u4,u9)],[0],[(0,8)]),
([u36,u1,u4,u8,u3],[],[],[]),
([u1,u4,u9,u15,u12],[(u15,u1,u3),(u7,u3,u2),(u9,u2,u0),(u12,u0,u7)],[0],[(3,9),(6,8)]),
([u1,u4,0xf0a0ffaa,u5,u3],[],[],[]),
([u10,u39,u1,u4,u16],[],[],[(2,9)]),
([u22,0x55555050,u4,u0,u2],[],[],[]),
([u1,u4,0xf0a0ffa0,u33,u3],[],[],[]),
([u1,u4,0xf0a0ffa0,u0,u3],[],[],[]),
([u22,u1,u4,u0,u49],[],[],[]),
([0x33ffcc,u1,u4,u0,u2],[(u28,u4,u2),(0xffcc0000,u28,u3),(0xffffffcc,u3,u28),(0x33ffcc,0xffcc0000,0xffffffcc)],[2],[]),
([u22,0xf0f0a0a,u1,u4,u2],[],[],[]),
([0x33333332,u1,u0,u2,u3],[],[],[]),
([u22,u1,u4,u51,u2],[],[],[]),
([u22,u1,u4,u0,0xff05ff00],[],[],[]),
([u1,u0,u21,0xffcccccc,u7],[(u21,u4,u0),(u11,u2,u3),(0xffcccccc,u4,u11),(u7,u2,u3)],[0],[(4,8)]),
([0xfafafa,u1,u4,u0,u7],[],[],[]),
([u19,u1,u4,u0,u8],[(u8,u1,u0),(u11,u2,u3),(u7,u2,u3),(u19,u11,u7)],[1],[]),
([0x30ff30,u1,u4,u0,u3],[],[],[]),
([u1,u4,u9,0xfff3fff0,u3],[],[],[(3,10)]),
([u10,0xf0f0300,u1,u4,u2],[],[],[(2,10)]),
([u36,u13,u1,u4,u3],[(u13,u4,u0),(u5,u0,u2),(u11,u2,u3),(u36,u11,u5)],[3],[]),
([u13,u1,u4,u11,u12],[(u13,u4,u0),(u17,u0,u3),(u11,u3,u2),(u12,u2,u17)],[0],[(0,11)]),
([u10,u39,u32,u1,u4],[],[],[(2,11)]),
([0x3030fff0,u1,u4,u2,u3],[],[],[]),
([0xaaa0fff0,u1,u4,u9,u3],[(u40,u1,u3),(u9,u0,u2),(u5,u0,u2),(0xaaa0fff0,u40,u5)],[3],[]),
([u19,u13,u1,u4,u0],[],[],[]),
([0x32223222,u1,u4,u5,u3],[],[],[]),
([u30,u1,u38,u5,u3],[],[],[]),
([u1,u4,u0,0xffaaaaaa,u12],[(u11,u2,u3),(0xffaaaaaa,u1,u11),(u7,u2,u3),(u12,u0,u7)],[0],[(10,8)]),
([u14,u1,u4,0xfaaafaaa,u3],[],[],[]),
([0x333300,u1,u4,u0,u7],[(u11,u2,u3),(0xffcccccc,u4,u11),(u7,u2,u3),(0x333300,0xffcccccc,u7)],[0],[]),
([u19,u1,u4,u0,0xffffffaa],[],[],[]),
([0xffffaa,u1,u4,u0,u7],[(u11,u2,u3),(u7,u2,u3),(0xffffffaa,u1,u7),(0xffffaa,u11,0xffffffaa)],[1],[]),
([u19,0x33333300,u1,u4,u0],[],[],[]),
([u19,u1,0xaaffffaa,u4,u0],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7),(0xaaffffaa,u19,u1)],[1],[(0,12)]),
([0x333300,u19,u1,u4,u0],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7),(0x333300,u19,u4)],[2],[(0,13),(0,15),(6,14)]),
([0xf0f000,u19,u1,u4,u0],[],[],[(0,16),(0,17)]),
([u19,u1,u4,u42],[],[],[(0,12),(0,15),(0,16),(0,18),(6,12),(6,15)]),
([u19,u1,u4,u0,u42],[],[],[(0,17),(0,18)]),
([0xff0,0xff00ff0,u1,u4,u3],[],[],[(0,20),(3,19)]),
([u19,u1,u4,0xf00000f0],[],[],[(0,18),(0,19)]),
([u19,u1,u4,0xf00000f0,u0],[],[],[(0,18),(4,20)]),
([u1,0xaaffffaa,u4,u0,u7],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7),(0xaaffffaa,u19,u1)],[1],[]),
([u19,u1,u4,u42,u7],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7),(u42,u19,u0)],[0,4],[]),
([u19,u1,u4,0xf00000f0,u7],[],[],[]),
([u19,u1,u4,u50,u0],[],[],[]),
([u19,u1,u4,u0,u12],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7),(u12,u0,u7)],[0],[]),
([0xf0,u19,u1,u4,u0],[],[],[(0,21)]),
([u14,0xff00ff0,u1,u4,u3],[(u9,u0,u2),(u5,u0,u2),(0xff00ff0,u9,u5),(u14,u3,u5)],[0,3],[]),
([u14,u1,u4,u9,u3],[(u9,u0,u2),(u5,u0,u2),(u41,u5,u3),(u14,u41,u5)],[3],[]),
([u1,u4,u9,u41,u12],[(u9,u0,u2),(u5,u0,u2),(u41,u5,u3),(u12,u5,u3)],[0],[(0,23),(3,22)]),
([u29,u1,u4,u0],[(u11,u2,u3),(u7,u2,u3),(u12,u7,u0),(u29,u11,u12)],[4],[(0,9),(0,11),(6,9),(6,11)]),
([u29,u1,u4,u0,u12],[(u11,u2,u3),(u7,u2,u3),(u12,u7,u0),(u29,u11,u12)],[0],[(4,24)]),
([u14,u1,u4,u9,u12],[(u9,u0,u2),(u5,u0,u2),(u12,u5,u3),(u14,u3,u12)],[0],[(0,24)]),
([u29,u1,u4,u0,u7],[(u11,u2,u3),(u7,u2,u3),(u12,u7,u0),(u29,u11,u12)],[4],[(0,22),(4,24)]),
([u1,u4,0xf000fff0,u3],[],[],[]),
([u14,u1,u4,0xf000fff0,u3],[(u9,u0,u2),(u5,u0,u2),(u14,u5,u3),(0xf000fff0,u14,u9)],[0],[]),
([u1,u4,u9,u3,u12],[(u9,u0,u2),(u5,u0,u2),(u14,u5,u3),(u12,u14,u3)],[0],[(3,21)]),
([u1,u4,0xf000fff0,u5,u3],[],[],[]),
([0xf0,u39,u1,u4,u11],[],[],[(4,23),(4,25)]),
([u1,u4,0xf00ff000,u5,u3],[(u9,u0,u2),(u5,u0,u2),(0xf0000,u5,u3),(0xf00ff000,0xf0000,u9)],[0],[(0,25)]),
([u36,u1,u4,u0,u12],[(u11,u2,u3),(u5,u2,u0),(u36,u11,u5),(u12,u36,u3)],[4],[(4,26)]),
([u36,u1,u4,u0,u17],[(u11,u2,u3),(u5,u2,u0),(u36,u11,u5),(u17,u0,u3)],[3],[]),
([u29,u1,u4,u0,u5],[(u11,u2,u3),(u5,u2,u0),(u12,u3,u5),(u29,u11,u12)],[4],[]),
([u14,u1,u4,u9,u17],[],[],[(0,26)]),
([u14,0xff00f0,u1,u4,u0],[],[],[(0,21)]),
([u14,u29,u1,u4,u0],[(u5,u2,u0),(u20,u2,u3),(u14,u3,u5),(u29,u20,u14)],[3],[]),
([u14,u1,u4,u0,u49],[],[],[]),
([u29,u1,u4,u0,u2],[(u5,u2,u0),(u20,u2,u3),(u14,u3,u5),(u29,u20,u14)],[4],[]),
([0xffff0,u1,u4,u0,u2],[],[],[(0,23)]),
([u1,u48,u4,u51,u2],[],[],[]),
([u10,u39,u1,u4,u2],[],[],[(2,21)]),
([u10,0xfff0f00,u1,u4],[(u44,u2,u0),(u20,u2,u3),(u10,u3,u0),(0xfff0f00,u20,u44)],[0],[(0,27),(5,28)])
]
set_option maxRecDepth 100000 in
def c5_0_L5 : Array W5Node := Array.mk [
([u6,u0,u2,u15,u18],[(u6,u4,u1),(u18,u4,u3),(u15,u1,u3)],[1,2,3],[(0,0),(2,0),(3,1),(5,1),(6,0),(8,0),(9,1),(11,1)]),
([u6,u0,u8,u21,u2,u3],[(u6,u4,u1),(u21,u4,u0),(u8,u1,u0)],[0,1,2],[]),
([u26,u6,u0,u8,u2,u3],[(u6,u1,u4),(u8,u1,u0),(u26,u4,u8)],[1,2],[]),
([u6,u0,u8,u2,u28,u3],[],[],[(0,3),(3,2),(4,0),(7,0)]),
([u1,u43,u6,u21,u2,u3],[(u6,u4,u1),(u21,u4,u0),(u43,u6,u0)],[2],[(2,4),(3,4)]),
([u24,u1,u6,u0,u2,u18],[(u6,u4,u1),(u18,u4,u3),(u24,u6,u3)],[2,3],[]),
([u1,u6,u0,u2,u18,u17],[],[],[(1,5),(2,2),(6,0)]),
([u10,u1,u6,u21,u2,u3],[],[],[(0,6),(5,7)]),
([u1,u6,u0,u2,0xfffcfffc,u3],[(u6,u4,u1),(u21,u4,u0),(0xfffcfffc,u21,u2)],[1],[(1,0),(4,0)]),
([u22,u4,u6,u0,u2,u3],[(u6,u1,u4),(u8,u1,u0),(u22,u8,u3)],[2],[(0,1)]),
([u24,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u6,u0,u2,0xffffe0e0],[(u6,u1,u4),(u43,u6,u0),(0xffffe0e0,u43,u3)],[0,1],[(2,4),(4,8),(8,4)]),
([0x1010f0f0,u1,u4,u6,u2,u3],[(u6,u1,u4),(0xeeee0000,u6,u3),(0x1010f0f0,0xeeee0000,u0)],[1],[]),
([u1,u4,u43,u23,u2,u3],[],[],[(0,10),(1,10),(4,8),(4,9),(5,8)]),
([u26,u1,u0,u23,u2,u3],[(u6,u4,u1),(u23,u6,u0),(u26,u4,u23)],[1],[(0,11),(4,12)]),
([u24,u1,u4,u0,u2,u37],[(u6,u1,u4),(u37,u6,u3),(u24,u3,u37)],[1],[(0,12),(0,13),(2,13),(6,12)]),
([u1,u4,u0,u2,u37,u17],[(u6,u1,u4),(u37,u6,u3),(u17,u3,u0)],[0,4],[]),
([u10,u1,u4,u23,u2,u3],[(u6,u1,u4),(u23,u6,u0),(u10,u0,u3)],[3,4],[(3,14),(5,15)]),
([u1,u4,u47,u2,0xffeeffee,u3],[],[],[(0,17),(1,13),(2,18),(4,16)]),
([u1,u4,u0,u2,0xfffefffe,u3],[(u6,u1,u4),(u23,u6,u0),(0xfffefffe,u23,u2)],[3],[(0,19),(1,16),(4,16)]),
([0xfefe,u1,u4,u0,u2],[],[],[]),
([0xfefe,u1,u4,u0,u23,u2],[(u6,u1,u4),(u23,u6,u0),(0xfefe,u23,u3)],[3],[(0,18),(0,20)]),
([0xfefe,u1,u4,u0,u2,u3],[],[],[]),
([u26,u1,u6,u0,u2,u3],[(u6,u4,u1),(u23,u6,u0),(u26,u4,u23)],[1],[(4,12)]),
([u1,u4,u6,u47,u2,u3],[(u6,u1,u4),(0xffeeffee,u6,u2),(u47,0xffeeffee,u0)],[1],[(1,13),(2,10)]),
([0xfefe,u1,u4,u6,u0,u2],[(u6,u1,u4),(u23,u6,u0),(0xfefe,u23,u3)],[1],[]),
([u1,u4,u0,0xf0f0fefe,u2,u3],[(u6,u1,u4),(u24,u6,u3),(0xf0f0fefe,u24,u0)],[4],[(0,16),(0,21),(1,22)]),
([0xee,u1,u4,u0,u2,u3],[],[],[(0,23)]),
([u1,u4,u0,u23,u2,u3],[(u6,u1,u4),(0xe0e0e0e,u6,u0),(u23,0xe0e0e0e,u0)],[3,4],[(0,16),(1,16)]),
([u24,u1,u4,0xf0f00000,u0,u2],[],[],[(1,14),(2,23)]),
([u24,u10,u1,u4,u0,u2],[],[],[(0,16),(0,21),(0,24),(2,25),(6,24)]),
([u24,0x11110000,u1,u4,u0,u2],[(u6,u1,u4),(u24,u6,u3),(0x11110000,u6,u3)],[1],[(0,9)]),
([u1,0xdcdcdcdc,u6,u0,u2,u3],[(u6,u4,u1),(0x10101010,u6,u0),(0xdcdcdcdc,0x10101010,u4)],[1],[]),
([u1,u6,u0,u38,u2,u3],[(u6,u4,u1),(u9,u0,u2),(u38,u4,u9)],[1,4],[(3,26)]),
([u1,u4,u0,0xfeeefeee,u2,u3],[(u6,u1,u4),(u9,u0,u2),(0xfeeefeee,u6,u9)],[0,3,4],[(0,28),(3,27)]),
([0xeeeeee,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u6,u9,u5,u3],[(u6,u1,u4),(u9,u0,u2),(u5,u0,u2)],[0,1],[(0,29),(3,23),(3,26),(3,27),(3,30),(9,26)]),
([u1,u4,u46,u0,u2,u3],[(u6,u1,u4),(u5,u0,u2),(u46,u6,u5)],[0,1,2,3,4],[(0,5),(0,29),(0,31),(6,5),(8,5)]),
([0x11101110,u1,u4,u0,u2,u3],[],[],[]),
([u1,0xccccfcfc,u6,u0,u2,u3],[(u6,u4,u1),(u10,u0,u3),(0xccccfcfc,u10,u4)],[1],[(0,24),(6,6)]),
([u1,u4,0xeeeefefe,u0,u2,u3],[],[],[(0,16)]),
([u1,u4,0xe0e0eeee,u0,u2,u3],[(u6,u1,u4),(u25,u3,u0),(0xe0e0eeee,u25,u6)],[0],[]),
([u1,u4,u6,u0,u2,u31],[(u6,u1,u4),(u34,u0,u2),(u31,u34,u3)],[0,1],[(4,7),(4,15),(10,7)]),
([u1,u4,u6,u52,u2,u3],[(u6,u1,u4),(u20,u3,u2),(u52,u20,u0)],[1,4],[(1,25)]),
([u10,u25,u1,u4,u6,u2],[(u6,u1,u4),(u10,u0,u3),(u25,u0,u3)],[1],[(2,30)]),
([u26,u1,u8,u21,u2,u3],[(u21,u4,u0),(u8,u1,u0),(u26,u4,u8)],[0],[]),
([u1,u4,u0,u2,u15,0xfffffcfc],[(u18,u4,u3),(u15,u1,u3),(0xfffffcfc,u0,u18)],[1],[(0,0)]),
([u22,u1,u4,u21,u2,u3],[],[],[(0,1)]),
([u26,u1,u0,u21,u2,u3],[(u21,u4,u0),(u8,u1,u0),(u26,u4,u8)],[1],[(0,11)]),
([u1,0xaaaacccc,u4,u0,u2,u18],[(u18,u4,u3),(u40,u1,u3),(0xaaaacccc,u40,u18)],[2,3],[]),
([u1,u4,u0,u53,u16,u3],[(u16,u1,u2),(u32,u4,u2),(u53,u32,u0)],[1],[]),
([u13,u1,u4,u2,u35,u3],[],[],[(10,32)]),
([u22,u13,u1,u4,u2,u3],[],[],[]),
([u24,u1,u4,u0,u2,u15],[(u15,u1,u3),(u37,u4,u15),(u24,u3,u37)],[1],[(0,12)]),
([u1,u4,u47,u2,u16,u3],[(u16,u1,u2),(0xffeeffee,u4,u16),(u47,0xffeeffee,u0)],[1],[]),
([0xfefe,u1,u4,u0,u8,u2],[(u8,u1,u0),(u23,u4,u8),(0xfefe,u23,u3)],[1],[]),
([u1,u4,u0,0xf3f2f3f2,u2,u3],[],[],[]),
([0x3232,u1,u4,u0,u2,u3],[],[],[]),
([u26,u1,u4,u2,u5,u3],[(u8,u1,u0),(u26,u4,u8),(u5,u0,u2)],[4],[]),
([u10,u26,u1,u4,u2,u3],[],[],[(1,33)]),
([u1,u4,u0,u16,u18,u7],[],[],[(0,2),(0,34)]),
([u1,u4,u0,0xfac8fac8,u2,u3],[(u8,u1,u0),(u28,u4,u2),(0xfac8fac8,u8,u28)],[1,2],[(0,3),(3,34)]),
([u1,u4,u0,u2,0xffff3030,u15],[(u15,u1,u3),(u13,u4,u0),(0xffff3030,u13,u3)],[1],[]),
([u1,u4,u0,0xfbfafbfa,u2,u3],[],[],[]),
([0xa8a8fcfc,u1,u4,u0,u2,u3],[(u21,u4,u0),(u40,u1,u3),(0xa8a8fcfc,u40,u21)],[1],[]),
([u13,u1,u4,u2,u15,u17],[(u15,u1,u3),(u13,u4,u0),(u17,u0,u3)],[0],[]),
([u30,u1,u0,u28,u5,u3],[(u28,u4,u2),(u5,u2,u0),(u30,u4,u5)],[2],[]),
([u30,u1,u4,u0,u16,u3],[(u16,u1,u2),(u5,u2,u0),(u30,u4,u5)],[1],[]),
([u1,u4,u9,u0,u15,u7],[(u15,u1,u3),(u7,u3,u2),(u9,u2,u0)],[0],[(0,37),(5,36),(6,35)]),
([u10,u1,u4,u0,u16,u7],[(u16,u1,u2),(u7,u2,u3),(u10,u3,u0)],[0,4],[(0,39),(5,38)]),
([u1,u4,0xf0a0f0a0,u16,u5,u3],[],[],[]),
([u22,u1,u4,u8,u2,u17],[(u8,u1,u0),(u17,u0,u3),(u22,u3,u8)],[3],[]),
([u1,u4,u0,u2,u15,u12],[(u15,u1,u3),(u17,u3,u0),(u12,u2,u17)],[0,1,4],[(0,37)]),
([u14,u1,u4,u0,u16,u3],[(u16,u1,u2),(u5,u2,u0),(u14,u3,u5)],[0,4],[(5,39)]),
([u30,u1,u0,u21,u2,u3],[(u21,u4,u0),(u5,u0,u2),(u30,u4,u5)],[1],[(7,40)]),
([u22,u1,u4,u0,u2,u17],[(u8,u1,u0),(u17,u0,u3),(u22,u8,u3)],[0,1],[(0,40)]),
([u1,u48,u4,u21,u2,u3],[],[],[(0,6)]),
([u1,u4,0xf0aaf0aa,u0,u16,u3],[(u16,u1,u2),(u44,u2,u0),(0xf0aaf0aa,u44,u16)],[4],[]),
([u1,u4,u0,u49,u15],[(u15,u1,u3),(u25,u3,u0),(u49,u25,u2)],[0,1,3,4],[(0,15),(3,33),(4,41),(6,7)]),
([u1,u4,u0,u33,u16,u3],[(u16,u1,u2),(u27,u2,u3),(u33,u27,u0)],[0],[(0,42)]),
([u1,u4,u0,u2,u15,u17],[(u15,u1,u3),(u25,u3,u0),(u17,u25,u0)],[0,1],[]),
([u10,u1,u4,u8,u2,u7],[(u8,u1,u0),(u10,u0,u3),(u7,u2,u3)],[4],[]),
([u10,u20,u1,u4,u8,u2],[],[],[(1,36)]),
([u1,0xccccfcfc,u0,u2,u3,u18],[(u18,u4,u3),(u10,u3,u0),(0xccccfcfc,u10,u4)],[1,2],[]),
([u1,u4,u0,u8,u2,0xffff0f00],[(u8,u1,u0),(u44,u0,u2),(0xffff0f00,u44,u3)],[0,1,4],[(1,43)]),
([u1,u4,u52,u2,u16,u3],[(u16,u1,u2),(u20,u2,u3),(u52,u20,u0)],[1],[]),
([u1,u4,u0,u2,u35,u3],[],[],[]),
([u10,0xf0f0a0a,u1,u4,u2,u3],[(u15,u1,u3),(u10,u3,u0),(0xf0f0a0a,u0,u15)],[1],[(5,43)]),
([u22,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,0xf0a0f0a0,u2,u35,u3],[(u16,u1,u2),(0xf0a0f0a0,u16,u0),(u35,u0,u16)],[1],[(11,44)]),
([u30,u1,u0,u2,0xfffcfffc,u3],[(u21,u4,u0),(0xfffcfffc,u21,u2),(u30,u4,0xfffcfffc)],[1],[(7,40),(10,40)]),
([0x33323332,u1,u4,u0,u2,u3],[],[],[]),
([u22,u1,u4,u0,u2,0xfffffafa],[(u15,u1,u3),(0xfffffafa,u15,u0),(u22,u3,0xfffffafa)],[1],[(0,40),(0,45)]),
([u1,u4,u0,u2,u3,0xfffffffa],[(u8,u1,u0),(u35,u8,u2),(0xfffffffa,u35,u3)],[2],[(0,46)]),
([0xfffa,u1,u4,u0,u2,u3],[],[],[]),
([u22,u1,u4,u0,u2,u15],[(u15,u1,u3),(0xfffffafa,u15,u0),(u22,u3,0xfffffafa)],[1],[(0,45)]),
([u1,0xaaaafefe,u4,u0,u2,u3],[(u21,u4,u0),(0xfcfc,u21,u3),(0xaaaafefe,0xfcfc,u1)],[1],[]),
([u1,u4,u0,0xf0f0fffa,u2,u3],[(u16,u1,u2),(0xffaa,u16,u3),(0xf0f0fffa,0xffaa,u0)],[4],[]),
([0xfa,u1,u4,u0,u2,u3],[],[],[]),
([u22,u1,u4,u0,u2,u7],[(u8,u1,u0),(u22,u8,u3),(u7,u2,u3)],[4],[]),
([u10,0xf0a0f0a,u1,u4,u2,u3],[],[],[(4,47)]),
([0x3030,0xf0f0c0c,u1,u4,u2,u3],[(u18,u4,u3),(0xf0f0c0c,u18,u0),(0x3030,u18,u0)],[2],[(4,44),(11,48)]),
([u1,u4,u0,u8,u2,0xffff0500],[(u8,u1,u0),(0x5000500,u8,u2),(0xffff0500,0x5000500,u3)],[1,4],[(1,48)]),
([u1,u4,0xf0a0f0f0,u2,u16,u3],[(u16,u1,u2),(0x550000,u16,u3),(0xf0a0f0f0,0x550000,u0)],[1],[]),
([u1,u4,u0,u2,0xffff3030,u18],[(u18,u4,u3),(0x3030,u18,u0),(0xffff3030,0x3030,u3)],[0,1,2],[]),
([u1,u0,u38,u2,u3,u18],[(u18,u4,u3),(u9,u0,u2),(u38,u4,u9)],[0,3],[(0,35),(2,35),(3,49)]),
([u1,u4,u0,u2,u15,0xfffff000],[(u15,u1,u3),(u9,u0,u2),(0xfffff000,u9,u3)],[1],[]),
([u1,u4,u0,u2,0xfffafafa,u3],[],[],[]),
([0xfafafa,u1,u4,u0,u2,u3],[],[],[(0,50)]),
([u1,u4,u9,u5,u3,u15],[(u15,u1,u3),(u9,u0,u2),(u5,u0,u2)],[0,1,3],[(0,37),(3,50),(3,51),(9,49)]),
([u1,u4,u0,0xfafafa00,u2,u3],[(u8,u1,u0),(u7,u2,u3),(0xfafafa00,u8,u7)],[1],[]),
([0x3330,u1,u4,u0,u2,u3],[(u18,u4,u3),(u5,u0,u2),(0x3330,u18,u5)],[0,4],[]),
([u1,u4,u0,u2,u31,u15],[(u15,u1,u3),(u34,u0,u2),(u31,u34,u3)],[0,1],[(5,47)]),
([u1,u4,u0,0xfafafffa,u2,u3],[(u8,u1,u0),(u27,u2,u3),(0xfafafffa,u27,u8)],[4],[]),
([u1,u4,0xf0a0ffaa,u0,u2,u3],[(u16,u1,u2),(u25,u3,u0),(0xf0a0ffaa,u25,u16)],[1],[(0,38)]),
([u10,u25,u1,u4,u2,u16],[(u16,u1,u2),(u10,u0,u3),(u25,u0,u3)],[1],[(2,51)]),
([0xbaba,u1,u4,u0,u2,u3],[],[],[]),
([u1,0xbabababa,u4,u2,u5,u3],[(u13,u4,u0),(0xbabababa,u13,u1),(u5,u0,u2)],[4],[]),
([u13,u1,u4,0xf5f0f5f0,u2,u3],[],[],[]),
([0x31303130,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u9,u0,0xff33ff00,u3],[],[],[(0,53),(5,52)]),
([u10,u1,u4,u0,u2,0xffff3300],[(u32,u4,u2),(0xffff3300,u32,u3),(u10,u3,u0)],[4],[(0,54)]),
([u1,u4,u0,u2,0xfff3fff0,u3],[],[],[(0,53)]),
([0xf3f0,u1,u4,u0,u2,u3],[(u32,u4,u2),(u53,u32,u0),(0xf3f0,u53,u3)],[0,4],[(5,54)]),
([0x73507350,u1,u4,u0,u2,u3],[],[],[]),
([u13,0x55005500,u1,u4,u5,u3],[(u13,u4,u0),(0x55005500,u1,u2),(u5,u0,u2)],[0],[]),
([u1,0xaaaaf0f0,u4,u0,u2,u17],[(u40,u1,u3),(u17,u3,u0),(0xaaaaf0f0,u40,u17)],[0,3,4],[]),
([u13,0x55505550,u1,u4,u2,u3],[],[],[]),
([u13,u1,u4,u11,u2,u17],[(u13,u4,u0),(u17,u0,u3),(u11,u3,u2)],[0,4],[(0,56),(1,55)]),
([u10,u32,u1,u4,u0,u7],[(u32,u4,u2),(u7,u2,u3),(u10,u3,u0)],[0,4],[(0,57)]),
([u13,u1,u4,u2,u3,u12],[(u13,u4,u0),(u5,u0,u2),(u12,u5,u3)],[0],[(0,56)]),
([u14,u13,u1,u4,u2,u3],[(u13,u4,u0),(u5,u0,u2),(u14,u5,u3)],[0,3],[(0,58),(3,57)]),
([u1,u4,u0,0xf333f000,u2,u3],[],[],[]),
([u13,u1,u4,u2,0xfff0f0f0,u3],[],[],[]),
([u13,u1,u4,u0,u11,u7],[(u13,u4,u0),(u11,u2,u3),(u7,u2,u3)],[0],[(0,56),(0,60),(4,53),(10,59)]),
([0xaaa0fff0,u1,u4,u0,u2,u3],[(u40,u1,u3),(u5,u0,u2),(0xaaa0fff0,u40,u5)],[0,1,3,4],[(0,59)]),
([0x3030ff30,u1,u4,u0,u2,u3],[(u13,u4,u0),(u27,u2,u3),(0x3030ff30,u27,u13)],[0,2],[]),
([u13,u1,u4,u33,u2,u3],[(u13,u4,u0),(u27,u2,u3),(u33,u27,u0)],[0],[]),
([u10,u25,u32,u1,u4,u2],[(u32,u4,u2),(u10,u0,u3),(u25,u0,u3)],[2],[(2,60)]),
([0x32223222,u1,u4,u0,u2,u3],[],[],[(0,61)]),
([u1,u4,u0,0xffaaaaaa,u7],[(u11,u2,u3),(0xffaaaaaa,u1,u11),(u7,u2,u3)],[0,1,4],[(0,27),(0,63),(4,61),(4,64),(6,26),(6,49),(6,65),(10,62)]),
([u1,u4,u0,0xfaaafaaa,u3,u7],[(u9,u2,u0),(0xfaaafaaa,u1,u9),(u7,u2,u3)],[0,3],[(3,63),(6,35)]),
([0xfaaa,u1,u4,u0,u2,u3],[],[],[]),
([0x33303030,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u9,u5,u35,u3],[(u9,u0,u2),(u5,u0,u2),(u35,u1,u5)],[1],[(3,66),(3,67)]),
([u30,u1,u4,u9,u5,u3],[(u9,u0,u2),(u5,u0,u2),(u30,u4,u5)],[2],[(0,62),(3,65),(3,68)]),
([u19,u1,u4,u0],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7)],[1,2],[(0,30),(0,51),(0,60),(0,69),(0,70),(0,71),(0,72),(0,73),(0,75),(0,76),(4,74),(6,51),(6,60),(6,69),(6,70)]),
([u19,u1,u4,u0,u7],[(u11,u2,u3),(u7,u2,u3),(u19,u11,u7)],[0,1,2,4],[(0,65),(0,66),(0,68),(0,77),(0,78),(0,79),(0,80),(0,81),(0,82),(4,83),(6,65),(6,66),(6,68),(6,77)]),
([u1,u4,u9,u41,u5,u3],[(u9,u0,u2),(u5,u0,u2),(u41,u5,u3)],[0,3],[(0,84),(0,85),(3,80)]),
([u1,u4,u9,u3,u12],[(u9,u0,u2),(u5,u0,u2),(u12,u5,u3)],[0,3],[(0,37),(0,84),(0,88),(3,56),(3,63),(3,86),(3,87),(6,37),(9,56),(9,63)]),
([u1,u4,u9,u5,u3,u12],[(u9,u0,u2),(u5,u0,u2),(u12,u5,u3)],[0],[(0,85),(0,88),(3,81),(3,89)]),
([u14,u1,u4,u9,u3],[(u9,u0,u2),(u5,u0,u2),(u14,u5,u3)],[0,3],[(0,64),(0,88),(0,90),(0,91),(0,92),(6,64)]),
([u14,u1,u4,u9,u5,u3],[(u9,u0,u2),(u5,u0,u2),(u14,u5,u3)],[0,3],[(0,83),(0,88),(0,93),(3,94)]),
([0xf0,u1,u4,u0,u11,u7],[(u11,u2,u3),(u7,u2,u3),(0xf0,u7,u0)],[0],[(0,82),(0,94),(4,92),(4,95)]),
([u36,u1,u4,u0,u3],[(u11,u2,u3),(u5,u2,u0),(u36,u11,u5)],[3,4],[(0,36),(0,55),(0,96),(0,97),(6,36),(6,55)]),
([u36,u1,u4,u0,u5,u3],[(u11,u2,u3),(u5,u2,u0),(u36,u11,u5)],[0,3,4],[(0,96)]),
([u1,u4,u9,u3,u17,u7],[(u9,u2,u0),(u7,u2,u3),(u17,u0,u3)],[0,4],[(3,97),(5,97)]),
([u1,u4,u9,u3,u17,u12],[(u9,u0,u2),(u17,u0,u3),(u12,u2,u17)],[0],[(0,99),(3,96),(3,98)]),
([u1,0xbbbabbba,u4,u0,u2,u3],[],[],[]),
([u1,u4,u0,0xf3f3f3f0,u2,u3],[],[],[]),
([u14,u1,u4,u0,u2,u17],[(u17,u0,u3),(u5,u0,u2),(u14,u3,u5)],[0,1,3],[(0,100)]),
([u1,u4,u0,u2,u3,u12],[(u5,u0,u2),(u17,u0,u3),(u12,u5,u17)],[0,4],[]),
([u1,u48,u4,u0,u2,u7],[(u7,u3,u2),(u10,u3,u0),(u48,u10,u1)],[4],[]),
([u10,u39,u1,u4,u2],[(u7,u3,u2),(u10,u3,u0),(u39,u0,u7)],[0],[(0,39),(0,57),(2,86),(4,101),(6,39),(6,57)]),
([u10,u39,u1,u4,u2,u7],[(u7,u3,u2),(u10,u3,u0),(u39,u0,u7)],[0,3],[(4,98)]),
([u1,u4,u0,u2,u31,u7],[(u7,u2,u3),(u34,u2,u0),(u31,u34,u3)],[0,1,4],[(4,102)]),
([u10,u39,u1,u4,u2,u3],[(u7,u3,u2),(u10,u3,u0),(u39,u0,u7)],[0,3],[(4,103),(5,102)]),
([u14,u1,u4,u0,u2,u3],[(u5,u0,u2),(u41,u5,u3),(u14,u41,u5)],[0,3,4],[(0,84)]),
([u1,u4,u50,u2,u3,u12],[(u7,u2,u3),(u50,u7,u0),(u12,u0,u7)],[0],[(4,85),(4,104)]),
([0x33333330,u1,u4,u0,u2,u3],[],[],[]),
([u14,u1,u4,u0,u2,u12],[(u17,u3,u0),(u12,u17,u2),(u14,u3,u12)],[0,1,4],[(0,88),(0,100),(2,100)]),
([u1,0xaaaafffa,u4,u0,u2,u3],[],[],[]),
([u14,u1,u4,u0,0xff00fff0,u3],[(u5,u2,u0),(u14,u5,u3),(0xff00fff0,u14,u2)],[0,3],[]),
([0xf0,u39,u1,u4,u2,u3],[],[],[(0,94),(4,102),(4,104),(5,102)]),
([0x22223232,u1,u4,u0,u2,u3],[],[],[]),
([0xaafa,u1,u4,u0,u2,u3],[],[],[]),
([u10,u1,0xafaaafaa,u4,u2,u3],[],[],[(4,105)]),
([u1,u4,u0,u2,u31,0xffffaafa],[(u34,u0,u2),(u31,u34,u3),(0xffffaafa,u1,u31)],[0,1],[(5,47)]),
([0x30303330,u1,u4,u33,u2,u3],[(u27,u2,u3),(u33,u27,u0),(0x30303330,u4,u33)],[0,2,4],[]),
([u10,u1,u4,u51,u2],[(u20,u3,u2),(u51,u20,u0),(u10,u3,u51)],[0,4],[(0,105),(6,105)]),
([u1,u4,u0,u2,u31,u12],[(u34,u0,u2),(u31,u34,u3),(u12,u2,u31)],[0,4],[(4,102)]),
([0x30303330,u1,u4,u0,u2,u3],[(u27,u2,u3),(u33,u27,u0),(0x30303330,u4,u33)],[2],[]),
([u10,u1,u4,u33,u2,u3],[(u27,u2,u3),(u33,u27,u0),(u10,u0,u3)],[0,3,4],[]),
([u30,u1,u4,u0,u2,u3],[],[],[]),
([u10,u1,u4,u0,u2,u7],[(u20,u3,u2),(u7,u20,u2),(u10,u3,u0)],[0,4],[(0,106)]),
([u10,u20,u44,u1,u4],[(u20,u3,u2),(u10,u3,u0),(u44,u0,u2)],[0,3,4],[(0,107),(3,107),(4,107)])
]
def c5_0_L6 : Array W5Node := Array.mk [
([u1,u6,u0,u21,u2,u3],[(u6,u4,u1),(u21,u4,u0)],[0,1,2],[(0,1),(0,4),(0,7),(0,8),(1,7),(1,8),(2,3),(3,3),(4,0),(4,5),(4,6),(5,6),(6,2),(6,9),(7,9)]),
([u1,u4,u43,u6,u0,u2,u3],[(u6,u1,u4),(u43,u6,u0)],[0,1,2],[(0,4),(0,11),(0,13),(1,11),(4,10),(4,12),(5,12),(6,4)]),
([u1,u4,u0,u23,u2,u3],[(u6,u1,u4),(u23,u6,u0)],[1,2,3,4],[(0,14),(0,17),(0,19),(0,20),(0,21),(0,22),(1,17),(1,19),(1,20),(1,21),(1,22),(2,18),(3,18),(4,10),(4,15),(4,16),(5,16),(6,14)]),
([u1,u4,u6,u0,u23,u2,u3],[(u6,u1,u4),(u23,u6,u0)],[0,1],[(0,13),(0,23),(0,25),(1,25),(2,24),(3,24),(4,15),(6,23)]),
([u24,u1,u4,u0,u2,u3],[(u6,u1,u4),(u24,u6,u3)],[0,1,2,4],[(0,15),(0,26),(0,27),(0,29),(0,30),(2,26),(2,27),(2,29),(2,30),(3,28)]),
([u24,u1,u4,u6,u0,u2,u3],[(u6,u1,u4),(u24,u6,u3)],[1,2,3],[(0,5),(0,15),(0,31),(6,5)]),
([0x10101010,u1,u4,u6,u0,u2,u3],[(u6,u1,u4),(0x10101010,u6,u0)],[0,1],[(0,28),(0,32),(4,31),(6,32)]),
([u1,u4,u6,u9,u0,u2,u3],[(u6,u1,u4),(u9,u0,u2)],[0,1,2,4],[(0,33),(0,34),(0,36),(1,29),(3,35),(4,29),(6,33)]),
([u1,u4,u6,u0,u2,u5,u3],[(u6,u1,u4),(u5,u0,u2)],[0,1,2,4],[(0,8),(0,19),(0,36),(0,37),(0,38),(1,6),(1,16),(3,27),(4,6),(4,16),(6,8),(7,6),(10,6)]),
([u10,u1,u4,u6,u0,u2,u3],[(u6,u1,u4),(u10,u0,u3)],[0,1,2,3],[(0,7),(0,17),(0,30),(0,39),(0,40),(0,44),(1,42),(4,43),(5,41),(6,7),(6,39)]),
([u1,u4,u0,u2,u15,u18],[(u15,u1,u3),(u18,u4,u3)],[1,2,3],[(0,0),(0,46),(2,46),(3,45),(3,47),(5,47),(6,46),(8,46),(9,45),(9,47),(11,47)]),
([u1,u4,u0,u8,u21,u2,u3],[(u8,u1,u0),(u21,u4,u0)],[0,1,2],[(0,1),(0,48),(6,48)]),
([u13,u1,u4,u8,u2,u3],[(u8,u1,u0),(u13,u4,u0)],[0,1,2],[(0,51),(0,52),(1,51),(1,52),(2,50),(3,50),(10,49)]),
([u1,u4,u0,u8,u23,u2,u3],[(u8,u1,u0),(u23,u4,u8)],[1,2],[(0,14),(0,55),(1,55),(2,54),(3,54),(4,53),(6,48)]),
([u26,u1,u4,u0,u2,u3],[(u8,u1,u0),(u26,u4,u8)],[1,2,3,4],[(0,14),(0,48),(0,57),(0,58),(0,59),(1,57),(1,58),(1,59),(2,56),(3,56)]),
([u26,u1,u4,u0,u8,u2,u3],[(u8,u1,u0),(u26,u4,u8)],[0,1,2],[(0,2),(0,14),(0,45)]),
([u1,u4,u0,u8,u2,u28,u3],[(u8,u1,u0),(u28,u4,u2)],[0,1,2,4],[(0,3),(0,19),(0,61),(1,57),(3,60),(4,46),(7,46),(10,57)]),
([u13,u1,u4,u0,u2,u16,u3],[(u16,u1,u2),(u13,u4,u0)],[0,1,2,4],[(0,51),(1,62),(1,65),(2,63),(10,64)]),
([u1,u4,u0,u2,u15,u17],[(u15,u1,u3),(u17,u3,u0)],[0,1,3,4],[(0,16),(0,46),(0,65),(0,72),(1,67),(1,70),(1,73),(2,68),(3,58),(4,60),(4,69),(5,71),(6,6),(7,66)]),
([u1,u4,u0,u8,u2,u5,u3],[(u8,u1,u0),(u5,u0,u2)],[0,1,4],[(1,75),(6,74)]),
([u10,u1,u4,u8,u2,u3],[(u8,u1,u0),(u10,u0,u3)],[0,1,3,4],[(0,17),(0,59),(0,81),(0,82),(2,79),(3,77),(5,78),(5,80),(6,7),(6,76)]),
([u10,u1,u4,u0,u2,u3,u15],[(u15,u1,u3),(u10,u3,u0)],[0,1,3],[(0,80),(0,87),(1,86),(3,84),(4,85),(6,83)]),
([u1,u4,0xf0a0f0a0,u0,u2,u16,u3],[(u16,u1,u2),(0xf0a0f0a0,u16,u0)],[0,1,4],[(0,70),(0,89),(4,88)]),
([u1,u4,u0,u2,u35,u3],[(u8,u1,u0),(u35,u8,u2)],[1,2,3],[(0,19),(0,51),(0,91),(0,93),(0,94),(1,88),(1,92),(2,51),(4,88),(4,92),(6,8),(6,90),(7,46),(10,46)]),
([u1,u4,u0,u8,u2,u35,u3],[(u8,u1,u0),(u35,u8,u2)],[1,4],[(1,92),(2,89),(4,95),(6,74)]),
([u22,u1,u4,u0,u2,u3],[(u8,u1,u0),(u22,u8,u3)],[0,1,2,4],[(0,9),(0,47),(0,52),(0,57),(0,75),(0,92),(0,98),(0,99),(1,86),(2,97),(3,100),(5,87),(6,96)]),
([u22,u1,u4,u0,u8,u2,u3],[(u8,u1,u0),(u22,u8,u3)],[1,3],[(0,71),(0,92),(11,101)]),
([0x3030,u1,u4,u0,u2,u3,u18],[(u18,u4,u3),(0x3030,u18,u0)],[0,2],[(0,83),(0,101),(0,104),(7,86),(9,102),(10,103)]),
([u1,u4,u9,u0,u2,u3,u15],[(u15,u1,u3),(u9,u0,u2)],[0,1,3],[(0,68),(0,106),(0,109),(2,68),(3,107),(3,108),(6,105)]),
([u1,u4,u0,u8,u2,u3,u7],[(u8,u1,u0),(u7,u2,u3)],[0,1,3,4],[(0,81),(0,93),(0,98),(0,99),(0,110),(1,81),(1,99),(4,72),(4,109),(10,111)]),
([u10,u1,u4,u0,u2,u16,u3],[(u16,u1,u2),(u10,u0,u3)],[0,1,4],[(0,69),(0,100),(0,115),(1,112),(2,113),(4,82),(5,114)]),
([u1,0xbabababa,u4,u0,u2,u3],[(u13,u4,u0),(0xbabababa,u13,u1)],[0,1,2,3,4],[(0,116),(0,117),(1,116),(1,117),(2,63),(3,63)]),
([u1,u4,u0,u53,u2,u3],[(u32,u4,u2),(u53,u32,u0)],[0,1,2,3,4],[(0,50),(0,63),(0,123),(1,122),(3,120),(4,62),(5,121),(6,118),(6,119)]),
([u13,0x55005500,u1,u4,u0,u2,u3],[(u13,u4,u0),(0x55005500,u1,u2)],[0,1,2,4],[(0,118),(0,125),(2,124),(8,118)]),
([u13,u1,u4,u2,u5,u3],[(u13,u4,u0),(u5,u0,u2)],[0,2,3,4],[(0,51),(0,117),(0,125),(0,127),(0,130),(0,131),(1,65),(1,128),(3,129),(10,126)]),
([u13,u1,u4,u0,u11,u2,u3],[(u13,u4,u0),(u11,u2,u3)],[0,2,3,4],[(0,128),(0,133),(0,134),(1,128),(4,120),(4,132),(5,120)]),
([u13,u1,u4,u0,u2,u3,u7],[(u13,u4,u0),(u7,u2,u3)],[0,2],[(0,130),(0,134),(4,122),(10,135)]),
([u10,u32,u1,u4,u0,u2,u3],[(u32,u4,u2),(u10,u0,u3)],[0,2,3,4],[(0,121),(0,129),(0,138),(2,136),(2,137)]),
([u1,u4,u0,0xfaaafaaa,u2,u3],[(u9,u0,u2),(0xfaaafaaa,u1,u9)],[0,1,2,3,4],[(0,34),(0,139),(0,141),(0,142),(2,141),(3,107),(3,140),(6,33),(6,105)]),
([u1,u4,u0,u2,0xfff0f0f0,u3],[(u11,u2,u3),(0xfff0f0f0,u11,u0)],[0,1,2,3,4],[(0,107),(0,133),(0,143),(4,106),(6,107),(6,133),(6,143),(10,106)]),
([u1,u4,u9,u5,u3],[(u9,u0,u2),(u5,u0,u2)],[0,1,2,3],[(0,36),(0,109),(0,144),(0,145),(0,148),(0,149),(0,150),(0,151),(0,152),(3,134),(3,140),(3,146),(3,147),(3,153),(6,109),(6,144),(6,145),(9,134),(9,140)]),
([u1,u4,u9,u0,u3,u7],[(u9,u2,u0),(u7,u2,u3)],[0,3,4],[(0,68),(0,141),(0,149),(0,156),(2,157),(3,128),(5,154),(5,155),(6,68),(6,141),(9,128)]),
([u1,u4,u0,u2,u5,u35,u3],[(u5,u0,u2),(u35,u1,u5)],[1],[(0,144),(1,75),(4,75),(6,90)]),
([u30,u1,u4,u0,u2,u3],[(u5,u0,u2),(u30,u4,u5)],[0,1,2,3,4],[(0,38),(0,67),(0,74),(0,90),(0,111),(0,158),(2,67),(2,74),(3,159),(6,127),(8,127)]),
([u30,u1,u4,u0,u2,u5,u3],[(u5,u0,u2),(u30,u4,u5)],[0,2,4],[(0,66),(0,90),(0,145),(2,66)]),
([u1,u4,u0,u2,u5,u3,u17],[(u5,u0,u2),(u17,u0,u3)],[0,3,4],[(0,160),(0,161),(1,160),(4,156)]),
([u10,u1,u4,u0,u2,u7],[(u7,u3,u2),(u10,u3,u0)],[0,3,4],[(0,69),(0,81),(0,129),(0,162),(0,163),(0,164),(6,69),(6,81),(6,129),(6,162)]),
([u10,u1,u4,u0,u2,u3,u7],[(u7,u3,u2),(u10,u3,u0)],[0,3,4],[(0,161),(0,166),(1,165)]),
([u1,u4,u50,u0,u2,u3,u7],[(u7,u2,u3),(u50,u7,u0)],[0],[(0,168),(4,148),(4,167)]),
([u1,u4,u0,u2,u3,u12],[(u5,u0,u2),(u12,u5,u3)],[0,1,2,3,4],[(0,72),(0,93),(0,130),(0,149),(0,167),(0,169),(0,170),(1,72),(1,149),(1,167),(1,170),(2,130),(3,130),(4,72),(4,149),(4,167),(4,170),(6,72),(6,93),(6,130),(6,169),(7,72),(8,130),(9,130),(10,72)]),
([u1,u4,u0,u2,u5,u3,u12],[(u5,u0,u2),(u12,u5,u3)],[0,3,4],[(0,150),(0,170),(1,157),(1,160),(3,168),(4,157),(4,160)]),
([u14,u1,u4,u0,u2,u3],[(u5,u0,u2),(u14,u5,u3)],[0,1,2,3,4],[(0,73),(0,111),(0,131),(0,151),(0,160),(0,161),(0,170),(0,171),(0,172),(2,73),(2,131),(2,160),(2,172),(3,163),(3,166),(5,163),(5,166),(6,73),(6,111),(6,131),(6,171),(8,73),(8,131)]),
([u14,u1,u4,u0,u2,u5,u3],[(u5,u0,u2),(u14,u5,u3)],[0,3,4],[(0,152),(0,170),(3,164),(3,173),(5,164)]),
([0xf0,u1,u4,u0,u2,u3,u7],[(u7,u2,u3),(0xf0,u7,u0)],[0],[(0,153),(0,161),(0,165),(0,173),(1,165)]),
([u1,u48,u4,u0,u2,u3],[(u10,u0,u3),(u48,u10,u1)],[0,1,2,4],[(0,40),(0,76),(0,162),(0,174),(1,86),(1,175),(2,113),(3,176),(6,39),(6,83)]),
([u1,u4,u0,u2,u31],[(u34,u0,u2),(u31,u34,u3)],[0,1,2,4],[(0,42),(0,177),(0,180),(1,172),(2,84),(3,178),(4,78),(5,179),(6,177),(8,84),(9,178),(10,78)]),
([u1,u4,u0,u33,u2,u3],[(u27,u2,u3),(u33,u27,u0)],[0,1,2,3,4],[(0,79),(0,113),(0,137),(0,161),(0,167),(0,181),(0,182),(1,179),(4,112),(4,165),(6,79),(6,113),(6,137),(6,181),(10,112)]),
([u1,u4,u52,u2,u3],[(u20,u3,u2),(u52,u20,u0)],[0,1,2,3,4],[(0,43),(0,85),(6,85)]),
([u1,u4,u0,u2,u5,u3],[(u34,u0,u2),(u5,u34,u2)],[0,1,2,3,4],[(0,86),(0,161),(0,167),(0,183),(1,80),(3,184),(4,80),(5,184),(6,86),(6,183),(7,80),(10,80)]),
([u10,u20,u1,u4,u0,u2],[(u20,u3,u2),(u10,u3,u0)],[0,3,4],[(0,82),(0,179),(0,184),(0,185),(1,154),(3,176),(6,82),(9,176)]),
([u10,u25,u1,u4,u2],[(u10,u0,u3),(u25,u0,u3)],[0,1,2,3],[(0,44),(0,115),(0,138),(2,146),(6,115),(6,138)]),
([u10,u27,u1,u4,u0,u2,u3],[(u10,u0,u3),(u27,u2,u3)],[0,3,4],[(0,167),(0,182),(0,184),(2,182),(2,184)])
]
def c5_0_L7 : Array W5Node := Array.mk [
([u1,u4,u6,u0,u2,u3],[(u6,u1,u4)],[0,1,2,3,4],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4),(1,5),(1,7),(1,8),(1,9),(2,0),(2,1),(2,2),(2,3),(2,6),(2,9),(3,0),(3,1),(3,2),(3,3),(3,6),(3,9),(4,4),(4,5),(4,7),(4,8),(4,9),(5,9),(6,0),(8,0),(9,0)]),
([u1,u4,u0,u8,u2,u3],[(u8,u1,u0)],[0,1,2,3,4],[(0,2),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,19),(0,20),(0,23),(0,24),(0,25),(0,26),(0,29),(1,16),(1,19),(1,20),(1,23),(1,24),(1,25),(1,26),(2,17),(2,22),(2,30),(3,17),(3,22),(3,30),(4,10),(4,18),(4,21),(4,28),(5,18),(5,21),(6,0),(10,27),(11,27)]),
([u13,u1,u4,u0,u2,u3],[(u13,u4,u0)],[0,1,2,3,4],[(0,12),(0,17),(0,31),(0,33),(0,34),(0,35),(0,36),(1,17),(1,33),(1,34),(2,32),(2,37),(3,32),(3,37)]),
([u1,u4,u9,u0,u2,u3],[(u9,u0,u2)],[0,1,2,3,4],[(0,7),(0,28),(0,38),(0,40),(0,41),(2,41),(3,35),(3,39),(6,28),(6,38),(9,35)]),
([u1,u4,u0,u2,u5,u3],[(u5,u0,u2)],[0,1,2,3,4],[(0,8),(0,19),(0,23),(0,34),(0,40),(0,42),(0,43),(0,44),(0,45),(0,49),(0,50),(0,51),(0,52),(1,18),(2,19),(2,34),(2,45),(3,29),(3,36),(3,41),(3,46),(3,47),(3,48),(3,53),(4,18),(5,41),(5,46),(5,47),(6,19),(6,23),(6,34),(6,42),(6,43),(6,44),(7,18),(8,19),(8,34),(9,29),(9,36),(10,18)]),
([u10,u1,u4,u0,u2,u3],[(u10,u0,u3)],[0,1,2,3,4],[(0,9),(0,20),(0,21),(0,30),(0,37),(0,46),(0,47),(0,54),(0,59),(0,60),(0,61),(1,55),(1,58),(2,56),(4,57),(4,59),(6,20),(6,21),(6,30),(6,37),(6,54)])
]
def c5_0_L8 : Array W5Node := Array.mk [
([u1,u4,u0,u2,u3],[],[1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5),(3,1),(3,2),(3,5),(4,3),(4,4),(4,5),(5,5),(6,1),(6,2),(8,1),(8,2),(9,1),(9,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_2_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 2 c5_0_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_2 : ∀ i < c5_0_L2.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 2 c5_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_0_L2.size = 2 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 c5_0_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 c5_0_L2 16 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_3 : ∀ i < c5_0_L3.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 c5_0_L2 i = true := by
  intro i hi
  have hsz : c5_0_L3.size = 29 := by decide +kernel
  have hi' : i < 29 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_0_chk_3_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_0_chk_3_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_2 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_3 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_4 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_5 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_6 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 96 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_4 : ∀ i < c5_0_L4.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 i = true := by
  intro i hi
  have hsz : c5_0_L4.size = 108 := by decide +kernel
  have hi' : i < 108 := hsz ▸ hi
  by_cases h : i < 64
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_0_chk_4_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_1 i (by omega) (by omega)
    ·
      by_cases h : i < 48
      ·
        exact checkBlockW5_at c5_0_chk_4_2 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_3 i (by omega) (by omega)
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 80
      ·
        exact checkBlockW5_at c5_0_chk_4_4 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_5 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_4_6 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_2 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_3 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_4 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_5 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_6 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_7 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_8 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_9 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_10 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_11 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 176 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_5 : ∀ i < c5_0_L5.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 i = true := by
  intro i hi
  have hsz : c5_0_L5.size = 186 := by decide +kernel
  have hi' : i < 186 := hsz ▸ hi
  by_cases h : i < 96
  ·
    by_cases h : i < 48
    ·
      by_cases h : i < 32
      ·
        by_cases h : i < 16
        ·
          exact checkBlockW5_at c5_0_chk_5_0 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_1 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_2 i (by omega) (by omega)
    ·
      by_cases h : i < 80
      ·
        by_cases h : i < 64
        ·
          exact checkBlockW5_at c5_0_chk_5_3 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_4 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_5 i (by omega) (by omega)
  ·
    by_cases h : i < 144
    ·
      by_cases h : i < 128
      ·
        by_cases h : i < 112
        ·
          exact checkBlockW5_at c5_0_chk_5_6 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_7 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_8 i (by omega) (by omega)
    ·
      by_cases h : i < 176
      ·
        by_cases h : i < 160
        ·
          exact checkBlockW5_at c5_0_chk_5_9 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_10 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_11 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_2 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_3 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 48 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_6 : ∀ i < c5_0_L6.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 i = true := by
  intro i hi
  have hsz : c5_0_L6.size = 62 := by decide +kernel
  have hi' : i < 62 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW5_at c5_0_chk_6_0 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_6_1 i (by omega) (by omega)
  ·
    by_cases h : i < 48
    ·
      exact checkBlockW5_at c5_0_chk_6_2 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_6_3 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_7 : ∀ i < c5_0_L7.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 i = true := by
  intro i hi
  have hsz : c5_0_L7.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_7_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_8_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 8 c5_0_L8 c5_0_L7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_8 : ∀ i < c5_0_L8.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 8 c5_0_L8 c5_0_L7 i = true := by
  intro i hi
  have hsz : c5_0_L8.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_8_0 i (Nat.zero_le _) (by omega)
theorem c5_0_L2_sound : ∀ i < c5_0_L2.size, ¬ live (basicOps 32) c5_0_goal 2 (c5_0_L2[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound (fun j hj => by simp at hj) c5_0_chk_2
theorem c5_0_L3_sound : ∀ i < c5_0_L3.size, ¬ live (basicOps 32) c5_0_goal 3 (c5_0_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L2_sound c5_0_chk_3
theorem c5_0_L4_sound : ∀ i < c5_0_L4.size, ¬ live (basicOps 32) c5_0_goal 4 (c5_0_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L3_sound c5_0_chk_4
theorem c5_0_L5_sound : ∀ i < c5_0_L5.size, ¬ live (basicOps 32) c5_0_goal 5 (c5_0_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L4_sound c5_0_chk_5
theorem c5_0_L6_sound : ∀ i < c5_0_L6.size, ¬ live (basicOps 32) c5_0_goal 6 (c5_0_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L5_sound c5_0_chk_6
theorem c5_0_L7_sound : ∀ i < c5_0_L7.size, ¬ live (basicOps 32) c5_0_goal 7 (c5_0_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L6_sound c5_0_chk_7
theorem c5_0_L8_sound : ∀ i < c5_0_L8.size, ¬ live (basicOps 32) c5_0_goal 8 (c5_0_L8[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L7_sound c5_0_chk_8
set_option maxRecDepth 100000 in
theorem c5_0_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_0_goal ws) = [rows5] := by decide +kernel
theorem c5_0_top_match : sameSet (rows5.map (actB 32 (c5_0_pow[0]?.getD []))) (c5_0_L8[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 8 rows5.toFinset :=
  no_build_of_top c5_0_G_valid (by decide) c5_0_sublists c5_0_top_match (c5_0_L8_sound 0 (by decide))

def c5_1_goal : BitVec 32 := 0xeee8eac0
def c5_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_1_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]
def c5_1_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768,65536,262144,131072,524288,16777216,67108864,33554432,134217728,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_1_idx : Array (List ℕ) := Array.mk [c5_1_s0,c5_1_s1]
def c5_1_pow : Array (List ℕ) := Array.mk [c5_1_p0,c5_1_p1]
def c5_1_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_G_valid : (List.range 2).all (symValid 32 2 c5_1_idx c5_1_pow c5_1_inv c5_1_goal) = true := by decide +kernel
def c5_1_m0 : BitVec 32 := 0xf0f0f0f
def c5_1_st0 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_1_ix0 : List ℕ := [0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_0 : c5_1_ix0.length = 16 ∧ (∀ idx ∈ c5_1_ix0, idx < 32) ∧ (∀ idx ∈ c5_1_ix0, c5_1_m0.getLsbD idx = true) ∧ projS 16 c5_1_ix0 c5_1_goal = b4_2_goal ∧ c5_1_st0.all (fun w => rows4.contains (projS 16 c5_1_ix0 w)) = true := by decide +kernel
def c5_1_m1 : BitVec 32 := 0xff00ff
def c5_1_st1 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_1_ix1 : List ℕ := [0,2,4,6,1,3,5,7,16,18,20,22,17,19,21,23]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_1 : c5_1_ix1.length = 16 ∧ (∀ idx ∈ c5_1_ix1, idx < 32) ∧ (∀ idx ∈ c5_1_ix1, c5_1_m1.getLsbD idx = true) ∧ projS 16 c5_1_ix1 c5_1_goal = b4_2_goal ∧ c5_1_st1.all (fun w => rows4.contains (projS 16 c5_1_ix1 w)) = true := by decide +kernel
def c5_1_m2 : BitVec 32 := 0xaaaaaaaa
def c5_1_st2 : List (BitVec 32) := [0x88888888,0xa0a0a0a0,0xaa00aa00,0xaaaa0000]
def c5_1_ix2 : List ℕ := [1,9,3,11,5,13,7,15,17,25,19,27,21,29,23,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_2 : c5_1_ix2.length = 16 ∧ (∀ idx ∈ c5_1_ix2, idx < 32) ∧ (∀ idx ∈ c5_1_ix2, c5_1_m2.getLsbD idx = true) ∧ projS 16 c5_1_ix2 c5_1_goal = b4_3_goal ∧ c5_1_st2.all (fun w => rows4.contains (projS 16 c5_1_ix2 w)) = true := by decide +kernel
def c5_1_m3 : BitVec 32 := 0xcccccccc
def c5_1_st3 : List (BitVec 32) := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def c5_1_ix3 : List ℕ := [2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_3 : c5_1_ix3.length = 16 ∧ (∀ idx ∈ c5_1_ix3, idx < 32) ∧ (∀ idx ∈ c5_1_ix3, c5_1_m3.getLsbD idx = true) ∧ projS 16 c5_1_ix3 c5_1_goal = b4_3_goal ∧ c5_1_st3.all (fun w => rows4.contains (projS 16 c5_1_ix3 w)) = true := by decide +kernel
def c5_1_m4 : BitVec 32 := 0xffff0000
def c5_1_st4 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_1_ix4 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_4 : c5_1_ix4.length = 16 ∧ (∀ idx ∈ c5_1_ix4, idx < 32) ∧ (∀ idx ∈ c5_1_ix4, c5_1_m4.getLsbD idx = true) ∧ projS 16 c5_1_ix4 c5_1_goal = b4_1_goal ∧ c5_1_st4.all (fun w => rows4.contains (projS 16 c5_1_ix4 w)) = true := by decide +kernel
def c5_1_cfMasks : Array (BitVec 32) := Array.mk [c5_1_m0,c5_1_m1,c5_1_m2,c5_1_m3,c5_1_m4]
def c5_1_cfB0s : Array ℕ := Array.mk [0,0,1,2,16]
def c5_1_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_1_st0,c5_1_st1,c5_1_st2,c5_1_st3,c5_1_st4]
def c5_1_cfLBs : Array ℕ := Array.mk [5,5,5,5,5]
theorem c5_1_cof_sound (c fuel : ℕ) (hc : c < 5) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_1_cfLBs[c]?.getD 0) fuel (c5_1_cfMasks[c]?.getD 0) (c5_1_cfB0s[c]?.getD 0) (c5_1_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_1_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix0 c5_1_cspec_0.1 c5_1_cspec_0.2.1 c5_1_m0 c5_1_cspec_0.2.2.1 0 c5_1_st0 b4_2_goal (by decide) c5_1_cspec_0.2.2.2.1 c5_1_cspec_0.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix1 c5_1_cspec_1.1 c5_1_cspec_1.2.1 c5_1_m1 c5_1_cspec_1.2.2.1 0 c5_1_st1 b4_2_goal (by decide) c5_1_cspec_1.2.2.2.1 c5_1_cspec_1.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix2 c5_1_cspec_2.1 c5_1_cspec_2.2.1 c5_1_m2 c5_1_cspec_2.2.2.1 1 c5_1_st2 b4_3_goal (by decide) c5_1_cspec_2.2.2.2.1 c5_1_cspec_2.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix3 c5_1_cspec_3.1 c5_1_cspec_3.2.1 c5_1_m3 c5_1_cspec_3.2.2.1 2 c5_1_st3 b4_3_goal (by decide) c5_1_cspec_3.2.2.2.1 c5_1_cspec_3.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix4 c5_1_cspec_4.1 c5_1_cspec_4.2.1 c5_1_m4 c5_1_cspec_4.2.2.1 16 c5_1_st4 b4_1_goal (by decide) c5_1_cspec_4.2.2.2.1 c5_1_cspec_4.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | c + 5 => omega
def c5_1_L4 : Array W5Node := Array.mk [
([u1,u4,u0,0xff88ff00,u3],[],[],[])
]
def c5_1_L5 : Array W5Node := Array.mk [
([u1,u4,u0,0xf8f8f8f8,u2,u3],[],[],[]),
([0x880088,u1,u4,u0,u2,u3],[],[],[]),
([0x88880000,u1,u4,u0,u2,u3],[(0x88888888,u1,u4),(0x88880000,0x88888888,u3)],[0,1],[(0,0),(1,0)]),
([0x77770000,u1,u4,u0,u2,u3],[],[],[]),
([0xaa22aa22,u1,u4,u0,u2,u3],[(0xcc00cc,u4,u2),(0xaa22aa22,0xcc00cc,u1)],[2],[]),
([u1,u4,u0,0xf0fcf0fc,u2,u3],[],[],[]),
([0xa000a,u1,u4,u0,u2,u3],[],[],[]),
([0xcc0000,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u0,0xf5f50000,u2,u3],[],[],[]),
([u45,0xcc00cc,u1,u4,u0,u3],[(0xcc00cc,u4,u2),(u45,u1,u2)],[2,3],[]),
([0xa2a2a2a2,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u0,0xf0faf0fa,u2,u3],[],[],[]),
([0xaa0000,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u0,0xf3f30000,u2,u3],[],[],[]),
([u45,u1,u4,u0,u5,u3],[(u45,u1,u2),(u5,u0,u2)],[2],[]),
([u45,u20,u1,u4,u0,u3],[(u45,u1,u2),(u20,u2,u3)],[2,4],[]),
([0x2222aaaa,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u0,0xfafaf0f0,u2,u3],[],[],[]),
([u1,u4,u0,0xfcfcf0f0,u2,u3],[(u54,u4,u3),(0xfcfcf0f0,u54,u0)],[0,3],[]),
([0xaaaa0000,u1,u54,u4,u0,u2],[(0xaaaa0000,u1,u3),(u54,u4,u3)],[2,3],[]),
([u20,u1,u54,u4,u0,u2],[(u54,u4,u3),(u20,u2,u3)],[1,3],[]),
([0xaaa0aaa0,u1,u4,u0,u2,u3],[(u5,u0,u2),(0xaaa0aaa0,u1,u5)],[2],[]),
([u1,u4,u0,u2,u41,u3],[(u5,u0,u2),(u41,u5,u3)],[0,1,4],[]),
([0xf0000,u1,u4,u0,u2,u3],[],[],[]),
([0xaa00aaaa,u1,u4,u0,u2,u3],[(u20,u2,u3),(0xaa00aaaa,u20,u1)],[2],[]),
([0xa0a0aaaa,u1,u4,u0,u2,u3],[],[],[]),
([u1,u4,u0,u51,u2,u3],[],[],[]),
([u20,u25,u1,u4,u0,u2],[(u20,u2,u3),(u25,u0,u3)],[0,1],[])
]
def c5_1_L6 : Array W5Node := Array.mk [
([0x88888888,u1,u4,u0,u2,u3],[(0x88888888,u1,u4)],[0,1,2,3,4],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)]),
([0xcc00cc,u1,u4,u0,u2,u3],[(0xcc00cc,u4,u2)],[0,1,2,3,4],[(0,1),(0,4),(0,5),(0,7),(0,9),(1,6),(1,8)]),
([u45,u1,u4,u0,u2,u3],[(u45,u1,u2)],[0,1,2,3,4],[(0,1),(0,6),(0,9),(0,11),(0,12),(0,14),(0,15),(1,10),(1,13)]),
([0xaaaa0000,u1,u4,u0,u2,u3],[(0xaaaa0000,u1,u3)],[0,1,2,3,4],[(0,2),(0,12),(0,17),(0,19),(1,7),(1,16),(1,18),(1,20)]),
([u1,u4,u0,u2,u5,u3],[(u5,u0,u2)],[0,1,2,3,4],[(0,6),(0,14),(0,21),(0,22),(0,23),(1,6),(1,14),(1,21)]),
([u20,u1,u4,u0,u2,u3],[(u20,u2,u3)],[0,1,2,3,4],[(0,7),(0,12),(0,15),(0,20),(0,23),(0,24),(0,26),(0,27),(1,25)])
]
def c5_1_L7 : Array W5Node := Array.mk [
([u1,u4,u0,u2,u3],[],[0,1,2,3,4],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_4 : ∀ i < c5_1_L4.size, checkNodeW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_1_L4.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_1 : checkBlockW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 16 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_5 : ∀ i < c5_1_L5.size, checkNodeW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 i = true := by
  intro i hi
  have hsz : c5_1_L5.size = 28 := by decide +kernel
  have hi' : i < 28 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_1_chk_5_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_1_chk_5_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_6_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_6 : ∀ i < c5_1_L6.size, checkNodeW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 i = true := by
  intro i hi
  have hsz : c5_1_L6.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_7_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 7 c5_1_L7 c5_1_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_7 : ∀ i < c5_1_L7.size, checkNodeW5 c5_1_goal 2 c5_1_pow 5 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 7 c5_1_L7 c5_1_L6 i = true := by
  intro i hi
  have hsz : c5_1_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_1_L4_sound : ∀ i < c5_1_L4.size, ¬ live (basicOps 32) c5_1_goal 4 (c5_1_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound (fun j hj => by simp at hj) c5_1_chk_4
theorem c5_1_L5_sound : ∀ i < c5_1_L5.size, ¬ live (basicOps 32) c5_1_goal 5 (c5_1_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L4_sound c5_1_chk_5
theorem c5_1_L6_sound : ∀ i < c5_1_L6.size, ¬ live (basicOps 32) c5_1_goal 6 (c5_1_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L5_sound c5_1_chk_6
theorem c5_1_L7_sound : ∀ i < c5_1_L7.size, ¬ live (basicOps 32) c5_1_goal 7 (c5_1_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L6_sound c5_1_chk_7
set_option maxRecDepth 100000 in
theorem c5_1_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_1_goal ws) = [rows5] := by decide +kernel
theorem c5_1_top_match : sameSet (rows5.map (actB 32 (c5_1_pow[0]?.getD []))) (c5_1_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_1_no_build : ¬ build (basicOps 32) c5_1_goal 7 rows5.toFinset :=
  no_build_of_top c5_1_G_valid (by decide) c5_1_sublists c5_1_top_match (c5_1_L7_sound 0 (by decide))

def c5_2_goal : BitVec 32 := 0xeee8eae0
def c5_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_2_idx : Array (List ℕ) := Array.mk [c5_2_s0]
def c5_2_pow : Array (List ℕ) := Array.mk [c5_2_p0]
def c5_2_inv : Array ℕ := Array.mk [0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_G_valid : (List.range 1).all (symValid 32 1 c5_2_idx c5_2_pow c5_2_inv c5_2_goal) = true := by decide +kernel
def c5_2_m0 : BitVec 32 := 0xcccccccc
def c5_2_st0 : List (BitVec 32) := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def c5_2_ix0 : List ℕ := [2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31]
set_option maxRecDepth 100000 in
theorem c5_2_cspec_0 : c5_2_ix0.length = 16 ∧ (∀ idx ∈ c5_2_ix0, idx < 32) ∧ (∀ idx ∈ c5_2_ix0, c5_2_m0.getLsbD idx = true) ∧ projS 16 c5_2_ix0 c5_2_goal = b4_3_goal ∧ c5_2_st0.all (fun w => rows4.contains (projS 16 c5_2_ix0 w)) = true := by decide +kernel
def c5_2_m1 : BitVec 32 := 0xf0f0f0f
def c5_2_st1 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_2_ix1 : List ℕ := [0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27]
set_option maxRecDepth 100000 in
theorem c5_2_cspec_1 : c5_2_ix1.length = 16 ∧ (∀ idx ∈ c5_2_ix1, idx < 32) ∧ (∀ idx ∈ c5_2_ix1, c5_2_m1.getLsbD idx = true) ∧ projS 16 c5_2_ix1 c5_2_goal = b4_2_goal ∧ c5_2_st1.all (fun w => rows4.contains (projS 16 c5_2_ix1 w)) = true := by decide +kernel
def c5_2_m2 : BitVec 32 := 0xff00ff
def c5_2_st2 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_2_ix2 : List ℕ := [0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23]
set_option maxRecDepth 100000 in
theorem c5_2_cspec_2 : c5_2_ix2.length = 16 ∧ (∀ idx ∈ c5_2_ix2, idx < 32) ∧ (∀ idx ∈ c5_2_ix2, c5_2_m2.getLsbD idx = true) ∧ projS 16 c5_2_ix2 c5_2_goal = b4_4_goal ∧ c5_2_st2.all (fun w => rows4.contains (projS 16 c5_2_ix2 w)) = true := by decide +kernel
def c5_2_m3 : BitVec 32 := 0xffff0000
def c5_2_st3 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_2_ix3 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_2_cspec_3 : c5_2_ix3.length = 16 ∧ (∀ idx ∈ c5_2_ix3, idx < 32) ∧ (∀ idx ∈ c5_2_ix3, c5_2_m3.getLsbD idx = true) ∧ projS 16 c5_2_ix3 c5_2_goal = b4_1_goal ∧ c5_2_st3.all (fun w => rows4.contains (projS 16 c5_2_ix3 w)) = true := by decide +kernel
def c5_2_cfMasks : Array (BitVec 32) := Array.mk [c5_2_m0,c5_2_m1,c5_2_m2,c5_2_m3]
def c5_2_cfB0s : Array ℕ := Array.mk [2,0,0,16]
def c5_2_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_2_st0,c5_2_st1,c5_2_st2,c5_2_st3]
def c5_2_cfLBs : Array ℕ := Array.mk [5,5,5,5]
theorem c5_2_cof_sound (c fuel : ℕ) (hc : c < 4) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_2_cfLBs[c]?.getD 0) fuel (c5_2_cfMasks[c]?.getD 0) (c5_2_cfB0s[c]?.getD 0) (c5_2_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_2_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_2_goal 5 c5_2_ix0 c5_2_cspec_0.1 c5_2_cspec_0.2.1 c5_2_m0 c5_2_cspec_0.2.2.1 2 c5_2_st0 b4_3_goal (by decide) c5_2_cspec_0.2.2.2.1 c5_2_cspec_0.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_2_goal 5 c5_2_ix1 c5_2_cspec_1.1 c5_2_cspec_1.2.1 c5_2_m1 c5_2_cspec_1.2.2.1 0 c5_2_st1 b4_2_goal (by decide) c5_2_cspec_1.2.2.2.1 c5_2_cspec_1.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_2_goal 5 c5_2_ix2 c5_2_cspec_2.1 c5_2_cspec_2.2.1 c5_2_m2 c5_2_cspec_2.2.2.1 0 c5_2_st2 b4_4_goal (by decide) c5_2_cspec_2.2.2.2.1 c5_2_cspec_2.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_2_goal 5 c5_2_ix3 c5_2_cspec_3.1 c5_2_cspec_3.2.1 c5_2_m3 c5_2_cspec_3.2.2.1 16 c5_2_st3 b4_1_goal (by decide) c5_2_cspec_3.2.2.2.1 c5_2_cspec_3.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | c + 4 => omega
def c5_2_L6 : Array W5Node := Array.mk [
([u1,u4,u0,u2,u3],[],[0,1,2,3],[])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_6_0 : checkBlockW5 c5_2_goal 1 c5_2_pow 4 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 6 c5_2_L6 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_6 : ∀ i < c5_2_L6.size, checkNodeW5 c5_2_goal 1 c5_2_pow 4 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 6 c5_2_L6 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_2_L6.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_2_chk_6_0 i (Nat.zero_le _) (by omega)
theorem c5_2_L6_sound : ∀ i < c5_2_L6.size, ¬ live (basicOps 32) c5_2_goal 6 (c5_2_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound (fun j hj => by simp at hj) c5_2_chk_6
set_option maxRecDepth 100000 in
theorem c5_2_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_2_goal ws) = [rows5] := by decide +kernel
theorem c5_2_top_match : sameSet (rows5.map (actB 32 (c5_2_pow[0]?.getD []))) (c5_2_L6[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_2_no_build : ¬ build (basicOps 32) c5_2_goal 6 rows5.toFinset :=
  no_build_of_top c5_2_G_valid (by decide) c5_2_sublists c5_2_top_match (c5_2_L6_sound 0 (by decide))

def c5_3_goal : BitVec 32 := 0xeaa8a8a8
def c5_3_idxs4 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_no_build : ¬ build (basicOps 32) c5_3_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_0_goal (by decide) b4_0_no_build c5_3_goal c5_3_idxs4 3 17 25 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_4_goal : BitVec 32 := 0xfeeeeeea
def c5_4_idxs4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_4_no_build : ¬ build (basicOps 32) c5_4_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_0_goal (by decide) b4_0_no_build c5_4_goal c5_4_idxs4 0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

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

def v0 : BitVec 64 := 0xaaaaaaaaaaaaaaaa
def v1 : BitVec 64 := 0xcccccccccccccccc
def v2 : BitVec 64 := 0xf0f0f0f0f0f0f0f0
def v3 : BitVec 64 := 0xff00ff00ff00ff00
def v4 : BitVec 64 := 0xffff0000ffff0000
def v5 : BitVec 64 := 0xffffffff00000000
def v6 : BitVec 64 := 0xeeeeeeeeeeeeeeee
def v7 : BitVec 64 := 0xfafafafafafafafa
def v8 : BitVec 64 := 0xfcfcfcfcfcfcfcfc
def v9 : BitVec 64 := 0xfefefefefefefefe
def v10 : BitVec 64 := 0xffccffccffccffcc
def v11 : BitVec 64 := 0xaaaa0000aaaa0000
def v12 : BitVec 64 := 0xcc00cc00cc00cc00
def v13 : BitVec 64 := 0xffffaaaaffffaaaa
def v14 : BitVec 64 := 0xf000f000f000f00
def v15 : BitVec 64 := 0xffccffcc00000000
def v16 : BitVec 64 := 0x3232323232323232
def v17 : BitVec 64 := 0xaaaa0000aaaa
def v18 : BitVec 64 := 0xe0e0e0e0e0e0e0e
def v19 : BitVec 64 := 0xfafaf0f0fafaf0f0
def v20 : BitVec 64 := 0xff000000ff000000
def v21 : BitVec 64 := 0xfcf0fcf0fcf0fcf0
def v22 : BitVec 64 := 0xeeeecccceeeecccc
def v23 : BitVec 64 := 0xffffaaaa00000000
def v24 : BitVec 64 := 0xfefefefe00000000
def v25 : BitVec 64 := 0x3333000033330000
def v26 : BitVec 64 := 0xcc00cc00cc00cc
def v27 : BitVec 64 := 0xfe00fe00fe00fe00
def v28 : BitVec 64 := 0xf0c0f0c0f0c0f0c
def v29 : BitVec 64 := 0xfefe0000fefe
def v30 : BitVec 64 := 0xf0f00000f0f0000
def v31 : BitVec 64 := 0x2222222222222222
def v32 : BitVec 64 := 0xeeaaeeaaeeaaeeaa
def v33 : BitVec 64 := 0xa0a0a0a0a0a0a0a
def v34 : BitVec 64 := 0xfefe0000fefe0000
def v35 : BitVec 64 := 0x303000003030000
def v36 : BitVec 64 := 0x5555000055550000
def v37 : BitVec 64 := 0xf0f0fafaf0f0fafa
def v38 : BitVec 64 := 0xaa00aa00aa00aa00
def v39 : BitVec 64 := 0x3300330033003300
def v40 : BitVec 64 := 0xf3f3f0f0f3f3f0f0
def v41 : BitVec 64 := 0x5500550055005500
def v42 : BitVec 64 := 0xaaeeaaeeaaeeaaee
def v43 : BitVec 64 := 0xcfcccfcccfcccfcc
def v44 : BitVec 64 := 0x3333222233332222
def v45 : BitVec 64 := 0xfffff0f0fffff0f0
def v46 : BitVec 64 := 0xa8a8a8a8a8a8a8a8
def v47 : BitVec 64 := 0xafaaafaaafaaafaa
def v48 : BitVec 64 := 0xfafefafefafefafe
def v49 : BitVec 64 := 0x33cc33cc33cc33cc
def v50 : BitVec 64 := 0x300030003000300
def v51 : BitVec 64 := 0x5454545454545454
def v52 : BitVec 64 := 0xff000000ff0000
def v53 : BitVec 64 := 0xeeaacc00eeaacc00
def v54 : BitVec 64 := 0xfa00fa00fa00fa00
def v55 : BitVec 64 := 0xafafaaaaafafaaaa
def v56 : BitVec 64 := 0xfefafefafefafefa
def v57 : BitVec 64 := 0xbbbbaaaabbbbaaaa
def v58 : BitVec 64 := 0xffaaaaaaffaaaaaa
def v59 : BitVec 64 := 0xffeeeeeeffeeeeee
def v60 : BitVec 64 := 0x4444444444444444
def v61 : BitVec 64 := 0xfff0fff0fff0fff0
def v62 : BitVec 64 := 0x33ff33ff00000000
def v63 : BitVec 64 := 0xf0fcf0fcf0fcf0fc
def v64 : BitVec 64 := 0xfff0f0f0fff0f0f0
def v65 : BitVec 64 := 0xcfcfcccccfcfcccc
def v66 : BitVec 64 := 0xfefefcfcfefefcfc
def v67 : BitVec 64 := 0x1100110011001100
def v68 : BitVec 64 := 0xff000000ff00
def v69 : BitVec 64 := 0x3232303032323030
def v70 : BitVec 64 := 0xfc00fc00fc00fc00
def v71 : BitVec 64 := 0xfefcfefcfefcfefc
def v72 : BitVec 64 := 0xee00ee00ee00ee00
def v73 : BitVec 64 := 0xfafa0000fafa0000
def v74 : BitVec 64 := 0xf2f2f2f2f2f2f2f2
def v75 : BitVec 64 := 0xffaaffaaffaaffaa
def v76 : BitVec 64 := 0xc0c0c0c0c0c0c0c
def v77 : BitVec 64 := 0x3333303033333030
def v78 : BitVec 64 := 0xffeeffeeaaaaaaaa
def v79 : BitVec 64 := 0x303020203030202
def v80 : BitVec 64 := 0xe0a0e0a0e0a0e0a
def v81 : BitVec 64 := 0xa0e0a0e0a0e0a0e
def v82 : BitVec 64 := 0xffccccccffcccccc
def v83 : BitVec 64 := 0xfafffafafafffafa
def v84 : BitVec 64 := 0x30f0000030f0000
def v85 : BitVec 64 := 0xefeeefeeefeeefee
def v86 : BitVec 64 := 0xfcfc0000fcfc
def v87 : BitVec 64 := 0xeecceecceecceecc
def v88 : BitVec 64 := 0xfaf0faf0faf0faf0
def v89 : BitVec 64 := 0xf0a0a0a0f0a0a0a
def v90 : BitVec 64 := 0xcccc0000cccc0000
def v91 : BitVec 64 := 0xfffffcfcfffffcfc
def v92 : BitVec 64 := 0xaeaeaeaeaeaeaeae
def v93 : BitVec 64 := 0xaa88aa8800000000
def v94 : BitVec 64 := 0xf0a0f0a0f0a0f0a
def v95 : BitVec 64 := 0x202020202020202
def v96 : BitVec 64 := 0xcccceeeecccceeee
def v97 : BitVec 64 := 0xfcfc0000fcfc0000
def v98 : BitVec 64 := 0xfbfbfafafbfbfafa
def v99 : BitVec 64 := 0xfffafafafffafafa
def v100 : BitVec 64 := 0xb0b0a0a0b0b0a0a
def v101 : BitVec 64 := 0x5500ff00ff00
def v102 : BitVec 64 := 0xffffeeeecccccccc
def v103 : BitVec 64 := 0xf5f0f5f0f5f0f5f0
def v104 : BitVec 64 := 0x100010001000100
def v105 : BitVec 64 := 0x500050005000500
def v106 : BitVec 64 := 0xf0f0fff0f0f0fff0
def v107 : BitVec 64 := 0x114433cc114433cc
def v108 : BitVec 64 := 0x2322232223222322
def v109 : BitVec 64 := 0x3636363636363636
def v110 : BitVec 64 := 0xee00cc00ee00cc00
def v111 : BitVec 64 := 0x3333222200000000
def v112 : BitVec 64 := 0xc8c8c8c8c8c8c8c8
def v113 : BitVec 64 := 0x20a020a020a020a
def v114 : BitVec 64 := 0xaaffaaaaaaffaaaa
def v115 : BitVec 64 := 0xfefafcf0fefafcf0
def v116 : BitVec 64 := 0x3322222233222222
def v117 : BitVec 64 := 0xe0c0e0c0e0c0e0c
def v118 : BitVec 64 := 0x3230323032303230
def v119 : BitVec 64 := 0x3333cccc3333cccc
def v120 : BitVec 64 := 0xffffccccffffcccc
def v121 : BitVec 64 := 0xff00aa0000000000
def v122 : BitVec 64 := 0xddccddccddccddcc
def v123 : BitVec 64 := 0x2323222223232222
def v124 : BitVec 64 := 0xa8a0a8a0a8a0a8a0
def v125 : BitVec 64 := 0xfcf00000fcf0
def v126 : BitVec 64 := 0x5450545054505450
def v127 : BitVec 64 := 0xfafefafe00000000
def v128 : BitVec 64 := 0xa0f0a0a0a0f0a0a
def v129 : BitVec 64 := 0xafaeafaeafaeafae
def v130 : BitVec 64 := 0xffcc000000000000
def v131 : BitVec 64 := 0xefefeeeeefefeeee
def v132 : BitVec 64 := 0x3030323230303232
def v133 : BitVec 64 := 0x3130313031303130
def v134 : BitVec 64 := 0x3330303033303030
def v135 : BitVec 64 := 0x3030333030303330
def v136 : BitVec 64 := 0xfafffaff00000000
def v137 : BitVec 64 := 0xffeeffccffeeffcc
def v138 : BitVec 64 := 0x33ff22aa33ff22aa
def v139 : BitVec 64 := 0xf0c0f0c00000000
def v140 : BitVec 64 := 0xffccaa88ffccaa88
def v141 : BitVec 64 := 0x5555aaaa5555aaaa
def v142 : BitVec 64 := 0xfe00fe00fe00fe
def v143 : BitVec 64 := 0xffeeeeee00000000
def v144 : BitVec 64 := 0xf3f3f2f2f3f3f2f2
def v145 : BitVec 64 := 0xfffcfffcf0f0f0f0
def v146 : BitVec 64 := 0xfdfcfdfcfdfcfdfc
def v147 : BitVec 64 := 0xfffcfcfcfffcfcfc
def v148 : BitVec 64 := 0xf4f4f4f4f4f4f4f4
def v149 : BitVec 64 := 0xcececececececece
def v150 : BitVec 64 := 0xfcfcfefefcfcfefe
def v151 : BitVec 64 := 0xfcfcfffcfcfcfffc
def v152 : BitVec 64 := 0xfa00f000fa00f000
def v153 : BitVec 64 := 0x115533ff00000000
def v154 : BitVec 64 := 0x33336666cccccccc
def v155 : BitVec 64 := 0xf0e0e0e0f0e0e0e
def v156 : BitVec 64 := 0xfaff0000faff0000
def v157 : BitVec 64 := 0x5555ffff00000000
def v158 : BitVec 64 := 0xffccaa8800000000
def v159 : BitVec 64 := 0xcccc888800000000
def v160 : BitVec 64 := 0xfffffafaf0f0f0f0
def v161 : BitVec 64 := 0xeeee0000eeee0000
def v162 : BitVec 64 := 0x404040404040404
def v163 : BitVec 64 := 0xc8c8c0c0c8c8c0c0
def v164 : BitVec 64 := 0xfffafff0fffafff0
def v165 : BitVec 64 := 0xf0f0a0a0f0f0a0a
def v166 : BitVec 64 := 0xfffafffafffafffa
def v167 : BitVec 64 := 0xfef0fcf0fef0fcf0
def v168 : BitVec 64 := 0xff00ee00cc00cc00
def v169 : BitVec 64 := 0xf1f0f1f0f1f0f1f0
def v170 : BitVec 64 := 0xcfcfcececfcfcece
def v171 : BitVec 64 := 0x4444cccccccc
def v172 : BitVec 64 := 0xfef0fef0fef0fef0
def v173 : BitVec 64 := 0x1100330011003300
def v174 : BitVec 64 := 0x105030f0105030f0
def v175 : BitVec 64 := 0xfafe0000fafe0000
def v176 : BitVec 64 := 0xaeae0c0caeae0c0c
def v177 : BitVec 64 := 0x33ff22aa00000000
def v178 : BitVec 64 := 0xafaa0f00afaa0f00
def v179 : BitVec 64 := 0xffffffccffff0000
def v180 : BitVec 64 := 0xfefeccccfefecccc
def v181 : BitVec 64 := 0x101000001010000
def v182 : BitVec 64 := 0xeeeeee00eeeeee
def v183 : BitVec 64 := 0xfeccfeccfeccfecc
def v184 : BitVec 64 := 0xfafffafa00000000
def v185 : BitVec 64 := 0xaaee00ccaaee00cc
def v186 : BitVec 64 := 0xffcc00000000
def v187 : BitVec 64 := 0x33ff000033ff0000
def v188 : BitVec 64 := 0xcccc0000cccc
def v189 : BitVec 64 := 0xffeeffcc00000000
def v190 : BitVec 64 := 0xb8b8b8b8b8b8b8b8
def v191 : BitVec 64 := 0x36363c3c36363c3c
def v192 : BitVec 64 := 0xff05ff0f00000000
def v193 : BitVec 64 := 0xffeeffccaaaa0000
def v194 : BitVec 64 := 0xfaf8faf8f0f0f0f0
def v195 : BitVec 64 := 0xffee0000aaaa
def v196 : BitVec 64 := 0xa8fca8fca8fca8fc
def v197 : BitVec 64 := 0xfafafa00fafafa
def v198 : BitVec 64 := 0xfefcfefc00000000
def v199 : BitVec 64 := 0xeeaa0000eeaa
def v200 : BitVec 64 := 0x32fa30f032fa30f0
def v201 : BitVec 64 := 0xa080a080a080a08
def v202 : BitVec 64 := 0xf0c00000f0c
def v203 : BitVec 64 := 0xa020a020a020a02
def v204 : BitVec 64 := 0xfff0fffafff0fffa
def v205 : BitVec 64 := 0x2022202220222022
def v206 : BitVec 64 := 0x3033000030330000
def v207 : BitVec 64 := 0x1155eeaa1155eeaa
def v208 : BitVec 64 := 0xffffffaaff00ff00
def v209 : BitVec 64 := 0x33ffccffff0000
def v210 : BitVec 64 := 0xfe00ff00fe00ff00
def v211 : BitVec 64 := 0xfefeffff00000000
def v212 : BitVec 64 := 0x4544454445444544
def v213 : BitVec 64 := 0x3030c0c03030c0c
def v214 : BitVec 64 := 0xf3f3fcfcf3f3fcfc
def v215 : BitVec 64 := 0xeeaa0000eeaa0000
def v216 : BitVec 64 := 0x5544ffcc5544ffcc
def v217 : BitVec 64 := 0xff00aa00000000
def v218 : BitVec 64 := 0xabaaabaaabaaabaa
def v219 : BitVec 64 := 0xe000e000e000e00
def v220 : BitVec 64 := 0x1111000011110000
def v221 : BitVec 64 := 0xfdf0fdf0fdf0fdf0
def v222 : BitVec 64 := 0x3200320032003200
def v223 : BitVec 64 := 0xcd00cd00cd00cd00
def v224 : BitVec 64 := 0x3232000032320000
def v225 : BitVec 64 := 0x504050405040504
def v226 : BitVec 64 := 0xfefefafafefefafa
def v227 : BitVec 64 := 0x303fcfc0303fcfc
def v228 : BitVec 64 := 0xaeae0000aeae0000
def v229 : BitVec 64 := 0x3100310031003100
def v230 : BitVec 64 := 0xfffaf0f0fffaf0f0
def v231 : BitVec 64 := 0x2233000022330000
def v232 : BitVec 64 := 0x7733550077335500
def v233 : BitVec 64 := 0x1155000011550000
def v234 : BitVec 64 := 0xfac8f0c0fac8f0c0
def v235 : BitVec 64 := 0xfafef0fcfafef0fc
def v236 : BitVec 64 := 0xfa00f000fa00f0
def v237 : BitVec 64 := 0x3300220033002200
def v238 : BitVec 64 := 0xcc00dd00cc00dd00
def v239 : BitVec 64 := 0xeceeeceeeceeecee
def v240 : BitVec 64 := 0xa0a2a0a2a0a2a0a2
def v241 : BitVec 64 := 0xffff0f0cffff0f0c
def v242 : BitVec 64 := 0xf0f30000f0f30000
def v243 : BitVec 64 := 0xf0c0ffccf0c0ffcc
def v244 : BitVec 64 := 0x3300110033001100
def v245 : BitVec 64 := 0xf0005000f000500
def v246 : BitVec 64 := 0x3300300033003000
def v247 : BitVec 64 := 0xafaa0000afaa0000
def v248 : BitVec 64 := 0x3000330030003300
def v249 : BitVec 64 := 0xe0e0eeeee0e0eeee
def v250 : BitVec 64 := 0x32fa32fa32fa32fa
def v251 : BitVec 64 := 0xfac8fac8fac8fac8
def v252 : BitVec 64 := 0xfa32fa32fa32fa32
def v253 : BitVec 64 := 0x3232fafa3232fafa
def v254 : BitVec 64 := 0xfa00fafafa00fafa
def v255 : BitVec 64 := 0x8888888888888888
def v256 : BitVec 64 := 0xffffff00ffffff00

def g6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s1 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31,32,34,33,35,36,38,37,39,48,50,49,51,52,54,53,55,40,42,41,43,44,46,45,47,56,58,57,59,60,62,61,63]
def g6_p1 : List ℕ := [1,4,2,8,16,64,32,128,65536,262144,131072,524288,1048576,4194304,2097152,8388608,256,1024,512,2048,4096,16384,8192,32768,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648,4294967296,17179869184,8589934592,34359738368,68719476736,274877906944,137438953472,549755813888,281474976710656,1125899906842624,562949953421312,2251799813685248,4503599627370496,18014398509481984,9007199254740992,36028797018963968,1099511627776,4398046511104,2199023255552,8796093022208,17592186044416,70368744177664,35184372088832,140737488355328,72057594037927936,288230376151711744,144115188075855872,576460752303423488,1152921504606846976,4611686018427387904,2305843009213693952,9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0,g6_s1]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0,g6_p1]
def g6_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_G_valid : (List.range 2).all (symValid 64 2 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel

def g6_m0 : BitVec 64 := 0xffffffff00000000

def g6_st0 : List (BitVec 64) := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]

def g6_ix0 : List ℕ := [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_0 : g6_ix0.length = 32 ∧ (∀ idx ∈ g6_ix0, idx < 64) ∧ (∀ idx ∈ g6_ix0, g6_m0.getLsbD idx = true) ∧ projS 32 g6_ix0 goal6 = c5_0_goal ∧ g6_st0.all (fun w => rows5.contains (projS 32 g6_ix0 w)) = true := by decide +kernel

def g6_m1 : BitVec 64 := 0x5555000055550000

def g6_st1 : List (BitVec 64) := [0x4444000044440000,0x5050000050500000,0x5500000055000000,0x5555000000000000]

def g6_ix1 : List ℕ := [16,18,20,22,24,26,28,30,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_1 : g6_ix1.length = 16 ∧ (∀ idx ∈ g6_ix1, idx < 64) ∧ (∀ idx ∈ g6_ix1, g6_m1.getLsbD idx = true) ∧ projS 16 g6_ix1 goal6 = b4_0_goal ∧ g6_st1.all (fun w => rows4.contains (projS 16 g6_ix1 w)) = true := by decide +kernel

def g6_m2 : BitVec 64 := 0x3300330033003300

def g6_st2 : List (BitVec 64) := [0x2200220022002200,0x3000300030003000,0x3300000033000000,0x3300330000000000]

def g6_ix2 : List ℕ := [8,9,12,13,24,25,28,29,40,41,44,45,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_2 : g6_ix2.length = 16 ∧ (∀ idx ∈ g6_ix2, idx < 64) ∧ (∀ idx ∈ g6_ix2, g6_m2.getLsbD idx = true) ∧ projS 16 g6_ix2 goal6 = b4_0_goal ∧ g6_st2.all (fun w => rows4.contains (projS 16 g6_ix2 w)) = true := by decide +kernel

def g6_m3 : BitVec 64 := 0xf0f0f0f0f0f0f0f

def g6_st3 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]

def g6_ix3 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,32,33,34,35,40,41,42,43,48,49,50,51,56,57,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_3 : g6_ix3.length = 32 ∧ (∀ idx ∈ g6_ix3, idx < 64) ∧ (∀ idx ∈ g6_ix3, g6_m3.getLsbD idx = true) ∧ projS 32 g6_ix3 goal6 = c5_1_goal ∧ g6_st3.all (fun w => rows5.contains (projS 32 g6_ix3 w)) = true := by decide +kernel

def g6_m4 : BitVec 64 := 0xff00ff00ff00ff

def g6_st4 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]

def g6_ix4 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_4 : g6_ix4.length = 32 ∧ (∀ idx ∈ g6_ix4, idx < 64) ∧ (∀ idx ∈ g6_ix4, g6_m4.getLsbD idx = true) ∧ projS 32 g6_ix4 goal6 = c5_2_goal ∧ g6_st4.all (fun w => rows5.contains (projS 32 g6_ix4 w)) = true := by decide +kernel

def g6_m5 : BitVec 64 := 0x5555555555555555

def g6_st5 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]

def g6_ix5 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_5 : g6_ix5.length = 32 ∧ (∀ idx ∈ g6_ix5, idx < 64) ∧ (∀ idx ∈ g6_ix5, g6_m5.getLsbD idx = true) ∧ projS 32 g6_ix5 goal6 = c5_3_goal ∧ g6_st5.all (fun w => rows5.contains (projS 32 g6_ix5 w)) = true := by decide +kernel

def g6_m6 : BitVec 64 := 0xffff0000ffff

def g6_st6 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]

def g6_ix6 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_6 : g6_ix6.length = 32 ∧ (∀ idx ∈ g6_ix6, idx < 64) ∧ (∀ idx ∈ g6_ix6, g6_m6.getLsbD idx = true) ∧ projS 32 g6_ix6 goal6 = c5_2_goal ∧ g6_st6.all (fun w => rows5.contains (projS 32 g6_ix6 w)) = true := by decide +kernel

def g6_m7 : BitVec 64 := 0x5555555500000000

def g6_st7 : List (BitVec 64) := [0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000]

def g6_ix7 : List ℕ := [32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_7 : g6_ix7.length = 16 ∧ (∀ idx ∈ g6_ix7, idx < 64) ∧ (∀ idx ∈ g6_ix7, g6_m7.getLsbD idx = true) ∧ projS 16 g6_ix7 goal6 = b4_0_goal ∧ g6_st7.all (fun w => rows4.contains (projS 16 g6_ix7 w)) = true := by decide +kernel

def g6_m8 : BitVec 64 := 0xffff0000ffff0000

def g6_st8 : List (BitVec 64) := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]

def g6_ix8 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_8 : g6_ix8.length = 32 ∧ (∀ idx ∈ g6_ix8, idx < 64) ∧ (∀ idx ∈ g6_ix8, g6_m8.getLsbD idx = true) ∧ projS 32 g6_ix8 goal6 = c5_4_goal ∧ g6_st8.all (fun w => rows5.contains (projS 32 g6_ix8 w)) = true := by decide +kernel

def g6_m9 : BitVec 64 := 0x3333333333333333

def g6_st9 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]

def g6_ix9 : List ℕ := [0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,40,41,44,45,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_9 : g6_ix9.length = 32 ∧ (∀ idx ∈ g6_ix9, idx < 64) ∧ (∀ idx ∈ g6_ix9, g6_m9.getLsbD idx = true) ∧ projS 32 g6_ix9 goal6 = c5_3_goal ∧ g6_st9.all (fun w => rows5.contains (projS 32 g6_ix9 w)) = true := by decide +kernel

def g6_m10 : BitVec 64 := 0xff00ff00ff00ff00

def g6_st10 : List (BitVec 64) := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]

def g6_ix10 : List ℕ := [8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31,40,42,41,43,44,46,45,47,56,58,57,59,60,62,61,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_10 : g6_ix10.length = 32 ∧ (∀ idx ∈ g6_ix10, idx < 64) ∧ (∀ idx ∈ g6_ix10, g6_m10.getLsbD idx = true) ∧ projS 32 g6_ix10 goal6 = c5_4_goal ∧ g6_st10.all (fun w => rows5.contains (projS 32 g6_ix10 w)) = true := by decide +kernel

def g6_m11 : BitVec 64 := 0x3333333300000000

def g6_st11 : List (BitVec 64) := [0x2222222200000000,0x3030303000000000,0x3300330000000000,0x3333000000000000]

def g6_ix11 : List ℕ := [32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_11 : g6_ix11.length = 16 ∧ (∀ idx ∈ g6_ix11, idx < 64) ∧ (∀ idx ∈ g6_ix11, g6_m11.getLsbD idx = true) ∧ projS 16 g6_ix11 goal6 = b4_0_goal ∧ g6_st11.all (fun w => rows4.contains (projS 16 g6_ix11 w)) = true := by decide +kernel

def g6_cfMasks : Array (BitVec 64) := Array.mk [g6_m0,g6_m1,g6_m2,g6_m3,g6_m4,g6_m5,g6_m6,g6_m7,g6_m8,g6_m9,g6_m10,g6_m11]

def g6_cfB0s : Array ℕ := Array.mk [32,16,8,0,0,0,0,32,16,0,8,32]

def g6_cfStocks : Array (List (BitVec 64)) := Array.mk [g6_st0,g6_st1,g6_st2,g6_st3,g6_st4,g6_st5,g6_st6,g6_st7,g6_st8,g6_st9,g6_st10,g6_st11]

def g6_cfLBs : Array ℕ := Array.mk [9,6,6,8,7,7,7,6,7,7,7,6]

theorem g6_cof_sound (c fuel : ℕ) (hc : c < 12) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) (hnd : nxt.Nodup) (hchk : checkCofClose64 (g6_cfLBs[c]?.getD 0) fuel (g6_cfMasks[c]?.getD 0) (g6_cfB0s[c]?.getD 0) (g6_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose64_sound_aux goal6 9 g6_ix0 g6_cspec_0.1 g6_cspec_0.2.1 g6_m0 g6_cspec_0.2.2.1 32 g6_st0 c5_0_goal (by decide) g6_cspec_0.2.2.2.1 g6_cspec_0.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix1 g6_cspec_1.1 g6_cspec_1.2.1 g6_m1 g6_cspec_1.2.2.1 16 g6_st1 b4_0_goal (by decide) g6_cspec_1.2.2.2.1 g6_cspec_1.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix2 g6_cspec_2.1 g6_cspec_2.2.1 g6_m2 g6_cspec_2.2.2.1 8 g6_st2 b4_0_goal (by decide) g6_cspec_2.2.2.2.1 g6_cspec_2.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_sound_aux goal6 8 g6_ix3 g6_cspec_3.1 g6_cspec_3.2.1 g6_m3 g6_cspec_3.2.2.1 0 g6_st3 c5_1_goal (by decide) g6_cspec_3.2.2.2.1 g6_cspec_3.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_sound_aux goal6 7 g6_ix4 g6_cspec_4.1 g6_cspec_4.2.1 g6_m4 g6_cspec_4.2.2.1 0 g6_st4 c5_2_goal (by decide) g6_cspec_4.2.2.2.1 g6_cspec_4.2.2.2.2 c5_2_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_sound_aux goal6 7 g6_ix5 g6_cspec_5.1 g6_cspec_5.2.1 g6_m5 g6_cspec_5.2.2.1 0 g6_st5 c5_3_goal (by decide) g6_cspec_5.2.2.2.1 g6_cspec_5.2.2.2.2 c5_3_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose64_sound_aux goal6 7 g6_ix6 g6_cspec_6.1 g6_cspec_6.2.1 g6_m6 g6_cspec_6.2.2.1 0 g6_st6 c5_2_goal (by decide) g6_cspec_6.2.2.2.1 g6_cspec_6.2.2.2.2 c5_2_no_build fuel hist nxt hnd hchk
  | 7 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix7 g6_cspec_7.1 g6_cspec_7.2.1 g6_m7 g6_cspec_7.2.2.1 32 g6_st7 b4_0_goal (by decide) g6_cspec_7.2.2.2.1 g6_cspec_7.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 8 => exact checkCofClose64_sound_aux goal6 7 g6_ix8 g6_cspec_8.1 g6_cspec_8.2.1 g6_m8 g6_cspec_8.2.2.1 16 g6_st8 c5_4_goal (by decide) g6_cspec_8.2.2.2.1 g6_cspec_8.2.2.2.2 c5_4_no_build fuel hist nxt hnd hchk
  | 9 => exact checkCofClose64_sound_aux goal6 7 g6_ix9 g6_cspec_9.1 g6_cspec_9.2.1 g6_m9 g6_cspec_9.2.2.1 0 g6_st9 c5_3_goal (by decide) g6_cspec_9.2.2.2.1 g6_cspec_9.2.2.2.2 c5_3_no_build fuel hist nxt hnd hchk
  | 10 => exact checkCofClose64_sound_aux goal6 7 g6_ix10 g6_cspec_10.1 g6_cspec_10.2.1 g6_m10 g6_cspec_10.2.2.1 8 g6_st10 c5_4_goal (by decide) g6_cspec_10.2.2.2.1 g6_cspec_10.2.2.2.2 c5_4_no_build fuel hist nxt hnd hchk
  | 11 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix11 g6_cspec_11.1 g6_cspec_11.2.1 g6_m11 g6_cspec_11.2.2.1 32 g6_st11 b4_0_goal (by decide) g6_cspec_11.2.2.2.1 g6_cspec_11.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | c + 12 => omega

def g6_L3 : Array W6Node := Array.mk [
([v107,0x115522aa115522aa,v2,v5],[],[],[])
]

def g6_L4 : Array W6Node := Array.mk [
([v0,v22,v167,v189,v4],[],[],[]),
([0x1155eeaa00000000,v207,v1,v2,v3],[],[],[]),
([v0,v22,v167,v15,v4],[],[],[]),
([0x114433cc00000000,v107,v0,v2,v4],[],[],[]),
([v49,v141,v2,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v11,v0,v4),(v13,v0,v4),(v141,v11,v13)],[0,1,2],[]),
([v14,v141,v1,v2,v15],[],[],[]),
([v53,v115,v10,v13,v5],[],[],[]),
([v174,v53,v10,v13,v5],[],[],[]),
([v107,v53,v2,v13,v5],[],[],[(0,0)]),
([v153,v53,v2,v10,v13],[],[],[]),
([v107,v0,v115,v4,v5],[],[],[]),
([v174,v107,v0,v4,v5],[],[],[]),
([v107,v153,v0,v2,v4],[],[],[]),
([v107,0x5544ffcc00000000,v0,v2,v4],[],[],[]),
([v14,0x55665566aaaaaaaa,v1,v2,v4],[],[],[]),
([v0,v1,v2,0xff0faa000f0f0000,v208],[],[],[]),
([v209,v14,v0,v1,v2],[],[],[]),
([0x33006600cc00cc00,v154,v0,v2,v4],[],[],[]),
([v154,v0,v2,v168,v4],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L5 : Array W6Node := Array.mk [
([v18,v16,v0,v3,v4,v5],[],[],[]),
([v33,0xd0c0d0c0d0c0d0c,v6,v3,v4,v5],[],[],[]),
([v0,v1,v40,v24,v3,v4],[],[],[]),
([v0,0xe4e0e4e0e4e0e4e0,v8,v3,v4,v5],[],[],[]),
([0x1b1f1b1f00000000,v0,v1,v2,v3,v4],[],[],[]),
([0x3f3f0e0e00000000,v0,v1,v2,v3,v4],[],[],[]),
([v18,v16,v51,v3,v4,v5],[],[],[]),
([v16,v51,v2,v27,v4,v5],[],[],[]),
([v29,v16,v51,v2,v3,v5],[],[],[]),
([v16,v51,v2,v24,v3,v4],[],[],[]),
([v29,v18,v51,v1,v3,v5],[],[],[]),
([v18,v16,v0,v34,v3,v5],[],[],[]),
([v29,v18,v16,v0,v3,v5],[],[],[]),
([v18,v16,v0,v24,v3,v4],[],[],[]),
([v16,v0,v2,v27,v34,v5],[],[],[]),
([v16,v0,v2,v27,v24,v4],[],[],[]),
([v18,v0,v1,v27,v34,v5],[],[],[]),
([v29,v18,v0,v1,v27,v5],[],[],[]),
([v18,v0,v1,v27,v24,v4],[],[],[]),
([v18,v0,v1,v27,v4,v5],[],[],[]),
([v29,v18,v0,v1,v24,v3],[],[],[]),
([v18,v0,0xcdcdcccccdcdcccc,v3,v4,v5],[],[],[]),
([v18,v0,0xcdcccdcccdcccdcc,v3,v4,v5],[],[],[]),
([v18,v0,v1,v210,v4,v5],[],[],[]),
([v18,v0,v1,v211,v3,v4],[],[],[]),
([v0,v1,v2,v27,v34,v24],[],[],[]),
([v0,v1,v2,v27,v34,v5],[],[],[]),
([v29,v0,v1,v2,v27,v24],[],[],[]),
([v0,v1,v169,v34,v3,v5],[],[],[]),
([v0,v1,v2,v3,0xfffe0100fffe0100,v5],[],[],[]),
([v0,v1,v2,v27,v211,v4],[],[],[]),
([v29,v0,v1,v2,v27,v5],[],[],[]),
([v0,v1,v2,v27,v24,v4],[],[],[]),
([v29,v142,v0,v1,v2,v24],[],[],[]),
([0x100fffe0100fffe,v0,v1,v2,v3,v5],[],[],[]),
([v29,v0,v1,v2,0xfefffeff00000000,v3],[],[],[]),
([v0,v1,v169,v24,v3,v4],[],[],[]),
([v0,v1,v2,v210,v24,v4],[],[],[]),
([v0,v1,v2,v3,0xfffefffe01000100,v4],[],[],[]),
([v0,v1,0xfef0fef0f0f0f0f0,v24,v3,v4],[],[],[]),
([v0,v1,v24,v3,v64,v4],[],[],[]),
([v155,v0,v1,v3,v4,v5],[],[],[]),
([v0,v1,v2,v3,0xfffefefe00000000,v4],[],[],[]),
([v0,v1,v2,v3,0xff0e0e0e00000000,v4],[],[],[]),
([0x1f0e1f0e00000000,v0,v1,v2,v3,v4],[],[],[]),
([v0,v1,0xe1e0e1e0e1e0e1e0,v3,v4,v5],[],[],[]),
([v108,v212,v2,v3,v4,v5],[],[],[]),
([v116,0x5544444455444444,v2,v3,v4,v5],[],[],[]),
([v0,v1,0xf0e0e0e0f0e0e0e0,v3,v143,v4],[],[],[]),
([v155,v0,v1,v3,v143,v4],[],[],[]),
([v0,v1,v2,0xf0fefefe00000000,v3,v4],[],[],[]),
([v0,0xeee0e0e0eee0e0e0,v8,v3,v4,v5],[],[],[]),
([0x111f1f1f00000000,v0,v1,v2,v3,v4],[],[],[]),
([v18,v0,v1,v24,v3,v4],[],[],[]),
([v18,v0,v190,v3,v4,v5],[],[],[]),
([0x1212121212121212,0x5656565656565656,v2,v3,v4,v5],[],[],[]),
([v16,0x5656565656565656,v2,v3,v4,v5],[],[],[]),
([v18,v109,v0,v3,v4,v5],[],[],[]),
([v109,v0,v2,v27,v4,v5],[],[],[]),
([v109,v0,v2,v34,v3,v5],[],[],[]),
([v29,v109,v0,v2,v3,v5],[],[],[]),
([v109,v0,v2,v24,v3,v4],[],[],[]),
([v18,v16,v46,v3,v4,v5],[],[],[]),
([v18,v46,v1,v27,v4,v5],[],[],[]),
([v18,v46,v1,v34,v3,v5],[],[],[]),
([v18,v46,v1,v24,v3,v4],[],[],[]),
([v46,v1,v2,v27,v34,v5],[],[],[]),
([v46,v1,v2,v34,v24,v3],[],[],[]),
([v16,v51,v2,v3,v4,v5],[],[],[]),
([v18,v0,v65,v3,v4,v5],[],[],[]),
([v18,v0,v1,v156,v3,v5],[],[],[]),
([0x2fe00fe02fe00fe,v0,v1,v2,v4,v5],[],[],[]),
([v0,v1,v2,v156,v24,v3],[],[],[]),
([v18,v0,v1,v136,v3,v4],[],[],[]),
([v0,v1,v2,v136,v34,v3],[],[],[]),
([v0,v1,v40,v27,v4,v5],[],[],[]),
([v0,v1,v2,v3,0xfffe0500fffe0500,v5],[],[],[]),
([v0,v1,v2,v3,0xfffefffe05000500,v4],[],[],[]),
([0x34343c3c34343c3c,v0,v19,v3,v4,v5],[],[],[]),
([v80,v126,v1,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v56,v12,v7),(v126,v0,v56),(v80,v2,v56)],[3],[]),
([v0,v170,v144,v3,v4,v5],[],[],[]),
([v0,v1,0xfac8fac800000000,v3,v145,v4],[],[],[]),
([v81,0x5054505450545054,v1,v3,v4,v5],[],[],[]),
([v81,v0,v1,v54,v4,v5],[],[],[]),
([v81,v0,v1,v175,v3,v5],[],[],[]),
([v81,v0,v1,v127,v3,v4],[],[],[]),
([v0,v1,v2,v175,v127,v3],[],[],[]),
([0xfafe0000fafe,v0,v1,v2,v127,v3],[],[],[]),
([v117,v118,v0,v3,v4,v5],[],[],[]),
([v100,0x5151505051515050,v1,v3,v4,v5],[],[],[]),
([v89,0x5550505055505050,v1,v3,v4,v5],[],[],[]),
([v128,0x5055505050555050,v1,v3,v4,v5],[],[],[]),
([v100,v92,v1,v3,v4,v5],[],[],[]),
([v69,v0,v176,v3,v4,v5],[],[],[]),
([0x1b5f1b5f00000000,v1,v32,v2,v3,v4],[],[],[]),
([v0,0xe2e2c0c0e2e2c0c0,v66,v3,v4,v5],[],[],[]),
([0x3e3e3c3c3e3e3c3c,v0,v3,v4,v5],[],[],[]),
([v69,0x3e3e3c3c3e3e3c3c,v0,v3,v4,v5],[],[],[]),
([0x3e3e3c3c3e3e3c3c,v0,v19,v3,v4,v5],[],[],[]),
([0xa5a4a5a4a5a4a5a4,v129,v1,v3,v4,v5],[],[],[]),
([v213,v119,v0,v214,v3,v5],[(v90,v1,v4),(v120,v1,v4),(v119,v90,v120),(v214,v119,v2),(v213,v119,v2)],[0],[]),
([0x3b3f0a0f00000000,v0,v1,v2,v3,v4],[],[],[]),
([v0,v1,v2,0xf8fcfaff00000000,v3,v4],[],[],[]),
([v0,v22,v167,v137,v4,v5],[],[],[(0,0)]),
([v207,v1,v2,v3,v5],[(v12,v1,v3),(v32,v12,v0),(v215,v32,v4),(0xffffeeaaffffeeaa,v32,v4),(v207,v215,0xffffeeaaffffeeaa)],[0,1,4],[(0,1)]),
([v207,v1,v32,v2,v3,v5],[],[],[]),
([v0,v110,v22,v2,v189,v4],[],[],[(0,0)]),
([v14,v0,v22,v2,v189,v4],[],[],[]),
([0x111f333f00000000,v0,v22,v2,v3,v4],[],[],[]),
([v0,v22,v167,v10,v4,v5],[],[],[(0,2)]),
([0x1155aaaa1155aaaa,v1,v32,v2,v3,v5],[],[],[]),
([v0,v110,v22,v2,v15,v4],[],[],[(0,2)]),
([v14,v0,v22,v2,v15,v4],[],[],[]),
([v0,v22,0xfef2fcf0fef2fcf0,v3,v4,v5],[],[],[]),
([0x1155bbff00000000,v1,v32,v2,v3,v4],[],[],[]),
([v0,0xddccffcc00000000,v22,v2,v3,v4],[],[],[]),
([v191,v0,v3,v4,v5],[],[],[]),
([v191,v0,v66,v3,v4,v5],[],[],[]),
([v191,v0,v19,v3,v4,v5],[],[],[]),
([v69,v191,v0,v3,v4,v5],[],[],[]),
([v49,v0,v19,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v12,v1,v3),(v10,v1,v3),(v49,v12,v10)],[0,1,2,5,6],[]),
([v84,v0,v1,v21,v3,v23],[],[],[]),
([0x30ffcf0030ffcf0,v0,v1,v21,v3,v5],[],[],[]),
([v84,v0,v1,v21,v3,0xffff030f00000000],[],[],[]),
([0x30ffcf0030ffcf0,v0,v1,v3,v5],[],[],[]),
([v191,v0,v2,v3,v4,v5],[],[],[]),
([v49,v0,v2,v19,v4,v5],[],[],[]),
([v14,v0,v1,v19,v15,v4],[],[],[]),
([0x30ff0f0030ff0f0,v0,v1,v21,v3,v5],[],[],[]),
([0xf0ffcf00f0ffcf0,v0,v1,v21,v3,v5],[],[],[]),
([v14,v0,v1,v19,v192,v4],[],[],[]),
([0x30ffcf0030ffcf0,v0,v1,v2,v3,v5],[],[],[]),
([v84,v0,v1,v2,v3,0xffff030f00000000],[],[],[]),
([v49,v157,v0,v2,v4],[(v11,v0,v4),(v157,v11,v5),(v12,v1,v3),(v10,v1,v3),(v49,v12,v10)],[2,7],[]),
([v14,0x5544ffcc00000000,v0,v1,v2,v4],[],[],[]),
([v107,v0,v2,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v11,v0,v4),(v107,v49,v11)],[0],[(0,3)]),
([v49,v11,v2,v13,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v11,v0,v4),(v13,v0,v4)],[0,2,5,8],[(0,4)]),
([v14,v141,v1,v2,v10,v5],[],[],[(0,5)]),
([v28,v141,v1,v2,v3,v5],[],[],[]),
([v49,v0,v2,v4,v23],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v13,v0,v4),(v23,v13,v5)],[2,5,8],[(1,5)]),
([v49,v0,v2,v37,v4,v5],[],[],[]),
([v17,v49,v36,v2,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v17,v0,v4),(v36,v0,v4)],[0,2,5,6],[(0,4)]),
([v49,v0,v55,v2,v4,v5],[],[],[]),
([v53,v2,v10,v13,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4),(v53,v11,v12),(v13,v0,v4)],[0,5,8,9,10],[(0,6),(0,7),(0,8),(0,9),(1,8)]),
([v0,v53,v115,v10,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4),(v53,v11,v12),(v115,v53,v2)],[9],[(0,6),(0,10)]),
([v174,v0,v53,v10,v4,v5],[],[],[(0,7),(0,11)]),
([v107,v0,v53,v2,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4),(v53,v11,v12),(v107,v53,v10)],[0,9],[(0,8),(0,10),(0,11),(0,12)]),
([v153,v0,v53,v2,v10,v4],[],[],[(0,9),(0,12)]),
([v107,v216,v0,v2,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4),(v216,v11,v10),(v107,v216,v12)],[0],[(0,13)]),
([v177,v138,v11,v1,v2,v3],[],[],[(1,13)]),
([v14,v11,v1,v2,v15,v13],[],[],[(0,5)]),
([v153,v0,v1,v115,v3,v4],[],[],[]),
([v0,v1,v115,v3,v4,v5],[],[],[]),
([v0,v1,v2,0xf1f5f3ff00000000,v3,v4],[],[],[]),
([v174,v153,v0,v1,v3,v4],[],[],[]),
([v0,v1,v2,0xf3fff2fa00000000,v3,v4],[],[],[]),
([v0,v178,v1,v2,v15,v4],[],[],[]),
([v14,v0,v1,v2,v193,v4],[],[],[]),
([v14,v0,v1,v2,v158,v4],[],[],[]),
([0x5544ffccffcc,v30,v0,v1,v2,v3],[],[],[]),
([v0,v1,v2,v3,0xfffcfaf800000000,v4],[],[],[]),
([v101,v0,v1,v2,v158,v4],[],[],[]),
([v0,v1,v2,v3,0xffccaaaa0000aaaa,v15],[],[],[]),
([v17,v14,v36,v1,v2,v15],[],[],[(0,5)]),
([v0,0xaf88af880f000f00,v1,v2,v15,v4],[],[],[]),
([v14,v0,v1,v194,v15,v4],[],[],[]),
([v14,v0,v1,v2,v15,0xffffaa88ffff0000],[],[],[]),
([v14,0x55770000ffff0000,v0,v1,v2,v15],[],[],[]),
([v14,v93,v1,v2,v78,v4],[],[],[(0,14)]),
([v14,v0,v1,v2,v15,0xffee0000aaaa0000],[],[],[]),
([v195,v14,v0,v1,v2,v15],[],[],[]),
([v171,v30,v111,v0,v2,v3],[],[],[(1,14)]),
([v0,v1,v2,v3,0xff0faa000f0f0000,v23],[],[],[(0,15)]),
([v14,v0,v1,v15,0xfffcf0f0f0f0f0f0,v4],[],[],[]),
([v14,v0,v1,v2,v130,v179],[],[],[(0,16),(1,15)]),
([v101,v217,v30,v0,v1,v2],[],[],[(1,16)]),
([0xa5a6a5a6a5a6a5a6,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,0xf00ff50af00ff50a,v2,v4,v5],[],[],[]),
([0x30300000f0f0000,v0,v1,0xfcfcf8f8f0f0f0f0,v3,v23],[],[],[]),
([v154,v0,v2,v3,v4],[(v13,v0,v4),(v23,v13,v5),(v159,v1,v23),(v102,v1,v23),(v154,v159,v102)],[2,5,8],[(0,17),(1,14)]),
([v154,v0,v2,v3,v4,v102],[(v13,v0,v4),(v23,v13,v5),(v159,v1,v23),(v102,v1,v23),(v154,v159,v102)],[2],[(0,18)]),
([v93,v1,v2,v3,0xffee0000aaaa0000,v78],[],[],[(1,18)]),
([v154,v0,v2,v3,v4,v23],[],[],[]),
([v0,v1,v2,v168,v4,v160],[(v13,v0,v4),(v23,v13,v5),(v102,v1,v23),(v160,v2,v23),(v168,v102,v3)],[9],[]),
([v139,v0,v1,v2,v3,0xffee0000aaaa0000],[],[],[]),
([v111,v154,v0,v2,v3,v4],[],[],[]),
([0xf0f0f0a0f000f00,v0,v1,v2,v121,v4],[],[],[]),
([v209,v0,v1,v2,v3],[(v10,v1,v3),(v15,v10,v5),(v130,v15,v4),(v179,v4,v15),(v209,v130,v179)],[9,10],[(0,16)]),
([v209,v0,v1,v2,v3,v15],[],[],[]),
([0x3c3c36363c3c3636,v0,v2,v3,v4,v5],[],[],[]),
([v0,v1,v2,v127,v3,v4],[],[],[]),
([v0,v1,v2,0xf0fcfafe00000000,v3,v4],[],[],[]),
([0xf03f0fc0f03f0fc,v0,v1,v2,v3,v5],[],[],[]),
([v89,0x5550555055505550,v1,v3,v4,v5],[],[],[]),
([0x6363666663636666,v0,v2,v3,v4,v5],[],[],[]),
([0x3033cfcc3033cfcc,v0,v1,v2,v3,v5],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L6 : Array W6Node := Array.mk [
([0x2626262626262626,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v112,v1,v7),(0x2626262626262626,v112,v6)],[3],[]),
([v16,v6,v2,v7,v3,v4,v5],[],[],[]),
([v18,v46,v6,v8,v3,v4,v5],[],[],[]),
([v18,v16,v6,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v16,v1,v7),(v18,v6,v2)],[3],[]),
([v0,v6,v103,v8,v3,v4,v5],[],[],[]),
([v0,v6,v2,v146,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v41,v0,v3),(v146,v41,v8)],[3],[]),
([v196,v0,v6,v2,v3,v4,v5],[],[],[]),
([v0,v6,v8,v172,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v72,v6,v3),(v172,v72,v2)],[2,3],[]),
([v0,v6,v169,v8,v3,v4,v5],[],[],[]),
([0x1010fcfc1010fcfc,v0,v6,v2,v3,v4,v5],[],[],[]),
([v57,v6,v2,v8,v3,v4,v5],[],[],[]),
([v0,v6,0xf1f1f0f0f1f1f0f0,v8,v3,v4,v5],[],[],[]),
([v6,v2,v7,v180,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v73,v7,v4),(v180,v1,v73)],[1,3],[]),
([v218,v6,v2,v8,v3,v4,v5],[],[],[]),
([v0,v85,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v50,v8,v3),(v85,v50,v6)],[3],[]),
([0xababaaaaababaaaa,v6,v2,v8,v3,v4,v5],[],[],[]),
([v0,v131,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v35,v8,v4),(v131,v35,v6)],[3],[]),
([v0,v6,v40,v8,v3,v4,v5],[],[],[]),
([v0,v6,v2,0xfc00ff00fc00ff00,v8,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v35,v8,v4),(0xfc00ff00fc00ff00,v35,v3)],[3],[]),
([v0,v6,v2,v8,0xfcfcffff00000000,v3,v4],[(v6,v1,v0),(v8,v1,v2),(v35,v8,v4),(0xfcfcffff00000000,v35,v5)],[3],[]),
([v6,v2,v7,v3,v82,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v20,v4,v3),(v82,v1,v20)],[1],[]),
([v0,v6,v8,v3,v64,v4,v5],[],[],[]),
([v0,v6,v2,v3,v147,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v20,v3,v4),(v147,v8,v20)],[5],[]),
([v197,v1,v6,v2,v3,v4,v5],[],[],[]),
([v16,v0,v6,v2,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v112,v1,v7),(v16,v112,v7)],[0],[(0,0)]),
([v18,v46,v1,v8,v3,v4,v5],[],[],[(1,0)]),
([v18,v16,v0,v3,v4,v5],[],[],[]),
([v18,v16,v0,v6,v3,v4,v5],[],[],[]),
([v18,v16,v0,v1,v3,v4,v5],[],[],[]),
([v18,v16,v0,v7,v3,v4,v5],[],[],[]),
([v33,v1,v6,v172,v3,v4,v5],[],[],[]),
([0x1b0a1b0a1b0a1b0a,v1,v6,v2,v3,v4,v5],[],[],[]),
([v33,v122,v6,v2,v3,v4,v5],[],[],[(0,1)]),
([v100,v1,v6,v2,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v57,v25,v0),(v100,v57,v2)],[9],[]),
([v0,v1,v40,v9,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v40,v25,v2),(v9,v6,v2)],[4,5,6],[(0,2)]),
([v0,v1,0xe2e2e0e0e2e2e0e0,v2,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v40,v25,v2),(0xe2e2e0e0e2e2e0e0,v6,v40)],[0,3,4,5,10],[(1,3),(1,4)]),
([v25,v0,v1,v2,v24,v3,v4],[(v6,v1,v0),(v25,v1,v4),(v9,v6,v2),(v24,v9,v5)],[3,9],[(0,2)]),
([0x3f3f0e0e3f3f0e0e,v0,v1,v2,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v18,v6,v2),(0x3f3f0e0e3f3f0e0e,v18,v25)],[0,3,4,6,8,10],[(0,5)]),
([v16,v51,v2,v3,v4,v5],[],[],[]),
([v16,v51,v0,v2,v3,v4,v5],[],[],[]),
([v16,v51,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v51,v0,v9)],[0],[(0,6),(0,7),(0,8),(0,9),(1,7),(1,8)]),
([v18,v16,v0,v9,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v18,v2,v9)],[0],[(0,6),(0,11),(0,12),(0,13),(1,10)]),
([v16,v0,v2,v27,v9,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v27,v9,v3)],[0],[(0,7),(0,14),(0,15)]),
([v29,v51,v1,v2,v9,v3,v5],[(v6,v0,v1),(v9,v6,v2),(v51,v0,v9),(v29,v9,v4)],[0],[(0,8),(0,10)]),
([v16,v0,v2,v34,v9,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v34,v9,v4)],[0],[(0,11),(0,14),(1,7)]),
([v29,v16,v0,v2,v9,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v29,v9,v4)],[0],[(0,8),(0,12)]),
([v16,v0,v2,v24,v9,v3,v4],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v24,v9,v5)],[0],[(0,9),(0,13),(0,15)]),
([v16,v0,v1,v2,v27,v4,v5],[],[],[]),
([v16,v0,v1,v2,v34,v3,v5],[],[],[]),
([v29,v16,v0,v1,v2,v3,v5],[],[],[]),
([v16,v0,v1,v2,v24,v3,v4],[],[],[]),
([v18,v0,v1,v27,v4,v5],[],[],[]),
([v18,v0,v1,v27,v9,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v18,v2,v9),(v27,v9,v3)],[0],[(0,16),(0,17),(0,18),(1,11)]),
([v18,v0,v1,v27,v3,v4,v5],[],[],[]),
([v29,v18,v0,v1,v9,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v18,v2,v9),(v29,v9,v4)],[0],[(0,10),(0,12),(0,17),(0,20),(1,19)]),
([v104,v18,v0,v1,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v18,v2,v9),(v104,v9,v3)],[10],[(0,19),(0,22),(1,21),(1,23),(1,24)]),
([v18,v0,v1,v24,v3,v4],[],[],[]),
([v18,v0,v1,v24,v9,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v18,v2,v9),(v24,v9,v5)],[0],[(0,13),(0,18),(0,20),(1,13),(1,18),(1,20)]),
([v0,v1,v2,v27,v34,v5],[],[],[]),
([v0,v1,v2,v27,v34,v9,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3),(v34,v9,v4)],[0,1,2],[(0,14),(0,16),(0,25),(1,14)]),
([v0,v1,v2,v27,v34,v3,v5],[],[],[]),
([v29,v0,v1,v2,v27,v5],[],[],[]),
([v29,v0,v1,v2,v27,v9,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3),(v29,v9,v4)],[0,2],[(0,17),(0,26),(0,27)]),
([v104,v0,v1,v2,v34,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v34,v9,v4),(v104,v9,v3)],[0],[(0,26),(0,28),(0,29),(1,30)]),
([v0,v1,v2,v27,v24,v4],[],[],[]),
([v0,v1,v2,v27,v24,v9,v4],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3),(v24,v9,v5)],[0,2],[(0,15),(0,18),(0,25),(0,27)]),
([v29,v0,v1,v2,v27,v3,v5],[],[],[]),
([v0,v1,v2,v27,v24,v3,v4],[],[],[]),
([v0,v1,v2,v27,v9,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v142,v9,v3),(v27,v142,v9)],[0],[(0,19),(0,26),(0,31),(0,32)]),
([v29,v142,v0,v1,v2,v5],[],[],[]),
([v29,v142,v0,v1,v2,v9,v5],[(v6,v1,v0),(v9,v6,v2),(v29,v9,v4),(v142,v9,v3)],[0],[(0,31),(0,33),(1,31)]),
([v29,v104,v0,v1,v2,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v29,v9,v4),(v104,v9,v3)],[0],[(0,31),(0,34),(0,35)]),
([v29,v0,v1,v2,v24,v3],[],[],[]),
([v29,v0,v1,v2,v24,v9,v3],[(v6,v1,v0),(v9,v6,v2),(v29,v9,v4),(v24,v9,v5)],[0],[(0,20),(0,27),(0,33),(1,32)]),
([v0,0xcdcdcccccdcdcccc,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v181,v9,v4),(0xcdcdcccccdcdcccc,v181,v1)],[0,6],[(0,21)]),
([v0,0xcdcccdcccdcccdcc,v2,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v104,v9,v3),(0xcdcccdcccdcccdcc,v104,v1)],[0,4],[(0,22)]),
([v0,v1,v169,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v104,v9,v3),(v169,v104,v2)],[0,4],[(0,28),(0,36)]),
([v0,v1,v2,v210,v9,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v181,v9,v4),(v210,v181,v3)],[0,1,4,6,10],[(0,23),(0,37)]),
([v0,v1,v2,v9,v211,v3,v4],[(v6,v1,v0),(v9,v6,v2),(v181,v9,v4),(v211,v181,v5)],[0,1,6],[(0,24),(0,30),(1,35)]),
([v104,v0,v1,v2,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v104,v9,v3),(v24,v9,v5)],[1],[(0,32),(0,36),(0,38),(1,37)]),
([0x3232323200000000,v0,v1,v2,v24,v3,v4],[],[],[]),
([v0,v1,v2,0xfe00fe0000000000,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5),(0xfe00fe0000000000,v24,v3)],[2,3],[(0,39)]),
([0x1000100ff00ff00,v0,v1,v2,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5),(0x1000100ff00ff00,v24,v3)],[2],[]),
([v0,v1,v2,v24,v20,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5),(v20,v3,v4)],[3],[(0,40)]),
([v0,v1,v9,v3,v64,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v20,v3,v4),(v64,v2,v20)],[4,6],[(0,40)]),
([v0,v1,v2,v3,0xfffefefefffefefe,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v20,v3,v4),(0xfffefefefffefefe,v9,v20)],[0,8,10],[(0,41),(0,42)]),
([0xfefefe00fefefe,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v20,v3,v4),(0xfefefe00fefefe,v9,v20)],[8,10],[]),
([v16,v51,v6,v2,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v51,v0,v9)],[3],[(0,6)]),
([v16,v0,v6,v2,v27,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v27,v9,v3)],[0],[]),
([v29,v51,v1,v6,v2,v3,v5],[(v6,v0,v1),(v9,v6,v2),(v51,v0,v9),(v29,v9,v4)],[0],[(0,10)]),
([v16,v0,v6,v2,v34,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v34,v9,v4)],[0],[(0,11)]),
([v29,v16,v0,v6,v2,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v29,v9,v4)],[0],[(0,12)]),
([v16,v0,v6,v2,v24,v3,v4],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9),(v24,v9,v5)],[0],[(0,13)]),
([v18,v0,v1,v6,v27,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v18,v6,v2),(v27,v9,v3)],[3],[]),
([v18,v0,v1,v6,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v18,v6,v2),(v24,v9,v5)],[3],[]),
([0x1010fefe1010fefe,v0,v1,v2,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v161,v6,v4),(0x1010fefe1010fefe,v161,v9)],[3],[]),
([v0,v1,v72,v2,v34,v3,v5],[(v6,v0,v1),(v9,v6,v2),(v72,v6,v3),(v34,v9,v4)],[2,9],[]),
([v0,v1,v72,v2,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v72,v6,v3),(v24,v9,v5)],[2,9],[]),
([v67,v0,v1,v2,v34,v3,v5],[(v6,v0,v1),(v9,v6,v2),(v67,v6,v3),(v34,v9,v4)],[3],[(0,28)]),
([v67,v0,v1,v2,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v67,v6,v3),(v24,v9,v5)],[3],[(0,36)]),
([v0,v1,v6,v2,v27,v34,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3),(v34,v9,v4)],[3],[(0,16)]),
([v29,v0,v1,v6,v2,v27,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3),(v29,v9,v4)],[3],[(0,17)]),
([v0,v1,v6,v2,v27,v24,v4],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3),(v24,v9,v5)],[3],[(0,18)]),
([v29,v142,v0,v1,v6,v2,v5],[],[],[]),
([v29,v0,v1,v6,v2,v24,v3],[(v6,v1,v0),(v9,v6,v2),(v29,v9,v4),(v24,v9,v5)],[3],[(0,20)]),
([v18,v0,v1,v172,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v219,v18,v3),(v172,v219,v2)],[0,3],[]),
([v18,v0,v65,v3,v4,v5],[],[],[]),
([v18,v0,v47,v1,v3,v4,v5],[],[],[]),
([v0,v1,v2,v3,0xff0e0e0eff0e0e0e,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v20,v3,v4),(0xff0e0e0eff0e0e0e,v18,v20)],[0,4,6,8,10],[(0,43)]),
([0xe0e0e000e0e0e,v0,v1,v2,v3,v4,v5],[],[],[]),
([0x1f0e1f0e1f0e1f0e,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v67,v6,v3),(0x1f0e1f0e1f0e1f0e,v18,v67)],[0,3,4,6,8,10],[(0,44)]),
([v18,v0,v65,v6,v3,v4,v5],[],[],[]),
([v18,v0,v1,v85,v3,v4,v5],[],[],[(0,45)]),
([v0,v1,v2,v3,0xff11ee00ff11ee00,v4,v5],[(v6,v0,v1),(v72,v6,v3),(v220,v6,v4),(0xff11ee00ff11ee00,v220,v72)],[8],[]),
([v108,v47,v6,v2,v3,v4,v5],[],[],[]),
([v108,v0,v6,v2,v3,v4,v5],[(v6,v0,v1),(v14,v2,v3),(v47,v14,v0),(v108,v47,v1)],[0],[]),
([v123,v0,v1,v2,v3,v4,v5],[],[],[]),
([v123,v0,v131,v2,v3,v4,v5],[(v6,v1,v0),(v30,v2,v4),(v131,v30,v6),(v123,v1,v131)],[0],[(1,46)]),
([v108,v0,v85,v2,v3,v4,v5],[(v6,v0,v1),(v14,v2,v3),(v85,v14,v6),(v108,v1,v85)],[0],[(0,46)]),
([v123,v0,v6,v2,v3,v4,v5],[(v6,v1,v0),(v30,v2,v4),(v131,v30,v6),(v123,v1,v131)],[0],[]),
([v116,v6,v2,v3,v58,v4,v5],[],[],[]),
([v89,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v58,v0,v20),(v89,v2,v58)],[2],[]),
([v116,v0,v2,v3,v59,v4,v5],[(v6,v1,v0),(v20,v4,v3),(v59,v6,v20),(v116,v1,v59)],[0],[(0,47)]),
([v0,v1,0xf0e0e0e0f0e0e0e0,v3,v59,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20),(0xf0e0e0e0f0e0e0e0,v2,v59)],[0,1,2,4,6],[(0,41),(0,48)]),
([v155,v0,v1,v3,v4,v5],[],[],[]),
([v155,v0,v1,v2,v3,v4,v5],[],[],[]),
([v155,v0,v1,v3,v59,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20),(v155,v2,v59)],[0,3,4,6],[(0,49)]),
([v0,v1,v2,v3,v143,v4],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20),(v143,v59,v5)],[1,2,4,6],[]),
([v0,v1,v2,v3,v143,v59,v4],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20),(v143,v59,v5)],[0,1,2,4,6],[(0,48),(0,49)]),
([v116,v0,v6,v2,v3,v4,v5],[(v6,v1,v0),(v20,v4,v3),(v59,v6,v20),(v116,v1,v59)],[0],[]),
([v155,v0,v1,v6,v3,v4,v5],[],[],[]),
([v0,v1,v6,v2,v3,v143,v4],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20),(v143,v59,v5)],[1,2,4,6],[]),
([v0,v1,v2,0xf0fefefef0fefefe,v3,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v182,v6,v20),(0xf0fefefef0fefefe,v182,v2)],[0,8,10],[(0,50)]),
([v0,v1,0xeee0e0e0eee0e0e0,v2,v3,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v64,v2,v20),(0xeee0e0e0eee0e0e0,v6,v64)],[0,3,4,5,9],[(0,52),(1,51)]),
([0x1110101011101010,v0,v1,v2,v3,v4,v5],[],[],[]),
([v18,v0,v6,v8,v3,v4,v5],[],[],[]),
([v16,v0,v2,v9,v3,v4,v5],[(v60,v1,v0),(v6,v60,v0),(v9,v6,v2),(v16,v1,v9)],[0,3],[(0,0)]),
([v18,v0,v1,v9,v3,v4,v5],[(v31,v0,v1),(v6,v31,v1),(v9,v6,v2),(v18,v2,v9)],[0,3],[(0,19),(0,53),(1,0),(1,19)]),
([v0,v1,v2,v24,v3,v4],[],[],[]),
([v0,v1,v2,v24,v9,v3,v4],[(v31,v0,v1),(v6,v31,v1),(v9,v6,v2),(v24,v9,v5)],[0,1,2],[(0,32),(0,53),(1,32)]),
([v0,v1,v6,v2,v27,v4,v5],[(v31,v0,v1),(v6,v31,v1),(v9,v6,v2),(v27,v9,v3)],[3],[(0,19)]),
([v0,v1,v6,v2,v24,v3,v4],[(v31,v0,v1),(v6,v31,v1),(v9,v6,v2),(v24,v9,v5)],[3],[(0,53)]),
([v16,v0,v148,v7,v3,v4,v5],[(v60,v1,v0),(v148,v60,v2),(v7,v0,v2),(v16,v1,v7)],[3],[]),
([v16,v0,v2,v148,v3,v4,v5],[(v60,v1,v0),(v148,v60,v2),(v9,v0,v148),(v16,v1,v9)],[3],[]),
([v18,v0,v1,v74,v3,v4,v5],[(v31,v0,v1),(v74,v31,v2),(v9,v1,v74),(v18,v2,v9)],[0,3],[]),
([v0,v1,v2,v74,v27,v4,v5],[],[],[]),
([v0,v1,v2,v74,v34,v3,v5],[],[],[]),
([v0,v1,v2,v74,v24,v3,v4],[],[],[]),
([v0,v65,v2,v148,v3,v4,v5],[],[],[]),
([v0,v1,v74,v221,v3,v4,v5],[(v31,v0,v1),(v74,v31,v2),(0xd000d000d000d00,v74,v3),(v221,0xd000d000d000d00,v2)],[0,4],[]),
([v0,v1,v2,v74,0xf2ff0000f2ff0000,v3,v5],[],[],[]),
([v0,v1,v2,v74,0xf2fff2ff00000000,v3,v4],[],[],[]),
([v0,v190,v2,v9,v3,v4,v5],[(v60,v1,v0),(v8,v1,v2),(v190,v60,v8),(v9,v0,v8)],[5],[(0,54)]),
([v18,v31,v1,v7,v3,v4,v5],[],[],[(1,54)]),
([v31,v1,v2,v7,v27,v4,v5],[],[],[]),
([v31,v1,v2,v7,v34,v3,v5],[],[],[]),
([v31,v1,v2,v7,v24,v3,v4],[],[],[]),
([0x2722272227222722,v1,v2,v7,v3,v4,v5],[],[],[]),
([v31,v1,v103,v7,v3,v4,v5],[],[],[]),
([v31,v1,v2,v7,v156,v3,v5],[],[],[]),
([v31,v1,v2,v7,v136,v3,v4],[],[],[]),
([v18,v0,v1,v7,v3,v4,v5],[(v60,v1,v0),(v7,v0,v2),(v9,v60,v7),(v18,v2,v9)],[0,3],[(0,0)]),
([v0,v1,v2,v7,v24,v3,v4],[(v60,v1,v0),(v7,v0,v2),(v9,v60,v7),(v24,v9,v5)],[3],[]),
([v16,0x7676767676767676,v0,v2,v3,v4,v5],[(v60,v1,v0),(v7,v0,v2),(v16,v1,v7),(0x7676767676767676,v60,v16)],[3],[]),
([0x8b8b88888b8b8888,v0,v65,v2,v3,v4,v5],[],[],[]),
([v94,v0,v1,v54,v7,v4,v5],[(v7,v0,v2),(v75,v0,v3),(v94,v2,v75),(v54,v7,v3)],[3,10],[]),
([v0,0xb8b8a8a8b8b8a8a8,v1,v2,v3,v4,v5],[],[],[]),
([v16,v0,v1,v103,v3,v4,v5],[],[],[]),
([v86,v0,v1,v40,v8,v3,v5],[(v8,v1,v2),(v25,v1,v4),(v40,v25,v2),(v86,v8,v4)],[3,6],[]),
([v109,v0,v2,v3,v4,v5],[(v7,v0,v2),(v112,v1,v7),(v9,v1,v7),(v109,v112,v9)],[9],[(1,55)]),
([v109,v0,v2,v9,v3,v4,v5],[(v7,v0,v2),(v112,v1,v7),(v9,v1,v7),(v109,v112,v9)],[0,2],[(0,57),(0,58),(0,59),(0,60),(0,61),(1,56)]),
([v16,v46,v1,v2,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v9,v0,v8),(v16,v1,v9)],[5,9],[]),
([v16,v46,v2,v9,v3,v4,v5],[],[],[(0,56),(0,62)]),
([v18,v46,v1,v9,v3,v4,v5],[],[],[(0,62),(0,63),(0,64),(0,65),(1,57)]),
([v46,v1,v2,v27,v9,v4,v5],[],[],[(0,63),(0,66),(1,59)]),
([v29,v0,v112,v2,v9,v3,v5],[],[],[(0,60)]),
([v46,v1,v2,v34,v9,v3,v5],[],[],[(0,64),(0,66),(0,67),(1,58)]),
([v46,v1,v2,v24,v9,v3,v4],[],[],[(0,65),(0,67),(1,61)]),
([v109,v0,v2,v7,v3,v4,v5],[(v7,v0,v2),(v112,v1,v7),(v9,v1,v7),(v109,v112,v9)],[3],[]),
([v16,v46,v2,v8,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v9,v0,v8),(v16,v1,v9)],[9],[(0,68)]),
([v46,v1,v2,0xfeaafeaafeaafeaa,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v70,v8,v3),(0xfeaafeaafeaafeaa,v0,v70)],[2,3],[]),
([v0,0xaba8aba8aba8aba8,v1,v2,v3,v4,v5],[],[],[]),
([v16,v0,v74,v8,v3,v4,v5],[],[],[]),
([v16,v51,v2,v7,v3,v4,v5],[],[],[]),
([v18,v16,v0,v8,v3,v4,v5],[],[],[(0,6),(0,62)]),
([v16,v0,v2,v8,v27,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9),(v27,v9,v3)],[0],[(0,7)]),
([v29,v51,v1,v2,v7,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v51,v0,v9),(v29,v9,v4)],[0,3],[(0,8)]),
([v16,v0,v2,v8,v34,v3,v5],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9),(v34,v9,v4)],[0],[(1,7)]),
([v29,v16,v0,v2,v8,v3,v5],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9),(v29,v9,v4)],[0],[(0,8)]),
([v16,v0,v2,v8,v24,v3,v4],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9),(v24,v9,v5)],[0],[(0,9)]),
([v18,v0,v1,v7,v27,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v18,v2,v9),(v27,v9,v3)],[0,3],[(1,64)]),
([v29,v18,v0,v1,v8,v3,v5],[(v8,v1,v2),(v9,v0,v8),(v18,v2,v9),(v29,v9,v4)],[0],[(0,10)]),
([v18,v0,v1,v7,v34,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v18,v2,v9),(v34,v9,v4)],[0,3],[(0,11),(1,63)]),
([v29,v18,v0,v1,v7,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v18,v2,v9),(v29,v9,v4)],[0,3],[(0,12)]),
([v18,v0,v1,v7,v24,v3,v4],[(v7,v0,v2),(v9,v1,v7),(v18,v2,v9),(v24,v9,v5)],[0,3],[(0,13),(1,65)]),
([v18,v0,v1,v54,v3,v4,v5],[],[],[]),
([v0,v1,v2,v54,v34,v3,v5],[],[],[]),
([v0,v1,v2,v54,v24,v3,v4],[],[],[]),
([v0,v65,v2,v9,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v35,v8,v4),(v65,v35,v1)],[5,6],[(0,69)]),
([v0,v1,v2,v156,v9,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v105,v7,v3),(v156,v105,v4)],[0,4,6,10],[(0,70),(0,72),(1,71)]),
([v0,v1,v2,v136,v9,v3,v4],[(v7,v0,v2),(v9,v1,v7),(v105,v7,v3),(v136,v105,v5)],[1,2,4,10,11],[(0,73),(0,74)]),
([v35,v18,v0,v1,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v35,v8,v4),(v18,v2,v9)],[8],[(0,69),(1,22),(1,70),(1,73)]),
([v35,v0,v1,v2,v27,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v35,v8,v4),(v27,v9,v3)],[0,4],[(0,75),(1,74),(1,76)]),
([v35,v0,v1,v2,v24,v3,v4],[(v8,v1,v2),(v9,v0,v8),(v35,v8,v4),(v24,v9,v5)],[1,2],[(0,2),(1,72),(1,77)]),
([v18,v0,v1,v73,v3,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v73,v7,v4),(v18,v2,v9)],[8],[]),
([0x2fe02fe02fe02fe,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v70,v8,v3),(0x2fe02fe02fe02fe,v70,v9)],[10],[]),
([v0,v1,v2,v73,v27,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v73,v7,v4),(v27,v9,v3)],[1,5],[]),
([v29,v0,v1,v2,v70,v3,v5],[(v8,v1,v2),(v9,v0,v8),(v70,v8,v3),(v29,v9,v4)],[9],[]),
([v0,v1,v2,v73,v24,v3,v4],[(v7,v0,v2),(v9,v1,v7),(v73,v7,v4),(v24,v9,v5)],[1,5],[]),
([v50,v18,v0,v1,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v50,v8,v3),(v18,v2,v9)],[10],[(1,21)]),
([v50,v0,v1,v2,v34,v3,v5],[],[],[]),
([v29,v50,v0,v1,v2,v3,v5],[],[],[]),
([v50,v0,v1,v2,v24,v3,v4],[],[],[]),
([v0,v1,v2,v7,v27,v34,v5],[(v7,v0,v2),(v9,v1,v7),(v27,v9,v3),(v34,v9,v4)],[3],[(0,14),(1,66)]),
([v29,v0,v1,v2,v7,v27,v5],[(v7,v0,v2),(v9,v1,v7),(v27,v9,v3),(v29,v9,v4)],[3],[]),
([v0,v1,v2,v7,v27,v24,v4],[(v7,v0,v2),(v9,v1,v7),(v27,v9,v3),(v24,v9,v5)],[3],[(0,15),(1,67)]),
([v29,v0,v1,v2,v8,v27,v5],[],[],[]),
([v29,v142,v0,v1,v2,v7,v5],[(v7,v0,v2),(v9,v1,v7),(v142,v9,v3),(v29,v9,v4)],[3],[]),
([v29,v0,v1,v2,v8,v24,v3],[],[],[]),
([v0,v1,v2,v7,v34,v24,v3],[(v7,v0,v2),(v9,v1,v7),(v34,v9,v4),(v24,v9,v5)],[3],[]),
([v29,v0,v1,v2,v7,v24,v3],[(v7,v0,v2),(v9,v1,v7),(v29,v9,v4),(v24,v9,v5)],[3],[]),
([v16,v92,v2,v7,v3,v4,v5],[(v7,v0,v2),(v162,v1,v7),(v92,v162,v0),(v16,v1,v7)],[5],[]),
([v18,v0,v149,v8,v3,v4,v5],[],[],[]),
([v16,v0,v92,v2,v3,v4,v5],[(v7,v0,v2),(v162,v1,v7),(v92,v162,v0),(v16,v1,v7)],[5],[]),
([v16,v109,v0,v2,v3,v4,v5],[(v7,v0,v2),(v162,v1,v7),(v16,v1,v7),(v109,v162,v16)],[3],[]),
([v0,v1,v2,0xfe02fe02fe02fe02,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8),(v70,v8,v3),(0xfe02fe02fe02fe02,v95,v70)],[5],[]),
([v95,v218,v1,v2,v3,v4,v5],[],[],[]),
([v16,v0,v2,v183,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v222,v16,v3),(v183,v222,v1)],[0,4],[]),
([v16,v1,0xefaaefaaefaaefaa,v2,v3,v4,v5],[],[],[]),
([v16,v0,v1,v221,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v223,v16,v3),(v221,v223,v2)],[4],[]),
([v16,0x32ff000032ff0000,v0,v1,v2,v3,v5],[],[],[]),
([v16,0x32ff32ff00000000,v0,v1,v2,v3,v4],[],[],[]),
([v16,v0,v2,v180,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v224,v16,v4),(v180,v224,v1)],[0,6],[]),
([v16,v0,v1,v40,v3,v4,v5],[],[],[]),
([v0,v1,v2,v3,0xff323232ff323232,v4,v5],[],[],[]),
([0x32323200323232,v0,v1,v2,v3,v4,v5],[],[],[]),
([v16,v0,v1,v3,v64,v4,v5],[],[],[]),
([v16,v47,v1,v2,v3,v4,v5],[],[],[]),
([v16,v0,v1,v2,v156,v3,v5],[],[],[]),
([v16,v0,v1,v2,v136,v3,v4],[],[],[]),
([0x3737323237373232,v0,v1,v2,v3,v4,v5],[],[],[]),
([v80,v1,v32,v7,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v32,v12,v0),(v80,v32,v2)],[0,3],[]),
([v80,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v32,v12,v0),(v80,v32,v2)],[0,3],[]),
([v124,v1,v7,v21,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v21,v12,v2),(v124,v0,v21)],[3,5],[(1,78)]),
([v69,v0,v19,v8,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4),(v19,v11,v2),(v69,v1,v19)],[0,9],[]),
([v69,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4),(v66,v11,v8),(v69,v1,v66)],[5,9],[]),
([v69,v0,v2,v66,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4),(v66,v11,v8),(v69,v1,v66)],[0],[(1,79)]),
([v80,v0,v1,v56,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v56,v12,v7),(v80,v2,v56)],[0,3],[(0,79)]),
([v69,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4),(v66,v11,v8),(v69,v1,v66)],[0,9],[]),
([v49,v0,v2,v7,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v10,v1,v3),(v49,v12,v10)],[0,1,2,3,5,6,8],[]),
([v0,v1,v144,v8,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v44,v1,v13),(v144,v44,v2)],[0],[]),
([v79,v0,v170,v2,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v79,v8,v13),(v170,v79,v1)],[0],[(0,80)]),
([v0,v129,v1,v2,v3,v4,v5],[(v7,v0,v2),(v10,v1,v3),(v225,v7,v10),(v129,v225,v0)],[5],[]),
([v79,v0,v1,v144,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v79,v8,v13),(v144,v79,v2)],[0],[(0,80)]),
([v0,v170,v2,v8,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v79,v8,v13),(v170,v79,v1)],[0,9],[]),
([v0,v1,v7,v3,v15,v145,v4],[(v7,v0,v2),(v10,v1,v3),(v15,v10,v5),(v145,v2,v15)],[5],[(0,81)]),
([v0,v1,v2,0xfac8fac800000000,v3,v15,v4],[(v7,v0,v2),(v10,v1,v3),(v15,v10,v5),(0xfac8fac800000000,v7,v15)],[4,5,9],[(0,81)]),
([v0,v1,v2,v3,v15,0xfffefffefafafafa,v4],[(v7,v0,v2),(v10,v1,v3),(v15,v10,v5),(0xfffefffefafafafa,v7,v15)],[6,8],[]),
([0x5454fcfcfcfc,v0,v1,v2,v3,v4,v23],[],[],[]),
([0x303020200000000,v0,v1,v2,v3,v4,v23],[],[],[]),
([v81,v42,v1,v7,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v42,v26,v0),(v81,v42,v2)],[3],[]),
([v0,v96,v2,v97,v8,v3,v5],[(v8,v1,v2),(v17,v0,v4),(v96,v17,v1),(v97,v8,v4)],[8],[]),
([v81,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v42,v26,v0),(v81,v42,v2)],[0,3,4],[]),
([v132,v0,v1,v2,v3,v4,v5],[],[],[]),
([v132,v0,v2,v150,v3,v4,v5],[(v8,v1,v2),(v17,v0,v4),(v150,v17,v8),(v132,v1,v150)],[0],[(1,82)]),
([v81,v0,v1,v48,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7),(v81,v2,v48)],[0],[(0,82),(0,83),(0,84),(0,85)]),
([v0,v1,v2,v54,v48,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7),(v54,v48,v3)],[10],[(0,83)]),
([v0,v1,v2,v175,v48,v3,v5],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7),(v175,v48,v4)],[0,8,10],[(0,84),(0,86)]),
([0xfafe0000fafe,v0,v1,v2,v48,v3,v5],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7),(0xfafe0000fafe,v48,v4)],[0,6,10],[(0,87)]),
([v0,v1,v2,v127,v3,v4],[],[],[]),
([v0,v1,v2,v127,v48,v3,v4],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7),(v127,v48,v5)],[0,10],[(0,85),(0,86),(0,87)]),
([v132,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v17,v0,v4),(v150,v17,v8),(v132,v1,v150)],[0],[]),
([v0,v1,v2,v7,v127,v3,v4],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7),(v127,v48,v5)],[3],[]),
([v117,v0,v87,v8,v3,v4,v5],[],[],[]),
([v118,v0,v88,v8,v3,v4,v5],[],[],[]),
([v118,v0,v2,v71,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v71,v38,v8),(v118,v1,v71)],[0],[(0,88)]),
([v117,v0,v1,v71,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v71,v38,v8),(v117,v2,v71)],[0],[(0,88)]),
([v0,v1,v2,v198,v3,v4],[],[],[]),
([v0,v1,v2,v198,v71,v3,v4],[(v8,v1,v2),(v38,v0,v3),(v71,v38,v8),(v198,v71,v5)],[0,2,4],[]),
([v118,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v71,v38,v8),(v118,v1,v71)],[0],[]),
([v117,v0,v1,v8,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v71,v38,v8),(v117,v2,v71)],[0],[]),
([v0,v1,v2,v7,0xfefefafa00000000,v3,v4],[(v7,v0,v2),(v90,v1,v4),(v226,v90,v7),(0xfefefafa00000000,v226,v5)],[1,3,6],[]),
([v133,v0,v103,v8,v3,v4,v5],[],[],[]),
([v133,v0,v2,v146,v3,v4,v5],[(v8,v1,v2),(v41,v0,v3),(v146,v41,v8),(v133,v1,v146)],[0],[(1,89)]),
([v100,v0,v1,v98,v3,v4,v5],[(v7,v0,v2),(v25,v1,v4),(v98,v25,v7),(v100,v2,v98)],[0],[(0,89)]),
([v133,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v41,v0,v3),(v146,v41,v8),(v133,v1,v146)],[0],[]),
([v100,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v25,v1,v4),(v98,v25,v7),(v100,v2,v98)],[0,3],[]),
([v0,v1,v2,v7,0xfeccfecc00000000,v3,v4],[(v7,v0,v2),(v54,v7,v3),(v183,v1,v54),(0xfeccfecc00000000,v183,v5)],[3],[]),
([v77,v0,v1,v2,v97,v3,v5],[(v8,v1,v2),(v97,v8,v4),(v91,v8,v4),(v77,v1,v91)],[9],[]),
([v227,v0,v1,v2,v3,v5],[(v8,v1,v2),(v97,v8,v4),(v91,v8,v4),(v227,v97,v91)],[1,2,3,9],[]),
([v77,v0,v2,v97,v8,v3,v5],[(v8,v1,v2),(v97,v8,v4),(v91,v8,v4),(v77,v1,v91)],[8,9],[]),
([v227,v0,v1,v2,v8,v3,v5],[(v8,v1,v2),(v97,v8,v4),(v91,v8,v4),(v227,v97,v91)],[3,9],[]),
([v0,v1,v2,v3,0xff05fa00ff05fa00,v4,v5],[],[],[]),
([v77,v0,v40,v8,v3,v4,v5],[],[],[]),
([0x3ff00fc03ff00fc,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v91,v8,v4),(v70,v8,v3),(0x3ff00fc03ff00fc,v70,v91)],[8],[]),
([0x300fffc0300fffc,v0,v1,v2,v3,v4,v5],[],[],[]),
([v86,v0,v1,v65,v2,v3,v5],[(v8,v1,v2),(v86,v8,v4),(v35,v8,v4),(v65,v35,v1)],[9],[]),
([v86,v0,v65,v2,v8,v3,v5],[(v8,v1,v2),(v86,v8,v4),(v35,v8,v4),(v65,v35,v1)],[6,9],[]),
([v108,v1,v2,v7,v3,v4,v5],[],[],[]),
([v94,v47,v1,v7,v3,v4,v5],[(v7,v0,v2),(v105,v7,v3),(v47,v105,v0),(v94,v47,v2)],[3],[]),
([v0,v1,v2,v73,v136,v3,v4],[(v7,v0,v2),(v105,v7,v3),(v136,v105,v5),(v73,v7,v4)],[1,5],[]),
([v50,v0,v1,v2,0xfcfcffff00000000,v3,v4],[],[],[]),
([v0,v1,v40,v70,v3,v4,v5],[],[],[]),
([v0,v1,v2,v3,0xff03fc00ff03fc00,v4,v5],[(v8,v1,v2),(v35,v8,v4),(v70,v8,v3),(0xff03fc00ff03fc00,v35,v70)],[10],[]),
([v50,v0,v1,v40,v3,v4,v5],[(v8,v1,v2),(v35,v8,v4),(v50,v8,v3),(v40,v35,v2)],[6,10],[]),
([v123,v1,v2,v7,v3,v4,v5],[],[],[]),
([v0,v1,v2,0xfac8c8c8fac8c8c8,v3,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v82,v1,v20),(0xfac8c8c8fac8c8c8,v7,v82)],[1],[]),
([0x302020203020202,v0,v1,v2,v3,v4,v5],[],[],[]),
([v134,v0,v8,v3,v64,v4,v5],[],[],[]),
([v134,v0,v2,v3,v147,v4,v5],[(v8,v1,v2),(v20,v4,v3),(v147,v8,v20),(v134,v1,v147)],[0],[(1,90)]),
([0x3332323233323232,v0,v1,v2,v3,v4,v5],[],[],[]),
([v89,v0,v1,v3,v99,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v99,v7,v20),(v89,v2,v99)],[0],[(0,90)]),
([v134,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v20,v4,v3),(v147,v8,v20),(v134,v1,v147)],[0],[]),
([v89,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v99,v7,v20),(v89,v2,v99)],[0,3],[]),
([v0,0xaafefefeaafefefe,v1,v2,v3,v4,v5],[(v8,v1,v2),(v20,v4,v3),(0xfcfcfc00fcfcfc,v8,v20),(0xaafefefeaafefefe,0xfcfcfc00fcfcfc,v0)],[8,10],[]),
([v135,v0,v106,v8,v3,v4,v5],[],[],[]),
([v135,v0,v2,v151,v3,v4,v5],[(v8,v1,v2),(v68,v4,v3),(v151,v68,v8),(v135,v1,v151)],[0],[(1,91)]),
([v128,v0,v1,v83,v3,v4,v5],[(v7,v0,v2),(v52,v3,v4),(v83,v52,v7),(v128,v2,v83)],[0],[(0,91)]),
([v0,v1,v2,v184,v3,v4],[],[],[]),
([v0,v1,v2,v184,v83,v3,v4],[(v7,v0,v2),(v52,v3,v4),(v83,v52,v7),(v184,v83,v5)],[0,1,6],[]),
([v135,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v68,v4,v3),(v151,v68,v8),(v135,v1,v151)],[0],[]),
([v128,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v52,v3,v4),(v83,v52,v7),(v128,v2,v83)],[0,3],[]),
([v0,v1,v2,v7,v184,v3,v4],[(v7,v0,v2),(v52,v3,v4),(v83,v52,v7),(v184,v83,v5)],[1,3,6],[]),
([v0,v92,v1,0xfefef0f0fefef0f0,v3,v4,v5],[(v76,v1,v2),(v92,v76,v0),(v228,v92,v4),(0xfefef0f0fefef0f0,v228,v2)],[6],[]),
([v0,v149,v2,0xfdccfdccfdccfdcc,v3,v4,v5],[(v33,v0,v2),(v149,v33,v1),(v229,v149,v3),(0xfdccfdccfdccfdcc,v229,v1)],[0,4],[(1,92)]),
([v0,v176,v1,v66,v3,v4,v5],[(v76,v1,v2),(v11,v0,v4),(v176,v76,v11),(v66,v176,v2)],[3],[(0,93)]),
([v0,0xe2e2c0c0e2e2c0c0,v22,v2,v3,v4,v5],[(v76,v1,v2),(v11,v0,v4),(v22,v1,v11),(0xe2e2c0c0e2e2c0c0,v76,v22)],[0,3,4,5,6,10],[(1,94)]),
([v33,v1,v32,v56,v3,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v32,v0,v12),(v56,v32,v2)],[3,9],[(1,95)]),
([v0,v1,v19,v66,v3,v4,v5],[(v76,v1,v2),(v11,v0,v4),(v19,v11,v2),(v66,v76,v19)],[6,8],[]),
([v33,v126,v1,v3,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v21,v12,v2),(v126,v0,v21)],[5],[(1,96),(1,97)]),
([v33,v126,v1,v21,v3,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v21,v12,v2),(v126,v0,v21)],[5],[(1,98)]),
([v33,v49,v0,v2,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v10,v1,v3),(v49,v12,v10)],[0,2,3,5,6,8],[]),
([v33,v129,v1,v3,v4,v5],[(v33,v0,v2),(v10,v1,v3),(v28,v2,v10),(v129,v28,v0)],[5],[(0,99)]),
([v33,v28,v129,v1,v3,v4,v5],[],[],[]),
([v0,v1,v2,v3,v15,0xffceffce0a0a0a0a,v4],[(v33,v0,v2),(v10,v1,v3),(v15,v10,v5),(0xffceffce0a0a0a0a,v33,v15)],[6,8],[]),
([v0,v1,v2,0xf3f3a2a200000000,v3,v4,v23],[],[],[]),
([0xa0e4a0e4a0e4a0e4,v42,v1,v2,v3,v4,v5],[(v33,v0,v2),(v26,v1,v3),(v42,v26,v0),(0xa0e4a0e4a0e4a0e4,v33,v42)],[10],[]),
([v118,v0,v87,v2,v3,v4,v5],[(v38,v0,v3),(v87,v38,v1),(v71,v87,v2),(v118,v1,v71)],[0],[(0,88)]),
([v0,v1,v87,v2,v198,v3,v4],[],[],[]),
([v117,v0,v1,v88,v3,v4,v5],[(v38,v0,v3),(v88,v38,v2),(v71,v1,v88),(v117,v2,v71)],[0],[(0,88)]),
([v0,v1,v2,v88,v198,v3,v4],[],[],[]),
([v119,v0,v2,v214,v3,v5],[(v90,v1,v4),(v120,v1,v4),(v119,v90,v120),(v214,v119,v2)],[0,1,3,4,5,10],[(0,100)]),
([v213,v119,v0,v2,v3,v5],[(v90,v1,v4),(v120,v1,v4),(v119,v90,v120),(v213,v119,v2)],[0,1,3,4,5,10],[(0,100)]),
([v94,v0,v1,v3,v230,v4,v5],[(v75,v0,v3),(v94,v2,v75),(0xf0a00000f0a0000,v94,v4),(v230,0xf0a00000f0a0000,v2)],[0,6],[]),
([v94,v0,v1,v2,0xf0f5ffff00000000,v3,v4],[],[],[]),
([v133,v0,v122,v2,v3,v4,v5],[(v41,v0,v3),(v122,v41,v1),(v146,v122,v2),(v133,v1,v146)],[0,4],[(1,89)]),
([v0,v122,0xeeffcccceeffcccc,v2,v3,v4,v5],[(v41,v0,v3),(v122,v41,v1),(v231,v122,v4),(0xeeffcccceeffcccc,v231,v1)],[0,6],[]),
([v0,v57,v1,0xf4f0f5f0f4f0f5f0,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(0x4400550044005500,v57,v3),(0xf4f0f5f0f4f0f5f0,0x4400550044005500,v2)],[2,4],[]),
([v0,v57,0xbbffaaff00000000,v1,v2,v3,v4],[],[],[]),
([v0,0xbfbbafaabfbbafaa,v1,v2,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(v14,v2,v3),(0xbfbbafaabfbbafaa,v14,v57)],[3],[]),
([v0,0xb0bba0aab0bba0aa,v1,v2,v3,v4,v5],[],[],[]),
([v100,v0,v1,v40,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2),(v98,v0,v40),(v100,v2,v98)],[0],[(0,89)]),
([v0,v1,v2,0xf7f3f5f0f7f3f5f0,v3,v4,v5],[],[],[]),
([0xa2f3a0f0a2f3a0f0,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2),(v41,v0,v3),(0xa2f3a0f0a2f3a0f0,v41,v40)],[0,3,4,5],[(1,101)]),
([v0,v47,v1,v40,v3,v4,v5],[],[],[]),
([v0,v1,v40,0xfcf0fff0fcf0fff0,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2),(0xc000f000c000f00,v40,v3),(0xfcf0fff0fcf0fff0,0xc000f000c000f00,v2)],[0,3],[]),
([0x703050007030500,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v41,v0,v3),(v232,v25,v41),(0x703050007030500,v232,v2)],[0,8,10],[(0,102)]),
([0x1303110013031100,v0,v1,v2,v3,v4,v5],[(v41,v0,v3),(v30,v2,v4),(0x5f0f55005f0f5500,v30,v41),(0x1303110013031100,0x5f0f55005f0f5500,v1)],[10],[]),
([0x8acf88cc8acf88cc,v0,v1,v2,v3,v4,v5],[],[],[]),
([v80,v1,v32,v56,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v56,v32,v2),(v80,v32,v2)],[0,3],[]),
([v0,v22,v66,v3,v61,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v66,v22,v2),(v61,v2,v3)],[4],[]),
([v32,v22,v2,v3,v4,v5],[],[],[]),
([v0,v22,v167,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v110,v22,v3),(v167,v110,v2)],[0,4],[(0,103)]),
([v0,v22,v2,v167,v3,v4,v5],[],[],[]),
([0x1155ffff00000000,v1,v32,v2,v3,v4],[],[],[]),
([v0,v110,v2,v137,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v110,v22,v3),(v137,v22,v3)],[0,4,5,10],[(1,104)]),
([v0,v110,v22,v2,v137,v4,v5],[],[],[(0,103),(0,106),(1,105)]),
([v14,v0,v22,v2,v137,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v137,v22,v3),(v14,v2,v3)],[6],[(0,107)]),
([0xf0e0f0c0f0e0f0c,v0,v22,v2,v3,v4,v5],[],[],[]),
([v0,v22,v2,v3,v189,v4],[(v11,v0,v4),(v22,v11,v1),(v137,v22,v3),(v189,v137,v5)],[10],[(0,106),(0,107)]),
([v0,v22,v2,0xf0fef0fcf0fef0fc,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(0xee00cc00ee00cc,v22,v3),(0xf0fef0fcf0fef0fc,0xee00cc00ee00cc,v2)],[6,8],[]),
([v199,v233,v1,v2,v3,v5],[(v12,v1,v3),(v32,v12,v0),(v199,v32,v4),(v233,v32,v4)],[6,8],[(0,104)]),
([v199,v233,v1,v32,v2,v3,v5],[],[],[(0,105)]),
([v0,v22,v2,0xf1f0f3f0f1f0f3f0,v3,v4,v5],[],[],[]),
([v173,v0,v22,v2,v61,v4,v5],[],[],[]),
([v0,0xeee0ccc0eee0ccc0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v61,v2,v3),(0xeee0ccc0eee0ccc0,v22,v61)],[0,3,4,5,6,9,10],[(0,108)]),
([0x1110333011103330,v0,v22,v2,v3,v4,v5],[],[],[]),
([v0,v22,0xefeecfccefeecfcc,v2,v3,v4,v5],[],[],[]),
([v0,0xe0eec0cce0eec0cc,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v14,v2,v3),(0xe0eec0cce0eec0cc,v14,v22)],[3,4],[]),
([0x22ee00cc22ee00cc,v0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v12,v1,v3),(0x22ee00cc22ee00cc,v12,v22)],[4,5],[]),
([v0,v22,v21,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v12,v1,v3),(v21,v12,v2)],[0,2,4],[]),
([v0,v22,v2,v21,v3,v4,v5],[],[],[]),
([v62,v0,v22,v2,v3,v4],[],[],[]),
([v0,v110,v22,v2,v10,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v10,v1,v3),(v110,v22,v3)],[5],[(0,109),(0,111),(1,110)]),
([v14,v0,v22,v2,v10,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v10,v1,v3),(v14,v2,v3)],[6],[(0,112)]),
([v28,v0,v22,v2,v3,v4,v5],[],[],[]),
([v0,v22,v2,v3,v15,v4],[(v11,v0,v4),(v22,v11,v1),(v10,v1,v3),(v15,v10,v5)],[10],[(0,111),(0,112)]),
([v0,0xee22cc00ee22cc00,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v26,v1,v3),(0xee22cc00ee22cc00,v26,v22)],[0,3,5,6,9,10],[(0,113),(1,114)]),
([v0,v22,v2,v63,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v26,v1,v3),(v63,v26,v2)],[6,8],[]),
([v17,v233,v1,v32,v2,v3,v5],[],[],[(0,110)]),
([v69,v0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v66,v22,v2),(v69,v1,v66)],[0,5],[(1,79)]),
([v0,v1,v32,0xfefaf0f0fefaf0f0,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v215,v32,v4),(0xfefaf0f0fefaf0f0,v215,v2)],[1,6],[(1,109)]),
([0x1155ffff00000000,v0,v1,v32,v2,v3,v4],[],[],[]),
([v0,0xddccffccddccffcc,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v173,v22,v3),(0xddccffccddccffcc,v173,v1)],[0,4,5,6,10],[(0,115)]),
([v0,v43,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v14,v2,v3),(v43,v14,v1)],[5],[]),
([v0,v1,0xefafeeaaefafeeaa,v2,v3,v4,v5],[],[],[]),
([v0,v1,0xe0a0eeaae0a0eeaa,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v30,v2,v4),(0xe0a0eeaae0a0eeaa,v30,v32)],[3,6,9],[]),
([v69,v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v163,v1,v19),(v69,v163,v19)],[9],[]),
([v0,v1,v19,0xffc8ffc0ffc8ffc0,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v163,v1,v19),(0xffc8ffc0ffc8ffc0,v163,v3)],[0,5,9],[]),
([0x37003f0037003f00,v0,v1,v19,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v163,v1,v19),(0x37003f0037003f00,v163,v3)],[0,5],[]),
([0x37373f3f00000000,v0,v1,v19,v3,v4],[(v11,v0,v4),(v19,v11,v2),(v163,v1,v19),(0x37373f3f00000000,v163,v5)],[1,5,6],[]),
([v124,v1,v56,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v124,v0,v21),(v56,v0,v21)],[0,2,4,5,9],[(1,116),(1,117)]),
([v124,v1,v21,v56,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v124,v0,v21),(v56,v0,v21)],[3],[(1,118)]),
([v69,v0,v19,v66,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v66,v1,v19),(v69,v1,v19)],[0,9],[]),
([v113,v126,v1,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v113,v0,v21),(v126,v0,v21)],[0,5,9],[(1,116),(1,119)]),
([v113,v126,v1,v21,v3,v4,v5],[],[],[(1,118)]),
([v0,v1,v115,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v11,v0,v4),(v115,v11,v21)],[0,5,9],[]),
([v0,v1,v19,v115,v3,v4,v5],[],[],[]),
([v200,v0,v1,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v12,v1,v3),(v200,v12,v19)],[0,5],[]),
([v200,v0,v1,v19,v3,v4,v5],[],[],[]),
([v62,v0,v1,v19,v3,v4],[(v11,v0,v4),(v19,v11,v2),(v12,v1,v3),(v62,v12,v5)],[1,5,6],[]),
([v11,v1,v21,v3,v13,v5],[(v12,v1,v3),(v21,v12,v2),(v11,v0,v4),(v13,v0,v4)],[0,5,8,9],[(1,120)]),
([v84,v0,v1,v21,v3,v13,v5],[(v12,v1,v3),(v21,v12,v2),(v13,v0,v4),(v84,v21,v4)],[4],[(0,121)]),
([v0,v1,v234,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3),(v234,v19,v10)],[9],[]),
([0x30f020a030f020a,v0,v1,v21,v3,v4,v5],[],[],[]),
([v0,v1,v19,v3,v15,v4],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3),(v15,v10,v5)],[1,5,6,9,10],[(1,121)]),
([v0,v1,v19,v235,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v26,v1,v3),(v235,v26,v19)],[6,8],[]),
([v0,v1,0xfa32f030fa32f030,v19,v3,v4,v5],[],[],[]),
([v17,v36,v1,v21,v3,v5],[(v12,v1,v3),(v21,v12,v2),(v17,v0,v4),(v36,v0,v4)],[0,5,6,9],[(1,120)]),
([v0,v1,v19,0xfeccfcccfeccfccc,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v152,v19,v3),(0xfeccfcccfeccfccc,v1,v152)],[6,8],[]),
([v0,v1,v152,v19,v164,v4,v5],[],[],[(1,122)]),
([v0,v1,v19,v3,v192,v4],[(v11,v0,v4),(v19,v11,v2),(v236,v19,v3),(v192,v236,v5)],[1,5,6,10],[(1,123)]),
([v125,v84,v0,v1,v3,v5],[(v12,v1,v3),(v21,v12,v2),(v125,v21,v4),(v84,v21,v4)],[0,4,6,8,9],[(0,124)]),
([v125,v84,v0,v1,v21,v3,v5],[(v12,v1,v3),(v21,v12,v2),(v125,v21,v4),(v84,v21,v4)],[4],[(0,122),(0,123)]),
([v0,0xabafaaaaabafaaaa,v1,v21,v3,v4,v5],[],[],[]),
([v0,v1,v2,v19,0xffc8ffc0ffc8ffc0,v4,v5],[],[],[]),
([0x37003f0037003f00,v0,v1,v2,v19,v4,v5],[],[],[]),
([0x37373f3f00000000,v0,v1,v2,v19,v3,v4],[],[],[]),
([v124,v1,v2,v56,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v124,v0,v21),(v56,v0,v21)],[3],[(1,125)]),
([v80,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v56,v0,v21),(v80,v2,v56)],[0,3],[(0,79)]),
([v0,v1,0xf2faf2faf2faf2fa,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v113,v0,v21),(0xf2faf2faf2faf2fa,v113,v2)],[0,3,4,5,10],[]),
([v0,v1,v2,v56,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v113,v0,v21),(v56,v113,v21)],[3,4],[]),
([v113,v126,v1,v2,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v113,v0,v21),(v126,v0,v21)],[3],[(1,125)]),
([v0,v1,v19,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v11,v0,v4),(v19,v11,v2)],[5],[]),
([v0,v1,v2,v115,v3,v4,v5],[],[],[]),
([v200,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v12,v1,v3),(v200,v12,v19)],[3,5],[]),
([v62,v0,v1,v2,v19,v3,v4],[],[],[]),
([v11,v1,v2,v21,v3,v13,v5],[],[],[(1,126)]),
([v14,v0,v1,v19,v10,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3),(v14,v2,v3)],[6],[(0,127)]),
([v28,v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3),(v28,v2,v10)],[5],[]),
([v0,v1,v2,v234,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3),(v234,v19,v10)],[5,9],[]),
([0x30f020a030f020a,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,v2,v19,v3,v15,v4],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3),(v15,v10,v5)],[4,10],[(0,127)]),
([v0,v1,v37,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v17,v0,v4),(v37,v17,v2)],[4,5,10],[]),
([v0,v1,v2,v235,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v26,v1,v3),(v235,v26,v19)],[6],[]),
([v0,v1,v2,0xfa32f030fa32f030,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v26,v1,v3),(0xfa32f030fa32f030,v26,v19)],[5],[]),
([v17,v36,v1,v2,v21,v3,v5],[],[],[(1,126)]),
([v0,v1,v152,v19,v61,v4,v5],[],[],[(1,128)]),
([v0,v55,v1,v21,v3,v4,v5],[],[],[]),
([v125,v30,v0,v1,v21,v3,v5],[(v12,v1,v3),(v21,v12,v2),(v30,v2,v4),(v125,v21,v4)],[4,9],[(0,129),(1,130)]),
([v0,v1,v2,v152,v164,v4,v5],[],[],[(1,131)]),
([0xf0a0f000f0a0f00,v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v164,v19,v3),(0xf0a0f000f0a0f00,v2,v164)],[0,3,6,8,10],[]),
([v0,v1,v2,v19,v3,v192,v4],[(v11,v0,v4),(v19,v11,v2),(v236,v19,v3),(v192,v236,v5)],[10],[(0,130),(1,132)]),
([v125,v84,v0,v1,v2,v3,v5],[(v12,v1,v3),(v21,v12,v2),(v125,v21,v4),(v84,v21,v4)],[3],[(0,131),(0,132)]),
([v0,v1,0xf3fff0f0f3fff0f0,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v84,v21,v4),(0xf3fff0f0f3fff0f0,v84,v2)],[0,3,6],[]),
([v153,v0,v1,v2,v3,v4],[],[],[]),
([v62,v11,v1,v2,v3,v13],[(v12,v1,v3),(v62,v12,v5),(v11,v0,v4),(v13,v0,v4)],[5,8],[(1,133)]),
([v177,v0,v1,v2,v3,v4],[(v12,v1,v3),(v62,v12,v5),(v13,v0,v4),(v177,v62,v13)],[5,8],[(1,134)]),
([v14,v157,v0,v1,v2,v10,v4],[],[],[(0,134)]),
([v28,v157,v0,v1,v2,v3,v4],[],[],[]),
([v62,v0,v1,v2,v37,v3,v4],[],[],[]),
([v17,v62,v36,v1,v2,v3],[(v12,v1,v3),(v62,v12,v5),(v17,v0,v4),(v36,v0,v4)],[5,6],[(1,133)]),
([v62,v0,v55,v1,v2,v3,v4],[],[],[]),
([v49,v11,v0,v2,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v11,v0,v4)],[0,1,2,3,5,6,8],[(0,120),(0,126),(0,133),(0,135),(0,136)]),
([v49,v0,v2,v4,v13,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v13,v0,v4)],[0,2,3,5,6,8],[(0,136),(0,139),(1,137),(1,138)]),
([v17,v49,v0,v2,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v17,v0,v4)],[0,2,3,5,8],[(0,140),(0,141)]),
([v39,v141,v1,v2,v3,v5],[(v11,v0,v4),(v13,v0,v4),(v141,v11,v13),(v39,v1,v3)],[0,1,2,3,4,9,10],[(1,141)]),
([v49,v0,v2,v4,v45,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10),(v45,v2,v4)],[0,1,2,3,5,8],[]),
([v14,v141,v1,v2,v3,v5],[(v11,v0,v4),(v13,v0,v4),(v141,v11,v13),(v14,v2,v3)],[0,1,3,4,9,10],[(0,137),(1,142)]),
([v0,v53,v2,v10,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4),(v53,v11,v12)],[0,5,6,8,9,10],[(0,135),(0,143),(0,144),(0,145),(0,146),(0,147)]),
([v138,v11,v1,v2,v3,v5],[(v11,v0,v4),(v13,v0,v4),(v12,v1,v3),(v138,v12,v13)],[0,5],[(0,149),(1,135),(1,148)]),
([v11,v12,v2,v10,v13,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4),(v13,v0,v4)],[0,5,8,9,10],[(0,136),(0,143),(1,136)]),
([v14,v11,v1,v2,v10,v13,v5],[],[],[(0,137),(0,150)]),
([v28,v11,v1,v2,v3,v13,v5],[],[],[(0,138)]),
([v11,v1,v2,v3,v15,v13],[(v11,v0,v4),(v13,v0,v4),(v10,v1,v3),(v15,v10,v5)],[5,8,9,10],[(0,150),(1,139)]),
([v11,v1,v2,v63,v3,v13,v5],[],[],[(1,140)]),
([v17,v36,v12,v2,v10,v5],[(v12,v1,v3),(v10,v1,v3),(v17,v0,v4),(v36,v0,v4)],[0,5,6,9,10],[(0,141),(1,136)]),
([v11,v1,v43,v2,v3,v13,v5],[],[],[(1,142)]),
([v0,v1,v53,v115,v3,v4,v5],[(v11,v0,v4),(v12,v1,v3),(v53,v11,v12),(v115,v53,v2)],[0,3,4,5,6,9],[(0,144),(0,151),(1,144)]),
([0xe0a0c000e0a0c00,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v12,v1,v3),(v53,v11,v12),(0xe0a0c000e0a0c00,v53,v2)],[0,5,9],[(0,152),(0,153)]),
([v174,v0,v1,v53,v3,v4,v5],[(v11,v0,v4),(v12,v1,v3),(v53,v11,v12),(v174,v53,v2)],[0,5,9],[(0,145),(0,152),(0,154),(1,145)]),
([v153,v0,v1,v53,v2,v3,v4],[(v11,v0,v4),(v12,v1,v3),(v53,v11,v12),(v153,v53,v5)],[0,5,9],[(0,147),(0,151),(0,154),(1,147)]),
([v0,v1,v2,0xf3fff2faf3fff2fa,v3,v4,v5],[(v12,v1,v3),(v13,v0,v4),(v138,v12,v13),(0xf3fff2faf3fff2fa,v138,v2)],[0,5,9],[(0,155)]),
([v177,v138,v0,v1,v2,v3,v4],[(v12,v1,v3),(v13,v0,v4),(v138,v12,v13),(v177,v138,v5)],[0,5,9],[(0,149)]),
([v14,v216,v0,v1,v2,v4,v5],[],[],[(0,134)]),
([v0,v178,v1,v2,v10,v4,v5],[],[],[(0,156)]),
([v14,v11,v0,v1,v2,v15,v4],[(v11,v0,v4),(v10,v1,v3),(v14,v2,v3),(v15,v10,v5)],[3,4,9],[(0,112),(0,127),(0,134),(0,150),(0,156),(0,157)]),
([v0,0xafae0f0cafae0f0c,v1,v2,v3,v4,v5],[(v11,v0,v4),(v10,v1,v3),(v28,v2,v10),(0xafae0f0cafae0f0c,v28,v11)],[3],[]),
([v0,v1,v2,v3,v193,v4],[(v11,v0,v4),(v10,v1,v3),(v15,v10,v5),(v193,v11,v15)],[1,5,6,9,10],[(0,157)]),
([v0,v1,v2,v3,v15,v193,v4],[(v11,v0,v4),(v10,v1,v3),(v15,v10,v5),(v193,v11,v15)],[1,6],[]),
([v177,v0,v1,v2,v3,v4,v23],[],[],[]),
([0xa0e000c0a0e000c,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v26,v1,v3),(v185,v26,v11),(0xa0e000c0a0e000c,v185,v2)],[5],[]),
([v39,v0,v185,v2,v4,v5],[(v11,v0,v4),(v26,v1,v3),(v185,v26,v11),(v39,v1,v3)],[2,4,5],[]),
([0x30f032fa30f032fa,v0,v1,v2,v3,v4,v5],[(v12,v1,v3),(v17,v0,v4),(v37,v17,v2),(0x30f032fa30f032fa,v12,v37)],[3],[]),
([0x2322030023220300,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v14,v2,v3),(v178,v14,v11),(0x2322030023220300,v178,v1)],[3,5],[]),
([0x23af22aa23af22aa,v0,v1,v2,v3,v4,v5],[(v12,v1,v3),(v30,v2,v4),(v55,v30,v0),(0x23af22aa23af22aa,v12,v55)],[5],[]),
([v44,v0,v170,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v79,v44,v2),(v170,v79,v1)],[0,8],[(0,80)]),
([v44,v0,v2,v3,0xffcceeccffcceecc,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v237,v44,v3),(0xffcceeccffcceecc,v237,v1)],[0,4],[]),
([v44,v1,0xeeaaffaaeeaaffaa,v2,v3,v4,v5],[],[],[]),
([v44,v0,v1,0xfcf0fdf0fcf0fdf0,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v238,v44,v3),(0xfcf0fdf0fcf0fdf0,v238,v2)],[2,4],[]),
([v44,0x33ff22ff00000000,v0,v1,v2,v3,v4],[],[],[]),
([0x3f332f223f332f22,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v14,v2,v3),(0x3f332f223f332f22,v14,v44)],[3],[]),
([0x3033202230332022,v0,v1,v2,v3,v4,v5],[],[],[]),
([v14,v0,v1,v2,v140,v4,v5],[],[],[(0,158)]),
([v14,v0,v1,v2,v15,v4,v13],[],[],[(0,150),(0,158),(1,159)]),
([v14,v0,v1,v2,v10,v4,v23],[],[],[(0,158)]),
([0xf0c0a080f0c0a08,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,0xf0c0f5c4f0c0f5c4,v2,v3,v4,v5],[],[],[]),
([v28,v165,v0,v1,v3,v4,v5],[(v10,v1,v3),(v13,v0,v4),(v28,v2,v10),(v165,v2,v13)],[10],[]),
([v28,v0,v1,v2,v3,v4,v23],[(v10,v1,v3),(v13,v0,v4),(v28,v2,v10),(v23,v13,v5)],[8],[]),
([v0,v1,v2,v3,0xfffcfaf8fffcfaf8,v4,v5],[(v10,v1,v3),(v13,v0,v4),(v140,v10,v13),(0xfffcfaf8fffcfaf8,v2,v140)],[0],[(0,160)]),
([v0,v1,v2,v3,v158,v4],[(v10,v1,v3),(v13,v0,v4),(v140,v10,v13),(v158,v140,v5)],[5,8,9,10],[(0,158),(0,161),(1,158),(1,161)]),
([v0,v1,v2,v3,v158,v140,v4],[(v10,v1,v3),(v13,v0,v4),(v140,v10,v13),(v158,v140,v5)],[0],[]),
([v101,v0,v1,v2,v10,v4,v23],[],[],[(0,161),(1,162)]),
([v0,v1,v2,v3,v158,v15,v4],[(v10,v1,v3),(v13,v0,v4),(v15,v10,v5),(v158,v15,v13)],[4,5,8,9],[(1,161)]),
([0x5544ffccffcc,v0,v1,v2,v3,v4],[(v13,v0,v4),(v10,v1,v3),(v23,v13,v5),(0x5544ffccffcc,v23,v10)],[5,8],[(0,159)]),
([0x5544ffccffcc,v0,v1,v2,v3,v4,v23],[],[],[]),
([v0,v1,0xf0c0fac8f0c0fac8,v2,v3,v4,v5],[],[],[]),
([0xf030a020f030a02,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,v2,v37,v3,v15,v4],[],[],[]),
([v0,v1,v2,v3,0xfff3faf2fff3faf2,v4,v5],[],[],[]),
([v14,v0,v1,v2,0xffcc5544ffcc5544,v4,v5],[],[],[]),
([v17,v14,v36,v1,v2,v10,v5],[],[],[(0,137),(0,163)]),
([v17,v28,v36,v1,v2,v3,v5],[],[],[(0,138)]),
([v17,v36,v1,v2,v3,v15],[(v10,v1,v3),(v17,v0,v4),(v36,v0,v4),(v15,v10,v5)],[5,6,9,10],[(0,163),(1,139)]),
([v17,v14,v0,v1,v2,v15,v4],[],[],[(0,163)]),
([0xf0cafae0f0cafae,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v17,v0,v4),(v28,v2,v10),(0xf0cafae0f0cafae,v17,v28)],[5],[]),
([v0,v1,v2,v3,v15,0xffccffee0000aaaa,v4],[(v10,v1,v3),(v17,v0,v4),(v15,v10,v5),(0xffccffee0000aaaa,v17,v15)],[8],[]),
([v0,v1,v2,v3,0xff33aa2200000000,v4,v23],[],[],[]),
([v17,v0,v1,v2,v3,v130,v15],[(v10,v1,v3),(v17,v0,v4),(v15,v10,v5),(v130,v15,v4)],[5],[(0,162)]),
([v14,v36,v0,v1,v2,v15,v4],[],[],[(0,163)]),
([v14,v93,v0,v1,v2,v15,v4],[(v10,v1,v3),(v14,v2,v3),(v15,v10,v5),(v93,v0,v15)],[3,4,9],[(0,164),(0,165),(0,166),(0,167),(0,168)]),
([v14,v0,v1,v2,v15,v78,v4],[],[],[(0,168),(0,169),(0,170)]),
([v171,v30,v0,v1,v2,v3,v23],[],[],[(0,171)]),
([v14,0x5544554400000000,v0,v1,v2,v15,v4],[],[],[(1,171)]),
([v14,v0,v1,v2,v130,v15,v4],[(v10,v1,v3),(v14,v2,v3),(v15,v10,v5),(v130,v15,v4)],[3,4],[(0,173),(0,174),(1,172)]),
([v14,v0,v1,v2,v15,v4,v179],[],[],[(0,174)]),
([v186,v14,v0,v1,v2,v15,v4],[],[],[(1,175)]),
([v101,v30,v0,v1,v2,v3,v23],[],[],[(0,175)]),
([v79,v0,v1,v2,v3,v4,v5],[],[],[]),
([v28,v0,v1,0xfaf8faf8faf8faf8,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v201,v28,v0),(0xfaf8faf8faf8faf8,v201,v2)],[0,5],[]),
([v201,v129,v1,v2,v3,v4,v5],[],[],[(0,176)]),
([v28,v0,v1,0xf5f4f5f4f5f4f5f4,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v225,v28,v0),(0xf5f4f5f4f5f4f5f4,v225,v2)],[0],[(1,80)]),
([v79,v0,0xc0c0c4c4c0c0c4c4,v2,v3,v4,v5],[],[],[(1,176)]),
([v28,v0,v239,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v240,v28,v0),(v239,v240,v1)],[5],[]),
([v28,0x5f5d5f5d00000000,v0,v1,v2,v3,v4],[],[],[]),
([v28,v0,v1,v3,0xfffcf0f0fffcf0f0,v4,v5],[(v10,v1,v3),(v28,v2,v10),(0xf0c00000f0c0000,v28,v4),(0xfffcf0f0fffcf0f0,0xf0c00000f0c0000,v2)],[0,6],[]),
([0xf000a000f000a00,v0,v1,v2,0xff0fff0aff0fff0a,v4,v5],[],[],[(0,177)]),
([v28,v0,v1,v2,v3,v4,0xffff0f0c00000000],[(v10,v1,v3),(v28,v2,v10),(v241,v28,v4),(0xffff0f0c00000000,v241,v5)],[8],[]),
([v28,v0,v1,0xf0f0fffcf0f0fffc,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v202,v28,v4),(0xf0f0fffcf0f0fffc,v202,v2)],[0,8],[]),
([v202,v0,v1,v2,v242,v3,v5],[],[],[(1,177)]),
([v28,v0,v1,v242,v3,v45,v5],[],[],[]),
([v0,v1,v2,v121,v61,v4,v23],[(v13,v0,v4),(v61,v2,v3),(v23,v13,v5),(v121,v23,v3)],[6,10],[]),
([v0,v1,v2,v3,0xffccf0c000000000,v15,v4],[(v10,v1,v3),(v45,v2,v4),(v15,v10,v5),(0xffccf0c000000000,v15,v45)],[4,9],[]),
([0x5550fff0fff0,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v61,v2,v3),(v23,v13,v5),(0x5550fff0fff0,v23,v61)],[3,10],[]),
([v0,0xaf8caa88af8caa88,v1,v2,v3,v4,v5],[],[],[]),
([v0,v55,v1,v2,v3,v15,v4],[],[],[]),
([v0,v1,v2,0xfaeaffeefaeaffee,v3,v4,v5],[(v10,v1,v3),(v30,v2,v4),(v243,v30,v10),(0xfaeaffeefaeaffee,v0,v243)],[3,10],[]),
([v0,v1,v2,v3,v15,0xffcfffcc0f0f0000,v4],[(v10,v1,v3),(v30,v2,v4),(v15,v10,v5),(0xffcfffcc0f0f0000,v30,v15)],[3,6],[]),
([v0,v1,0xf0c0ffcc00000000,v2,v3,v15,v4],[],[],[]),
([v186,v30,v0,v1,v2,v3,v15],[],[],[]),
([v0,v1,v194,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v93,v0,v15),(v194,v93,v2)],[1,5,9,10],[(1,178)]),
([v0,v1,v2,v194,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v93,v0,v15),(v194,v93,v2)],[4,10],[(0,165)]),
([v111,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v159,v1,v23),(v111,v159,v23)],[9],[]),
([v0,v1,v2,v3,v15,0xffffaa88ffff0000],[(v10,v1,v3),(v15,v10,v5),(v93,v0,v15),(0xffffaa88ffff0000,v93,v4)],[5,8,9,10],[(0,166)]),
([0x33007700ff00ff00,v0,v1,v2,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v159,v1,v23),(0x33007700ff00ff00,v159,v3)],[5,8],[(1,167)]),
([v93,v1,v2,v3,v78,v4],[(v10,v1,v3),(v15,v10,v5),(v93,v0,v15),(v78,v0,v15)],[1,5,9,10],[(0,168),(0,181),(1,179),(1,180)]),
([v93,v1,v2,v3,v15,v78,v4],[],[],[(1,182)]),
([v111,v0,v2,v3,v4,v23,v102],[(v13,v0,v4),(v23,v13,v5),(v102,v1,v23),(v111,v1,v23)],[0,9],[]),
([v0,v1,v2,v3,v78,v145,v4],[(v10,v1,v3),(v15,v10,v5),(v78,v0,v15),(v145,v2,v15)],[3,5],[(1,183)]),
([v139,v0,v1,v2,v3,v78,v4],[],[],[(0,184)]),
([0xf0e0f0e0a0a0a0a,v0,v1,v2,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v78,v0,v15),(0xf0e0f0e0a0a0a0a,v2,v78)],[10],[]),
([v0,v1,v2,v168,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v102,v1,v23),(v168,v102,v3)],[4,5,8,9],[(0,183),(1,169),(1,184)]),
([v0,v1,v2,v168,v4,v23,v102],[(v13,v0,v4),(v23,v13,v5),(v102,v1,v23),(v168,v102,v3)],[9,10],[(1,181)]),
([v195,v0,v1,v2,v3,v15],[(v10,v1,v3),(v15,v10,v5),(v78,v0,v15),(v195,v78,v4)],[9,10],[(0,170)]),
([v195,v0,v1,v2,v3,v15,v78],[(v10,v1,v3),(v15,v10,v5),(v78,v0,v15),(v195,v78,v4)],[1,6],[]),
([v0,v1,v2,0xf0f0f4f4fcfcfcfc,v3,v4,v23],[],[],[]),
([v0,v1,v2,v3,v15,v78,v4],[(v10,v1,v3),(v15,v10,v5),(0x220022aaaaaaaa,v0,v15),(v78,0x220022aaaaaaaa,v15)],[5,6,8],[]),
([v171,v111,v0,v2,v3,v4],[(v13,v0,v4),(v23,v13,v5),(v171,v1,v23),(v111,v1,v23)],[5,8,9],[(0,171),(0,179),(0,185)]),
([v171,v111,v0,v2,v3,v4,v23],[],[],[(0,182)]),
([v0,v1,v2,0xf3f3f2f2f0f0f0f0,v3,v4,v23],[],[],[]),
([v111,v0,v1,v2,v3,v4,v160],[(v13,v0,v4),(v23,v13,v5),(v111,v1,v23),(v160,v2,v23)],[3],[]),
([v139,0x5544554400000000,v0,v1,v2,v3,v4],[(v10,v1,v3),(v15,v10,v5),(0x5544554400000000,v0,v15),(v139,v2,v15)],[3,5],[]),
([0x3333323230303030,v0,v1,v2,v3,v4,v23],[],[],[]),
([v139,v0,v1,v3,v15,v145,v4],[(v10,v1,v3),(v15,v10,v5),(v145,v2,v15),(v139,v2,v15)],[0,3],[]),
([v0,v1,v2,v121,v3,v4,v160],[(v13,v0,v4),(v23,v13,v5),(v160,v2,v23),(v121,v23,v3)],[10],[]),
([v101,v0,v1,v2,v3,v4,v160],[(v13,v0,v4),(v23,v13,v5),(v160,v2,v23),(v101,v23,v3)],[3,10],[]),
([v0,0xafaeafaeaaaaaaaa,v1,v2,v3,v15,v4],[],[],[]),
([v139,v0,v1,v2,v3,v130,v4],[(v10,v1,v3),(v15,v10,v5),(v139,v2,v15),(v130,v15,v4)],[3,8],[]),
([v101,0xf0f0a0a00000000,v0,v1,v2,v3,v4],[],[],[]),
([v0,v1,v2,v3,0xffcceecccccccccc,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v121,v23,v3),(0xffcceecccccccccc,v1,v121)],[2,4],[]),
([v0,v1,v2,v3,v15,0xfffcf0f0f0f0f0f0,v4],[(v10,v1,v3),(v15,v10,v5),(v130,v15,v4),(0xfffcf0f0f0f0f0f0,v2,v130)],[4,10],[(0,173)]),
([v0,v1,v2,v121,v4,v208],[(v13,v0,v4),(v23,v13,v5),(v121,v23,v3),(v208,v3,v23)],[2,4,5,8,9,10],[(0,186),(1,174),(1,187)]),
([v0,v1,v2,v121,v4,v23,v208],[],[],[(1,188)]),
([0xf0f0f0a0f000f00,v0,v1,v2,v3,v4,v23],[],[],[(0,186)]),
([v0,v1,v2,0xf0f0fffcf0f0f0f0,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v186,v15,v4),(0xf0f0fffcf0f0f0f0,v186,v2)],[10],[]),
([v101,v217,v0,v1,v2,v4],[(v13,v0,v4),(v23,v13,v5),(v217,v23,v3),(v101,v23,v3)],[4,5,8,10],[(0,175),(1,187)]),
([v101,v217,v0,v1,v2,v4,v23],[],[],[(1,188)]),
([v0,0xaabbaaaaffffaaaa,v1,v2,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(0x330000ffff0000,v15,v4),(0xaabbaaaaffffaaaa,0x330000ffff0000,v0)],[1],[]),
([v0,v1,v2,0xf0f0f5f0fff0fff0,v3,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v101,v23,v3),(0xf0f0f5f0fff0fff0,v101,v2)],[8],[]),
([v132,v0,v96,v2,v3,v4,v5],[(v17,v0,v4),(v96,v17,v1),(v150,v96,v2),(v132,v1,v150)],[0],[(1,82)]),
([v0,v42,v1,v2,v175,v3,v5],[(v26,v1,v3),(v42,v26,v0),(v48,v42,v2),(v175,v48,v4)],[3],[(0,84)]),
([v0,v42,v1,v2,v127,v3,v4],[(v26,v1,v3),(v42,v26,v0),(v48,v42,v2),(v127,v48,v5)],[3],[(0,85)]),
([v81,v30,v0,v1,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(v81,v42,v2),(v30,v2,v4)],[4,8],[]),
([v0,v96,v2,v3,0xffccddccffccddcc,v4,v5],[(v17,v0,v4),(v96,v17,v1),(v244,v96,v3),(0xffccddccffccddcc,v244,v1)],[0,4,8],[]),
([v0,0xafefaaeeafefaaee,v1,v2,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(v30,v2,v4),(0xafefaaeeafefaaee,v30,v42)],[8],[]),
([0xa0e0aaeea0e0aaee,v0,v1,v2,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(v30,v2,v4),(0xa0e0aaeea0e0aaee,v30,v42)],[3],[]),
([0xa0a8a0a8a0a8a0a8,v1,v2,v48,v3,v4,v5],[],[],[(1,189)]),
([v81,v0,v1,v63,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(v48,v0,v63),(v81,v2,v48)],[0],[(0,82)]),
([v0,v1,v2,v37,0xfc00fe00fc00fe00,v4,v5],[],[],[]),
([0xfafe0000fafe,v0,v1,v2,v63,v3,v5],[],[],[]),
([v0,v1,v2,v37,0xfcfcfefe00000000,v3,v4],[],[],[]),
([v0,v1,v37,0xfcfcf4f4fcfcf4f4,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(0xc0c04040c0c0404,v1,v37),(0xfcfcf4f4fcfcf4f4,0xc0c04040c0c0404,v2)],[0,8],[]),
([v0,v1,v2,v48,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(v203,v0,v63),(v48,v203,v63)],[0,6,8,10],[(0,190)]),
([v203,0x5054505450545054,v1,v2,v3,v4,v5],[],[],[(1,189)]),
([v0,v1,v2,0xf0fcfafef0fcfafe,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(v17,v0,v4),(0xf0fcfafef0fcfafe,v17,v63)],[0,8,10],[(0,191)]),
([v0,v1,0xf030fa32f030fa32,v2,v3,v4,v5],[],[],[]),
([v17,v36,v1,v2,v63,v3,v5],[],[],[(1,140)]),
([v0,v1,0xf000fa00f000fa00,v2,v204,v4,v5],[],[],[(1,192)]),
([0xf000f0a0f000f0a,v0,v1,v37,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v204,v37,v3),(0xf000f0a0f000f0a,v2,v204)],[0,8,10],[]),
([0xf0fc0000f0fc,0xf0300000f030000,v0,v1,v2,v3,v5],[],[],[(0,192)]),
([v0,v1,v37,v3,0xfff0f5f0fff0f5f0,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v245,v37,v3),(0xfff0f5f0fff0f5f0,v245,v2)],[0,4],[]),
([v0,v1,v2,v37,0xf0fffaff00000000,v3,v4],[],[],[]),
([v17,v26,v39,v36,v2,v5],[(v26,v1,v3),(v39,v1,v3),(v17,v0,v4),(v36,v0,v4)],[4,5,6,9],[(0,141),(1,141)]),
([v17,v36,v1,v43,v2,v3,v5],[],[],[(1,142)]),
([0xc0a0e000c0a0e,v0,v1,v2,v3,v4,v5],[],[],[]),
([0x300232203002322,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,0xaf23aa22af23aa22,v1,v2,v3,v4,v5],[],[],[]),
([v77,v0,v2,v3,0xffccfcccffccfccc,v4,v5],[(v45,v2,v4),(v77,v1,v45),(v246,v77,v3),(0xffccfcccffccfccc,v246,v1)],[0,4,8],[(1,193)]),
([v77,v0,v1,0xfcf0fff0fcf0fff0,v3,v4,v5],[],[],[]),
([v89,v0,v1,v58,v61,v4,v5],[(v61,v2,v3),(v20,v3,v4),(v58,v0,v20),(v89,v2,v58)],[3],[]),
([v123,v0,v65,v2,v3,v4,v5],[(v30,v2,v4),(v65,v30,v1),(v131,v65,v0),(v123,v1,v131)],[0,6],[(1,46)]),
([v0,v47,v1,v3,v230,v4,v5],[(v14,v2,v3),(v47,v14,v0),(v247,v47,v4),(v230,v247,v2)],[6],[]),
([0x30ff33ff00000000,v0,v1,v65,v2,v3,v4],[],[],[]),
([v0,v65,v2,0xfcccffccfcccffcc,v3,v4,v5],[(v30,v2,v4),(v65,v30,v1),(v248,v65,v3),(0xfcccffccfcccffcc,v248,v1)],[0,4,6],[]),
([0x8a888a888a888a88,v1,v85,v2,v3,v4,v5],[],[],[(1,194)]),
([v108,v0,v43,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(v85,v43,v0),(v108,v1,v85)],[0,4],[(0,46)]),
([v0,v1,v85,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(v212,v43,v0),(v85,v212,v0)],[10],[]),
([v205,v212,v1,v2,v3,v4,v5],[],[],[(1,194)]),
([v0,v43,v239,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(v205,v43,v0),(v239,v205,v1)],[0,2],[]),
([v0,v55,0xbfbfbbbb00000000,v1,v2,v3,v4],[],[],[]),
([v0,0xaf00aa00af00aa00,v1,v2,0xffafffaaffafffaa,v4,v5],[],[],[(1,195)]),
([0x3333030033330300,v0,v43,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(0xffffcfccffffcfcc,v43,v4),(0x3333030033330300,v1,0xffffcfccffffcfcc)],[0,2,8],[]),
([v0,v55,v1,v2,v3,0xffafffaa00000000,v4],[],[],[]),
([0xcfcc0000cfcc,v206,v0,v1,v2,v3,v5],[],[],[(0,195)]),
([v0,v43,v2,0xfcffccccfcffcccc,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(v206,v43,v4),(0xfcffccccfcffcccc,v206,v1)],[0,4,6],[]),
([v116,v0,v2,v3,v82,v4,v5],[(v20,v4,v3),(v82,v1,v20),(v59,v0,v82),(v116,v1,v59)],[0],[(0,47)]),
([v155,v0,v1,v3,v58,v4,v5],[],[],[]),
([v0,v1,v2,v3,v58,v143,v4],[],[],[]),
([v0,v1,v2,0xf3f2f2f2f3f2f2f2,v3,v4,v5],[],[],[]),
([v134,v0,v2,v3,v82,v4,v5],[(v20,v4,v3),(v82,v1,v20),(v147,v2,v82),(v134,v1,v147)],[0,4,6],[(1,90)]),
([v0,0xafaeaeaeafaeaeae,v1,v2,v3,v4,v5],[(v20,v4,v3),(v82,v1,v20),(0xf0c0c0c0f0c0c0c,v2,v82),(0xafaeaeaeafaeaeae,0xf0c0c0c0f0c0c0c,v0)],[1],[]),
([v89,v0,v1,v3,v64,v4,v5],[(v20,v3,v4),(v64,v2,v20),(v99,v0,v64),(v89,v2,v99)],[0],[(0,90)]),
([v0,0xbbbabababbbababa,v1,v2,v3,v4,v5],[],[],[]),
([v135,v0,0xccccffccccccffcc,v2,v3,v4,v5],[(v68,v3,v4),(0xccccffccccccffcc,v68,v1),(v151,0xccccffccccccffcc,v2),(v135,v1,v151)],[0,8],[(1,91)]),
([v0,v114,v1,v2,v184,v3,v4],[],[],[]),
([v128,v0,v1,0xf0fff0f0f0fff0f0,v3,v4,v5],[(v52,v4,v3),(0xf0fff0f0f0fff0f0,v52,v2),(v83,v0,0xf0fff0f0f0fff0f0),(v128,v2,v83)],[0],[(0,91)]),
([v0,v1,v2,v106,0xfcfcfffc00000000,v3,v4],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L7 : Array W6Node := Array.mk [
([v46,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v46,v0,v8)],[0,2,3,5,9,10],[(0,2),(1,0),(1,1)]),
([v16,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v16,v1,v7)],[0,1,2,3,5,8,9],[(0,3)]),
([v16,v1,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v16,v1,v7)],[3,9],[]),
([v25,v1,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v25,v1,v4)],[1,3,8,9],[(1,4),(1,5),(1,6)]),
([v18,v0,v6,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v18,v6,v2)],[0,2,3,9,10],[(0,2),(1,3)]),
([v0,v72,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v72,v6,v3)],[2,3,5,9],[(0,7)]),
([v67,v0,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v67,v6,v3)],[2,3],[(0,5),(0,8)]),
([v0,v161,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v161,v6,v4)],[1,3,8],[(0,9)]),
([v67,v1,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v67,v6,v3)],[2,3],[(1,10),(1,11)]),
([v0,v6,v2,v70,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v70,v8,v3)],[2,3,5,9],[(1,12)]),
([v50,v0,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v50,v8,v3)],[2,3,5],[(0,13),(0,14)]),
([v0,v6,v2,v97,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v97,v8,v4)],[1,3,8],[]),
([v35,v0,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v35,v8,v4)],[0,1,2,3,5,8],[(0,15),(0,16),(0,17),(0,18),(0,19)]),
([v0,v6,v2,v8,v20,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v20,v3,v4)],[2,3,5],[(0,21),(0,22),(1,20),(1,23)]),
([v25,v0,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v25,v1,v4)],[3,5,8],[(0,10),(0,17)]),
([v46,v1,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2),(v46,v0,v8)],[3,5,9],[(0,25),(1,24)]),
([v16,v0,v6,v2,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v16,v1,v7)],[0,2,3,5,8,9],[(0,26),(0,27)]),
([v16,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v16,v1,v7)],[3,5,9],[(0,28)]),
([v16,v0,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v16,v1,v7)],[0,3,5,9],[(0,29)]),
([v18,v0,v1,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v18,v6,v2)],[0,3,4,5,6,8],[(0,26),(0,28),(0,29),(1,25)]),
([v18,v0,v1,v6,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v18,v6,v2)],[0,3,5],[(0,27)]),
([v0,0xe2e2e2e2e2e2e2e2,v6,v2,v3,v4,v5],[(v6,v1,v0),(v76,v1,v2),(0xe2e2e2e2e2e2e2e2,v76,v6)],[0,2,3,5,8,9],[]),
([v33,v1,v72,v6,v2,v3,v4,v5],[(v6,v0,v1),(v33,v0,v2),(v72,v6,v3)],[2,3,5,10],[(0,30)]),
([v33,v67,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v33,v0,v2),(v67,v6,v3)],[2],[(0,31),(0,32)]),
([v0,v122,v6,v2,v3,v4,v5],[(v6,v0,v1),(v41,v0,v3),(v122,v41,v1)],[0,2,4,5,8,9,10],[(0,5),(1,10),(1,33)]),
([v0,v1,v6,v2,v40,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v40,v25,v2)],[1,3,5,8],[(0,17),(0,34),(0,35),(1,4),(1,5)]),
([v25,v0,v1,v2,v9,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v9,v6,v2)],[0,3,4,6,8,9,10],[(0,34),(0,36)]),
([v18,v25,v0,v1,v2,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4),(v18,v6,v2)],[1,3,5,6,8,9],[(0,37)]),
([v16,v0,v1,v2,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9)],[0,3,4,5,6,8,9,10],[]),
([v16,v0,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9)],[0,3],[(0,26),(0,38),(0,39),(0,40),(0,41),(0,42),(0,44),(0,45),(0,46),(1,43)]),
([v16,v0,v1,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9)],[0,2],[(0,28),(0,47),(0,48),(0,49),(0,50),(1,39)]),
([v18,v0,v1,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v18,v2,v9)],[0],[(0,26),(0,28),(0,41),(0,51),(0,52),(0,53),(0,54),(0,55),(0,56),(0,57),(1,26),(1,28),(1,41),(1,51),(1,52),(1,53),(1,54),(1,55)]),
([v0,v1,v2,v27,v9,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3)],[0,1,2,3,10],[(0,42),(0,47),(0,51),(0,52),(0,58),(0,59),(0,61),(0,62),(0,64),(0,65),(1,44),(1,48),(1,60),(1,63)]),
([v0,v1,v2,v27,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3)],[0,2,4,10],[(0,53),(0,60),(0,66),(0,67)]),
([v29,v0,v1,v2,v9,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v29,v9,v4)],[0,1,2,3,6],[(0,43),(0,45),(0,49),(0,54),(0,61),(0,62),(0,66),(0,69),(0,70),(0,71),(0,72),(0,73),(1,68)]),
([v104,v0,v1,v2,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v104,v9,v3)],[0,1,2,4,10],[(0,55),(0,63),(0,68),(0,71),(0,75),(0,76),(0,79),(1,74),(1,77),(1,78)]),
([v0,v1,v2,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5)],[0,1,2,3,5,9],[(0,36),(0,80),(0,81),(0,82),(0,83),(1,36),(1,80),(1,81),(1,82)]),
([v0,v1,v2,v24,v9,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5)],[0,1,2,3],[(0,46),(0,50),(0,56),(0,57),(0,64),(0,65),(0,67),(0,72),(0,73),(0,79),(1,46),(1,50),(1,64),(1,65),(1,67),(1,72),(1,73),(1,79)]),
([v0,v1,v2,v9,v20,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v20,v3,v4)],[0,3,4,6,8,10],[(0,83),(0,84),(0,85),(0,86)]),
([v16,v0,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v6,v2),(v16,v1,v9)],[0,3],[(0,27),(0,41),(0,87),(0,88),(0,90),(0,91),(0,92),(1,89)]),
([v18,v0,v1,v6,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v18,v6,v2)],[0,3],[(0,27),(0,93),(0,94),(1,27),(1,93)]),
([v0,v1,v72,v2,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v72,v6,v3)],[0,1,2,3,9,10],[(0,96),(0,97),(1,95)]),
([v67,v0,v1,v2,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v67,v6,v3)],[0,1,3,4,10],[(0,76),(0,98),(0,99)]),
([v0,v1,v6,v2,v27,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3)],[0,1,3,4,5,9],[(0,51),(0,93),(1,96),(1,98)]),
([v0,v1,v6,v2,v27,v9,v4,v5],[(v6,v0,v1),(v9,v6,v2),(v27,v9,v3)],[0,3,10],[(0,52),(0,88),(0,93),(0,100),(0,101),(0,102),(1,90)]),
([v29,v0,v1,v6,v2,v9,v3,v5],[(v6,v1,v0),(v9,v6,v2),(v29,v9,v4)],[0,3,6],[(0,54),(0,89),(0,91),(0,101),(0,103),(0,104)]),
([v0,v1,v6,v2,v24,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5)],[0,1,2,3,5,9],[(0,56),(0,94),(0,97),(0,99),(1,97),(1,99)]),
([v0,v1,v6,v2,v24,v9,v3,v4],[(v6,v0,v1),(v9,v6,v2),(v24,v9,v5)],[0,3],[(0,57),(0,92),(0,94),(0,102),(0,104),(1,92),(1,102),(1,104)]),
([v219,v18,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v219,v18,v3)],[2,3,4,5,9,10],[(0,105)]),
([v18,v0,v1,v2,0xf100f100f100f100,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(0xf100f100f100f100,v18,v3)],[2,3,4,10],[]),
([v18,v14,v0,v1,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v14,v2,v3)],[0,2,3,4,6,10],[(0,107),(1,106)]),
([v18,v0,v1,v2,v20,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v20,v3,v4)],[3,4,6,8,10],[(0,108),(0,109)]),
([v18,v0,v1,v72,v2,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v72,v6,v3)],[2,3,4,9,10],[(0,105)]),
([v18,v67,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v67,v6,v3)],[3,4,10],[(0,110)]),
([v18,v14,v0,v1,v6,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2),(v14,v2,v3)],[2,3,4,10],[(0,112),(1,111)]),
([v0,v1,v6,v2,v172,v3,v4,v5],[(v6,v0,v1),(v72,v6,v3),(v172,v72,v2)],[2,3,4,5,10],[(0,7),(0,30),(0,105)]),
([v0,v1,v72,v161,v2,v3,v4,v5],[(v6,v0,v1),(v72,v6,v3),(v161,v6,v4)],[1,2,4,5,6,8,9,10],[]),
([v67,v0,v1,v161,v2,v3,v4,v5],[(v6,v1,v0),(v161,v6,v4),(v67,v6,v3)],[1,4,5,8],[(1,113)]),
([v0,v1,v6,v2,v169,v3,v4,v5],[(v6,v0,v1),(v67,v6,v3),(v169,v67,v2)],[2,3,10],[(0,5),(0,8),(0,76),(1,11)]),
([v67,v220,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v67,v6,v3),(v220,v6,v4)],[1,4,6,8,10],[]),
([v0,v65,v6,v2,v3,v4,v5],[(v6,v1,v0),(v30,v2,v4),(v65,v30,v1)],[1,2,3,5,6,9],[(0,106),(0,111),(1,114)]),
([v0,v47,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v14,v2,v3),(v47,v14,v0)],[3,4,5,9],[(0,107),(0,115)]),
([v0,v1,v85,v2,v3,v4,v5],[(v6,v0,v1),(v14,v2,v3),(v85,v14,v6)],[0,2,3,6,8,10],[(0,118),(1,116),(1,117)]),
([v0,v1,v6,v85,v2,v3,v4,v5],[(v6,v0,v1),(v14,v2,v3),(v85,v14,v6)],[3,4,10],[(0,112),(0,115),(1,119)]),
([v0,v1,v249,v2,v3,v4,v5],[(v6,v1,v0),(v30,v2,v4),(v249,v30,v6)],[0,1,3,4,5,6,8,9,10],[]),
([v0,v1,v249,v6,v2,v3,v4,v5],[(v6,v1,v0),(v30,v2,v4),(v249,v30,v6)],[1,3,5,6,9],[]),
([v0,v6,v2,v3,v82,v4,v5],[(v6,v1,v0),(v20,v4,v3),(v82,v1,v20)],[1,2,4,5,6,9,10],[(0,20),(0,22),(1,120),(1,121)]),
([v0,v1,v2,v3,v59,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20)],[0,1,2,3,4,6,8,10],[(0,85),(0,122),(0,123),(0,124),(0,125),(0,126),(0,127),(0,128),(1,122)]),
([v0,v1,v6,v2,v3,v59,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v59,v6,v20)],[0,1,2,3,4,6,8,10],[(0,129),(0,130),(0,131),(1,129)]),
([v182,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v182,v6,v20)],[0,3,5,8,9,10],[(0,109),(0,132)]),
([v182,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v182,v6,v20)],[4,5,9],[]),
([v0,v1,v6,v2,v3,v64,v4,v5],[(v6,v0,v1),(v20,v3,v4),(v64,v2,v20)],[3,5,9],[(0,21),(0,22),(0,84),(0,85),(0,109),(0,133),(0,134),(1,21),(1,22)]),
([v0,v6,v2,v8,v3,v4,v5],[(v60,v1,v0),(v6,v60,v0),(v8,v1,v2)],[0,2,3,5,8,9],[(0,135)]),
([v0,v1,v2,v9,v3,v4,v5],[(v31,v0,v1),(v6,v31,v1),(v9,v6,v2)],[0,1,2,3,4,5,6,8,10],[(0,68),(0,137),(0,138),(0,139),(1,68),(1,136)]),
([v0,v1,v6,v2,v9,v3,v4,v5],[(v31,v0,v1),(v6,v31,v1),(v9,v6,v2)],[0,1,2,3],[(0,137),(0,140),(0,141),(1,24),(1,140)]),
([v18,v0,v1,v2,v3,v4,v5],[(v31,v0,v1),(v6,v31,v1),(v18,v6,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,137)]),
([v18,v0,v1,v6,v2,v3,v4,v5],[(v31,v0,v1),(v6,v31,v1),(v18,v6,v2)],[3,9],[(0,135),(0,137),(1,135)]),
([v0,v1,v74,v8,v3,v4,v5],[(v31,v0,v1),(v74,v31,v2),(v8,v1,v2)],[0,3,5,8,10],[(1,142)]),
([v0,v1,v2,v74,v9,v3,v4,v5],[(v31,v0,v1),(v74,v31,v2),(v9,v1,v74)],[0,1,2,3],[(0,144),(0,145),(0,146),(0,147),(1,143)]),
([v0,v1,v2,0xf200f200f200f200,v74,v3,v4,v5],[(v31,v0,v1),(v74,v31,v2),(0xf200f200f200f200,v74,v3)],[2,4,10],[]),
([0xb0b00000b0b0000,v0,v1,v2,v148,v3,v4,v5],[(v60,v1,v0),(v148,v60,v2),(0xb0b00000b0b0000,v148,v4)],[0,1,2,5,6,8],[(0,148),(1,149),(1,150),(1,151)]),
([v0,v190,v2,v8,v3,v4,v5],[(v60,v1,v0),(v8,v1,v2),(v190,v60,v8)],[0,2,3,9],[(0,152)]),
([v31,v1,v2,v7,v9,v3,v4,v5],[(v31,v0,v1),(v7,v0,v2),(v9,v1,v7)],[0,1,2,3,9],[(0,153),(0,154),(0,155),(0,156),(1,152)]),
([v31,v1,v2,v54,v7,v3,v4,v5],[(v31,v0,v1),(v7,v0,v2),(v54,v7,v3)],[2,10],[]),
([v35,v60,v0,v2,v8,v3,v4,v5],[(v60,v1,v0),(v8,v1,v2),(v35,v8,v4)],[0,1,2,8],[(1,157),(1,158),(1,159),(1,160)]),
([v0,v1,v2,v7,v9,v3,v4,v5],[(v60,v1,v0),(v7,v0,v2),(v9,v60,v7)],[0,3,4,6,8,9,10],[(0,136),(0,161),(0,162)]),
([v31,v51,v1,v2,v3,v4,v5],[(v31,v0,v1),(v8,v1,v2),(v51,v0,v8)],[3,5,9,10],[(1,163)]),
([v31,v51,v1,v2,v8,v3,v4,v5],[(v31,v0,v1),(v8,v1,v2),(v51,v0,v8)],[3,5],[(1,1),(1,136),(1,142)]),
([0x2f222f222f222f22,v0,v1,v2,v3,v4,v5],[(v31,v0,v1),(v14,v2,v3),(0x2f222f222f222f22,v14,v31)],[0,2,3,4,5,6,8,9],[]),
([v31,v47,v1,v2,v3,v4,v5],[(v31,v0,v1),(v14,v2,v3),(v47,v14,v0)],[2,3,4,5,9],[(1,164)]),
([v94,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v75,v0,v3),(v94,v2,v75)],[0,2,3,5,8,9,10],[(0,165)]),
([v0,v1,v2,v54,v7,v75,v4,v5],[(v7,v0,v2),(v75,v0,v3),(v54,v7,v3)],[3,4,10],[(0,165)]),
([v0,v57,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v25,v1,v4),(v57,v25,v0)],[1,5,8],[(0,10),(0,166)]),
([v0,v1,v40,v8,v3,v4,v5],[(v8,v1,v2),(v25,v1,v4),(v40,v25,v2)],[0,3,4,6,9,10],[(0,17),(0,34),(0,168),(1,167)]),
([v16,v41,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v41,v0,v3),(v16,v1,v7)],[2,3,5],[(0,167)]),
([v86,v25,v0,v1,v2,v8,v3,v5],[(v8,v1,v2),(v25,v1,v4),(v86,v8,v4)],[3,6,8],[(0,168)]),
([v16,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v112,v1,v7),(v16,v112,v7)],[0,3,9],[(0,1),(0,136)]),
([v46,v1,v2,v9,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v9,v0,v8)],[0,1,2,3,5,9],[(0,171),(0,172),(0,173),(0,174),(0,176),(0,177),(1,169),(1,170),(1,175)]),
([v46,v1,v2,v8,v9,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v9,v0,v8)],[5,9],[(0,25),(0,179),(1,136),(1,178)]),
([v46,v0,v1,v2,v70,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v70,v8,v3)],[2,3,4,5,9,10],[(0,180)]),
([v50,v46,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8),(v50,v8,v3)],[3],[(0,181)]),
([v16,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9)],[0,2,3,9],[(0,38),(0,39),(0,179),(0,182),(1,183)]),
([v16,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9)],[0,3,5,9],[(0,171),(1,39)]),
([v16,v0,v2,v8,v9,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v16,v1,v9)],[0],[(0,40),(0,172),(0,184),(0,185),(0,187),(0,188),(0,189),(1,183),(1,186)]),
([v16,v0,v2,v7,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v16,v1,v7)],[0,3,9],[(0,29),(0,183)]),
([v18,v0,v1,v7,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v18,v2,v9)],[0,3],[(0,29),(0,41),(0,190),(0,192),(0,193),(0,194),(1,173),(1,184),(1,191)]),
([v0,v1,v2,v54,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v54,v7,v3)],[0,1,2,4,10],[(0,195),(0,196),(0,197)]),
([v35,v0,v1,v2,v9,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v35,v8,v4)],[0,1,2,5,6,8],[(0,34),(0,198),(0,201),(0,202),(0,203),(1,75),(1,199),(1,200)]),
([v0,v1,v2,v73,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v73,v7,v4)],[0,1,5,6,8],[(0,204),(0,206),(0,208),(1,205),(1,207)]),
([v50,v0,v1,v2,v9,v3,v4,v5],[(v8,v1,v2),(v9,v0,v8),(v50,v8,v3)],[0,2,4,5,10],[(0,209),(0,210),(0,211),(0,212),(1,74)]),
([v0,v1,v2,v7,v27,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v27,v9,v3)],[0,1,3,4,5,9],[(0,47),(0,154),(0,206),(1,210)]),
([v0,v1,v2,v7,v27,v9,v4,v5],[(v7,v0,v2),(v9,v1,v7),(v27,v9,v3)],[0,3,9,10],[(0,42),(0,190),(0,213),(0,214),(0,215),(1,176),(1,187)]),
([v29,v0,v1,v2,v8,v3,v5],[(v8,v1,v2),(v9,v0,v8),(v29,v9,v4)],[0,1,2,3,5,8,9],[(0,207),(0,211)]),
([v29,v0,v1,v2,v8,v9,v3,v5],[(v8,v1,v2),(v9,v0,v8),(v29,v9,v4)],[0,1,5,6],[(0,43),(0,188),(0,191),(0,216),(0,218),(1,217)]),
([v0,v1,v2,v7,v34,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v34,v9,v4)],[0,2,3,5,6,9],[(0,48),(0,155),(0,196),(1,202)]),
([v0,v1,v2,v7,v34,v9,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v34,v9,v4)],[0,3,8,9],[(0,44),(0,192),(0,213),(0,219),(1,174),(1,185),(1,216)]),
([v29,v0,v1,v2,v7,v9,v3,v5],[(v7,v0,v2),(v9,v1,v7),(v29,v9,v4)],[0,3,6,9],[(0,45),(0,175),(0,186),(0,193),(0,214),(0,217),(0,220)]),
([v0,v1,v2,v7,v24,v3,v4],[(v7,v0,v2),(v9,v1,v7),(v24,v9,v5)],[0,1,2,3,5,9],[(0,50),(0,156),(0,197),(0,208),(1,203),(1,212)]),
([v0,v1,v2,v7,v24,v9,v3,v4],[(v7,v0,v2),(v9,v1,v7),(v24,v9,v5)],[0,3,9],[(0,46),(0,194),(0,215),(0,219),(0,220),(1,177),(1,189),(1,218)]),
([v0,v149,v2,v8,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8),(v149,v95,v1)],[0,1,2,3,5,9],[(0,222),(1,221)]),
([v0,v92,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v162,v1,v7),(v92,v162,v0)],[0,3,5,9],[(0,223)]),
([v95,v51,v1,v2,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8),(v51,v0,v8)],[2,3,5,9],[(1,169),(1,223),(1,224)]),
([v95,v51,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8),(v51,v0,v8)],[3,5,9],[(1,136),(1,142),(1,178),(1,221)]),
([v95,v0,v1,v2,v70,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8),(v70,v8,v3)],[2,5,9],[(0,225)]),
([v95,v50,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8),(v50,v8,v3)],[2,4,5,10],[(0,226)]),
([v222,v16,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v222,v16,v3)],[2,4,10],[(0,227)]),
([v16,v0,v1,v223,v2,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v223,v16,v3)],[0,1,2,3,4,5,10],[(0,228),(0,229),(0,230),(0,231)]),
([v224,v16,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v224,v16,v4)],[1,3,5,6,8],[(0,232)]),
([v16,v0,v1,0xcdcd0000cdcd0000,v2,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(0xcdcd0000cdcd0000,v16,v4)],[1,6,8],[]),
([v16,v25,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v25,v1,v4)],[3,6,8,9],[(0,233)]),
([v16,v0,v1,v2,v20,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v20,v3,v4)],[3,4],[(0,234),(0,235),(0,236)]),
([v16,v0,v1,v2,v54,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v54,v7,v3)],[2,4,9,10],[(0,227)]),
([v35,v51,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v51,v0,v8),(v35,v8,v4)],[0,1,2],[(1,167),(1,237),(1,238),(1,239)]),
([v16,v0,v1,v2,v73,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7),(v73,v7,v4)],[1,5,6,8,9],[(0,232)]),
([v50,v51,v0,v1,v2,v3,v4,v5],[],[],[(1,240)]),
([v0,v22,v2,v8,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4),(v22,v11,v1)],[0,1,2,3,4,5,6,8,9,10],[(1,241)]),
([v0,v1,v32,v2,v7,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v32,v12,v0)],[3,4,5,9,10],[(0,242)]),
([v0,v1,v19,v8,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4),(v19,v11,v2)],[0,1,3,4,5,6,8,9,10],[(0,244),(1,243)]),
([v0,v1,v2,v56,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v56,v12,v7)],[0,1,2,3,4,5,6,8,9,10],[(0,247),(1,245),(1,246)]),
([v0,v1,v2,v7,v56,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v56,v12,v7)],[2,3,4,5,9],[(0,242),(1,248)]),
([v250,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v250,v12,v7)],[0,1,3,4,5,6,8,9,10],[]),
([v250,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v12,v1,v3),(v250,v12,v7)],[3,5,9],[]),
([v187,v0,v1,v2,v7,v3,v5],[(v7,v0,v2),(v12,v1,v3),(v187,v12,v4)],[0,3,4,5,6,9,10],[]),
([v62,v0,v1,v2,v7,v3,v4],[(v7,v0,v2),(v12,v1,v3),(v62,v12,v5)],[1,3,4,5,6,8,9,10,11],[]),
([v11,v1,v2,v8,v3,v13,v5],[(v8,v1,v2),(v11,v0,v4),(v13,v0,v4)],[0,2,3,4,5,8,9,10],[(1,249)]),
([v44,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v44,v1,v13)],[3,8],[(0,250)]),
([v0,v1,v2,v251,v3,v4,v5],[(v7,v0,v2),(v10,v1,v3),(v251,v7,v10)],[0,1,2,3,4,5,6,8,9,10],[]),
([v0,v1,v2,v251,v7,v3,v4,v5],[(v7,v0,v2),(v10,v1,v3),(v251,v7,v10)],[3,5,10],[]),
([v79,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v79,v8,v13)],[0,1,2,3,4,5,6,8,9,10],[(0,251),(0,253),(1,252)]),
([v79,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v13,v0,v4),(v79,v8,v13)],[8,9],[(0,250),(0,254)]),
([v0,v1,v2,v7,v3,v15,v4],[(v7,v0,v2),(v10,v1,v3),(v15,v10,v5)],[1,2,3,5,6,8,9,10],[(0,255),(0,256),(0,257),(1,258),(1,259)]),
([v0,v96,v2,v8,v3,v4,v5],[(v8,v1,v2),(v17,v0,v4),(v96,v17,v1)],[2,3,5,8,9],[(0,261),(1,260)]),
([v0,v42,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v42,v26,v0)],[3,4,5,9,10],[(0,262)]),
([v0,v1,v2,v48,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7)],[0,3,6,8,9,10],[(0,265),(0,266),(0,267),(0,268),(0,269),(0,270),(1,263),(1,264)]),
([v0,v1,v2,v7,v48,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v48,v26,v7)],[0,3,6,8,9,10],[(0,262),(0,266),(0,272),(1,271)]),
([v0,v1,v2,v252,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v252,v26,v7)],[0,3,5,6,8,9,10],[]),
([v0,v1,v2,v252,v7,v3,v4,v5],[(v7,v0,v2),(v26,v1,v3),(v252,v26,v7)],[3,9],[]),
([v17,v36,v1,v2,v8,v3,v5],[(v8,v1,v2),(v17,v0,v4),(v36,v0,v4)],[0,2,3,4,5,6,9,10],[(1,249)]),
([v17,v0,v1,v2,v97,v8,v3,v5],[(v8,v1,v2),(v17,v0,v4),(v97,v8,v4)],[5,8],[(0,261),(1,266)]),
([v0,v87,v2,v8,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v87,v38,v1)],[0,2,3,4,5,8,9,10],[(0,273)]),
([v0,v1,v88,v8,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v88,v38,v2)],[0,2,3,4,5,8,9],[(0,274)]),
([v0,v1,v2,v71,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3),(v71,v38,v8)],[0,2,3,4,5,6,8,10],[(0,275),(0,276),(0,277),(0,278)]),
([v0,v1,v2,v7,v226,v3,v4,v5],[(v7,v0,v2),(v90,v1,v4),(v226,v90,v7)],[0,1,3,6,9],[(0,281),(1,279),(1,280)]),
([v253,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v90,v1,v4),(v253,v90,v7)],[0,3,4,5,6,8,9,10],[]),
([v253,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v90,v1,v4),(v253,v90,v7)],[3,5,9],[]),
([v0,v1,v40,v7,v3,v4,v5],[(v7,v0,v2),(v25,v1,v4),(v40,v25,v2)],[0,1,3,4,5,6],[(0,34),(0,233),(1,4),(1,282)]),
([v0,v1,v2,v98,v3,v4,v5],[(v7,v0,v2),(v25,v1,v4),(v98,v25,v7)],[0,1,3,4,8,9,10],[(0,284),(1,5),(1,283)]),
([v0,v1,v2,v7,v98,v3,v4,v5],[(v7,v0,v2),(v25,v1,v4),(v98,v25,v7)],[3,6],[(0,286),(1,285)]),
([v196,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v41,v0,v3),(v196,v41,v8)],[0,1,2,3,4,5,6,8,9,10],[(0,6)]),
([v196,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v41,v0,v3),(v196,v41,v8)],[2,3,4,9],[]),
([v0,v1,v2,v7,v183,v3,v4,v5],[(v7,v0,v2),(v54,v7,v3),(v183,v1,v54)],[0,2,3,4,9,10],[(0,227),(0,287)]),
([v0,v1,v2,v54,v166,v4,v5],[(v7,v0,v2),(v54,v7,v3),(v166,v7,v3)],[1,2,3,4,5,9,10],[(1,288),(1,289)]),
([v0,v1,v2,v54,v7,v166,v4,v5],[(v7,v0,v2),(v54,v7,v3),(v166,v7,v3)],[3,4,5,10],[(0,165),(1,290),(1,291)]),
([v0,v1,v2,v54,v73,v3,v4,v5],[(v7,v0,v2),(v54,v7,v3),(v73,v7,v4)],[1,4,5,6,8,10],[]),
([v50,v0,v1,v2,v97,v3,v4,v5],[],[],[(1,292)]),
([v77,v0,v2,v8,v3,v4,v5],[(v8,v1,v2),(v91,v8,v4),(v77,v1,v91)],[0,1,2,3,8,9],[(0,290),(0,293)]),
([v77,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v91,v8,v4),(v77,v1,v91)],[0,3,8,9],[(0,288)]),
([v0,v1,v2,v73,v3,v166,v4,v5],[(v7,v0,v2),(v166,v7,v3),(v73,v7,v4)],[1,5,10],[(1,294)]),
([v50,v0,v1,v2,v3,v4,v91,v5],[(v8,v1,v2),(v91,v8,v4),(v50,v8,v3)],[2,4,6,8,10],[]),
([v86,v0,v1,v2,v70,v3,v4,v5],[(v8,v1,v2),(v86,v8,v4),(v70,v8,v3)],[2,4,6,8,9,10],[]),
([v86,v50,v0,v1,v2,v3,v4,v5],[],[],[(0,295)]),
([v86,v35,v0,v1,v2,v3,v5],[(v8,v1,v2),(v86,v8,v4),(v35,v8,v4)],[0,1,2,3,5,6,8,9],[(0,289),(0,296)]),
([v86,v35,v0,v1,v2,v8,v3,v5],[(v8,v1,v2),(v86,v8,v4),(v35,v8,v4)],[3,6,8,9],[(0,168),(0,291),(0,297)]),
([v0,0xababaaaaababaaaa,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v35,v8,v4),(0xababaaaaababaaaa,v35,v0)],[1,5,8],[(0,15),(0,16),(1,75)]),
([v0,v65,v2,v8,v3,v4,v5],[(v8,v1,v2),(v35,v8,v4),(v65,v35,v1)],[0,2,3,6,9],[(0,16),(0,198),(0,297),(1,237),(1,298),(1,299)]),
([v0,v47,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v105,v7,v3),(v47,v105,v0)],[0,3,4,5],[(1,296)]),
([v0,v1,v2,v7,v156,v3,v5],[(v7,v0,v2),(v105,v7,v3),(v156,v105,v4)],[0,2,3,4,5,6,10],[(0,159),(0,199),(0,238),(1,18)]),
([v0,v1,v2,v7,v136,v3,v4],[(v7,v0,v2),(v105,v7,v3),(v136,v105,v5)],[0,1,2,3,4,5,10],[(0,160),(0,200),(0,239),(0,300),(1,19),(1,301)]),
([v35,v0,v1,v2,v70,v3,v4,v5],[(v8,v1,v2),(v35,v8,v4),(v70,v8,v3)],[0,4,9,10],[(0,302),(0,303),(1,300)]),
([v50,v35,v0,v1,v2,v3,v4,v5],[(v8,v1,v2),(v35,v8,v4),(v50,v8,v3)],[0,2,4,6,8,10],[(0,301),(0,304)]),
([v0,v1,v2,v7,v180,v3,v4,v5],[(v7,v0,v2),(v73,v7,v4),(v180,v1,v73)],[1,3,6,8,9],[(0,12),(0,232),(1,180)]),
([v0,v218,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v50,v8,v3),(v218,v50,v0)],[2,5,10],[(0,13),(0,14),(0,226),(1,74)]),
([v0,v43,v2,v8,v3,v4,v5],[(v8,v1,v2),(v50,v8,v3),(v43,v50,v1)],[0,2,3,4,9,10],[(0,14),(1,305)]),
([v0,v1,v2,v7,v3,v82,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v82,v1,v20)],[1,3],[(0,20),(0,85),(0,235),(0,306),(1,307)]),
([v0,v1,v7,v3,v64,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v64,v2,v20)],[0,1,3,4,5,6],[(0,84),(0,236),(1,21),(1,308)]),
([v0,v1,v2,v3,v99,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v99,v7,v20)],[0,1,3,8,9,10],[(0,85),(0,310),(0,311),(1,22),(1,309)]),
([v0,v1,v2,v7,v3,v99,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v99,v7,v20)],[3,4],[(0,313),(1,312)]),
([v197,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v197,v7,v20)],[0,1,3,5,8,9,10],[(0,23),(0,235),(1,314)]),
([v197,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v20,v3,v4),(v197,v7,v20)],[1,3,4,5],[]),
([v0,v1,v106,v8,v3,v4,v5],[(v8,v1,v2),(v68,v4,v3),(v106,v68,v2)],[0,1,2,3,4,5,8,9],[(0,315)]),
([v0,v1,v2,v83,v3,v4,v5],[(v7,v0,v2),(v52,v3,v4),(v83,v52,v7)],[0,1,2,3,4,6,8,9,10],[(0,317),(0,318),(0,319),(1,316)]),
([v0,v1,v2,v7,v83,v3,v4,v5],[(v7,v0,v2),(v52,v3,v4),(v83,v52,v7)],[0,1,3,4,6,10],[(0,321),(0,322),(1,320)]),
([v0,v1,v2,v254,v3,v4,v5],[(v7,v0,v2),(v52,v3,v4),(v254,v52,v7)],[0,2,3,4,5,8,9,10],[]),
([v0,v1,v2,v254,v7,v3,v4,v5],[(v7,v0,v2),(v52,v3,v4),(v254,v52,v7)],[3,5,10],[]),
([v0,v228,v92,v1,v2,v3,v4,v5],[(v76,v1,v2),(v92,v76,v0),(v228,v92,v4)],[1,3,5,6,8,9],[(0,323)]),
([v229,v0,v1,v149,v2,v3,v4,v5],[(v33,v0,v2),(v149,v33,v1),(v229,v149,v3)],[2,4,10],[(0,324)]),
([v0,v176,v1,v2,v3,v4,v5],[(v76,v1,v2),(v11,v0,v4),(v176,v76,v11)],[0,3,4,5,6,9,10],[(0,325)]),
([v33,v1,v32,v2,v3,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v32,v0,v12)],[0,3,4,5,6,8,9,10],[(0,327),(1,326)]),
([v33,v0,v1,v21,v3,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v21,v12,v2)],[0,3,4,5,6,8,9,10],[(0,329),(0,330),(1,328)]),
([v33,v187,v0,v1,v2,v3,v5],[(v33,v0,v2),(v12,v1,v3),(v187,v12,v4)],[0,3,4,5,6,9,10],[]),
([v33,v62,v0,v1,v2,v3,v4],[(v33,v0,v2),(v12,v1,v3),(v62,v12,v5)],[3,4,5,6,8,9,10,11],[]),
([v33,v0,v12,v2,v10,v4,v5],[(v33,v0,v2),(v12,v1,v3),(v10,v1,v3)],[0,3,5,6,8,9,10],[(0,331)]),
([v0,v1,v2,0xf3f3a2a2f3f3a2a2,v3,v4,v5],[(v76,v1,v2),(v13,v0,v4),(0xf3f3a2a2f3f3a2a2,v76,v13)],[0,1,3,4,5,6,9,10],[]),
([v33,v28,v0,v1,v3,v4,v5],[(v33,v0,v2),(v10,v1,v3),(v28,v2,v10)],[2,3,5,8,10],[(0,332),(0,333)]),
([v33,v0,v1,v2,v3,v15,v4],[(v33,v0,v2),(v10,v1,v3),(v15,v10,v5)],[2,3,5,6,8,9,10],[(0,334),(1,335)]),
([0xace0ace0ace0ace,v0,v1,v2,v3,v4,v5],[(v33,v0,v2),(v26,v1,v3),(0xace0ace0ace0ace,v26,v33)],[0,3,5,6,8,9,10],[]),
([v33,v42,v1,v2,v3,v4,v5],[(v33,v0,v2),(v26,v1,v3),(v42,v26,v0)],[3,5,9,10],[(0,336)]),
([v17,v76,v36,v1,v2,v3,v5],[(v76,v1,v2),(v17,v0,v4),(v36,v0,v4)],[0,3,4,5,6,9,10],[(1,331)]),
([v0,v1,v87,v2,v71,v3,v4,v5],[(v38,v0,v3),(v87,v38,v1),(v71,v87,v2)],[0,3,4,10],[(0,276),(0,337),(0,338)]),
([v117,v0,v1,v2,v3,v4,v5],[(v38,v0,v3),(v87,v38,v1),(v117,v87,v2)],[0,2,3,4,5,6,8,9],[(0,276)]),
([v117,v0,v1,v87,v2,v3,v4,v5],[(v38,v0,v3),(v87,v38,v1),(v117,v87,v2)],[3,5],[(0,273),(0,276)]),
([v0,v1,v2,v88,v71,v3,v4,v5],[(v38,v0,v3),(v88,v38,v2),(v71,v1,v88)],[0,2,4,9,10],[(0,275),(0,339),(0,340)]),
([v118,v0,v1,v2,v3,v4,v5],[(v38,v0,v3),(v88,v38,v2),(v118,v1,v88)],[0,2,3,4,5,6,8],[(0,275)]),
([v118,v0,v1,v2,v88,v3,v4,v5],[(v38,v0,v3),(v88,v38,v2),(v118,v1,v88)],[2,3,5,9],[(0,274),(0,275)]),
([v119,v0,v2,v3,v5],[(v90,v1,v4),(v120,v1,v4),(v119,v90,v120)],[0,1,2,3],[(0,341),(0,342)]),
([0xf000c000f000c00,0xf0f0c0c0f0f0c0c,v0,v1,v2,v3,v4,v5],[(v120,v1,v4),(0xf0f0c0c0f0f0c0c,v2,v120),(0xf000c000f000c00,0xf0f0c0c0f0f0c0c,v3)],[0,2,4,6,9,10],[(1,343),(1,344)]),
([v94,v0,v1,v2,0xf0f50000f0f50000,v3,v4,v5],[(v75,v0,v3),(v94,v2,v75),(0xf0f50000f0f50000,v94,v4)],[1,6,8],[]),
([v0,v1,0xf0a0ffaaf0a0ffaa,v2,v3,v4,v5],[(v75,v0,v3),(v30,v2,v4),(0xf0a0ffaaf0a0ffaa,v30,v75)],[0,1,2,3,4,5,6,9,10],[]),
([v0,v57,v1,v2,v98,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(v98,v57,v2)],[3],[(0,284),(1,345)]),
([v100,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(v100,v57,v2)],[0,1,2,3,4,5,6,9,10],[(0,33),(0,284),(1,252)]),
([v100,v0,v57,v1,v2,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(v100,v57,v2)],[3],[(0,284)]),
([v0,0xbb00aa00bb00aa00,v57,v1,v2,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(0xbb00aa00bb00aa00,v57,v3)],[2,4,10],[]),
([v231,v0,v1,v122,v2,v3,v4,v5],[(v41,v0,v3),(v122,v41,v1),(v231,v122,v4)],[0,1,3,5,6,8,10],[(0,346),(1,347),(1,348)]),
([v14,v0,v57,v1,v2,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0),(v14,v2,v3)],[3,4,10],[(0,349),(0,350)]),
([v0,v1,v2,v40,v98,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2),(v98,v0,v40)],[1,5],[(0,351),(1,283)]),
([v133,v0,v1,v2,v3,v4,v5],[(v41,v0,v3),(v103,v41,v2),(v133,v1,v103)],[0,2,3,4,6,8],[(0,283)]),
([v133,v0,v1,v2,v103,v3,v4,v5],[(v41,v0,v3),(v103,v41,v2),(v133,v1,v103)],[2,3,4,9],[(0,282),(0,283)]),
([v25,v0,v1,v2,v103,v3,v4,v5],[(v41,v0,v3),(v103,v41,v2),(v25,v1,v4)],[1,3,6,8],[(0,352),(1,353)]),
([v14,v0,v1,v40,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2),(v14,v2,v3)],[0,2,3,4,6,10],[(0,354)]),
([v0,v1,v2,0xf300f000f300f000,v40,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2),(0xf300f000f300f000,v40,v3)],[2,3,4,10],[]),
([0xa0f00000a0f0000,v0,v1,v2,v103,v3,v4,v5],[(v41,v0,v3),(v103,v41,v2),(0xa0f00000a0f0000,v103,v4)],[1,3,5,6,8,10],[(1,355)]),
([v232,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v41,v0,v3),(v232,v25,v41)],[0,3,5,8,9,10],[(0,352),(0,356)]),
([0x3f330f003f330f00,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v14,v2,v3),(0x3f330f003f330f00,v14,v25)],[0,2,3,4,5,6,8,9,10],[(0,349),(1,357)]),
([v25,v0,v47,v1,v2,v3,v4,v5],[(v25,v1,v4),(v14,v2,v3),(v47,v14,v0)],[1,3,6],[(0,349),(0,354),(1,358)]),
([v0,v22,v2,v66,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v66,v22,v2)],[0,1,3,4,5,6,8,10],[(0,360),(1,359)]),
([v80,v1,v32,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v80,v32,v2)],[0,3,4,5,6,8,9,10],[(0,359)]),
([v0,v110,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v110,v22,v3)],[0,3,4,5,6,8,9,10],[(0,361),(0,362),(0,363),(0,365),(0,366),(1,364)]),
([v0,v22,v2,v3,v137,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v137,v22,v3)],[0,3,4,5,6,8,10],[(0,365),(0,366),(0,367),(0,368),(0,369)]),
([v199,v1,v32,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v199,v32,v4)],[0,3,4,5,6,8,9,10],[(0,371),(0,372),(1,370)]),
([v173,v0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v173,v22,v3)],[0,3,4,5,6,8,10],[(0,373),(0,374),(1,371),(1,372)]),
([v0,v22,v2,v3,v61,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v61,v2,v3)],[0,3,5,6,8,10],[(0,360),(0,374),(0,375),(0,376)]),
([v14,v0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v14,v2,v3)],[0,3,4,5,6,8,10],[(0,367),(0,377),(0,378)]),
([v11,v1,v32,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v11,v0,v4)],[0,1,3,4,5,6,8,9,10],[(0,361),(1,379),(1,380),(1,381),(1,382)]),
([v0,v22,v2,v3,v10,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v10,v1,v3)],[0,3,4,5,6,8,9,10],[(0,383),(0,384),(0,385),(0,386)]),
([v17,v1,v32,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v17,v0,v4)],[0,3,4,5,6,8,9,10],[(0,389),(1,387),(1,388)]),
([v39,v0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v39,v1,v3)],[0,2,3,4,5,6,8,9,10],[]),
([v0,v1,v32,v2,v56,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v56,v32,v2)],[3,4,10],[(0,247),(0,327),(1,390)]),
([v80,v0,v1,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v80,v32,v2)],[0,3,4,5,6,8,9],[(0,242),(0,247)]),
([v80,v0,v1,v32,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0),(v80,v32,v2)],[3,9],[(0,241),(0,247)]),
([v0,v1,v110,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v110,v22,v3)],[0,2,3,4,5,6,9,10],[(0,383),(1,391),(1,392)]),
([v173,v0,v1,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v173,v22,v3)],[2,4,10],[(0,393),(1,389)]),
([v14,v0,v1,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1),(v14,v2,v3)],[3,4,6,8,9,10],[(0,384),(0,394),(1,395),(1,396)]),
([v124,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v124,v0,v21)],[0,3,4,5,6,8,9],[(0,401),(0,402),(1,397),(1,398),(1,399),(1,400)]),
([v0,v1,v19,v66,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v66,v1,v19)],[0,1,2,4,5,6,8,9,10],[(0,397),(0,403),(1,402)]),
([v113,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v113,v0,v21)],[0,4,5,6,8,9,10],[(0,404),(0,405),(1,328)]),
([v69,v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v69,v1,v19)],[0,2,3,4,5,6,9,10],[(0,328),(0,403),(1,404),(1,405)]),
([v11,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v11,v0,v4)],[0,4,5,6,8,9,10],[(0,380),(0,406),(0,411),(1,407),(1,408),(1,409),(1,410)]),
([v0,v1,v19,v3,v10,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3)],[0,4,5,6,8,9,10],[(0,413),(0,415),(1,411),(1,412),(1,414)]),
([v17,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v17,v0,v4)],[0,4,5,8,9,10],[(0,418),(1,416),(1,417)]),
([v39,v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v39,v1,v3)],[0,2,4,5,6,8,9,10],[(1,418)]),
([v0,v1,v152,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v152,v19,v3)],[0,3,4,5,6,9,10],[(0,419),(0,420)]),
([v0,v1,v19,v3,v164,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v164,v19,v3)],[0,2,4,5,6,8,9,10],[(0,420)]),
([v125,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v125,v21,v4)],[0,1,3,4,5,6,8,9],[(0,422),(0,423),(1,421)]),
([v84,v0,v1,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v84,v21,v4)],[0,4,5,6,8,9,10],[(0,412),(0,422),(0,423),(0,424)]),
([v124,v0,v1,v2,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v124,v0,v21)],[0,3,4,5,9],[(0,243),(0,428),(1,245),(1,425),(1,426),(1,427)]),
([v0,v1,v2,v19,v66,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v66,v1,v19)],[3,6,8,9],[(0,246),(1,428),(1,429)]),
([v113,v0,v1,v2,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v113,v0,v21)],[3,5],[(0,430),(0,431),(0,432)]),
([v69,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v69,v1,v19)],[0,2,3,4,5,6,9,10],[(0,246),(1,329),(1,431)]),
([v69,v0,v1,v2,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v69,v1,v19)],[3,5,9],[(0,244),(0,246),(1,330),(1,432)]),
([v11,v0,v1,v2,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v11,v0,v4)],[0,3,4,5,9,10],[(0,381),(0,433),(0,434),(0,437),(1,435),(1,436)]),
([v0,v1,v2,v19,v3,v10,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v10,v1,v3)],[0,3,4,6,8,10],[(0,438),(0,439),(0,440),(0,442),(1,437),(1,441)]),
([v17,v0,v1,v2,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v17,v0,v4)],[3,5],[(0,443),(0,446),(1,444),(1,445)]),
([v39,v0,v1,v2,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v39,v1,v3)],[2,3,4,10],[(1,446)]),
([v0,v1,v19,v3,v61,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v61,v2,v3)],[0,2,3,4,5,6,8,9,10],[(0,447)]),
([v14,v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v14,v2,v3)],[0,3,4,5,6,8,9,10],[(0,438),(1,448),(1,449)]),
([v0,v1,v2,v152,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v152,v19,v3)],[3,4,5,10],[(0,447),(0,450)]),
([v0,v1,v2,v19,v3,v164,v4,v5],[(v11,v0,v4),(v19,v11,v2),(v164,v19,v3)],[3,4,10],[(0,450),(0,451)]),
([v125,v0,v1,v2,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v125,v21,v4)],[0,3,4,6,8,9],[(0,449),(0,453),(1,452)]),
([v84,v0,v1,v2,v21,v3,v4,v5],[(v12,v1,v3),(v21,v12,v2),(v84,v21,v4)],[3,4,6,8,10],[(0,453),(0,454)]),
([v62,v11,v0,v1,v2,v3,v4],[(v12,v1,v3),(v62,v12,v5),(v11,v0,v4)],[1,3,4,5,6,8,9,10,11],[(0,382),(0,410),(0,436),(0,455),(0,456)]),
([v62,v0,v1,v2,v3,v4,v13],[(v12,v1,v3),(v62,v12,v5),(v13,v0,v4)],[3,4,5,6,8,9,10,11],[(0,456),(0,457),(1,458),(1,459)]),
([v17,v62,v0,v1,v2,v3,v4],[(v12,v1,v3),(v62,v12,v5),(v17,v0,v4)],[3,4,5,8,9,10,11],[(0,460),(0,461)]),
([v39,v157,v0,v1,v2,v3,v4],[(v11,v0,v4),(v157,v11,v5),(v39,v1,v3)],[2,3,4,5,6,7,8,9,10],[(1,461)]),
([v62,v0,v1,v2,v3,v4,v45],[(v12,v1,v3),(v62,v12,v5),(v45,v2,v4)],[1,3,4,5,8,9,10,11],[]),
([v14,v157,v0,v1,v2,v3,v4],[(v11,v0,v4),(v157,v11,v5),(v14,v2,v3)],[3,4,5,6,7,8,9,10],[(0,458),(1,462)]),
([v49,v0,v2,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v49,v12,v10)],[0,2,3],[(0,249),(0,331),(0,463),(0,464),(0,465),(0,467),(1,466),(1,468)]),
([v11,v0,v12,v2,v10,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v11,v0,v4)],[0,3,5,6,8,9,10],[(0,463),(0,469),(0,471),(1,411),(1,437),(1,456),(1,470)]),
([v11,v1,v2,v3,v10,v13,v5],[(v11,v0,v4),(v13,v0,v4),(v10,v1,v3)],[0,3,4,5,8,9,10],[(0,471),(0,472),(0,473),(0,474),(1,464)]),
([v17,v0,v12,v2,v10,v4,v5],[(v12,v1,v3),(v10,v1,v3),(v17,v0,v4)],[0,3,5,8,9,10],[(0,465),(0,476),(1,475)]),
([v39,v11,v1,v2,v3,v13,v5],[(v11,v0,v4),(v13,v0,v4),(v39,v1,v3)],[0,2,3,4,5,8,9,10],[(0,466),(1,476)]),
([v11,v1,v2,v3,v61,v13,v5],[(v11,v0,v4),(v13,v0,v4),(v61,v2,v3)],[0,2,3,5,8,9,10],[(1,467)]),
([v14,v11,v1,v2,v3,v13,v5],[(v11,v0,v4),(v13,v0,v4),(v14,v2,v3)],[0,3,4,5,8,9,10],[(0,468),(0,472),(0,477)]),
([v0,v1,v53,v2,v3,v4,v5],[(v11,v0,v4),(v12,v1,v3),(v53,v11,v12)],[0,3,4,5,6,8,9,10],[(0,406),(0,434),(0,455),(0,469),(0,478),(0,479),(0,480),(0,481),(1,469)]),
([v138,v0,v1,v2,v3,v4,v5],[(v12,v1,v3),(v13,v0,v4),(v138,v12,v13)],[0,3,4,5,6,8,9,10],[(0,441),(0,457),(0,470),(0,482),(0,483),(1,484)]),
([v14,v11,v0,v1,v2,v10,v4,v5],[(v11,v0,v4),(v10,v1,v3),(v14,v2,v3)],[0,3,4,6,9,10],[(0,384),(0,438),(0,458),(0,472),(0,484),(0,485),(0,486)]),
([v28,v11,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v10,v1,v3),(v28,v2,v10)],[0,3,4,5,9,10],[(0,385),(0,439),(0,459),(0,473),(0,487),(1,441)]),
([v11,v0,v1,v2,v3,v15,v4],[(v11,v0,v4),(v10,v1,v3),(v15,v10,v5)],[1,2,3,4,5,6,8,9,10],[(0,386),(0,415),(0,442),(0,474),(0,486),(0,488),(0,489),(1,457),(1,490)]),
([v0,v185,v1,v2,v3,v4,v5],[(v11,v0,v4),(v26,v1,v3),(v185,v26,v11)],[0,3,5,6,9,10],[(0,444),(0,491),(0,492)]),
([v11,v0,v1,v2,v63,v3,v4,v5],[(v11,v0,v4),(v26,v1,v3),(v63,v26,v2)],[0,3,4,5,6,8,9,10],[(0,388),(0,444),(0,475),(1,443),(1,460),(1,493)]),
([v17,v36,v12,v1,v2,v3,v5],[(v12,v1,v3),(v17,v0,v4),(v36,v0,v4)],[0,1,3,4,5,6,9,10],[(0,418),(0,446),(0,461),(0,476),(1,463),(1,492)]),
([0x33ff30f033ff30f0,v0,v1,v2,v3,v4,v5],[(v12,v1,v3),(v45,v2,v4),(0x33ff30f033ff30f0,v12,v45)],[0,1,3,4,5,6,8,9,10],[]),
([v0,v178,v1,v2,v3,v4,v5],[(v11,v0,v4),(v14,v2,v3),(v178,v14,v11)],[0,3,4,5,6,8,9,10],[(0,485),(0,494),(1,395)]),
([v11,v0,v1,v43,v2,v3,v4,v5],[(v11,v0,v4),(v14,v2,v3),(v43,v14,v1)],[0,3,4,5,9,10],[(0,394),(0,477),(1,395),(1,448),(1,462),(1,495)]),
([v0,v1,v2,v144,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v144,v44,v2)],[0,1,3,4,5,8,9,10],[(0,250),(0,253)]),
([v44,v0,v1,v2,v144,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v144,v44,v2)],[3],[(0,253)]),
([v79,v44,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v79,v44,v2)],[3],[(0,253),(0,496)]),
([v237,v44,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v237,v44,v3)],[2,4,10],[(0,497)]),
([v44,v0,v238,v1,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v238,v44,v3)],[0,2,3,4,5,8,9,10],[(0,498),(0,499),(0,500)]),
([v14,v44,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13),(v14,v2,v3)],[3,4,10],[(0,501),(0,502)]),
([v14,0x5544554455445544,v0,v1,v2,v4,v5],[(v10,v1,v3),(0x5544554455445544,v0,v10),(v14,v2,v3)],[0,2,3,4,6,10],[]),
([v14,v0,v1,v2,v10,v4,v13,v5],[(v10,v1,v3),(v13,v0,v4),(v14,v2,v3)],[0,10],[(0,472),(0,503),(0,504),(0,505)]),
([v28,v0,v1,v2,v3,v4,v13,v5],[(v10,v1,v3),(v13,v0,v4),(v28,v2,v10)],[0,3,8],[(0,473),(0,506),(0,508),(0,509),(1,507)]),
([v0,v1,v2,v3,v140,v4,v5],[(v10,v1,v3),(v13,v0,v4),(v140,v10,v13)],[0,3,4,5,6,8,9,10],[(0,503),(0,506),(0,510),(0,511),(0,512),(1,503)]),
([v0,v1,v2,v3,v15,v4,v13],[(v10,v1,v3),(v13,v0,v4),(v15,v10,v5)],[2,3,5,6,8,9,10],[(0,474),(0,504),(0,511),(0,514),(1,505),(1,509),(1,513),(1,515),(1,516)]),
([v0,v1,v2,v37,v3,v10,v4,v5],[(v10,v1,v3),(v17,v0,v4),(v37,v17,v2)],[0,6,8,10],[(0,517),(0,519),(1,475),(1,518)]),
([v0,v1,v2,v3,0xff33aa22ff33aa22,v4,v5],[(v13,v0,v4),(v26,v1,v3),(0xff33aa22ff33aa22,v26,v13)],[0,3,5,6,8,9,10],[(0,518),(0,520),(1,521)]),
([v17,v36,v1,v2,v3,v10,v5],[(v10,v1,v3),(v17,v0,v4),(v36,v0,v4)],[0,3,4,5,6,9,10],[(0,476),(0,522),(0,523),(0,524),(1,464)]),
([v17,v14,v0,v1,v2,v10,v4,v5],[(v10,v1,v3),(v17,v0,v4),(v14,v2,v3)],[6,10],[(0,521),(0,522),(0,525)]),
([v17,v28,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v17,v0,v4),(v28,v2,v10)],[3,5],[(0,523),(0,526),(1,518)]),
([v17,v0,v1,v2,v3,v15,v4],[(v10,v1,v3),(v17,v0,v4),(v15,v10,v5)],[2,3,5,8,9,10],[(0,519),(0,524),(0,525),(0,527),(0,529),(1,528)]),
([v14,v36,v0,v1,v2,v10,v4,v5],[(v10,v1,v3),(v36,v0,v4),(v14,v2,v3)],[6,10],[(0,522),(0,530)]),
([v28,v36,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v36,v0,v4),(v28,v2,v10)],[1,3,6],[(0,523)]),
([v39,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v39,v1,v3),(v23,v13,v5)],[1,2,3,4,5,8,9,10],[(1,524),(1,530)]),
([v14,v0,v1,v2,v15,v4],[(v10,v1,v3),(v14,v2,v3),(v15,v10,v5)],[0,2,3,4,9,10],[(0,486),(0,504),(0,525),(0,530),(0,531),(0,532),(0,534),(0,535),(0,536),(0,537),(1,533),(1,538)]),
([v201,v28,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v201,v28,v0)],[5],[(0,540),(0,541),(1,539)]),
([v0,v129,v1,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v129,v28,v0)],[0,1,2,3,5,6,8,10],[(0,332),(1,251),(1,539)]),
([v28,v0,v129,v1,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v129,v28,v0)],[3,5,10],[(0,333),(0,541),(1,251)]),
([v79,v165,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v165,v2,v13),(v79,v165,v1)],[9],[(0,251),(0,543),(1,542)]),
([v28,v240,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v240,v28,v0)],[0,3,5,10],[(0,252),(0,544),(0,545),(1,543)]),
([0xf000a000f000a00,v165,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v165,v2,v13),(0xf000a000f000a00,v165,v3)],[4,10],[(0,547),(1,546)]),
([v28,v0,v1,v2,v3,v4,v241,v5],[(v10,v1,v3),(v28,v2,v10),(v241,v28,v4)],[0,3,6,8,10],[(0,548),(1,547)]),
([v202,v28,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v202,v28,v4)],[6,8],[(0,549),(0,550)]),
([v28,v0,v1,v2,v242,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10),(v242,v28,v4)],[3,6,8,10],[(0,550),(0,551)]),
([v28,v0,v1,v3,v4,v45,v5],[(v10,v1,v3),(v28,v2,v10),(v45,v2,v4)],[0,1,2,3,5,6,8,10],[(0,551)]),
([v0,v1,v2,v3,0xffccf0c0ffccf0c0,v4,v5],[(v10,v1,v3),(v45,v2,v4),(0xffccf0c0ffccf0c0,v10,v45)],[0,1,2,3,4,5,8,9,10],[]),
([v0,v1,v2,v3,v15,v4,v45],[(v10,v1,v3),(v45,v2,v4),(v15,v10,v5)],[1,2,3,5,8,9,10],[(0,553),(1,552),(1,554)]),
([v0,v55,v1,v2,v3,v10,v4,v5],[(v10,v1,v3),(v30,v2,v4),(v55,v30,v0)],[0,10],[(0,555),(0,556),(1,477),(1,502)]),
([v0,v1,v243,v2,v3,v4,v5],[(v10,v1,v3),(v30,v2,v4),(v243,v30,v10)],[0,2,3,4,5,6,8,9,10],[(0,557),(1,502)]),
([v14,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v14,v2,v3),(v23,v13,v5)],[1,3,4,5,8,9,10],[(0,505),(1,556),(1,558),(1,559),(1,560)]),
([v93,v0,v1,v2,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v93,v0,v15)],[1,3,4,5,6,8,9,10],[(0,531),(0,561),(0,562),(0,564),(0,566),(0,567),(1,563),(1,565)]),
([v0,v1,v2,v3,v15,v78,v4],[(v10,v1,v3),(v15,v10,v5),(v78,v0,v15)],[0,1,2,3,5,6,8,9,10],[(0,257),(0,532),(0,566),(0,567),(0,569),(0,570),(0,571),(0,574),(0,575),(1,563),(1,568),(1,572),(1,573)]),
([v171,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v171,v1,v23)],[0,1,2,3,4,5,8,9,10],[(0,533),(0,576),(0,578),(0,579),(1,577)]),
([v111,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v111,v1,v23)],[2,3,4,5,6,8,9,10],[(0,259),(0,568),(0,578),(0,579),(0,580),(0,581),(1,534),(1,577),(1,582)]),
([v0,v1,v2,v3,v15,v145,v4],[(v10,v1,v3),(v15,v10,v5),(v145,v2,v15)],[0,2,3,4,5,6,8,9,10],[(0,255),(0,257),(0,569),(0,584),(1,581),(1,583),(1,585),(1,586)]),
([v139,v0,v1,v2,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v139,v2,v15)],[0,3,4,5,6,8,9,10],[(0,570),(0,582),(0,584),(0,587),(0,588),(1,259),(1,589)]),
([v0,v1,v2,v121,v3,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v121,v23,v3)],[2,3,4,5,6,8,9,10],[(0,552),(0,585),(0,590),(0,592),(0,593),(1,529),(1,535),(1,588),(1,591)]),
([v0,v1,v2,v3,v15,v4,v179],[(v10,v1,v3),(v15,v10,v5),(v179,v15,v4)],[0,1,2,3,5,6,8,9,10],[(0,536),(1,592),(1,593),(1,594)]),
([v186,v0,v1,v2,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5),(v186,v15,v4)],[1,3,4,5,6,8,9,10],[(0,537),(0,560),(0,595),(1,596),(1,597)]),
([v101,v0,v1,v2,v3,v4,v23],[(v13,v0,v4),(v23,v13,v5),(v101,v23,v3)],[0,1,2,3,4,5,8,9,10],[(0,513),(0,538),(0,586),(0,589),(0,596),(0,597),(0,599),(1,598)]),
([v0,v42,v1,v2,v48,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(v48,v42,v2)],[0,1,3,4,10],[(0,265),(0,601),(0,602),(1,600)]),
([v81,v0,v1,v2,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(v81,v42,v2)],[0,3,5,6,8,9,10],[(0,262),(0,265),(0,603)]),
([v81,v0,v42,v1,v2,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(v81,v42,v2)],[3,9],[(0,260),(0,265)]),
([v0,0xaaee0000aaee0000,v42,v1,v2,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0),(0xaaee0000aaee0000,v42,v4)],[1,5,6,8,9,10],[]),
([v244,v0,v1,v96,v2,v3,v4,v5],[(v17,v0,v4),(v96,v17,v1),(v244,v96,v3)],[2,4,10],[(0,604)]),
([v14,v0,v1,v96,v2,v3,v4,v5],[(v17,v0,v4),(v96,v17,v1),(v14,v2,v3)],[3,4,6,8,10],[(1,603),(1,605),(1,606)]),
([0xa0a8a0a8a0a8a0a8,v0,v1,v2,v63,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(0xa0a8a0a8a0a8a0a8,v0,v63)],[3,5,9,10],[(0,607),(1,263)]),
([v0,v1,v2,v37,v150,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v150,v1,v37)],[0,6,8,9],[(0,264),(0,609),(0,611),(1,607),(1,608),(1,610)]),
([v203,v0,v1,v2,v63,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(v203,v0,v63)],[5],[(0,613),(0,614),(1,612)]),
([v132,v0,v1,v2,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v132,v1,v37)],[0,3,4,5,8,10],[(0,264),(1,613)]),
([v132,v0,v1,v2,v37,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v132,v1,v37)],[9],[(0,264),(1,614)]),
([v17,v0,v1,v2,v63,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(v17,v0,v4)],[5,6,8],[(0,615),(0,617),(1,616)]),
([v39,v0,v1,v2,v37,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v39,v1,v3)],[2,4],[(1,617)]),
([v0,v1,0xf000fa00f000fa00,v2,v37,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(0xf000fa00f000fa00,v37,v3)],[4,10],[(0,618)]),
([v0,v1,v2,v37,v3,v204,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v204,v37,v3)],[4,10],[(0,618),(0,619)]),
([0xf0fc0000f0fc,v0,v1,v2,v63,v3,v4,v5],[(v26,v1,v3),(v63,v26,v2),(0xf0fc0000f0fc,v63,v4)],[3,6,8,10],[(0,620)]),
([v245,v0,v1,v2,v37,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2),(v245,v37,v3)],[0,4,6,8,10],[(0,621),(0,622),(1,620)]),
([v17,v26,v39,v0,v2,v4,v5],[(v26,v1,v3),(v39,v1,v3),(v17,v0,v4)],[0,3,4,5,8,9],[(0,465),(0,623),(1,617)]),
([v17,v39,v36,v1,v2,v3,v5],[(v17,v0,v4),(v36,v0,v4),(v39,v1,v3)],[0,2,3,4,5,6,9,10],[(0,466),(0,623)]),
([v17,v36,v1,v2,v3,v61,v5],[(v17,v0,v4),(v36,v0,v4),(v61,v2,v3)],[0,2,3,5,6,9,10],[(1,467)]),
([v17,v14,v36,v1,v2,v3,v5],[(v17,v0,v4),(v36,v0,v4),(v14,v2,v3)],[0,3,4,5,6,9,10],[(0,468),(0,522),(0,624)]),
([0xccaaee00ccaaee,v0,v1,v2,v3,v4,v5],[(v17,v0,v4),(v26,v1,v3),(0xccaaee00ccaaee,v17,v26)],[0,3,5,8,9,10],[(0,615),(0,625)]),
([v0,v1,v2,v3,0xff33f030ff33f030,v4,v5],[(v26,v1,v3),(v45,v2,v4),(0xff33f030ff33f030,v26,v45)],[0,1,3,5,9,10],[]),
([0xf00afaa0f00afaa,v0,v1,v2,v3,v4,v5],[(v17,v0,v4),(v14,v2,v3),(0xf00afaa0f00afaa,v17,v14)],[0,3,5,8,9],[(0,626),(1,605)]),
([v17,v0,v1,v43,v2,v3,v4,v5],[(v17,v0,v4),(v14,v2,v3),(v43,v14,v1)],[5],[(0,624),(1,605),(1,627)]),
([v39,v0,v55,v1,v2,v3,v4,v5],[(v39,v1,v3),(v30,v2,v4),(v55,v30,v0)],[2,4],[(1,624)]),
([v246,v77,v0,v1,v2,v3,v4,v5],[(v45,v2,v4),(v77,v1,v45),(v246,v77,v3)],[2,4,10],[(0,628)]),
([v77,v0,0xcc00cf00cc00cf00,v1,v2,v3,v4,v5],[(v45,v2,v4),(v77,v1,v45),(0xcc00cf00cc00cf00,v77,v3)],[2,3,4,8,9,10],[(0,629)]),
([v0,v1,v2,v3,v82,v45,v5],[(v45,v2,v4),(v20,v4,v3),(v82,v1,v20)],[0,1,3,4,8,10],[(1,630)]),
([v0,v47,v1,v85,v2,v3,v4,v5],[(v14,v2,v3),(v47,v14,v0),(v85,v47,v1)],[2,3,9,10],[(0,118),(1,631)]),
([v108,v0,v1,v2,v3,v4,v5],[(v14,v2,v3),(v47,v14,v0),(v108,v47,v1)],[0,2,3,4,5,6,8],[(0,115),(0,118)]),
([v108,v0,v47,v1,v2,v3,v4,v5],[(v14,v2,v3),(v47,v14,v0),(v108,v47,v1)],[2,4,5,9],[(0,114),(0,118)]),
([v0,v247,v47,v1,v2,v3,v4,v5],[(v14,v2,v3),(v47,v14,v0),(v247,v47,v4)],[0,1,3,4,5,6,8],[(0,632),(1,633)]),
([v248,v0,v1,v65,v2,v3,v4,v5],[(v30,v2,v4),(v65,v30,v1),(v248,v65,v3)],[2,4,10],[(0,634)]),
([0x8a888a888a888a88,v0,v1,v43,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(0x8a888a888a888a88,v43,v0)],[5],[(0,635),(1,116)]),
([v0,v55,v1,v131,v2,v3,v4,v5],[(v30,v2,v4),(v55,v30,v0),(v131,v55,v1)],[3,8,9],[(0,117),(1,635),(1,636)]),
([v123,v0,v1,v2,v3,v4,v5],[(v30,v2,v4),(v55,v30,v0),(v123,v55,v1)],[0,1,3,4,5,6,10],[(0,117),(1,637)]),
([v123,v0,v55,v1,v2,v3,v4,v5],[(v30,v2,v4),(v55,v30,v0),(v123,v55,v1)],[9],[(0,117),(1,638)]),
([v205,v0,v1,v43,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(v205,v43,v0)],[0,3,5,10],[(0,637),(0,638),(0,639),(1,640)]),
([v0,0xaf00aa00af00aa00,v55,v1,v2,v3,v4,v5],[(v30,v2,v4),(v55,v30,v0),(0xaf00aa00af00aa00,v55,v3)],[4,10],[(0,641)]),
([v0,v55,v1,v2,v3,0xffafffaaffafffaa,v4,v5],[(v30,v2,v4),(v55,v30,v0),(0xffafffaaffafffaa,v55,v3)],[0,3,4,8,10],[(0,641),(0,643),(1,642)]),
([0xcfcc0000cfcc,v0,v1,v43,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(0xcfcc0000cfcc,v43,v4)],[6,8],[(0,644)]),
([v206,v0,v1,v43,v2,v3,v4,v5],[(v14,v2,v3),(v43,v14,v1),(v206,v43,v4)],[3,6,8,10],[(0,644),(0,645)]),
([v14,v0,v114,v1,v2,v4,v5],[(v14,v2,v3),(v52,v3,v4),(v114,v52,v0)],[0,2,3,4,6,8,10],[]),
([v0,v1,v2,v3,v58,v59,v4,v5],[(v20,v3,v4),(v58,v0,v20),(v59,v1,v58)],[0,2,3,8,9,10],[(0,122),(0,647),(0,648),(1,646)]),
([v116,v0,v1,v2,v3,v4,v5],[(v20,v3,v4),(v58,v0,v20),(v116,v1,v58)],[0,1,2,3,4,5,6],[(0,122),(0,307),(0,649)]),
([v116,v0,v1,v2,v3,v58,v4,v5],[(v20,v3,v4),(v58,v0,v20),(v116,v1,v58)],[2,4,5,9],[(0,120),(0,122)]),
([v0,v1,v2,v3,v58,v99,v4,v5],[(v20,v3,v4),(v58,v0,v20),(v99,v2,v58)],[3],[(0,311),(1,650)]),
([v89,v0,v1,v2,v3,v4,v5],[(v20,v3,v4),(v58,v0,v20),(v89,v2,v58)],[0,1,2,3,4,5,6,9,10],[(0,121),(0,307),(0,311),(1,651)]),
([v89,v0,v1,v2,v3,v58,v4,v5],[(v20,v3,v4),(v58,v0,v20),(v89,v2,v58)],[3],[(0,311),(0,630)]),
([v0,v1,v2,v3,v64,v99,v4,v5],[(v20,v3,v4),(v64,v2,v20),(v99,v0,v64)],[1,5],[(0,652),(1,309)]),
([v134,v0,v1,v2,v3,v4,v5],[(v20,v4,v3),(v64,v2,v20),(v134,v1,v64)],[0,2,3,4,5,6],[(0,134),(0,309),(0,653)]),
([v134,v0,v1,v2,v3,v64,v4,v5],[(v20,v4,v3),(v64,v2,v20),(v134,v1,v64)],[2,3,4,9],[(0,308),(0,309)]),
([v0,v114,v1,v2,v83,v3,v4,v5],[(v52,v4,v3),(v114,v52,v0),(v83,v114,v2)],[0,3,4,8],[(0,317),(0,655),(1,654)]),
([v128,v0,v1,v2,v3,v4,v5],[(v52,v4,v3),(v114,v52,v0),(v128,v114,v2)],[0,1,2,3,5,6,9,10],[(0,317)]),
([v128,v0,v114,v1,v2,v3,v4,v5],[(v52,v4,v3),(v114,v52,v0),(v128,v114,v2)],[3],[(0,317)]),
([v0,v1,v2,v106,v151,v3,v4,v5],[(v68,v3,v4),(v106,v68,v2),(v151,v1,v106)],[0,2,4,9,10],[(0,316),(0,657),(1,656)]),
([v135,v0,v1,v2,v3,v4,v5],[(v68,v3,v4),(v106,v68,v2),(v135,v1,v106)],[0,1,2,3,4,5,8],[(0,316)]),
([v135,v0,v1,v2,v106,v3,v4,v5],[(v68,v3,v4),(v106,v68,v2),(v135,v1,v106)],[2,3,8,9],[(0,315),(0,316)])
]

set_option maxRecDepth 100000 in

def g6_L8 : Array W6Node := Array.mk [
([v0,v1,v2,0xf8f8f8f8f8f8f8f8,v3,v4,v5],[(v255,v0,v1),(0xf8f8f8f8f8f8f8f8,v255,v2)],[0,1,2,3,4,5,6,8,9,10],[]),
([v0,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v1,v2)],[0,1,2,3,5,8,9],[(0,0),(0,4),(0,5),(0,6),(0,7),(0,9),(0,10),(0,11),(0,12),(0,13),(1,1),(1,2),(1,3),(1,8)]),
([v0,v1,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,16),(0,17),(0,18),(0,19),(0,20),(1,14),(1,15)]),
([v33,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v33,v0,v2)],[0,1,2,3,5,9,10],[(0,22),(0,23),(1,21)]),
([v25,v0,v1,v6,v2,v3,v4,v5],[(v6,v1,v0),(v25,v1,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,3),(0,14),(0,25),(0,26),(0,27),(1,24)]),
([v0,v1,v2,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,26),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(1,26),(1,28),(1,29),(1,30),(1,32),(1,33),(1,34),(1,35)]),
([v0,v1,v6,v2,v9,v3,v4,v5],[(v6,v0,v1),(v9,v6,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,16),(0,17),(0,31),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,46),(0,47),(1,16),(1,17),(1,39),(1,41),(1,42),(1,43),(1,44),(1,45)]),
([v18,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,19),(0,27),(0,31),(0,48),(0,49),(0,50),(0,51),(1,19),(1,27),(1,48),(1,49),(1,50)]),
([v18,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v18,v6,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,4),(0,20),(0,31),(0,40),(0,52),(0,53),(0,54),(1,4),(1,20),(1,52),(1,53),(1,54)]),
([v0,v1,v72,v6,v2,v3,v4,v5],[(v6,v0,v1),(v72,v6,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,5),(0,22),(0,41),(0,52),(0,55),(0,56),(1,7),(1,57)]),
([v67,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v67,v6,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,6),(0,8),(0,23),(0,24),(0,42),(0,53),(0,57),(0,58),(0,59)]),
([v14,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v14,v2,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,50),(0,54),(0,61),(0,62),(0,63),(1,60),(1,64),(1,65)]),
([v0,v1,v6,v2,v20,v3,v4,v5],[(v6,v0,v1),(v20,v3,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,13),(0,38),(0,51),(0,66),(0,67),(0,68),(0,69),(0,70),(0,71),(1,13),(1,66)]),
([v0,v1,v6,v2,v3,v4,v5],[(v31,v0,v1),(v6,v31,v1)],[0,1,2,3,4,5,6,8,9,10],[(0,72),(0,73),(0,74),(0,75),(0,76),(1,72)]),
([v0,v1,v2,v74,v3,v4,v5],[(v31,v0,v1),(v74,v31,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,73),(0,77),(0,78),(0,79),(1,80)]),
([v31,v60,v2,v3,v4,v5],[(v31,v0,v1),(v60,v0,v1)],[0,1,2,3,5,9],[]),
([v31,v1,v2,v7,v3,v4,v5],[(v31,v0,v1),(v7,v0,v2)],[0,1,2,3,5,9,10],[(0,82),(0,83),(1,72),(1,81),(1,84)]),
([v31,v0,v1,v2,v8,v3,v4,v5],[(v31,v0,v1),(v8,v1,v2)],[0,2,3,4,5,6,8,9,10],[(0,72),(0,73),(0,77),(0,86),(0,87),(1,85)]),
([v14,v31,v0,v1,v2,v3,v4,v5],[(v31,v0,v1),(v14,v2,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,88),(0,89)]),
([v0,v1,v2,v7,v3,v75,v4,v5],[(v7,v0,v2),(v75,v0,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,90),(0,91)]),
([v25,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v25,v1,v4)],[0,2,3,4,5,6,8,9,10],[(0,14),(0,26),(0,92),(0,93),(0,95),(1,94)]),
([v46,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v46,v0,v8)],[0,1,2,3,4,5,6,8,9,10],[(0,0),(0,15),(0,97),(0,98),(0,99),(0,100),(1,28),(1,96)]),
([v0,v1,v2,v7,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v7)],[0,1,2,3,4,5,6,8,9,10],[(0,19),(0,29),(0,30),(0,82),(0,96),(0,104),(0,105),(0,106),(0,108),(0,110),(0,111),(0,114),(0,115),(0,116),(0,117),(0,118),(1,97),(1,98),(1,101),(1,102),(1,103),(1,107),(1,109),(1,112),(1,113)]),
([v95,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v95,v0,v8)],[0,1,2,3,4,5,6,8,9,10],[(0,73),(0,77),(0,119),(0,121),(0,122),(0,123),(0,124),(1,85),(1,120)]),
([v16,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7)],[0,1,2,3,4,5,6,8,9,10],[(0,16),(0,17),(0,29),(0,30),(0,73),(0,94),(0,125),(0,126),(0,127),(0,128),(0,129),(0,130),(1,86)]),
([v16,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v16,v1,v7)],[0,1,2,3,4,5,6,8,9,10],[(0,1),(0,2),(0,18),(0,29),(0,30),(0,85),(0,104),(0,131),(0,133),(1,87),(1,121),(1,122),(1,132),(1,134)]),
([v11,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v11,v0,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,135),(0,137),(0,144),(1,136),(1,138),(1,139),(1,140),(1,141),(1,142),(1,143)]),
([v0,v1,v2,v7,v3,v10,v4,v5],[(v7,v0,v2),(v10,v1,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,146),(0,147),(0,150),(1,144),(1,145),(1,148),(1,149)]),
([v17,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v17,v0,v4)],[0,2,3,4,5,6,8,9,10],[(0,151),(0,157),(0,158),(1,152),(1,153),(1,154),(1,155),(1,156)]),
([v39,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v39,v1,v3)],[0,1,2,3,4,5,6,8,9,10],[(1,157)]),
([v38,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v38,v0,v3)],[0,2,3,4,5,6,8,9,10],[(0,159),(0,160),(0,161),(1,162),(1,163),(1,164)]),
([v25,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v25,v1,v4)],[0,1,3,4,5,6,8,9,10],[(0,3),(0,26),(0,129),(0,165),(0,166),(0,167),(1,168),(1,169)]),
([v0,v1,v2,v54,v7,v3,v4,v5],[(v7,v0,v2),(v54,v7,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,83),(0,91),(0,106),(0,131),(0,170),(0,171),(0,172),(0,173),(1,11),(1,158),(1,174)]),
([v0,v1,v2,v7,v3,v166,v4,v5],[(v7,v0,v2),(v166,v7,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,90),(0,171),(0,172),(0,177),(1,175),(1,176),(1,178)]),
([v86,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v86,v8,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,95),(0,179),(0,180),(0,181),(0,182)]),
([v35,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v35,v8,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,12),(0,84),(0,93),(0,107),(0,132),(0,181),(0,182),(0,183),(0,184),(0,188),(0,189),(1,185),(1,186),(1,187)]),
([v0,v1,v2,v73,v7,v3,v4,v5],[(v7,v0,v2),(v73,v7,v4)],[0,1,3,4,5,6,8,9,10],[(0,108),(0,133),(0,173),(0,177),(0,190),(1,9),(1,99),(1,123),(1,179),(1,188)]),
([v50,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v50,v8,v3)],[0,2,3,4,5,6,8,9,10],[(0,10),(0,100),(0,109),(0,124),(0,134),(0,174),(0,178),(0,180),(0,189),(0,191),(0,192)]),
([v0,v1,v2,v7,v20,v3,v4,v5],[(v7,v0,v2),(v20,v3,v4)],[0,1,3,4,5,6,8,9,10],[(0,38),(0,130),(0,193),(0,194),(0,195),(0,196),(0,197),(0,198),(1,13)]),
([v68,v0,v1,v2,v8,v3,v4,v5],[(v8,v1,v2),(v68,v4,v3)],[0,1,2,3,4,5,8,9,10],[(0,199),(1,200),(1,201),(1,202),(1,203)]),
([v0,v92,v1,v2,v3,v4,v5],[(v76,v1,v2),(v92,v76,v0)],[0,1,2,3,4,5,6,8,9,10],[(0,204),(1,205)]),
([v33,v0,v12,v1,v2,v3,v4,v5],[(v33,v0,v2),(v12,v1,v3)],[0,1,3,4,5,6,8,9,10],[(0,207),(0,208),(0,209),(0,210),(0,211),(1,206)]),
([v33,v0,v1,v2,v3,v10,v4,v5],[(v33,v0,v2),(v10,v1,v3)],[0,2,3,4,5,6,8,9,10],[(0,211),(0,213),(0,214),(1,212)]),
([v17,v76,v0,v1,v2,v3,v4,v5],[(v76,v1,v2),(v17,v0,v4)],[0,3,4,5,8,9,10],[(0,217),(1,215),(1,216)]),
([v33,v39,v0,v1,v2,v3,v4,v5],[(v33,v0,v2),(v39,v1,v3)],[0,2,3,4,5,6,8,9,10],[(1,217)]),
([v0,v1,v87,v2,v3,v4,v5],[(v38,v0,v3),(v87,v38,v1)],[0,1,2,3,4,5,6,8,9,10],[(0,159),(0,161),(0,218),(0,219),(0,220)]),
([v0,v1,v2,v88,v3,v4,v5],[(v38,v0,v3),(v88,v38,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,160),(0,161),(0,221),(0,222),(0,223)]),
([v38,v1,v2,v75,v4,v5],[(v38,v0,v3),(v75,v0,v3)],[0,1,2,3,5,10],[(1,224)]),
([v14,v0,v1,v2,v75,v4,v5],[(v75,v0,v3),(v14,v2,v3)],[0,1,2,3,4,5,6,8,10],[]),
([v94,v0,v1,v2,v3,v4,v5],[(v75,v0,v3),(v94,v2,v75)],[0,1,2,3,4,5,6,8,9,10],[(0,90),(0,226),(1,225)]),
([v14,v0,v1,v2,v3,v4,v120,v5],[(v120,v1,v4),(v14,v2,v3)],[0,1,2,3,4,5,6,8,9,10],[(1,227)]),
([v0,v1,v2,0xf0f0fcfcf0f0fcfc,v3,v4,v5],[(v188,v1,v4),(0xf0f0fcfcf0f0fcfc,v188,v2)],[0,1,2,3,4,5,8,9,10],[]),
([v188,v25,v0,v2,v3,v5],[(v188,v1,v4),(v25,v1,v4)],[0,1,2,3,6,9],[(0,224)]),
([v0,v57,v1,v2,v3,v4,v5],[(v25,v1,v4),(v57,v25,v0)],[0,1,2,3,4,5,6,8,9,10],[(0,92),(0,166),(0,228),(0,229),(0,230),(0,231),(0,233),(1,24),(1,232)]),
([v0,v1,v2,v40,v3,v4,v5],[(v25,v1,v4),(v40,v25,v2)],[0,1,2,3,4,5,6,8,9,10],[(0,25),(0,93),(0,165),(0,166),(0,234),(0,238),(0,239),(1,235),(1,236),(1,237),(1,240)]),
([v25,v41,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v41,v0,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,237),(0,241),(1,237)]),
([v14,v25,v0,v1,v2,v3,v4,v5],[(v25,v1,v4),(v14,v2,v3)],[0,2,3,4,5,6,8,9,10],[(0,233),(0,238),(0,242),(0,243)]),
([v25,v0,v1,v2,v3,v45,v5],[(v25,v1,v4),(v45,v2,v4)],[0,1,2,3,4,6,8,9,10],[]),
([v0,v22,v2,v3,v4,v5],[(v11,v0,v4),(v22,v11,v1)],[0,3,5,6,8],[(0,244),(0,246),(0,247),(0,249),(0,250),(0,251),(1,245),(1,248)]),
([v0,v1,v32,v2,v3,v4,v5],[(v12,v1,v3),(v32,v12,v0)],[0,1,3,4,5,6,8,9,10],[(0,136),(0,138),(0,207),(0,252),(0,254),(0,256),(0,257),(0,258),(1,135),(1,253),(1,255),(1,259),(1,260),(1,261)]),
([0x22aa22aa22aa22aa,v1,v2,v3,v4,v5],[(v12,v1,v3),(0x22aa22aa22aa22aa,v12,v0)],[0,1,3,4,5,9,10],[]),
([v0,v1,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2)],[0,3,5,6,8],[(0,263),(0,265),(0,267),(0,269),(0,270),(0,271),(1,262),(1,264),(1,266),(1,268),(1,272),(1,273)]),
([v0,v1,v2,v19,v3,v4,v5],[(v11,v0,v4),(v19,v11,v2)],[0,3,4,5,6,8,9,10],[(0,137),(0,275),(0,277),(0,278),(0,280),(0,282),(0,283),(0,284),(0,285),(0,286),(1,138),(1,208),(1,274),(1,276),(1,279),(1,281),(1,287),(1,288)]),
([v0,v1,v2,v3,0xffffcc00ffffcc00,v5],[(v12,v1,v3),(0xffffcc00ffffcc00,v12,v4)],[0,1,3,4,8,9,10],[]),
([v187,v0,v1,v2,v3,v5],[(v12,v1,v3),(v187,v12,v4)],[0,3,4,6,9,10],[(0,142),(0,209)]),
([v62,v0,v1,v2,v3,v4],[(v12,v1,v3),(v62,v12,v5)],[0,3,4,9,10,11],[(0,143),(0,210),(0,289),(0,290),(0,291),(0,293),(1,292),(1,294)]),
([v11,v1,v2,v3,v13,v5],[(v11,v0,v4),(v13,v0,v4)],[0,3,5,8],[(0,144),(0,297),(0,299),(0,300),(0,301),(1,211),(1,295),(1,296),(1,298)]),
([v11,v0,v12,v1,v2,v3,v4,v5],[(v11,v0,v4),(v12,v1,v3)],[0,3,4,5,6,8,9,10],[(0,252),(0,266),(0,279),(0,289),(0,296),(0,302),(1,252),(1,266),(1,279),(1,289),(1,296)]),
([v11,v0,v1,v2,v3,v10,v4,v5],[(v11,v0,v4),(v10,v1,v3)],[0,2,3,4,5,6,8,9,10],[(0,253),(0,267),(0,280),(0,296),(0,297),(0,304),(0,305),(0,306),(1,290),(1,303)]),
([v17,v0,v12,v1,v2,v3,v4,v5],[(v12,v1,v3),(v17,v0,v4)],[0,3,4,5,6,8,9,10],[(0,254),(0,268),(0,281),(0,291),(0,298),(0,309),(1,307),(1,308)]),
([v39,v11,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v39,v1,v3)],[0,2,3,4,5,6,8,9,10],[(0,255),(0,269),(0,282),(0,292),(0,299),(1,309)]),
([v11,v0,v1,v2,v3,v61,v4,v5],[(v11,v0,v4),(v61,v2,v3)],[0,2,3,4,5,6,8,9,10],[(0,250),(0,283),(0,300),(1,293),(1,310)]),
([v14,v11,v0,v1,v2,v3,v4,v5],[(v11,v0,v4),(v14,v2,v3)],[0,2,3,4,5,6,8,9,10],[(0,251),(0,261),(0,284),(0,294),(0,301),(0,304),(0,311),(0,312)]),
([v44,v0,v1,v2,v3,v4,v5],[(v13,v0,v4),(v44,v1,v13)],[0,1,2,3,4,5,6,8,9,10],[(0,145),(0,148),(0,313),(0,314),(0,315),(0,316),(0,317),(0,318),(1,319)]),
([v0,v1,v2,v3,v10,v4,v13,v5],[(v10,v1,v3),(v13,v0,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,297),(0,320),(0,321),(0,322),(0,323),(1,297),(1,320),(1,321),(1,323)]),
([v17,v0,v1,v2,v3,v10,v4,v5],[(v10,v1,v3),(v17,v0,v4)],[0,2,3,4,5,6,8,9,10],[(0,298),(0,324),(0,326),(0,327),(0,328),(0,329),(1,325)]),
([v39,v0,v1,v2,v3,v4,v13,v5],[(v13,v0,v4),(v39,v1,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,299),(0,332),(1,326),(1,330),(1,331)]),
([v14,v0,v1,v2,v10,v4,v5],[(v10,v1,v3),(v14,v2,v3)],[0,2,3,4,6,9,10],[(0,304),(0,319),(0,320),(0,327),(0,330),(0,333)]),
([v28,v0,v1,v2,v3,v4,v5],[(v10,v1,v3),(v28,v2,v10)],[0,2,3,4,5,6,8,9,10],[(0,213),(0,305),(0,321),(0,328),(0,331),(0,334),(0,335),(0,336),(0,338),(0,340),(0,341),(0,342),(0,343),(1,148),(1,337),(1,339)]),
([v0,v1,v2,v3,v10,v4,v45,v5],[(v10,v1,v3),(v45,v2,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,343),(0,344),(0,345),(1,300)]),
([v14,v0,v1,v2,v3,v4,v13,v5],[(v13,v0,v4),(v14,v2,v3)],[0,1,3,4,5,6,8,9,10],[(0,301),(0,318),(0,320),(0,348),(1,346),(1,347)]),
([v0,v1,v2,v3,v15,v4],[(v10,v1,v3),(v15,v10,v5)],[0,2,3,4,9,10],[(0,150),(0,214),(0,306),(0,323),(0,329),(0,333),(0,345),(0,349),(0,350),(0,353),(0,354),(0,356),(0,357),(1,332),(1,348),(1,351),(1,352),(1,355),(1,358)]),
([v0,v42,v1,v2,v3,v4,v5],[(v26,v1,v3),(v42,v26,v0)],[0,1,3,5,6,8,9,10],[(0,152),(0,153),(0,216),(0,359),(0,360),(0,361),(0,362),(1,151),(1,363),(1,364)]),
([v0,v1,v2,v37,v3,v4,v5],[(v17,v0,v4),(v37,v17,v2)],[0,3,4,5,8,9,10],[(0,324),(0,366),(0,368),(0,369),(0,371),(0,372),(0,373),(0,375),(1,153),(1,308),(1,365),(1,367),(1,370),(1,374)]),
([v17,v36,v1,v2,v3,v5],[(v17,v0,v4),(v36,v0,v4)],[0,3,5,6],[(0,157),(0,217),(0,309),(0,326),(0,377),(0,378),(0,379),(1,295),(1,376)]),
([v17,v26,v0,v1,v2,v3,v4,v5],[(v17,v0,v4),(v26,v1,v3)],[0,3,5,8,9,10],[(0,370),(0,376),(0,380),(1,370),(1,376)]),
([v17,v39,v0,v1,v2,v3,v4,v5],[(v17,v0,v4),(v39,v1,v3)],[0,2,3,4,5,8,9,10],[(0,371),(0,376),(0,377)]),
([v17,v0,v1,v2,v3,v61,v4,v5],[(v17,v0,v4),(v61,v2,v3)],[0,2,3,4,5,8,9,10],[(0,378),(1,381)]),
([v17,v14,v0,v1,v2,v3,v4,v5],[(v17,v0,v4),(v14,v2,v3)],[0,3,4,5,6,8,9,10],[(0,327),(0,364),(0,379),(0,382),(0,383)]),
([v39,v36,v0,v1,v2,v3,v4,v5],[(v39,v1,v3),(v36,v0,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,377),(1,377)]),
([v39,v0,v1,v2,v3,v4,v45,v5],[(v39,v1,v3),(v45,v2,v4)],[0,1,2,3,4,5,8,9,10],[(1,378)]),
([v14,v36,v0,v1,v2,v3,v4,v5],[(v36,v0,v4),(v14,v2,v3)],[0,1,3,4,5,6,8,9,10],[(0,330),(0,379),(1,384)]),
([v77,v0,v1,v2,v3,v4,v5],[(v45,v2,v4),(v77,v1,v45)],[0,1,2,3,4,5,8,9,10],[(0,385),(0,386)]),
([v0,v1,v2,v20,v3,v45,v5],[(v45,v2,v4),(v20,v4,v3)],[0,1,3,4,8,10],[(0,387)]),
([v0,v47,v1,v2,v3,v4,v5],[(v14,v2,v3),(v47,v14,v0)],[0,1,2,3,4,5,6,8,9,10],[(0,61),(0,62),(0,89),(0,243),(0,388),(0,389),(0,390),(0,391),(1,60),(1,392)]),
([v0,v55,v1,v2,v3,v4,v5],[(v30,v2,v4),(v55,v30,v0)],[0,1,3,4,5,6,8,9,10],[(0,346),(0,384),(0,394),(0,395),(0,396),(0,398),(0,399),(1,62),(1,312),(1,383),(1,393),(1,397),(1,400),(1,401)]),
([v68,v30,v0,v1,v2,v3,v5],[(v30,v2,v4),(v68,v4,v3)],[0,1,3,4,6,8,10],[(1,402)]),
([v0,v1,v2,v3,v58,v4,v5],[(v20,v3,v4),(v58,v0,v20)],[0,1,2,3,4,5,6,8,9,10],[(0,67),(0,195),(0,403),(0,404),(0,405),(0,406),(0,407),(0,408),(1,66),(1,193),(1,387)]),
([v0,v1,v2,v3,v64,v4,v5],[(v20,v3,v4),(v64,v2,v20)],[0,1,2,3,4,5,6,8,9,10],[(0,71),(0,194),(0,195),(0,409),(0,410),(0,411),(1,194),(1,195),(1,409),(1,410),(1,411)]),
([0xf0f0f000f0f0f00,v0,v1,v2,v3,v4,v5],[(v256,v3,v4),(0xf0f0f000f0f0f00,v2,v256)],[0,1,2,3,5,8,9,10],[]),
([v0,v114,v1,v2,v3,v4,v5],[(v52,v4,v3),(v114,v52,v0)],[0,1,2,3,4,5,6,8,9,10],[(0,200),(0,402),(0,412),(0,413),(0,414)]),
([v0,v1,v2,v106,v3,v4,v5],[(v68,v3,v4),(v106,v68,v2)],[0,1,2,3,4,5,8,9,10],[(0,199),(0,415),(0,416),(0,417),(1,200)]),
([v68,v52,v0,v1,v2,v5],[(v68,v3,v4),(v52,v3,v4)],[0,1,2,3,8,10],[])
]

def g6_L9 : Array W6Node := Array.mk [
([v255,v0,v1,v2,v3,v4,v5],[(v255,v0,v1)],[0,1,2,3,4,5,6,8,9,10],[(0,0)]),
([v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1)],[0,1,2,3,4,5,6,8,9,10],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(1,1),(1,2),(1,3),(1,4),(1,9),(1,10),(1,11)]),
([v31,v0,v1,v2,v3,v4,v5],[(v31,v0,v1)],[0,1,2,3,4,5,6,8,9,10],[(0,13),(0,14),(0,15),(0,16),(0,17),(0,18)]),
([v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2)],[0,1,3,4,5,6,8,9,10],[(0,2),(0,5),(0,16),(0,19),(0,22),(0,24),(0,25),(0,27),(0,29),(0,31),(0,32),(0,33),(0,36),(0,38),(1,1),(1,17),(1,20),(1,21),(1,23),(1,26),(1,28),(1,30),(1,34),(1,35),(1,37),(1,39)]),
([v33,v0,v1,v2,v3,v4,v5],[(v33,v0,v2)],[0,1,3,4,5,6,8,9,10],[(0,3),(0,41),(0,42),(0,44),(1,40),(1,43)]),
([v38,v0,v1,v2,v3,v4,v5],[(v38,v0,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,30),(0,45),(0,46),(0,47)]),
([v0,v1,v2,v3,v75,v4,v5],[(v75,v0,v3)],[0,1,2,3,4,5,6,8,9,10],[(0,19),(0,47),(0,48),(0,49),(1,50)]),
([v188,v0,v1,v2,v3,v4,v5],[(v188,v1,v4)],[0,1,2,3,4,5,8,9,10],[(0,51),(0,52)]),
([v25,v0,v1,v2,v3,v4,v5],[(v25,v1,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,4),(0,20),(0,31),(0,52),(0,53),(0,54),(0,55),(0,56),(0,57)]),
([v11,v0,v1,v2,v3,v4,v5],[(v11,v0,v4)],[0,3,4,5,6,8,9,10],[(0,26),(0,58),(0,61),(0,62),(0,66),(0,67),(0,68),(0,70),(0,71),(0,72),(1,41),(1,59),(1,60),(1,63),(1,64),(1,65),(1,69)]),
([v0,v1,v2,v3,v10,v4,v5],[(v10,v1,v3)],[0,2,3,4,5,6,8,9,10],[(0,27),(0,42),(0,68),(0,74),(0,75),(0,77),(0,78),(0,79),(0,81),(1,66),(1,73),(1,76),(1,80)]),
([v17,v0,v1,v2,v3,v4,v5],[(v17,v0,v4)],[0,3,4,5,8,9,10],[(0,28),(0,43),(0,69),(0,75),(0,83),(0,84),(0,85),(0,86),(0,87),(0,88),(1,82)]),
([v39,v0,v1,v2,v3,v4,v5],[(v39,v1,v3)],[0,2,3,4,5,6,8,9,10],[(0,29),(0,44),(0,70),(0,76),(0,86),(0,89),(0,90),(1,84),(1,91)]),
([v0,v1,v2,v3,v61,v4,v5],[(v61,v2,v3)],[0,2,3,5,6,8,9,10],[(0,71),(0,87),(1,57),(1,79),(1,90),(1,92),(1,93)]),
([v14,v0,v1,v2,v3,v4,v5],[(v14,v2,v3)],[0,2,3,4,5,6,8,9,10],[(0,11),(0,18),(0,48),(0,50),(0,56),(0,72),(0,77),(0,80),(0,88),(0,91),(0,94),(1,95),(1,96)]),
([v0,v1,v2,v20,v3,v4,v5],[(v20,v3,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,12),(0,38),(0,93),(0,97),(0,98),(1,38),(1,93),(1,97)]),
([v0,v1,v2,v3,v4,v256,v5],[(v256,v3,v4)],[0,1,2,3,5,8,9,10],[(0,99)]),
([v68,v0,v1,v2,v3,v4,v5],[(v68,v3,v4)],[0,1,2,3,4,5,8,9,10],[(0,39),(0,96),(0,101),(0,102),(1,100)])
]

def g6_L10 : Array W6Node := Array.mk [
([v0,v1,v2,v3,v4,v5],[],[0,3],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,17)])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_3_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_3 : ∀ i < g6_L3.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : g6_L3.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_3_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_1 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 16 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 i = true := by
  intro i hi
  have hsz : g6_L4.size = 19 := by decide +kernel
  have hi' : i < 19 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW6_at g6_chk_4_0 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_4_1 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_1 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_2 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_3 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_4 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_5 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_6 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_7 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_8 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_9 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_10 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_11 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_12 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 192 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 i = true := by
  intro i hi
  have hsz : g6_L5.size = 196 := by decide +kernel
  have hi' : i < 196 := hsz ▸ hi
  by_cases h : i < 112
  ·
    by_cases h : i < 64
    ·
      by_cases h : i < 32
      ·
        by_cases h : i < 16
        ·
          exact checkBlockW6_at g6_chk_5_0 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_1 i (by omega) (by omega)
      ·
        by_cases h : i < 48
        ·
          exact checkBlockW6_at g6_chk_5_2 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_3 i (by omega) (by omega)
    ·
      by_cases h : i < 96
      ·
        by_cases h : i < 80
        ·
          exact checkBlockW6_at g6_chk_5_4 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_5 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_6 i (by omega) (by omega)
  ·
    by_cases h : i < 160
    ·
      by_cases h : i < 144
      ·
        by_cases h : i < 128
        ·
          exact checkBlockW6_at g6_chk_5_7 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_8 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_9 i (by omega) (by omega)
    ·
      by_cases h : i < 192
      ·
        by_cases h : i < 176
        ·
          exact checkBlockW6_at g6_chk_5_10 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_5_11 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_12 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_1 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_2 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_3 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_4 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_5 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_6 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_7 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_8 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_9 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_10 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_11 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_12 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_13 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_14 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_15 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_16 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_17 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_18 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_19 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_20 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_21 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_22 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_23 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_24 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_25 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_26 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_27 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_28 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_29 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_30 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_31 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_32 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 512 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_33 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 528 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_34 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 544 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_35 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 560 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_36 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 576 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_37 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 592 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_38 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 608 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_39 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 624 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_40 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 640 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_41 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 656 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : g6_L6.size = 658 := by decide +kernel
  have hi' : i < 658 := hsz ▸ hi
  by_cases h : i < 336
  ·
    by_cases h : i < 176
    ·
      by_cases h : i < 96
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
          by_cases h : i < 80
          ·
            by_cases h : i < 64
            ·
              exact checkBlockW6_at g6_chk_6_3 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_4 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_5 i (by omega) (by omega)
      ·
        by_cases h : i < 144
        ·
          by_cases h : i < 128
          ·
            by_cases h : i < 112
            ·
              exact checkBlockW6_at g6_chk_6_6 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_7 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_8 i (by omega) (by omega)
        ·
          by_cases h : i < 160
          ·
            exact checkBlockW6_at g6_chk_6_9 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_10 i (by omega) (by omega)
    ·
      by_cases h : i < 256
      ·
        by_cases h : i < 224
        ·
          by_cases h : i < 208
          ·
            by_cases h : i < 192
            ·
              exact checkBlockW6_at g6_chk_6_11 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_12 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_13 i (by omega) (by omega)
        ·
          by_cases h : i < 240
          ·
            exact checkBlockW6_at g6_chk_6_14 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_15 i (by omega) (by omega)
      ·
        by_cases h : i < 304
        ·
          by_cases h : i < 288
          ·
            by_cases h : i < 272
            ·
              exact checkBlockW6_at g6_chk_6_16 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_17 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_18 i (by omega) (by omega)
        ·
          by_cases h : i < 320
          ·
            exact checkBlockW6_at g6_chk_6_19 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_20 i (by omega) (by omega)
  ·
    by_cases h : i < 512
    ·
      by_cases h : i < 432
      ·
        by_cases h : i < 384
        ·
          by_cases h : i < 368
          ·
            by_cases h : i < 352
            ·
              exact checkBlockW6_at g6_chk_6_21 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_22 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_23 i (by omega) (by omega)
        ·
          by_cases h : i < 416
          ·
            by_cases h : i < 400
            ·
              exact checkBlockW6_at g6_chk_6_24 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_25 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_26 i (by omega) (by omega)
      ·
        by_cases h : i < 480
        ·
          by_cases h : i < 464
          ·
            by_cases h : i < 448
            ·
              exact checkBlockW6_at g6_chk_6_27 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_28 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_29 i (by omega) (by omega)
        ·
          by_cases h : i < 496
          ·
            exact checkBlockW6_at g6_chk_6_30 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_31 i (by omega) (by omega)
    ·
      by_cases h : i < 592
      ·
        by_cases h : i < 560
        ·
          by_cases h : i < 544
          ·
            by_cases h : i < 528
            ·
              exact checkBlockW6_at g6_chk_6_32 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_33 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_34 i (by omega) (by omega)
        ·
          by_cases h : i < 576
          ·
            exact checkBlockW6_at g6_chk_6_35 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_36 i (by omega) (by omega)
      ·
        by_cases h : i < 640
        ·
          by_cases h : i < 624
          ·
            by_cases h : i < 608
            ·
              exact checkBlockW6_at g6_chk_6_37 i (by omega) (by omega)
            ·
              exact checkBlockW6_at g6_chk_6_38 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_39 i (by omega) (by omega)
        ·
          by_cases h : i < 656
          ·
            exact checkBlockW6_at g6_chk_6_40 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_41 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_1 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_2 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_3 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_4 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_5 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_6 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_7 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_8 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_9 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_10 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_11 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_12 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_13 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_14 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_15 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_16 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_17 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_18 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_19 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_20 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_21 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_22 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_23 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_24 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_25 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_26 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 416 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 i = true := by
  intro i hi
  have hsz : g6_L7.size = 418 := by decide +kernel
  have hi' : i < 418 := hsz ▸ hi
  by_cases h : i < 224
  ·
    by_cases h : i < 112
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
          exact checkBlockW6_at g6_chk_7_6 i (by omega) (by omega)
    ·
      by_cases h : i < 176
      ·
        by_cases h : i < 144
        ·
          by_cases h : i < 128
          ·
            exact checkBlockW6_at g6_chk_7_7 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_8 i (by omega) (by omega)
        ·
          by_cases h : i < 160
          ·
            exact checkBlockW6_at g6_chk_7_9 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_10 i (by omega) (by omega)
      ·
        by_cases h : i < 208
        ·
          by_cases h : i < 192
          ·
            exact checkBlockW6_at g6_chk_7_11 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_12 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_13 i (by omega) (by omega)
  ·
    by_cases h : i < 336
    ·
      by_cases h : i < 288
      ·
        by_cases h : i < 256
        ·
          by_cases h : i < 240
          ·
            exact checkBlockW6_at g6_chk_7_14 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_15 i (by omega) (by omega)
        ·
          by_cases h : i < 272
          ·
            exact checkBlockW6_at g6_chk_7_16 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_17 i (by omega) (by omega)
      ·
        by_cases h : i < 320
        ·
          by_cases h : i < 304
          ·
            exact checkBlockW6_at g6_chk_7_18 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_19 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_20 i (by omega) (by omega)
    ·
      by_cases h : i < 384
      ·
        by_cases h : i < 368
        ·
          by_cases h : i < 352
          ·
            exact checkBlockW6_at g6_chk_7_21 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_22 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_23 i (by omega) (by omega)
      ·
        by_cases h : i < 416
        ·
          by_cases h : i < 400
          ·
            exact checkBlockW6_at g6_chk_7_24 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_25 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_26 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_1 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_2 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_3 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_4 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_5 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_6 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 96 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 i = true := by
  intro i hi
  have hsz : g6_L8.size = 103 := by decide +kernel
  have hi' : i < 103 := hsz ▸ hi
  by_cases h : i < 64
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW6_at g6_chk_8_0 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_8_1 i (by omega) (by omega)
    ·
      by_cases h : i < 48
      ·
        exact checkBlockW6_at g6_chk_8_2 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_8_3 i (by omega) (by omega)
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 80
      ·
        exact checkBlockW6_at g6_chk_8_4 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_8_5 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_8_6 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_1 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 16 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_9 : ∀ i < g6_L9.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 i = true := by
  intro i hi
  have hsz : g6_L9.size = 18 := by decide +kernel
  have hi' : i < 18 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW6_at g6_chk_9_0 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_9_1 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_10_0 : checkBlockW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_10 : ∀ i < g6_L10.size, checkNodeW6 goal6 2 g6_pow 12 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 i = true := by
  intro i hi
  have hsz : g6_L10.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_10_0 i (Nat.zero_le _) (by omega)

theorem g6_L3_sound : ∀ i < g6_L3.size, ¬ live (basicOps 64) goal6 3 (g6_L3[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound (fun j hj => by simp at hj) g6_chk_3

theorem g6_L4_sound : ∀ i < g6_L4.size, ¬ live (basicOps 64) goal6 4 (g6_L4[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L3_sound g6_chk_4

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
  Nat.testBit (4277071592 * 2 ^ 32 + 4008373472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  ⟨.or, [3, 1]⟩,
  ⟨.and, [5, 6]⟩,
  ⟨.or, [2, 4]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.and, [7, 4]⟩,
  ⟨.and, [0, 10]⟩,
  ⟨.and, [11, 2]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.and, [14, 1]⟩,
  ⟨.or, [15, 12]⟩,
  ⟨.or, [16, 13]⟩
]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_41522_aux

open PEqualNP.Outside.L_meta_41522_aux in
theorem PEqualNP.Outside.L_meta_41522 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4008373472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4008373472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
