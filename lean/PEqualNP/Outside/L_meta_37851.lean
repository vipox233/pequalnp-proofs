import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37851

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
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

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277074664 * 2 ^ 32 + 4243388552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x4020c186c83862a2#64 ++ 0x0a01060c3641c315#64 ++ 0xa069c78fc87867fb#64 ++ 0xfd034e3c7e43c33f#64 : BitVec 256),
   (0x8082243102838548#64 ++ 0x2404112188141c2a#64 ++ 0x719624718f8f87ff#64 ++ 0x7b8cb1238c7c7c3f#64 : BitVec 256),
   (0x0218085a11d0a990#64 ++ 0x8810c042d08e854c#64 ++ 0xee18387e71f1f99f#64 ++ 0xd770c1c3f38f8fcc#64 : BitVec 256),
   (0x05e036806e015603#64 ++ 0x302f01b403700ab0#64 ++ 0xefe03f807e01fe16#64 ++ 0xcf7f01fc03f00ff0#64 : BitVec 256),
   (0x077d40007d6c0003#64 ++ 0xc03bea0003eb6000#64 ++ 0xf7ffc0007ffe000e#64 ++ 0x3fbffe0003fff000#64 : BitVec 256),
   (0x0fdfbf6d8000001c#64 ++ 0x007efdfb6c000000#64 ++ 0xffffffff80000001#64 ++ 0xfffffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000001000808100 0x0000000080040408 0x60102471898987ff 0x7b0081238c4c4c3f

def z1 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e71f1f99f 0xd770c1c3f38f8fcc

def z2 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807e01fe16 0xcf7f01fc03f00ff0

def z3 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z4 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff80000001 0xfffffffffc000000

def z5 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fc87867fb 0xfd034e3c7e43c33f

def z6 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x719624718f8f87ff 0x7b8cb1238c7c7c3f

def z7 : W := mkw 0x075d000000000000 0x003ae80000000000 0xf7ffc00000000000 0x3fbffe0000000000

def z8 : W := mkw 0x0fffff6dfd6c001f 0xc07ffffb6feb6000 0xfffffffffffe000f 0xfffffffffffff000

def z9 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x4e10387e3181f995 0xc27081c3f18c0fcc

def z10 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xff963c71ff8fffff 0xfffcb1e38ffc7fff

def z11 : W := mkw 0x0080368002015600 0x300401b400100ab0 0x08003f800001fe10 0xc04001fc00000ff0

def z12 : W := mkw 0x05c0360026011401 0x302e01b0013008a0 0x4f80380036019804 0x027c01c001b00cc0

def z13 : W := mkw 0x002040006c2c0003 0x4001020003616000 0x000000000e0e0000 0x0000000000707000

def z14 : W := mkw 0x077d40127dfca983 0xc83bea0093efe54c 0xf7ffc0007ffff99e 0x3fbffe0003ffffcc

def z15 : W := mkw 0x0a1f896d8000001c 0x0050fc4b6c000000 0x101fc07f80000001 0x3080fe03fc000000

def z16 : W := mkw 0x0dc7b7258000000c 0x006e3db92c000000 0x11e7c78180000000 0x288f3e3c0c000000

def z17 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x0818387e01f1f999 0xd040c1c3f00f8fcc

def z18 : W := mkw 0x45e0f786ee3976a3 0x3a2f07bc3771cbb5 0xefe9ff8ffe79ffff 0xff7f4ffc7ff3cfff

def z19 : W := mkw 0x85e236b16e83d74b 0x342f11b58b741eba 0xfff63ff1ff8fffff 0xffffb1ff8ffc7fff

def z20 : W := mkw 0x0000810480000000 0x0000040824000000 0xa069c78f80000001 0xfd034e3c7c000000

def z21 : W := mkw 0x477dc184fd6c4223 0xc23bee0c27eb6211 0xf7ffc781fffe066e 0x3fbffe3c0ffff033

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000401880807fb 0x790000200c40403f

def z23 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f81fe09ffff 0xff7f01fc0ff04fff

def z24 : W := mkw 0x07f83ec86e015613 0x303fc1f643700ab0 0xeff83ffe7e01fe17 0xdf7fc1fff3f00ff0

def z25 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee183c7ff9f9ffff 0xff70c1e3ffcfcfff

def z26 : W := mkw 0x0080368002015600 0x300401b400100ab0 0xee003f807001fe16 0xc77001fc03800ff0

def z27 : W := mkw 0x0fdfbf7f91d0a99c 0x887efdfbfc8e854c 0xfffffffff1f1f99f 0xffffffffff8f8fcc

def z28 : W := mkw 0x0540000000000000 0x002a000000000000 0xe7e0000000000000 0x0f3f000000000000

def z29 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0x719fc0000ffe000e 0x3b8cfe00007ff000

def z30 : W := mkw 0x056012806c005203 0x102b009403600290 0x8e601b8070007800 0x847300dc038003c0

def z31 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0xa069c78f800067f1 0xfd034e3c7c00033f

def z32 : W := mkw 0x8fdfbf7d8283855c 0x247efdfbec141c2a 0xffffffff800187f1 0xfffffffffc000c3f

def z33 : W := mkw 0x0000000200102080 0x0800000010008104 0x000000004070619a 0x000000000203830c

def z34 : W := mkw 0x0000001211d0a980 0x88000000908e854c 0x0000000071f1f99e 0x00000000038f8fcc

def z35 : W := mkw 0x077d40107dec8103 0xc03bea0083ef6408 0xf7ffe0707fff819f 0x7fbfff0383fffc0c

def z36 : W := mkw 0x8082242102030448 0x2404112108101822 0x118604018e0e0660 0x288c30200c707033

def z37 : W := mkw 0x0000128000005200 0x1000009400000290 0x08001b8000007800 0x804000dc000003c0

def z38 : W := mkw 0x0020008048004202 0x0001000402400210 0xa060078048006612 0xcd03003c02400330

def z39 : W := mkw 0x077d00007d440003 0xc03be80003ea2000 0xf7f600007f860006 0x0fbfb00003fc3000

def z40 : W := mkw 0x07781ada7dd0fb93 0x983bc0d6d3ee87dc 0xee783bfe71f1f99f 0xd773c1dff38f8fcc

def z41 : W := mkw 0x075d085a11d0a990 0x883ae842d08e854c 0xfffff87e71f1f99f 0xffffffc3f38f8fcc

def z42 : W := mkw 0x4238c9cec83862b2 0x0a11c64e7641c315 0xee79ffffc87867fb 0xff73cffffe43c33f

def z43 : W := mkw 0x80a264314aab854a 0x240513218a555c2a 0xf1ffe471cfff87ff 0x7f8fff238e7ffc3f

def z44 : W := mkw 0x4020409259f8eba2 0x8a01020492cfc75d 0x0000000079f9fffe 0x0000000003cfcfff

def z45 : W := mkw 0x4238c9ded9f8ebb2 0x8a11c64ef6cfc75d 0xee79fffff9f9ffff 0xff73cfffffcfcfff

def z46 : W := mkw 0x8002003100828148 0x040010018804140a 0x10160071818e01e9 0x3080b0038c0c700f

def z47 : W := mkw 0x47fdf786ff7d76a3 0xfa3fefbc37fbebb5 0xffffff8fffffffff 0xfffffffc7fffffff

def z48 : W := mkw 0x0fffbfedee01561f 0x307ffdff6f700ab0 0xfffffffffe01fe17 0xfffffffffff00ff0

def z49 : W := mkw 0x40204082483862a2 0x0a0102041241c315 0x00000000487867fa 0x000000000243c33f

def z50 : W := mkw 0x85e764316eaf854b 0x642f3b218b757c2a 0x71f7e4718f8f87ff 0x7b8fbf238c7c7c3f

def z51 : W := mkw 0x0000001000808100 0x0000000080040408 0x601020700181819f 0x53008103800c0c0c

def z52 : W := mkw 0x829a2c7b13d3add8 0xac14d163d89e9d6e 0xff9e3c7fffffffff 0xfffcf1e3ffffffff

def z53 : W := mkw 0x0080240002010400 0x2004012000100820 0x4180200006018004 0x020c010000300c00

def z54 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0000078fc87867fb 0xc000003c7e43c33f

def z55 : W := mkw 0x0f7ddb4cfd6c0017 0xc07beeda67eb6000 0xffffdb8e7ffe000e 0xbffffedc73fff000

def z56 : W := mkw 0x0020400048280002 0x0001020002414000 0xa069c0004878000a 0x3d034e000243c000

def z57 : W := mkw 0x05c0368026015601 0x302e01b401300ab0 0x4f803f803601fe14 0xc27c01fc01b00ff0

def z58 : W := mkw 0x075d000035440001 0xc03ae80001aa2000 0x5796000037860004 0x02bcb00001bc3000

def z59 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0x8e69db8e00000000 0x84734edc70000000

def z60 : W := mkw 0x4fffffefc83862be 0x0a7fffff7e41c315 0xffffffffc87867fb 0xfffffffffe43c33f

def z61 : W := mkw 0x4020c184c8284222 0x0201060c26414211 0x0061c78188080660 0x28030e3c0c404033

def z62 : W := mkw 0x40008106801020a0 0x0a00040834008105 0x0000000f800001e1 0x000000007c00000f

def z63 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0009c00fc87867fb 0x30004e007e43c33f

def z64 : W := mkw 0x0f7ddb4cfd6c0017 0xc07beeda67eb6000 0x8e69db8e70700000 0x84734edc73838000

def z65 : W := mkw 0xc0a2e5b7cabbe7ea 0x2e05172dbe55df3f 0xf1ffe7ffcfffe7ff 0xff8fff3ffe7fff3f

def z66 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xee69ff8ff879ffff 0xff734ffc7fc3cfff

def z67 : W := mkw 0x4de7f7a7c83862ae 0x0a6f3fbd3e41c315 0xb1efc78fc87867fb 0xfd8f7e3c7e43c33f

def z68 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0x8e08180e70707800 0x847040c0738383c0

def z69 : W := mkw 0x077d00006c000003 0x003be80003600000 0xf7ffc0007e000006 0x3fbffe0003f00000

def z70 : W := mkw 0x0020400048280002 0x0001020002414000 0x8069c00040700000 0x04034e0002038000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0xee0038007001f816 0xc77001c003800fc0

def z72 : W := mkw 0x002000806e015603 0x3001000403700ab0 0xee0038007e01fe16 0xc77001c003f00ff0

def z73 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0xffe63f81fe0ffe76 0xefff31fc0ff07ff3

def z74 : W := mkw 0x0fffffedff6d561f 0xf07fffff6ffb6ab0 0xfffffffffffffe1f 0xfffffffffffffff0

def z75 : W := mkw 0x8fdfbf7d8283855c 0x247efdfbec141c2a 0xffffffff87878005 0xfffffffffc3c3c00

def z76 : W := mkw 0x07fd76807f6d5603 0xf03febb403fb6ab0 0xffffff807ffffe1e 0xfffffffc03fffff0

def z77 : W := mkw 0x0882bf6d8000001c 0x004415fb6c000000 0x08003fff80000001 0xc04001fffc000000

def z78 : W := mkw 0x0882bf6d8000001c 0x004415fb6c000000 0x79963fff80000001 0xfbccb1fffc000000

def z79 : W := mkw 0x0fdfbf6d9140001c 0x807efdfb6c8a0000 0xfffffffff1f0000f 0xffffffffff8f8000

def z80 : W := mkw 0x4000c106803820a0 0x0a0006083401c105 0x0009c00f807801e9 0x30004e007c03c00f

def z81 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x5196207007878004 0x028cb103803c3c00

def z82 : W := mkw 0x0fffbfffffd1ff9f 0xb87ffdfffffe8ffc 0xfffffffffff1ff9f 0xffffffffffff8ffc

def z83 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0x0000078f800067f1 0xc000003c7c00033f

def z84 : W := mkw 0xc082a5b78293e7e8 0x2e04152dbc149f3f 0x719627ff8f8fe7ff 0xfb8cb13ffc7c7f3f

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x719600000f8e000e 0x3b8cb000007c7000

def z86 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x00002471800187f1 0x400001238c000c3f

def z87 : W := mkw 0x002000927fd1ff83 0xb801000493fe8ffc 0x000000007ff1ff9e 0x0000000003ff8ffc

def z88 : W := mkw 0x002040007d6c0003 0xc001020003eb6000 0x000000007ffe000e 0x0000000003fff000

def z89 : W := mkw 0x056540006c2c0003 0x402b2a0003616000 0x11e7c0000e0e0000 0x288f3e0000707000

def z90 : W := mkw 0x4fffffefee3976bf 0x3a7fffff7f71cbb5 0xfffffffffe79ffff 0xfffffffffff3cfff

def z91 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc07067f1 0xc4034e3c7e03833f

def z92 : W := mkw 0x0020400048280002 0x0001020002414000 0xf1ffc0004ffe000e 0x3f8ffe00027ff000

def z93 : W := mkw 0x07f83eda7fd1ff93 0xb83fc1f6d3fe8ffc 0xeff83ffe7ff1ff9f 0xdf7fc1fff3ff8ffc

def z94 : W := mkw 0x075d000011400000 0x803ae800008a0000 0xf7ffc00071f0000e 0x3fbffe00038f8000

def z95 : W := mkw 0x0540120000000000 0x002a009000000000 0x8e601b8000000000 0x847300dc00000000

def z96 : W := mkw 0x07fd36806e015603 0x303fe9b403700ab0 0xffffff807e01fe16 0xfffffffc03f00ff0

def z97 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x8669c00070700000 0x04334e0003838000

def z98 : W := mkw 0x87ff64317fef854b 0xe43ffb218bff7c2a 0xf7ffe471ffff87ff 0x7fbfff238ffffc3f

def z99 : W := mkw 0x002000806e015603 0x3001000403700ab0 0xa06007807e01fe16 0xcd03003c03f00ff0

def z100 : W := mkw 0x000000120090a180 0x080000009004850c 0xe018207e41f1e19f 0xd700c103f20f8f0c

def z101 : W := mkw 0x0218000011400000 0x8010c000008a0000 0x4610000031800004 0x02308000018c0000

def z102 : W := mkw 0x0545000024040001 0x402a280001202000 0x1186000006060000 0x008c300000303000

def z103 : W := mkw 0x0080240002010400 0x2004012000100820 0x618024000e018616 0x4b0c012000700c30

def z104 : W := mkw 0x0fdf3e690000001c 0x007ef9f348000000 0x5f96387000000000 0x02fcb1c380000000

def z105 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x6018207e01f1819f 0x5300c103f00f8c0c

def z106 : W := mkw 0x0020c104c8280002 0x0001060826414000 0xa069c78fc878000b 0xfd034e3c7e43c000

def z107 : W := mkw 0x0fdf3e693544001d 0xc07ef9f349aa2000 0x5f96387037860004 0x02fcb1c381bc3000

def z108 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xcfe03b807601f804 0x867f01dc03b00fc0

def z109 : W := mkw 0x0218000011400000 0x8010c000008a0000 0xe618000071f0000e 0x1730c000038f8000

def z110 : W := mkw 0x0882bf7f8090a99c 0x084415fbfc04854c 0x08003fff8001f991 0xc04001fffc000fcc

def z111 : W := mkw 0x05c0360000000000 0x002e01b000000000 0x4f80380000000000 0x027c01c000000000

def z112 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x4e18387e31f1998d 0x1270c1c3f18f8ccc

def z113 : W := mkw 0x0082242100000008 0x0004112108000000 0x7196247180000001 0x7b8cb1238c000000

def z114 : W := mkw 0x8fdfbf7d8283855c 0x247efdfbec141c2a 0xffffffff8f8f87ff 0xfffffffffc7c7c3f

def z115 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xd7ffc00077f60004 0x06bffe0003bfb000

def z116 : W := mkw 0x0000000035440001 0xc000000001aa2000 0x0000000037860004 0x0000000001bc3000

def z117 : W := mkw 0x0fdfbf6db544001d 0xc07efdfb6daa2000 0xffffffffb7860005 0xfffffffffdbc3000

def z118 : W := mkw 0x0218084800000010 0x0010c04240000000 0x8e08180e00000000 0x847040c070000000

def z119 : W := mkw 0x0fdfbfed8201561c 0x307efdff6c100ab0 0xffffffff8001fe11 0xfffffffffc000ff0

def z120 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xfffff8007ffff81e 0xffffffc003ffffc0

def z121 : W := mkw 0x056540006c2c0003 0x402b2a0003616000 0xf7e7c0007e0e0006 0x2fbf3e0003f07000

def z122 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x118604018f8f87fe 0x288c30200c7c7c3f

def z123 : W := mkw 0x023840007d6c0003 0xc011c20003eb6000 0xe61800007ffe000e 0x1730c00003fff000

def z124 : W := mkw 0x0fdfbf7d8080811c 0x007efdfbec040408 0xffffffff8181819f 0xfffffffffc0c0c0c

def z125 : W := mkw 0x077d40807d6c4203 0xc03bea0403eb6210 0xf7ffc7807ffe661e 0xffbffe3c03fff330

def z126 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xf1ffc78fcffe67ff 0xff8ffe3c7e7ff33f

def z127 : W := mkw 0x4218c95e91f8a9b0 0x8a10c64af48fc54d 0x0019c07f81f801e9 0x3000ce03fc0fc00f

def z128 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0x101fc00001fe0008 0x3080fe00000ff000

def z129 : W := mkw 0x056000006c000003 0x002b000003600000 0xe7e000007e000006 0x0f3f000003f00000

def z130 : W := mkw 0x075d810480000000 0x003aec0824000000 0xf7ffc78f80000001 0xffbffe3c7c000000

def z131 : W := mkw 0x45e076826e3976a3 0x3a2f03b41371cbb5 0xefe03f807e79fffe 0xcf7f01fc03f3cfff

def z132 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff880807fb 0xfffffffffc40403f

def z133 : W := mkw 0x8082242102030448 0x2404112108101822 0x718624018e0f8676 0x6b8c31200c707c33

def z134 : W := mkw 0x45e0f786ee3976a3 0x3a2f07bc3771cbb5 0xa1e9c78fce7867fb 0xfd0f4e3c7e73c33f

def z135 : W := mkw 0x077d40027d7c2083 0xc83bea0013ebe104 0xf7ffc00e7ffe619f 0xffbffe0073fff30c

def z136 : W := mkw 0x423dc186d97c62a2 0xca11ee0c36cbe315 0xb07fc78fc9fe67fb 0xfd83fe3c7e4ff33f

def z137 : W := mkw 0x075d4000356c0001 0xc03aea0001ab6000 0x579fc00037fe000c 0x32bcfe0001bff000

def z138 : W := mkw 0x0020008048004202 0x0001000402400210 0x8060038040006000 0x8403001c02000300

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0xee00380000000000 0xc77001c000000000

def z140 : W := mkw 0x0000000200102080 0x0800000010008104 0x0000000e00006191 0xc00000007000030c

def z141 : W := mkw 0x002000806e015603 0x3001000403700ab0 0x000000007e01fe16 0x0000000003f00ff0

def z142 : W := mkw 0x05c0360000000000 0x002e01b000000000 0xefe03f8000000000 0xcf7f01fc00000000

def z143 : W := mkw 0x0dc7bf6d8000001c 0x006e3dfb6c000000 0x19e7ffff80000001 0xe8cf3ffffc000000

def z144 : W := mkw 0x0082242102010408 0x2004112108100820 0x719624718e018617 0x7b8cb1238c700c30

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000001800801e9 0x300000000c00400f

def z146 : W := mkw 0x056000806c004203 0x002b000403600210 0xe7e007807e006616 0xcf3f003c03f00330

def z147 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8f8e000f 0xfffffffffc7c7000

def z148 : W := mkw 0x05c0360000000000 0x002e01b000000000 0x01e0078000000000 0x080f003c00000000

def z149 : W := mkw 0x0000000200102080 0x0800000010008104 0xa008000e4070619b 0xd50040007203830c

def z150 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xffffffff8e018617 0xfffffffffc700c30

def z151 : W := mkw 0x056012806c005203 0x102b009403600290 0x0060038000000000 0x0003001c00000000

def z152 : W := mkw 0x0082243100808108 0x0004112188040408 0x719624718181819f 0x7b8cb1238c0c0c0c

def z153 : W := mkw 0x0000001211d0a980 0x88000000908e854c 0x0000000001f00188 0x00000000000f800c

def z154 : W := mkw 0x0a1fc96d916c001c 0xc050fe4b6c8b6000 0x101fc07f81fe0009 0x3080fe03fc0ff000

def z155 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xfffffffff001f817 0xffffffffff800fc0

def z156 : W := mkw 0x0fffbf6dec00001f 0x007ffdfb6f600000 0xfffffffffe000007 0xfffffffffff00000

def z157 : W := mkw 0x45e0b786ee1176a3 0x3a2f05bc37708bb5 0xefe03f8ffe01fff7 0xcf7f01fc7ff00fff

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0xa060078000000000 0xcd03003c00000000

def z159 : W := mkw 0x87df243102838548 0x243ef92188141c2a 0xf7ffe4718f8f87ff 0x7fbfff238c7c7c3f

def z160 : W := mkw 0xcfffffffcabbe7fe 0x2e7ffffffe55df3f 0xffffffffcfffe7ff 0xfffffffffe7fff3f

def z161 : W := mkw 0x0000000211502880 0x88000000108a8144 0x0000000070707800 0x00000000038383c0

def z162 : W := mkw 0x0080240002010400 0x2004012000100820 0xef803c007e01fe16 0xcf7c01e003f00ff0

def z163 : W := mkw 0x8fdf3e790283855c 0x247ef9f3c8141c2a 0x7f963c718f8f87ff 0x7bfcb1e38c7c7c3f

def z164 : W := mkw 0x056540007d6c0003 0xc02b2a0003eb6000 0x11e7c0007ffe000e 0x288f3e0003fff000

def z165 : W := mkw 0x8082242102030448 0x2404112108101822 0x1186000006060000 0x008c300000303000

def z166 : W := mkw 0x0a1d894c80000014 0x0050ec4a64000000 0x0009c00e00000000 0x00004e0070000000

def z167 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0x11e607818e0e0660 0x288f303c0c707033

def z168 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x8e603f807001fe10 0xc47301fc03800ff0

def z169 : W := mkw 0x077d485a7dfca993 0xc83bea42d3efe54c 0xfffff87e7ffff99f 0xffffffc3f3ffffcc

def z170 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0061c781c87867fa 0x28030e3c0e43c33f

def z171 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x5f963fff80000001 0xc2fcb1fffc000000

def z172 : W := mkw 0x829a243113c38548 0xa414d121889e1c2a 0xf79e2471ffff87ff 0x7fbcf1238ffffc3f

def z173 : W := mkw 0x8fdf3e790283855c 0x247ef9f3c8141c2a 0x5f96387007878004 0x02fcb1c3803c3c00

def z174 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x01e007800e000600 0x080f003c00700030

def z175 : W := mkw 0x8082242102030448 0x2404112108101822 0x0000040180000660 0x000000200c000033

def z176 : W := mkw 0x80822c7b0293add8 0x2c041163d8149d6e 0x08003c7f8001fff1 0xc04001e3fc000fff

def z177 : W := mkw 0x077d484a7d7c2893 0xc83bea4253ebe144 0xffffd80e7ffe780e 0xbffffec073fff3c0

def z178 : W := mkw 0x02983eda13d1ff90 0xb814c1f6d09e8ffc 0xee183ffe71f1ff9f 0xd770c1fff38f8ffc

def z179 : W := mkw 0xc7ffe5b7ffffe7eb 0xee3fff2dbfffff3f 0xf7ffe7ffffffe7ff 0xffbfff3fffffff3f

def z180 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x4e10387071f1f99e 0x027081c3838f8fcc

def z181 : W := mkw 0x8000001213d3adc0 0xac000000909e9d6e 0x000000007ffffffe 0x0000000003ffffff

def z182 : W := mkw 0x87df243137c78549 0xe43ef92189be3c2a 0x77962471bf8f87ff 0x7bbcb1238dfc7c3f

def z183 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0x2000078f880867fb 0xf900003c7c40433f

def z184 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x11ffc7ff80000001 0x388ffe3ffc000000

def z185 : W := mkw 0x0000085a0090a990 0x08000042d004854c 0x0800387e0001f991 0xc04001c3f0000fcc

def z186 : W := mkw 0x05e036906e81d703 0x302f01b483740eb8 0xeff03ff07f81ff9f 0xdf7f81ff83fc0ffc

def z187 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x9fefdf8f80000000 0xacff7efc7c000000

def z188 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc401fffe07ff 0x7fbffe200ffff03f

def z189 : W := mkw 0x0020008048004202 0x0001000402400210 0xee603f807801fe16 0xcf7301fc03c00ff0

def z190 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x719620700787819f 0x538cb103803c3c0c

def z191 : W := mkw 0x0080360002011400 0x300401b0001008a0 0x0800380000019800 0x004001c000000cc0

def z192 : W := mkw 0x0218000011400000 0x8010c000008a0000 0xf79e00007ffe000e 0x3fbcf00003fff000

def z193 : W := mkw 0x0a1f08690000001c 0x0050f84348000000 0x1016007000000000 0x0080b00380000000

def z194 : W := mkw 0x05c0b70480000000 0x002e05b824000000 0xefe9ff8f80000001 0xff7f4ffc7c000000

def z195 : W := mkw 0x87df243137c78549 0xe43ef92189be3c2a 0x5796207037878004 0x02bcb10381bc3c00

def z196 : W := mkw 0x075d084800000010 0x003ae84240000000 0xfffff87e00000001 0xffffffc3f0000000

def z197 : W := mkw 0x077d48487d6c0013 0xc03bea4243eb6000 0xfffff87e7ffe000f 0xffffffc3f3fff000

def z198 : W := mkw 0x0218000000000000 0x0010c00000000000 0xe618000000000000 0x1730c00000000000

def z199 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x60102471818187ff 0x530081238c0c0c3f

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0x10160000018e0008 0x3080b000000c7000

def z201 : W := mkw 0x4080b786821176a0 0x3a0405bc34108bb5 0x08003f8f8001fff1 0xc04001fc7c000fff

def z202 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x000024718f8f87ff 0x400001238c7c7c3f

def z203 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519620700f8f87fe 0x028cb103807c7c3f

def z204 : W := mkw 0x87ff76b17fefd74b 0xf43ffbb58bff7eba 0xfffffff1ffffffff 0xffffffff8fffffff

def z205 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0x9e7fdbff80000001 0xb4f3fedffc000000

def z206 : W := mkw 0x05e076806e295603 0x302f03b403714ab0 0xefe9ff807e79fe1e 0xff7f4ffc03f3cff0

def z207 : W := mkw 0x477dc186fd7c62a3 0xca3bee0c37ebe315 0xf7ffc38e7ffe600e 0xbfbffe1c73fff300

def z208 : W := mkw 0x0000085800808910 0x00000042c0040448 0x0800387000019800 0x004001c380000cc0

def z209 : W := mkw 0x0000400000280000 0x0000020000014000 0x0009c00000780008 0x30004e000003c000

def z210 : W := mkw 0x8000001002838540 0x2400000080141c2a 0x719600000f8f87fe 0x3b8cb000007c7c3f

def z211 : W := mkw 0x0fdf3e7911c0891c 0x807ef9f3c88e0448 0x5f96387031819804 0x02fcb1c3818c0cc0

def z212 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x719624700f878616 0x4b8cb123807c3c30

def z213 : W := mkw 0x0a9fad6d8000001c 0x0054fd6b6c000000 0x719fe47f80000001 0x7b8cff23fc000000

def z214 : W := mkw 0x00a024806e015603 0x3005012403700ab0 0x618024007e01fe16 0x4b0c012003f00ff0

def z215 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c38e40706000 0x84034e1c72038300

def z216 : W := mkw 0x05c0360000000000 0x002e01b000000000 0xefe03f807001f816 0xcf7f01fc03800fc0

def z217 : W := mkw 0x0fdf3e692601141d 0x307ef9f3493008a0 0x5f96387036019804 0x02fcb1c381b00cc0

def z218 : W := mkw 0x0fdfbf6da601141d 0x307efdfb6d3008a0 0xffffffffb6019805 0xfffffffffdb00cc0

def z219 : W := mkw 0xc0a2e5a5ca2b466a 0x2605172d2e515a33 0x11e7c7818e0e0660 0x288f3e3c0c707033

def z220 : W := mkw 0x0545000000000000 0x002a280000000000 0x11e7c00000000000 0x288f3e0000000000

def z221 : W := mkw 0x0a9abf6d8000001c 0x0054d5fb6c000000 0xee183fff80000001 0xd770c1fffc000000

def z222 : W := mkw 0x0000810480000000 0x0000040824000000 0xa069c78f880807fb 0xfd034e3c7c40403f

def z223 : W := mkw 0xc02040924abbe7e2 0x2e0102049255df3f 0x000000004fffe7fe 0x00000000027fff3f

def z224 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0xae69df8f80000001 0xfd734efc7c000000

def z225 : W := mkw 0x0000000200102080 0x0800000010008104 0x0008000e00700189 0x100040007003800c

def z226 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x0018007e01f00189 0x1000c003f00f800c

def z227 : W := mkw 0x0218085811c08910 0x8010c042c08e0448 0x4e10387031819804 0x027081c3818c0cc0

def z228 : W := mkw 0x0fdf3e690000001c 0x007ef9f348000000 0xfff63ff000000000 0xcfffb1ff80000000

def z229 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x119604718f8e07e9 0x388cb0238c7c703f

def z230 : W := mkw 0x0fdfbf6f9150289c 0x887efdfb7c8a8144 0xfffffffff0707801 0xffffffffff8383c0

def z231 : W := mkw 0x402040826e3976a3 0x3a0102041371cbb5 0x000000007e79fffe 0x0000000003f3cfff

def z232 : W := mkw 0x8fdfbf7f93d3addc 0xac7efdfbfc9e9d6e 0xffffffffffffffff 0xffffffffffffffff

def z233 : W := mkw 0x0ffff725fd6c000f 0xc07fffb92feb6000 0xf7ffc781fffe000e 0x3fbffe3c0ffff000

def z234 : W := mkw 0x07fd64007f6d0403 0xe03feb2003fb6820 0xf7ffe4007fff861e 0x7fbfff2003fffc30

def z235 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0xee18180e71f0780e 0x9770c0c0738f83c0

def z236 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xe7e007807e000606 0x0f3f003c03f00030

def z237 : W := mkw 0x4020c184c8284222 0x0201060c26414211 0xa069c781c878066a 0x3d034e3c0e43c033

def z238 : W := mkw 0x8882bf7d8283855c 0x244415fbec141c2a 0x08003fff800187f1 0xc04001fffc000c3f

def z239 : W := mkw 0x0238400059680002 0x8011c20002cb4000 0xe679c00079f8000e 0x3f33ce0003cfc000

def z240 : W := mkw 0x0218000011400000 0x8010c000008a0000 0xee18380071f1f81e 0xd770c1c0038f8fc0

def z241 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0xffffdb8e00000000 0xbffffedc70000000

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x618000000e000006 0x0b0c000000700000

def z243 : W := mkw 0x4565c184ec2c4223 0x422b2e0c27616211 0x11e7c7818e0e0660 0x288f3e3c0c707033

def z244 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xfff63f807f8ffe1e 0xffffb1fc03fc7ff0

def z245 : W := mkw 0x4f7ddbcec83862b6 0x0a7beede7641c315 0xae69df8fc87867fb 0xfd734efc7e43c33f

def z246 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xce18387e71f1f804 0x8670c1c3f38f8fc0

def z247 : W := mkw 0x0a1f897f91d0a99c 0x8850fc4bfc8e854c 0x101fc07f81f00189 0x3080fe03fc0f800c

def z248 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xe679c00071f0000e 0x1733ce00038f8000

def z249 : W := mkw 0x40208186c81062a2 0x0a01040c36408315 0xa060078fc80067f3 0xcd03003c7e40033f

def z250 : W := mkw 0x477dc9defdfcebb3 0xca3bee4ef7efe75d 0xffffffffffffffff 0xffffffffffffffff

def z251 : W := mkw 0x05e036006c000003 0x002f01b003600000 0xefe03f807e000006 0xcf7f01fc03f00000

def z252 : W := mkw 0x07f83ed87fc1df13 0xb03fc1f6c3fe0ef8 0xeff03ff07f81fe16 0xcf7f81ff83fc0ff0

def z253 : W := mkw 0x8fffbffdee83d75f 0x347ffdffef741eba 0xffffffffff8fffff 0xfffffffffffc7fff

def z254 : W := mkw 0x45e0f784ee295623 0x322f07bc27714ab1 0x01e1c7818e080660 0x280f0e3c0c704033

def z255 : W := mkw 0x0a1f896d8000001c 0x0050fc4b6c000000 0xb07fc7ff80000001 0xfd83fe3ffc000000

def z256 : W := mkw 0x40a0e586ca3966a2 0x2a05072c3651cb35 0xe1e9e78fce79e7ff 0xff0f4f3c7e73cf3f

def z257 : W := mkw 0x056012806e015603 0x302b009403700ab0 0x8e601b807e01fe16 0x847300dc03f00ff0

def z258 : W := mkw 0x056012806c005203 0x102b009403600290 0xae601f8078007e12 0xcd7300fc03c003f0

def z259 : W := mkw 0x47f8ffdefff9ffb3 0xba3fc7fef7ffcffd 0xeff9fffffff9ffff 0xff7fcfffffffcfff

def z260 : W := mkw 0x8000000002030440 0x2400000000101822 0x000000000e0e0660 0x0000000000707033

def z261 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x8e08180e71f1f99e 0x847040c0738f8fcc

def z262 : W := mkw 0x077d52807d6c5203 0xd03bea9403eb6290 0x8e69db8070707800 0x84734edc038383c0

def z263 : W := mkw 0x40204082483862a2 0x0a0102041241c315 0x0000000040706000 0x0000000002038300

def z264 : W := mkw 0x4238c9ded9f8ebb2 0x8a11c64ef6cfc75d 0xee79fbfe71f1f99f 0xd773cfdff38f8fcc

def z265 : W := mkw 0x056000006c000003 0x002b000003600000 0x8660000070000000 0x0433000003800000

def z266 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c38fc07861e9 0xb4034e1c7e03c30f

def z267 : W := mkw 0x0082a52580000008 0x000415292c000000 0xf1ffe7ff80000001 0xff8fff3ffc000000

def z268 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x11ffc0000ffe0008 0x388ffe00007ff000

def z269 : W := mkw 0x87fa3efb7fd3ffdb 0xbc3fd1f7dbfe9ffe 0xfffe3fffffffffff 0xfffff1ffffffffff

def z270 : W := mkw 0x0218084800000010 0x0010c04240000000 0xee18387e00000001 0xd770c1c3f0000000

def z271 : W := mkw 0x8082242102030448 0x2404112108101822 0x318604018e0e07fb 0x798c30200c70703f

def z272 : W := mkw 0x0080240000000000 0x0004012000000000 0x6180240000000000 0x4b0c012000000000

def z273 : W := mkw 0x477dc186fd7c62a3 0xca3bee0c37ebe315 0xf7ffc78ffffe67ff 0xffbffe3c7ffff33f

def z274 : W := mkw 0x0ffdbfccee015617 0x307fedfe67700ab0 0xefe9ff8e7e01fe16 0xcf7f4ffc73f00ff0

def z275 : W := mkw 0x8000001002838540 0x2400000080141c2a 0x000000000f8f87fe 0x00000000007c7c3f

def z276 : W := mkw 0x05c0360026011401 0x302e01b0013008a0 0x0180000006000000 0x000c000000300000

def z277 : W := mkw 0x4020408048284222 0x0201020402414211 0x0000000008080660 0x0000000000404033

def z278 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc8786660 0xac034e3c7e43c333

def z279 : W := mkw 0x0218894c80000010 0x0010c44a64000000 0xee79ffff80000001 0xff73cffffc000000

def z280 : W := mkw 0x08009b4c80000014 0x004004da64000000 0x08001b8e00000000 0x804000dc70000000

def z281 : W := mkw 0x0fffff6dc828001e 0x007ffffb6e414000 0xffffffffc878000b 0xfffffffffe43c000

def z282 : W := mkw 0x07fd76807f6d5603 0xf03febb403fb6ab0 0xefe9ff807e71fe16 0xcf7f4ffc03f38ff0

def z283 : W := mkw 0x0082242100000008 0x0004112108000000 0x5196207000000000 0x028cb10380000000

def z284 : W := mkw 0x8000001002838540 0x2400000080141c2a 0x601020700f8f87ff 0x53008103807c7c3f

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000040188080660 0x280000200c404033

def z286 : W := mkw 0x4020c186fd7c62a3 0xca01060c37ebe315 0xa069c78ffffe67ff 0xfd034e3c7ffff33f

def z287 : W := mkw 0x877d40107fef8543 0xe43bea0083ff7c2a 0xf7ffc0007fff87fe 0x3fbffe0003fffc3f

def z288 : W := mkw 0x0000008000004200 0x0000000400000210 0x0000078000006610 0xc000003c00000330

def z289 : W := mkw 0x477dc186c83862a2 0x0a3bee0c3641c315 0xf7ffc78fc87867fb 0xffbffe3c7e43c33f

def z290 : W := mkw 0x05c0360026011401 0x302e01b0013008a0 0x6f803c003e019e16 0x4b7c01e001f00cf0

def z291 : W := mkw 0x0dc7b7258000000c 0x006e3db92c000000 0xffe7ff8180000000 0xefff3ffc0c000000

def z292 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e01f00189 0xd770c1c3f00f800c

def z293 : W := mkw 0x023d40007d6c0003 0xc011ea0003eb6000 0x101fc0007ffe000e 0x3080fe0003fff000

def z294 : W := mkw 0x0882bf6d8000001c 0x004415fb6c000000 0xa869ffff80000001 0xfd434ffffc000000

def z295 : W := mkw 0x0080368002015600 0x300401b400100ab0 0x69803f800e01fe16 0xcb4c01fc00700ff0

def z296 : W := mkw 0xc002c13780baa1e8 0x0e001609bc05d50f 0x101fc07f81fe01e9 0x3080fe03fc0ff00f

def z297 : W := mkw 0x4000818480004220 0x0200040c24000211 0x0000078180000660 0x0000003c0c000033

def z298 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0xee18387e70707801 0xd770c1c3f38383c0

def z299 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xff9e387e7ffff99f 0xfffcf1c3f3ffffcc

def z300 : W := mkw 0xc2baedffdbfbeffa 0xae15d76ffedfdf7f 0xffffffffffffffff 0xffffffffffffffff

def z301 : W := mkw 0x80a264317fef854b 0xe40513218bff7c2a 0x71962471ffff87ff 0x7b8cb1238ffffc3f

def z302 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x51962471878787f5 0x428cb1238c3c3c3f

def z303 : W := mkw 0x829a2c7913c38d58 0xa414d163c89e1c6a 0x7f963c71bf8f9fff 0x7bfcb1e38dfc7cff

def z304 : W := mkw 0x45e0f786ee3976a3 0x3a2f07bc3771cbb5 0xefe9ff8e7e71fe16 0xcf7f4ffc73f38ff0

def z305 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0xae08180e7070799b 0xd57040c0738383cc

def z306 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x8e69ffff80000001 0xc4734ffffc000000

def z307 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x118624718e0f87f1 0x688c31238c707c3f

def z308 : W := mkw 0x056000006c000003 0x002b000003600000 0xefe038007e01f816 0xcf7f01c003f00fc0

def z309 : W := mkw 0x877f40317dee814b 0xc43bfa018bef740a 0xf7ffc071fffe01ef 0x3fbffe038ffff00f

def z310 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x71962471800187f1 0x7b8cb1238c000c3f

def z311 : W := mkw 0x829a2c7913c38d58 0xa414d163c89e1c6a 0x5f96387037879804 0x02fcb1c381bc3cc0

def z312 : W := mkw 0x07ff64217d6c000b 0xc03ffb210beb6000 0xf7ffe471fffe000f 0x7fbfff238ffff000

def z313 : W := mkw 0x4238c9ded9f8ebb2 0x8a11c64ef6cfc75d 0xa079c7ffc9f867fb 0xfd03ce3ffe4fc33f

def z314 : W := mkw 0x0020008048004202 0x0001000402400210 0x0000000048006612 0x0000000002400330

def z315 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x8e08387e7071f991 0xc47041c3f3838fcc

def z316 : W := mkw 0x8dc7b7358283854c 0x246e3db9ac141c2a 0x71f7e7f18f8f87ff 0x7b8fbf3f8c7c7c3f

def z317 : W := mkw 0x075d085a35d4a991 0xc83ae842d1aea54c 0xff9e387e77f7f99f 0xd7fcf1c3f3bfbfcc

def z318 : W := mkw 0x0000001000808100 0x0000000080040408 0xee1038707181f99f 0xd77081c3838c0fcc

def z319 : W := mkw 0x0218001211d0a980 0x8810c000908e854c 0xe618000071f1f99e 0x1730c000038f8fcc

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000808000a 0x3900000000404000

def z321 : W := mkw 0x8000001002838540 0x2400000080141c2a 0x0000000007878004 0x00000000003c3c00

def z322 : W := mkw 0x0fffbfedee01561f 0x307ffdff6f700ab0 0xffffffff8e000601 0xfffffffffc700030

def z323 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xdffffbfe00000000 0x86ffffdff0000000

def z324 : W := mkw 0x85e236b16e83d74b 0x342f11b58b741eba 0xfff63ff07f87fe16 0xcfffb1ff83fc3ff0

def z325 : W := mkw 0x002040007d6c0003 0xc001020003eb6000 0xa069c0007ffe000e 0x3d034e0003fff000

def z326 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c38e487867fa 0x84034e1c7243c33f

def z327 : W := mkw 0x0218085811c08910 0x8010c042c08e0448 0x6e1038703181999f 0x537081c3818c0ccc

def z328 : W := mkw 0x0218085811c08910 0x8010c042c08e0448 0x0010007001800000 0x00008003800c0000

def z329 : W := mkw 0x8002003100828148 0x040010018804140a 0x70162071818f81ff 0x7380b1038c0c7c0f

def z330 : W := mkw 0x4020c196d9f8eba2 0x8a01060cb6cfc75d 0xa069c78ff9f9ffff 0xfd034e3c7fcfcfff

def z331 : W := mkw 0x0000000200102080 0x0800000010008104 0x8008000e40706000 0x8400400072038300

def z332 : W := mkw 0x4020c184c8284222 0x0201060c26414211 0xa061c781c8086672 0xed030e3c0e404333

def z333 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0x0009c00000700000 0x00004e0000038000

def z334 : W := mkw 0xc082a5b78293e7e8 0x2e04152dbc149f3f 0x000027ff8001e7f1 0xc000013ffc000f3f

def z335 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0x0008000e00700000 0x0000400070038000

def z336 : W := mkw 0x07fd76807f6d5603 0xf03febb403fb6ab0 0xf7ffc7807ffe060e 0x3fbffe3c03fff030

def z337 : W := mkw 0x0000084800000010 0x0000004240000000 0x0800387e00000001 0xc04001c3f0000000

def z338 : W := mkw 0x0238485a7dfca993 0xc811c242d3efe54c 0xee18387e7ffff99f 0xd770c1c3f3ffffcc

def z339 : W := mkw 0x0218085a0090a990 0x0810c042d004854c 0xee18387e0001f991 0xd770c1c3f0000fcc

def z340 : W := mkw 0x0a9abf7f91d0a99c 0x8854d5fbfc8e854c 0xee183ffff1f1f99f 0xd770c1ffff8f8fcc

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x601000000180000e 0x13008000000c0000

def z342 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0xee79fbfe00000001 0xd773cfdff0000000

def z343 : W := mkw 0x87ff64317fef854b 0xe43ffb218bff7c2a 0xf7ffe0707fff800e 0x3fbfff0383fffc00

def z344 : W := mkw 0x07d83e5a37d1bd91 0xb83ec1f2d1be8dec 0xef98387e77f1f99f 0xd77cc1c3f3bf8fcc

def z345 : W := mkw 0x4fffffeffd7c62bf 0xca7fffff7febe315 0xfffffffffffe67ff 0xfffffffffffff33f

def z346 : W := mkw 0x0020400248382082 0x080102001241c104 0xa069c00e4878619b 0xfd034e007243c30c

def z347 : W := mkw 0x0fdfb7258000000c 0x007efdb92c000000 0xf7ffc78180000000 0x3fbffe3c0c000000

def z348 : W := mkw 0x8082243100828148 0x040411218804140a 0x71962471818e01e9 0x7b8cb1238c0c700f

def z349 : W := mkw 0x0dc7b7258000000c 0x006e3db92c000000 0xb1efc78f80000001 0xfd8f7e3c7c000000

def z350 : W := mkw 0x4f7ddbcec83862b6 0x0a7beede7641c315 0x8e69db8e40706000 0x84734edc72038300

def z351 : W := mkw 0x00a024804a014602 0x2005012402500a30 0xe1e027804e01e616 0xcf0f013c02700f30

def z352 : W := mkw 0x85e236b16e83d74b 0x342f11b58b741eba 0x71f627f18f8f87ff 0x7b8fb13f8c7c7c3f

def z353 : W := mkw 0x0000001000808100 0x0000000080040408 0x4010207001818004 0x02008103800c0c00

def z354 : W := mkw 0x4020c184c8284222 0x0201060c26414211 0x0061c38000000000 0x00030e1c00000000

def z355 : W := mkw 0x07781aca7d507a93 0x983bc0d653ea83d4 0x8e681b8e70707800 0x847340dc738383c0

def z356 : W := mkw 0x075d000035440001 0xc03ae80001aa2000 0xf79e000077f6000e 0x17bcf00003bfb000

def z357 : W := mkw 0x40204082483862a2 0x0a0102041241c315 0xa008000e487867fb 0xd50040007243c33f

def z358 : W := mkw 0x0000000002010400 0x2000000000100820 0x000000000e018616 0x0000000000700c30

def z359 : W := mkw 0x0000001000808100 0x0000000080040408 0x000000000181819e 0x00000000000c0c0c

def z360 : W := mkw 0x075d000035440001 0xc03ae80001aa2000 0x0600000030000000 0x0030000001800000

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000401800007f1 0x400000200c00003f

def z362 : W := mkw 0x05c0360002010400 0x202e01b000100820 0xefe03f800e018616 0xcf7f01fc00700c30

def z363 : W := mkw 0x0fdfff6d916c001c 0xc07efffb6c8b6000 0xffffffff81fe0009 0xfffffffffc0ff000

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000007001f816 0x0000000003800fc0

def z365 : W := mkw 0x0218000011400000 0x8010c000008a0000 0x8608000070700000 0x0430400003838000

def z366 : W := mkw 0x05e036826e117683 0x382f01b413708bb4 0xefe83f8e7e71ff9f 0xdf7f41fc73f38ffc

def z367 : W := mkw 0x0a9fbf6d8000001c 0x0054fdfb6c000000 0x181fffff80000001 0xf0c0fffffc000000

def z368 : W := mkw 0x802000906e83d743 0x3401000483741eba 0x000000007f8ffffe 0x0000000003fc7fff

def z369 : W := mkw 0x07f836807f415603 0xb03fc1b403fa0ab0 0xeff83f807ff1fe1e 0xdf7fc1fc03ff8ff0

def z370 : W := mkw 0x0882b7258000000c 0x004415b92c000000 0x0000078180000000 0x0000003c0c000000

def z371 : W := mkw 0x0fdfbf7f91d0a99c 0x887efdfbfc8e854c 0xffffffff81f00189 0xfffffffffc0f800c

def z372 : W := mkw 0x002040127dfca983 0xc801020093efe54c 0x000000007ffff99e 0x0000000003ffffcc

def z373 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0xa008078fc07067fb 0xd500403c7e03833f

def z374 : W := mkw 0x829a2c7902838558 0x2414d163c8141c2a 0xff9e3c7f8f8f87ff 0xfffcf1e3fc7c7c3f

def z375 : W := mkw 0xc082e53782bba5e8 0x2e041729bc15dd2f 0x719fe47f8fff87ff 0x7b8cff23fc7ffc3f

def z376 : W := mkw 0x821a087b11d2a9d8 0x8c10d043d88e954e 0xfe1e387ff1fff9ff 0xf7f0f1c3ff8fffcf

def z377 : W := mkw 0x4000c10480280020 0x0200060824014001 0x0001c00180080060 0x20000e000c004003

def z378 : W := mkw 0x0218084800000010 0x0010c04240000000 0x0018007e00000001 0x1000c003f0000000

def z379 : W := mkw 0x0080240002010400 0x2004012000100820 0x0000240000018610 0x4000012000000c30

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x719604018f8e07ff 0x7b8cb0200c7c703f

def z381 : W := mkw 0x05e036006e011403 0x302f01b0037008a0 0xefe038007e019806 0x0f7f01c003f00cc0

def z382 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fc0706001 0xfd034e3c7e038300

def z383 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x5ff7fff180000000 0x2affbfff8c000000

def z384 : W := mkw 0xc0a2e5b5caabc76a 0x2605172dae555e3b 0x71f7e7f18f8f87ff 0x7b8fbf3f8c7c7c3f

def z385 : W := mkw 0x808236b10283d748 0x340411b588141eba 0x08003ff18001fff1 0xc04001ff8c000fff

def z386 : W := mkw 0x0218084a00102090 0x0810c04250008104 0xee18387e4070619b 0xd770c1c3f203830c

def z387 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x8fe01f807e007e00 0x8c7f00fc03f003f0

def z388 : W := mkw 0x8fdfbf6d8203045c 0x247efdfb6c101822 0xffffffff8e0e0661 0xfffffffffc707033

def z389 : W := mkw 0x8080241002838540 0x2404012080141c2a 0x618024000f8f87fe 0x4b0c0120007c7c3f

def z390 : W := mkw 0x0de2bfedee01561f 0x306f15ff6f700ab0 0xefe03ffffe01fe17 0xcf7f01fffff00ff0

def z391 : W := mkw 0x0fddbf4c80000014 0x007eedfa64000000 0xefe9ff8e00000000 0xcf7f4ffc70000000

def z392 : W := mkw 0x075d000000000000 0x003ae80000000000 0x8669c00000000000 0x04334e0000000000

def z393 : W := mkw 0x4de7f7a5c828422e 0x026f3fbd2e414211 0x11e7c78188080660 0x288f3e3c0c404033

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x6010207000000001 0x5300810380000000

def z395 : W := mkw 0x4fffffffd9f8ebbe 0x8a7ffffffecfc75d 0xfffffffff9f9ffff 0xffffffffffcfcfff

def z396 : W := mkw 0x077d40006c2c0003 0x403bea0003616000 0xf7ffc0000e0e0000 0x3fbffe0000707000

def z397 : W := mkw 0x0080240002010400 0x2004012000100820 0x719624000f8f861e 0x7b8cb120007c7c30

def z398 : W := mkw 0x0fff3ee96e01561f 0x307ff9f74b700ab0 0xfff63ff07e01fe16 0xcfffb1ff83f00ff0

def z399 : W := mkw 0x0fffff7ffdfca99f 0xc87ffffbffefe54c 0xfffffffffffff99f 0xffffffffffffffcc

def z400 : W := mkw 0x40a0f786ca3976a2 0x3a0507bc3651cbb5 0xa869ff8fc879fffb 0xfd434ffc7e43cfff

def z401 : W := mkw 0x8000001002838540 0x2400000080141c2a 0x200004018f8f87ff 0x790000200c7c7c3f

def z402 : W := mkw 0x0020000048000002 0x0001000002400000 0xa060000048000002 0x0d03000002400000

def z403 : W := mkw 0x40204082483862a2 0x0a0102041241c315 0x20000401c87867fb 0x790000200e43c33f

def z404 : W := mkw 0x4fdfbfef801062bc 0x0a7efdff7c008315 0xffffffff800067f1 0xfffffffffc00033f

def z405 : W := mkw 0x0080241002818500 0x2004012080140c28 0x619024700f81879f 0x5b0c8123807c0c3c

def z406 : W := mkw 0x0020008048004202 0x0001000402400210 0xa0600781c80867fb 0xfd03003c0e40433f

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000000019b 0x510000000000000c

def z408 : W := mkw 0x05c2362100000008 0x002e11b108000000 0xfff63ff180000001 0xffffb1ff8c000000

def z409 : W := mkw 0x0000085a0090a990 0x08000042d004854c 0x0000007e00000181 0x00000003f000000c

def z410 : W := mkw 0x056012806c005203 0x102b009403600290 0xee603b807001f816 0xc77301dc03800fc0

def z411 : W := mkw 0x0218895e91d0a990 0x8810c44af48e854c 0xee79fffff1f1f99f 0xff73cfffff8f8fcc

def z412 : W := mkw 0x075d4000116c0000 0xc03aea00008b6000 0xf7ffc00001fe0008 0x3fbffe00000ff000

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x7196000000000000 0x3b8cb00000000000

def z414 : W := mkw 0x07fd36807f455603 0xf03fe9b403fa2ab0 0xfff63f807f87fe16 0xcfffb1fc03fc3ff0

def z415 : W := mkw 0xc0a264b34abbe7ea 0x2e0513259a55df3f 0x71962471cfffe7ff 0x7b8cb1238e7fff3f

def z416 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f800e000600 0xcf7f01fc00700030

def z417 : W := mkw 0x0000001000808100 0x0000000080040408 0x0000207000018191 0x4000010380000c0c

def z418 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x618024718e0187f7 0x4b0c01238c700c3f

def z419 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xe7e9c0007e700006 0x0f3f4e0003f38000

def z420 : W := mkw 0x05e03eda6e91ff93 0x382f01f6d3748ffc 0xefe03ffe7e01ff97 0xcf7f01fff3f00ffc

def z421 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x967fc00071fe0008 0x34b3fe00038ff000

def z422 : W := mkw 0x4238c9ced9786ab2 0x8a11c64e76cbc355 0x8e69db8e70707800 0x84734edc738383c0

def z423 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0069c78f887807e9 0x38034e3c7c43c03f

def z424 : W := mkw 0x021d485a11fca990 0xc810ea42d08fe54c 0x101fc07e01fe0189 0x3080fe03f00ff00c

def z425 : W := mkw 0x0fdfbf7f8090a99c 0x087efdfbfc04854c 0xffffffff8001f991 0xfffffffffc000fcc

def z426 : W := mkw 0x40204082483862a2 0x0a0102041241c315 0xa0600780487867fa 0xcd03003c0243c33f

def z427 : W := mkw 0x05c0360026011401 0x302e01b0013008a0 0xefe03f8036019804 0xcf7f01fc01b00cc0

def z428 : W := mkw 0x0000001000808100 0x0000000080040408 0x719620700f8f819f 0x7b8cb103807c7c0c

def z429 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c38e4070619b 0xd5034e1c7203830c

def z430 : W := mkw 0x077d52807d6c5203 0xd03bea9403eb6290 0xffffdb807ffe780e 0xbffffedc03fff3c0

def z431 : W := mkw 0x40204082483862a2 0x0a0102041241c315 0xa069c000487867fa 0x3d034e000243c33f

def z432 : W := mkw 0x0218000211502080 0x8810c000108a8104 0xe618000e71f0619f 0xd730c000738f830c

def z433 : W := mkw 0x821f403111ee8148 0xc410fa01888f740a 0x101fc07181fe01e9 0x3080fe038c0ff00f

def z434 : W := mkw 0x05e576806e2d5603 0x702f2bb403716ab0 0xffe7ff807e0ffe16 0xefff3ffc03f07ff0

def z435 : W := mkw 0x0020400048280002 0x0001020002414000 0x000000004878000a 0x000000000243c000

def z436 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78e48706612 0xcd034e3c72438330

def z437 : W := mkw 0x0000085a11d0a990 0x88000042d08e854c 0x0800387e71f1f99f 0xc04001c3f38f8fcc

def z438 : W := mkw 0x00a036804a015602 0x300501b402500ab0 0xa8603f804801fe12 0xcd4301fc02400ff0

def z439 : W := mkw 0x802040107fef8543 0xe401020083ff7c2a 0x000000007fff87fe 0x0000000003fffc3f

def z440 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0xf61fc00071fe000e 0x37b0fe00038ff000

def z441 : W := mkw 0x07df242100000008 0x003ef92108000000 0xf7ffe47180000001 0x7fbfff238c000000

def z442 : W := mkw 0x075d000000000000 0x003ae80000000000 0x5796000000000000 0x02bcb00000000000

def z443 : W := mkw 0x4882bfef801062bc 0x0a4415ff7c008315 0x08003fff800067f1 0xc04001fffc00033f

def z444 : W := mkw 0x0000001011c08900 0x80000000808e0448 0x0000000031819804 0x00000000018c0cc0

def z445 : W := mkw 0x07d83e4800000010 0x003ec1f240000000 0xeff83ffe00000001 0xdf7fc1fff0000000

def z446 : W := mkw 0x4fffffedc828423e 0x027fffff6e414211 0xffffffff88080661 0xfffffffffc404033

def z447 : W := mkw 0x0020408048284202 0x0001020402414210 0xa069c7804878661a 0xfd034e3c0243c330

def z448 : W := mkw 0x0000001211d0a980 0x88000000908e854c 0xee00380071f1f99e 0xc77001c0038f8fcc

def z449 : W := mkw 0x402040827d7c62a3 0xca01020413ebe315 0x000000007ffe67fe 0x0000000003fff33f

def z450 : W := mkw 0x85e036906e83d743 0x342f01b483741eba 0xefe03f807f8ffffe 0xcf7f01fc03fc7fff

def z451 : W := mkw 0x075d085835c48911 0xc03ae842c1ae2448 0x5f96387037879804 0x02fcb1c381bc3cc0

def z452 : W := mkw 0x85e764216e2f044b 0x642f3b210b717822 0x11e7c4018e0e0660 0x288f3e200c707033

def z453 : W := mkw 0x0f5d9b5e91d0a994 0x887aecdaf48e854c 0xee79fbfe71f1f99f 0xd773cfdff38f8fcc

def z454 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc00070700000 0x3fbffe0003838000

def z455 : W := mkw 0xc020c196cabbe7e2 0x2e01060cb655df3f 0xa069c78fcfffe7ff 0xfd034e3c7e7fff3f

def z456 : W := mkw 0x05c0360026011401 0x302e01b0013008a0 0xef8038007601f816 0xc77c01c003b00fc0

def z457 : W := mkw 0x0fffbfedc800421e 0x007ffdff6e400210 0xffffffffc8006613 0xfffffffffe400330

def z458 : W := mkw 0x0000085a0090a990 0x08000042d004854c 0x6810387e0181f99f 0xd34081c3f00c0fcc

def z459 : W := mkw 0x0020008248106282 0x0801000412408314 0xa068078e4870679b 0xdd03403c7243833c

def z460 : W := mkw 0x4000c106803820a0 0x0a0006083401c105 0xa009c00fc07861fb 0xf5004e007e03c30f

def z461 : W := mkw 0x8082243313d3adc8 0xac041121989e9d6e 0x71962471ffffffff 0x7b8cb1238fffffff

def z462 : W := mkw 0x8002003100828148 0x040010018804140a 0x719600718f8e01ef 0x3b8cb0038c7c700f

def z463 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xa669c0007878000a 0x3d334e0003c3c000

def z464 : W := mkw 0x80822c7b0293add8 0x2c041163d8149d6e 0x79963c7f8f8fffff 0xfbccb1e3fc7c7fff

def z465 : W := mkw 0x85e224316e83854b 0x242f11218b741c2a 0xf7f62471ff8f87ff 0x7fbfb1238ffc7c3f

def z466 : W := mkw 0x0218085800808110 0x0010c042c0040408 0xee18387e0181819f 0xd770c1c3f00c0c0c

def z467 : W := mkw 0x0000810480000000 0x0000040824000000 0x0009c00f80000001 0x30004e007c000000

def z468 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xa1e007804e006612 0xcd0f003c02700330

def z469 : W := mkw 0x0540000024000001 0x002a000001200000 0x4780000036000004 0x023c000001b00000

def z470 : W := mkw 0x07f83eca7f517e93 0xb83fc1f653fa8bf4 0xefe83f8e7e71fe16 0xcf7f41fc73f38ff0

def z471 : W := mkw 0x40004002003820a0 0x0a0002001001c105 0x00000000007801e8 0x000000000003c00f

def z472 : W := mkw 0x056000806e015603 0x302b000403700ab0 0xe7e000007e01fe16 0x0f3f000003f00ff0

def z473 : W := mkw 0x05e236a16e01560b 0x302f11b50b700ab0 0xfff63ff1fe01fe17 0xffffb1ff8ff00ff0

def z474 : W := mkw 0x05e576806e2d5603 0x702f2bb403716ab0 0x11e7c7800e0e0600 0x288f3e3c00707030

def z475 : W := mkw 0x4fdfff6f803820bc 0x0a7efffb7c01c105 0xffffffff807801e9 0xfffffffffc03c00f

def z476 : W := mkw 0x80a224b16e83d74b 0x340511258b741eba 0x71962471ff8fffff 0x7b8cb1238ffc7fff

def z477 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x0018007e71f1f99f 0x1000c003f38f8fcc

def z478 : W := mkw 0x40000082001062a0 0x0a00000410008315 0x00000000000067f0 0x000000000000033f

def z479 : W := mkw 0x0218085811c08910 0x8010c042c08e0448 0xee18387071f1980e 0x1770c1c3838f8cc0

def z480 : W := mkw 0x40a2e5a7c83862aa 0x0a05172d3e41c315 0xf1ffe7ffc87867fb 0xff8fff3ffe43c33f

def z481 : W := mkw 0x0fdfbf6f8010209c 0x087efdfb7c008104 0xffffffffc070619b 0xfffffffffe03830c

def z482 : W := mkw 0x4000c106803820a0 0x0a0006083401c105 0x0009c00e00700000 0x00004e0070038000

def z483 : W := mkw 0x0fffff6dfd6c001f 0xc07ffffb6feb6000 0xfffffffff0700001 0xffffffffff838000

def z484 : W := mkw 0x8002002100020048 0x0400100108001002 0x10060001800e0060 0x208030000c007003

def z485 : W := mkw 0x0000810680102080 0x0800040834008104 0xa069c78fc070619b 0xfd034e3c7e03830c

def z486 : W := mkw 0x05e024006e010403 0x202f012003700820 0xe7e024007e018616 0x4f3f012003f00c30

def z487 : W := mkw 0x075d000035440001 0xc03ae80001aa2000 0xf7ffc00037860004 0x3fbffe0001bc3000

def z488 : W := mkw 0x0d45930480000004 0x006a2c9824000000 0x0061c38000000000 0x00030e1c00000000

def z489 : W := mkw 0x056040006c280003 0x002b020003614000 0xe7e9c0007e78000e 0x3f3f4e0003f3c000

def z490 : W := mkw 0x0000000011400000 0x80000000008a0000 0x0000000071f0000e 0x00000000038f8000

def z491 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x4fe03f803e019e04 0x0a7f01fc01f00cf0

def z492 : W := mkw 0x07dd360000000000 0x003ee9b000000000 0xffffff8000000000 0xfffffffc00000000

def z493 : W := mkw 0xc0a2e5b7cabbe7ea 0x2e05172dbe55df3f 0xa069e7ffc879e7fb 0xfd034f3ffe43cf3f

def z494 : W := mkw 0x477dc186fd7c62a3 0xca3bee0c37ebe315 0x8669c38e70706000 0x84334e1c73838300

def z495 : W := mkw 0x4238c9ced9786ab2 0x8a11c64e76cbc355 0xae69df8ff8787ffb 0xfd734efc7fc3c3ff

def z496 : W := mkw 0x87ff64217f6f044b 0xe43ffb210bfb7822 0xf7ffc401fffe066e 0x3fbffe200ffff033

def z497 : W := mkw 0x021d000000000000 0x0010e80000000000 0x101fc00000000000 0x3080fe0000000000

def z498 : W := mkw 0x8000001002838540 0x2400000080141c2a 0x00000000000187f0 0x0000000000000c3f

def z499 : W := mkw 0x0000000200102080 0x0800000010008104 0xee08380e7071f99f 0xd77041c073838fcc

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000040006012 0xc500000002000300

def z501 : W := mkw 0x0080368002015600 0x300401b400100ab0 0x0000078000000600 0x0000003c00000030

def z502 : W := mkw 0x8fdfbf7d8082815c 0x047efdfbec04140a 0xffffffff818e01e9 0xfffffffffc0c700f

def z503 : W := mkw 0x8082a53582838548 0x24041529ac141c2a 0xf1ffe7ff8f8f87ff 0xff8fff3ffc7c7c3f

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00180070007800 0x847000c0038003c0

def z505 : W := mkw 0x8882bf7d8283855c 0x244415fbec141c2a 0x79963fff8f8f87ff 0xfbccb1fffc7c7c3f

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000040008000612 0x4900002000400030

def z507 : W := mkw 0x0082242100000008 0x0004112108000000 0x71962471880807fb 0x7b8cb1238c40403f

def z508 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c38e4878600a 0xbd034e1c7243c300

def z509 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0061c78f880867f1 0xe8030e3c7c40433f

def z510 : W := mkw 0x077dc104fd6c0003 0xc03bee0827eb6000 0xf7ffc78ffffe000f 0xffbffe3c7ffff000

def z511 : W := mkw 0x029a2c7b11d0a998 0x8814d163d88e854c 0xff9e3c7ff1f1f99f 0xfffcf1e3ff8f8fcc

def z512 : W := mkw 0x0000008002015600 0x3000000400100ab0 0x000000000001fe10 0x0000000000000ff0

def z513 : W := mkw 0x829f643113ef8548 0xe414fb21889f7c2a 0x719fe4718fff87ff 0x7b8cff238c7ffc3f

def z514 : W := mkw 0x0dc7b7258000000c 0x006e3db92c000000 0x71f7e7f180000001 0x7b8fbf3f8c000000

def z515 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x4f8038007e01fe16 0x027c01c003f00ff0

def z516 : W := mkw 0x07fd76007f6d1403 0xf03febb003fb68a0 0xfffff8007fff980e 0x3fffffc003fffcc0

def z517 : W := mkw 0x05e0368048004202 0x002f01b402400210 0xefe03f8048006612 0xcf7f01fc02400330

def z518 : W := mkw 0x002000806e015603 0x3001000403700ab0 0x000000000e000600 0x0000000000700030

def z519 : W := mkw 0x0fdf3e690000001c 0x007ef9f348000000 0xff9e387e00000001 0xd7fcf1c3f0000000

def z520 : W := mkw 0x0080240002010400 0x2004012000100820 0x618024018e0987ff 0x7b0c01200c704c3f

def z521 : W := mkw 0x808224330293a5c8 0x2c04112198149d2e 0xf19e247fcfffe7ff 0xff8cf123fe7fff3f

def z522 : W := mkw 0x4020c9dec8b8ebb2 0x0a01064ef645c75d 0xa869ffffc879fffb 0xfd434ffffe43cfff

def z523 : W := mkw 0x0020400048280002 0x0001020002414000 0xa069c401c87807fb 0x7d034e200e43c03f

def z524 : W := mkw 0x056540006c2c0003 0x402b2a0003616000 0x71f7c0000f8e000e 0x3b8fbe00007c7000

def z525 : W := mkw 0x0082242100000008 0x0004112108000000 0x719624718f8e000f 0x7b8cb1238c7c7000

def z526 : W := mkw 0x002040007d6c0003 0xc001020003eb6000 0x0000000070700000 0x0000000003838000

def z527 : W := mkw 0x0082242100000008 0x0004112108000000 0x1186040180000000 0x288c30200c000000

def z528 : W := mkw 0x07fd76007d6c0003 0xc03febb003eb6000 0xffffff807ffe000e 0xfffffffc03fff000

def z529 : W := mkw 0x80a224b14a83c74a 0x240511258a541e3a 0xf1f627f1cf8fe7ff 0xff8fb13f8e7c7f3f

def z530 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x719620700f8f800e 0x3b8cb103807c7c00

def z531 : W := mkw 0x077d400048280002 0x003bea0002414000 0xf7ffc0004878000a 0x3fbffe000243c000

def z532 : W := mkw 0xc0a2e5a7ca3b66ea 0x2e05172d3e51db37 0xb1efc78fce7e67fb 0xfd8f7e3c7e73f33f

def z533 : W := mkw 0x8002003100828148 0x040010018804140a 0x1016007001860000 0x0080b003800c3000

def z534 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x01e007807e01fe16 0x080f003c03f00ff0

def z535 : W := mkw 0x0218085811c08910 0x8010c042c08e0448 0xee18387e31819805 0xd770c1c3f18c0cc0

def z536 : W := mkw 0x0020400048280002 0x0001020002414000 0x0061c00008080000 0x28030e0000404000

def z537 : W := mkw 0x075d000035440001 0xc03ae80001aa2000 0x779600003f8e000e 0x3bbcb00001fc7000

def z538 : W := mkw 0x029a2c6900000018 0x0014d16348000000 0xff9e3c7f80000001 0xfffcf1e3fc000000

def z539 : W := mkw 0x0540120024001001 0x102a009001200080 0x0e00180030001800 0x007000c0018000c0

def z540 : W := mkw 0x0f5d1a4800000014 0x007ae8d240000000 0x0e00180000000000 0x007000c000000000

def z541 : W := mkw 0x002040007d6c0003 0xc001020003eb6000 0x719600007ffe000e 0x3b8cb00003fff000

def z542 : W := mkw 0x002000006c000003 0x0001000003600000 0x000000007e000006 0x0000000003f00000

def z543 : W := mkw 0x05e076807f6d5603 0xf02f03b403fb6ab0 0xefe03f807ffffe1e 0xcf7f01fc03fffff0

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0xe600000070000006 0x0730000003800000

def z546 : W := mkw 0x07d83e5a11d0a990 0x883ec1f2d08e854c 0xeff83ffe71f1f99f 0xdf7fc1fff38f8fcc

def z547 : W := mkw 0x05e0b784ee015603 0x302f05bc27700ab0 0xefe9ff8ffe01fe17 0xff7f4ffc7ff00ff0

def z548 : W := mkw 0x477d40827d7c62a3 0xca3bea0413ebe315 0xf7ffc0007ffe67fe 0x3fbffe0003fff33f

def z549 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x8669c0007ffe000e 0x04334e0003fff000

def z550 : W := mkw 0x4020c184c8284222 0x0201060c26414211 0xa069c78f88080661 0xfd034e3c7c404033

def z551 : W := mkw 0x056040007d6c0003 0xc02b020003eb6000 0xe7e000007ffe000e 0x0f3f000003fff000

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00800004070000a 0x1500400002038000

def z553 : W := mkw 0x0000000200102080 0x0800000010008104 0xa008040fc87867fb 0xfd0040207e43c33f

def z554 : W := mkw 0x4560c186ec3862a3 0x0a2b060c3761c315 0xe7e9c78ffe7867ff 0xff3f4e3c7ff3c33f

def z555 : W := mkw 0x056540006c2c0003 0x402b2a0003616000 0x0061c00000000000 0x00030e0000000000

def z556 : W := mkw 0x021d000011440000 0xc010e800008a2000 0x1016000001860000 0x0080b000000c3000

def z557 : W := mkw 0xc5e2f7b7eebbf7eb 0x3e2f17bdbf75dfbf 0xffffffffffffffff 0xffffffffffffffff

def z558 : W := mkw 0x85c2363126839549 0x342e11b189341caa 0x7f963c71bf8f9fff 0x7bfcb1e38dfc7cff

def z559 : W := mkw 0x477dc186fd7c62a3 0xca3bee0c37ebe315 0xa669c78ff87867fb 0xfd334e3c7fc3c33f

def z560 : W := mkw 0x4238c186d97862a2 0x8a11c60c36cbc315 0xe679c78ff9f867ff 0xff33ce3c7fcfc33f

def z561 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x61e027800e018616 0x4b0f013c00700c30

def z562 : W := mkw 0x0f5d9b4e91502894 0x887aecda748a8144 0x8e69db8e70707800 0x84734edc738383c0

def z563 : W := mkw 0x0fdfbf7d91c0891c 0x807efdfbec8e0448 0xffffffffb1819805 0xfffffffffd8c0cc0

def z564 : W := mkw 0x85c2363126839549 0x342e11b189341caa 0x5f96387037879804 0x02fcb1c381bc3cc0

def z565 : W := mkw 0x0000000026011401 0x30000000013008a0 0x0000000036019804 0x0000000001b00cc0

def z566 : W := mkw 0x0fffff6dec2c001f 0x407ffffb6f616000 0xffffffff8e0e0001 0xfffffffffc707000

def z567 : W := mkw 0x0fdf3e690000001c 0x007ef9f348000000 0x7f963c7180000001 0x7bfcb1e38c000000

def z568 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x97efc0007e7e0000 0x2cbf7e0003f3f000

def z569 : W := mkw 0x4218c95e91f8a9b0 0x8a10c64af48fc54d 0xee19f87ff1f9f9ff 0xf770cfc3ff8fcfcf

def z570 : W := mkw 0x05e036806c005203 0x102f01b403600290 0xefe03f8070007800 0xcf7f01fc038003c0

def z571 : W := mkw 0x0080240002010400 0x2004012000100820 0x018004000e000600 0x080c002000700030

def z572 : W := mkw 0x0218084800000010 0x0010c04240000000 0x4e10387000000000 0x027081c380000000

def z573 : W := mkw 0x4000c106803820a0 0x0a0006083401c105 0xa069c78f807801e9 0xfd034e3c7c03c00f

def z574 : W := mkw 0x023d4000596c0002 0xc011ea0002cb6000 0xb07fc00049fe000a 0x3d83fe00024ff000

def z575 : W := mkw 0x8082242102030448 0x2404112108101822 0x719604018f8e066e 0x3b8cb0200c7c7033

def z576 : W := mkw 0x0238485a59f8a992 0x8811c242d2cfc54c 0xee79f87e79f9f99f 0xff73cfc3f3cfcfcc

def z577 : W := mkw 0x00a036806e015603 0x300501b403700ab0 0x08003f807e01fe16 0xc04001fc03f00ff0

def z578 : W := mkw 0x0218084811400010 0x8010c042408a0000 0xee18387e71f0000f 0xd770c1c3f38f8000

def z579 : W := mkw 0x0218085811c08910 0x8010c042c08e0448 0xee1038707181f816 0xc77081c3838c0fc0

def z580 : W := mkw 0x07d83e5837c19d11 0xb03ec1f2c1be0ce8 0x4f90387037819804 0x027c81c381bc0cc0

def z581 : W := mkw 0x0de7b7a5ee01560f 0x306f3dbd2f700ab0 0xffe7ff81fe01fe16 0xefff3ffc0ff00ff0

def z582 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x10162471818f87f9 0x7080b1238c0c7c3f

def z583 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0xee08380e7071f816 0xc77041c073838fc0

def z584 : W := mkw 0x07fd7eda7ffdff93 0xf83febf6d3ffeffc 0xfffffffe7fffff9f 0xfffffffff3fffffc

def z585 : W := mkw 0x0fff7e697d6c001f 0xc07ffbf34beb6000 0xfffff8707ffe000e 0x3fffffc383fff000

def z586 : W := mkw 0x4020c196c8b8e3a2 0x0a01060cb645c71d 0xe079e7ffc9f9e7ff 0xff03cf3ffe4fcf3f

def z587 : W := mkw 0x0fffbfedec00521f 0x107ffdff6f600290 0xfffffffff0007801 0xffffffffff8003c0

def z588 : W := mkw 0x0a1f896d8000001c 0x0050fc4b6c000000 0xfe1ff87f80000001 0xf7f0ffc3fc000000

def z589 : W := mkw 0x021d485a11fca990 0xc810ea42d08fe54c 0xfe1ff87e71fff99f 0xf7f0ffc3f38fffcc

def z590 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x579600007ffe000e 0x02bcb00003fff000

def z591 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xa018007e41f0619b 0xd500c003f20f830c

def z592 : W := mkw 0x056000006c000003 0x002b000003600000 0x01e000000e000000 0x080f000000700000

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x118600000e0e0000 0x288c300000707000

def z594 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x51962071878f81ed 0x328cb1038c3c7c0f

def z595 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x8e18187e71f07989 0x9470c0c3f38f83cc

def z596 : W := mkw 0x8002003100828148 0x040010018804140a 0x30160471898e07fb 0x7980b0238c4c703f

def z597 : W := mkw 0x4000c106803820a0 0x0a0006083401c105 0x2009c40f887807fb 0x79004e207c43c03f

def z598 : W := mkw 0x00803eda0291ff90 0x380401f6d0148ffc 0x08003ffe0001ff91 0xc04001fff0000ffc

def z599 : W := mkw 0x077d40807f6d5603 0xf03bea0403fb6ab0 0xf7ffc0007ffffe1e 0x3fbffe0003fffff0

def z600 : W := mkw 0x48a2ffefc83862be 0x0a4517ff7e41c315 0xa869ffffc87867fb 0xfd434ffffe43c33f

def z601 : W := mkw 0x400089de8090ebb0 0x0a00044ef404875d 0x08003fff8001fff1 0xc04001fffc000fff

def z602 : W := mkw 0x0de7b7a5ee01560f 0x306f3dbd2f700ab0 0x11e7c7818e000600 0x288f3e3c0c700030

def z603 : W := mkw 0x4560d386ec3872a3 0x1a2b069c3761c395 0x8e69db8e70707800 0x84734edc738383c0

def z604 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x7196247187878005 0x7b8cb1238c3c3c00

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0xa008000e00000001 0xd500400070000000

def z606 : W := mkw 0x85c2363102838548 0x242e11b188141c2a 0xfff63ff18f8f87ff 0xffffb1ff8c7c7c3f

def z607 : W := mkw 0x829a2c7b13d3add8 0xac14d163d89e9d6e 0xff9e387e77f7f99f 0xd7fcf1c3f3bfbfcc

def z608 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519624718f8f8664 0x2a8cb1238c7c7c33

def z609 : W := mkw 0x077d48587dec8913 0xc03bea42c3ef6448 0xfffff8707fff980e 0x3fffffc383fffcc0

def z610 : W := mkw 0x0fdf3e7b11d0a99c 0x887ef9f3d88e854c 0xff9e387e71f1f99f 0xd7fcf1c3f38f8fcc

def z611 : W := mkw 0x8218085a13d3add0 0xac10c042d09e9d6e 0xee18387e7fffffff 0xd770c1c3f3ffffff

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x5196000007860004 0x028cb000003c3000

def z613 : W := mkw 0x4000c186803862a0 0x0a00060c3401c315 0x0009c78f807867f9 0xf0004e3c7c03c33f

def z614 : W := mkw 0x0080360000000000 0x000401b000000000 0x08003f8000000000 0xc04001fc00000000

def z615 : W := mkw 0x02982c5a13d1ad90 0xa814c162d09e8d6c 0xef983c7e7ff1ff9f 0xdf7cc1e3f3ff8ffc

def z616 : W := mkw 0x077d485a7dfca993 0xc83bea42d3efe54c 0xf7ffc07e7ffe018f 0x3fbffe03f3fff00c

def z617 : W := mkw 0x023808da7fd1ff93 0xb811c046d3fe8ffc 0xee18387e7ff1ff9f 0xd770c1c3f3ff8ffc

def z618 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x0000207000018000 0x0000010380000c00

def z619 : W := mkw 0x0218000011400000 0x8010c000008a0000 0x0018000001f00008 0x1000c000000f8000

def z620 : W := mkw 0x0000084a00102890 0x0800004250008144 0x0800180e00007800 0x804000c0700003c0

def z621 : W := mkw 0x0000810480000000 0x0000040824000000 0x0000078f80000001 0xc000003c7c000000

def z622 : W := mkw 0x8a1f897d8082815c 0x0450fc4bec04140a 0x101fc07f818e01e9 0x3080fe03fc0c700f

def z623 : W := mkw 0x808236b10283d748 0x340411b588141eba 0x79963ff18f8fffff 0xfbccb1ff8c7c7fff

def z624 : W := mkw 0x0218084800000010 0x0010c04240000000 0xee18387e7001f817 0xd770c1c3f3800fc0

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x080038000001f810 0xc04001c000000fc0

def z626 : W := mkw 0x4565c186ec3c62a3 0x4a2b2e0c3761e315 0xb1efc78fce7e67fb 0xfd8f7e3c7e73f33f

def z627 : W := mkw 0x4fffffefc83862be 0x0a7fffff7e41c315 0xffffffffc0706001 0xfffffffffe038300

def z628 : W := mkw 0x477dc106fd7c20a3 0xca3bee0837ebe105 0xf7ffc00ffffe01ef 0x3fbffe007ffff00f

def z629 : W := mkw 0x8dc7b7258203044c 0x246e3db92c101822 0x11e7c7818e0e0660 0x288f3e3c0c707033

def z630 : W := mkw 0x821a087b11d2a9d8 0x8c10d043d88e954e 0x101e007f81fe01e9 0x3080f003fc0ff00f

def z631 : W := mkw 0x002040807f6d5603 0xf001020403fb6ab0 0x000000007ffffe1e 0x0000000003fffff0

def z632 : W := mkw 0x056540006c2c0003 0x402b2a0003616000 0xb1efc0004e7e000a 0x3d8f7e000273f000

def z633 : W := mkw 0x4020c184c8284222 0x0201060c26414211 0x2061c781880807fb 0x79030e3c0c40403f

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000040180000001 0x790000200c000000

def z635 : W := mkw 0x0000810480000000 0x0000040824000000 0x8069c38e00000000 0x84034e1c70000000

def z636 : W := mkw 0x0002002100000008 0x0000100108000000 0x1016007180000001 0x3080b0038c000000

def z637 : W := mkw 0x0020008048004202 0x0001000402400210 0x0060078008000600 0x0803003c00400030

def z638 : W := mkw 0x0dc736210000000c 0x006e39b108000000 0x1186000000000000 0x008c300000000000

def z639 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xe618007e71f0018f 0x1730c003f38f800c

def z640 : W := mkw 0x0000001211d0a980 0x88000000908e854c 0x6010207071f1f99f 0x53008103838f8fcc

def z641 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x5f9ff87f80000001 0x32fcffc3fc000000

def z642 : W := mkw 0x45e0f784ee295623 0x322f07bc27714ab1 0xefe1ff81fe09fe76 0xef7f0ffc0ff04ff3

def z643 : W := mkw 0x0000085a0090a990 0x08000042d004854c 0xee00387e7001f997 0xc77001c3f3800fcc

def z644 : W := mkw 0x0882bfed8201561c 0x304415ff6c100ab0 0x08003fff8001fe11 0xc04001fffc000ff0

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0xa069c00000000000 0x3d034e0000000000

def z646 : W := mkw 0x0218001011c08100 0x8010c000808e0408 0xe618207071f1819f 0x5730c103838f8c0c

def z647 : W := mkw 0x0000085a0090a990 0x08000042d004854c 0xa808387e4071f99b 0xd54041c3f2038fcc

def z648 : W := mkw 0x00054000002c0000 0x40002a0000016000 0x1007c000000e0000 0x20803e0000007000

def z649 : W := mkw 0x0218084811400810 0x8010c042408a0040 0x0e00180030001800 0x007000c0018000c0

def z650 : W := mkw 0x0f5f896d8000001c 0x007afc4b6c000000 0xf7ffc07f80000001 0x3fbffe03fc000000

def z651 : W := mkw 0x421dc106917c20a0 0xca10ee08348be105 0x101fc00f81fe01e9 0x3080fe007c0ff00f

def z652 : W := mkw 0x4a3fc9efc83862be 0x0a51fe4f7e41c315 0xb07fc7ffc87867fb 0xfd83fe3ffe43c33f

def z653 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000080807fa 0x000000000040403f

def z654 : W := mkw 0x0000810480000000 0x0000040824000000 0x0061c78180000000 0x28030e3c0c000000

def z655 : W := mkw 0x00208184c8004202 0x0001040c26400210 0xa069c78fc8006613 0xfd034e3c7e400330

def z656 : W := mkw 0x0f7d9bccec005217 0x107becde67600290 0x8e69db8e70007800 0x84734edc738003c0

def z657 : W := mkw 0x0082242100000008 0x0004112108000000 0x0000247180000001 0x400001238c000000

def z658 : W := mkw 0x077d484a7d7c2893 0xc83bea4253ebe144 0x8e69d80e70707800 0x84734ec0738383c0

def z659 : W := mkw 0x0de7f725ec2c000f 0x406f3fb92f616000 0x11e7c7818e0e0000 0x288f3e3c0c707000

def z660 : W := mkw 0x05c0368002015600 0x302e01b400100ab0 0xefe03f800001fe10 0xcf7f01fc00000ff0

def z661 : W := mkw 0x421889de91d0ebb0 0x8a10c44ef48e875d 0xee183ffff1f1ffff 0xd770c1ffff8f8fff

def z662 : W := mkw 0x00004000116c0000 0xc0000200008b6000 0x0000000001fe0008 0x00000000000ff000

def z663 : W := mkw 0x4560d386ec3872a3 0x1a2b069c3761c395 0xae69df8ff8787ffb 0xfd734efc7fc3c3ff

def z664 : W := mkw 0xc022c1b7c8bae3ea 0x0e01160dbe45d71f 0xb07fc7ffc9fe67fb 0xfd83fe3ffe4ff33f

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000200000018016 0x4300010000000c00

def z666 : W := mkw 0x87ff6c7b7fffaddb 0xec3ffb63dbfffd6e 0xfffffc7fffffffff 0xffffffe3ffffffff

def z667 : W := mkw 0x0778085a7dd0a993 0x883bc042d3ee854c 0xeff8387e7ff1f99f 0xdf7fc1c3f3ff8fcc

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00380030019804 0x027001c001800cc0

def z669 : W := mkw 0x8000001000828140 0x040000008004140a 0x00000000018e01e8 0x00000000000c700f

def z670 : W := mkw 0x45e0f786c83862a2 0x0a2f07bc3641c315 0xefe9ff8fc87867fb 0xff7f4ffc7e43c33f

def z671 : W := mkw 0x0fdf3e690000001c 0x007ef9f348000000 0xfffff87000000000 0x3fffffc380000000

def z672 : W := mkw 0x4a1fc96f803820bc 0x0a50fe4b7c01c105 0x101fc07f807801e9 0x3080fe03fc03c00f

def z673 : W := mkw 0x0802896d8000001c 0x0040144b6c000000 0x0000007f80000001 0x00000003fc000000

def z674 : W := mkw 0x002000806c005203 0x1001000403600290 0x0000000070007800 0x00000000038003c0

def z675 : W := mkw 0x423848da59f8ebb2 0x8a11c246d2cfc75d 0xee18387e79f9ffff 0xd770c1c3f3cfcfff

def z676 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x20002471880987fb 0x790001238c404c3f

def z677 : W := mkw 0x0000001000808100 0x0000000080040408 0x0010007001800189 0x10008003800c000c

def z678 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x09e03f800e01fe10 0xc84f01fc00700ff0

def z679 : W := mkw 0x8002003102838548 0x2400100188141c2a 0x101600718f8f87ff 0x3080b0038c7c7c3f

def z680 : W := mkw 0x0a1f897f91d0a99c 0x8850fc4bfc8e854c 0xfe1ff87ff1f1f99f 0xf7f0ffc3ff8f8fcc

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000f8e000e 0x00000000007c7000

def z682 : W := mkw 0x023808da59d0eb92 0x8811c046d2ce875c 0xee783ffe79f1ff9f 0xdf73c1fff3cf8ffc

def z683 : W := mkw 0x000000120090a980 0x080000009004854c 0x000000000001f990 0x0000000000000fcc

def z684 : W := mkw 0x056000006c000003 0x002b000003600000 0xf7f600007f8e000e 0x3fbfb00003fc7000

def z685 : W := mkw 0x8a9fad7d8283855c 0x2454fd6bec141c2a 0x719fe47f8f8f87ff 0x7b8cff23fc7c7c3f

def z686 : W := mkw 0x0f7fc96dfd6c001f 0xc07bfe4b6feb6000 0xf7ffc07ffffe000f 0x3fbffe03fffff000

def z687 : W := mkw 0x056012806c005203 0x102b009403600290 0xefe01b807e007806 0x8f7f00dc03f003c0

def z688 : W := mkw 0x0000001211d0a980 0x88000000908e854c 0xa008000e71f1f99f 0xd5004000738f8fcc

def z689 : W := mkw 0x05e036927fd1ff83 0xb82f01b493fe8ffc 0xefe03f807ff1ff9e 0xcf7f01fc03ff8ffc

def z690 : W := mkw 0x0dc2bf6d8000001c 0x006e15fb6c000000 0xefe03fff80000001 0xcf7f01fffc000000

def z691 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0x0000038e00006000 0x8000001c70000300

def z692 : W := mkw 0x077800007d400003 0x803bc00003ea0000 0xe7f800007ff0000e 0x1f3fc00003ff8000

def z693 : W := mkw 0x8002003100828148 0x040010018804140a 0x00000071800001e1 0x000000038c00000f

def z694 : W := mkw 0x829a2c7b13d3add8 0xac14d163d89e9d6e 0xee183c7ff1f1ffff 0xd770c1e3ff8f8fff

def z695 : W := mkw 0x8082242102030448 0x2404112108101822 0x719624718e0e0661 0x7b8cb1238c707033

def z696 : W := mkw 0x4020c106c83820a2 0x0a0106083641c105 0xa069c00fc87801eb 0x3d034e007e43c00f

def z697 : W := mkw 0x08823e690000001c 0x004411f348000000 0x0800387000000000 0x004001c380000000

def z698 : W := mkw 0x829a2c7b13d3add8 0xac14d163d89e9d6e 0x719e247f8fff87ff 0x7b8cf123fc7ffc3f

def z699 : W := mkw 0x4020c186ee3976a3 0x3a01060c3771cbb5 0xa069c78ffe79ffff 0xfd034e3c7ff3cfff

def z700 : W := mkw 0x8fffff7dffef855f 0xe47ffffbefff7c2a 0xffffffffffff87ff 0xfffffffffffffc3f

def z701 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x57f7c0003f8e0004 0x2abfbe0001fc7000

def z702 : W := mkw 0x077d485a7dfca993 0xc83bea42d3efe54c 0xee79f87e71f1f99f 0xd773cfc3f38f8fcc

def z703 : W := mkw 0x075d000000000000 0x003ae80000000000 0xf7ffc0000f8e000e 0x3fbffe00007c7000

def z704 : W := mkw 0x85e236b16e83d74b 0x342f11b58b741eba 0xefe03ff1fe01fff7 0xcf7f01ff8ff00fff

def z705 : W := mkw 0x080781258000000c 0x00403c092c000000 0x1007c00180000000 0x20803e000c000000

def z706 : W := mkw 0x07dd360037451401 0xf03ee9b001ba28a0 0x5f96380037879804 0x02fcb1c001bc3cc0

def z707 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0x107fc3ff80000001 0x3083fe1ffc000000

def z708 : W := mkw 0x4de7f7a5ee29562f 0x326f3fbd2f714ab1 0x11e7c7818e080660 0x288f3e3c0c704033

def z709 : W := mkw 0x0fdfbf6d9140001c 0x807efdfb6c8a0000 0xfffffffff1f1f81f 0xffffffffff8f8fc0

def z710 : W := mkw 0x475d8186b55462a1 0xca3aec0c35aaa315 0x5796078fb78667f5 0xc2bcb03c7dbc333f

def z711 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519624718f8f87ed 0x3a8cb1238c7c7c3f

def z712 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f81fe01fff7 0xcf7f01fc0ff00fff

def z713 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0000ffe0008 0x3fbffe00007ff000

def z714 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc87867fb 0xc4034e3c7e43c33f

def z715 : W := mkw 0x05e076806e295603 0x302f03b403714ab0 0xefe1ff807e09fe16 0xef7f0ffc03f04ff0

def z716 : W := mkw 0x0002812580000008 0x000014092c000000 0xb07fc7ff80000001 0xfd83fe3ffc000000

def z717 : W := mkw 0x4fff7eeb483862be 0x0a7ffbf75a41c315 0x5f963870487867fa 0x02fcb1c38243c33f

def z718 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e71f1f805 0xd770c1c3f38f8fc0

def z719 : W := mkw 0x077d48487d6c0013 0xc03bea4243eb6000 0xf7ffc07e7ffe000f 0x3fbffe03f3fff000

def z720 : W := mkw 0x075d4000356c0001 0xc03aea0001ab6000 0x119fc00007fe0008 0x308cfe00003ff000

def z721 : W := mkw 0x80a264314aab854a 0x240513218a555c2a 0xa069e471c87987fb 0x7d034f238e43cc3f

def z722 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0xffffdbff80000001 0xbffffedffc000000

def z723 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff88080661 0xfffffffffc404033

def z724 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xfffff8007ffe000e 0xffffffc003fff000

def z725 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc87867fa 0xac034e3c7e43c33f

def z726 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xcfe03f807e01fe04 0x8e7f01fc03f00ff0

def z727 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xfffff8007fff980e 0x3fffffc003fffcc0

def z728 : W := mkw 0xc082b7b78293f7e8 0x3e0415bdbc149fbf 0x08003fff8001fff1 0xc04001fffc000fff

def z729 : W := mkw 0x021d085a11d0a990 0x8810e842d08e854c 0xfe1ff87e71f1f99f 0xf7f0ffc3f38f8fcc

def z730 : W := mkw 0xc02040924abbe7e2 0x2e0102049255df3f 0x000000004879e7fa 0x000000000243cf3f

def z731 : W := mkw 0x0020008048004202 0x0001000402400210 0xee603b807001f816 0xc77301dc03800fc0

def z732 : W := mkw 0x056012806c005203 0x102b009403600290 0xefe03b807e01f816 0xcf7f01dc03f00fc0

def z733 : W := mkw 0x4020409259f8eba2 0x8a01020492cfc75d 0x0000000071f1f99e 0x00000000038f8fcc

def z734 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff88000613 0xfffffffffc400030

def z735 : W := mkw 0x05e076806e295603 0x302f03b403714ab0 0xffffff807ffffe1e 0xfffffffc03fffff0

def z736 : W := mkw 0xc02040925bfbefe2 0xae01020492dfdf7f 0x000000007ffffffe 0x0000000003ffffff

def z737 : W := mkw 0xc02040926ebbf7e3 0x3e0102049375dfbf 0x000000007ffffffe 0x0000000003ffffff

def z738 : W := mkw 0x00a036806e015603 0x300501b403700ab0 0xee003f807e01fe16 0xc77001fc03f00ff0

def z739 : W := mkw 0x4020c186ec3862a3 0x0a01060c3761c315 0xa069c78ffe7867ff 0xfd034e3c7ff3c33f

def z740 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xf1f627f18f8f87ff 0xff8fb13f8c7c7c3f

def z741 : W := mkw 0x0a1a897f91d0a99c 0x8850d44bfc8e854c 0x0018007f81f00189 0x1000c003fc0f800c

def z742 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xeff03ff07e01fe17 0xdf7f81ff83f00ff0

def z743 : W := mkw 0x08a2ff6dfd6c001f 0xc04517fb6feb6000 0x08003ffffffe000f 0xc04001fffffff000

def z744 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xff963c718f8f87ff 0xfffcb1e38c7c7c3f

def z745 : W := mkw 0x8fdfbf6d8002005c 0x047efdfb6c001002 0xffffffff800e0061 0xfffffffffc007003

def z746 : W := mkw 0x85e036806e035643 0x342f01b403701ab2 0xefe03f807e0ffe76 0xcf7f01fc03f07ff3

def z747 : W := mkw 0x0fdfbf6db745141d 0xf07efdfb6dba28a0 0xffffffffb7879805 0xfffffffffdbc3cc0

def z748 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xf1ffe4718f8f87ff 0x7f8fff238c7c7c3f

def z749 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e7ffff99f 0xd770c1c3f3ffffcc

def z750 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xf19e247f8f8f87ff 0xff8cf123fc7c7c3f

def z751 : W := mkw 0x829a2c6b13532cd8 0xac14d163589a9966 0x9f8e1c0ffe7e7e60 0xacfc70e07ff3f3f3

def z752 : W := mkw 0x8f5d9b5c82838554 0x247aecdae4141c2a 0x8e69db8e0f8f87fe 0x84734edc707c7c3f

def z753 : W := mkw 0x0dc7b73791d0a98c 0x886e3db9bc8e854c 0x11e7c781f1f1f99e 0x288f3e3c0f8f8fcc

def z754 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0x119fc0000ffe0008 0x388cfe00007ff000

def z755 : W := mkw 0x856212b16c82d34b 0x142b10958b64169a 0x9e761bf1f18e79e9 0xb4f3b0df8f8c73cf

def z756 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807e09fe1e 0xff7f01fc03f04ff0

def z757 : W := mkw 0x056012806e015603 0x302b009403700ab0 0xae601f807e01fe16 0xcd7300fc03f00ff0

def z758 : W := mkw 0x0080368002015600 0x300401b400100ab0 0x4e003f803001fe14 0xc27001fc01800ff0

def z759 : W := mkw 0x077d40807d6c4203 0xc03bea0403eb6210 0xf7ffc3807ffe600e 0xbfbffe1c03fff300

def z760 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xce18387e71f1f995 0xc670c1c3f38f8fcc

def z761 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffffc070000b 0xfffffffffe038000

def z762 : W := mkw 0x4238c9dcd9e8cb32 0x8211c64ee6cf4659 0x4e71fff1b9899e64 0x2a738fff8dcc4cf3

def z763 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xfff63f807e01fe16 0xffffb1fc03f00ff0

def z764 : W := mkw 0x0a3f89edee01561f 0x3051fc4f6f700ab0 0x101fc07ffe01fe17 0x3080fe03fff00ff0

def z765 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807001fe10 0xcf7f01fc03800ff0

def z766 : W := mkw 0x8fdfbf6d8203045c 0x247efdfb6c101822 0xffffffff8e0e07fb 0xfffffffffc70703f

def z767 : W := mkw 0x87ff64317fef854b 0xe43ffb218bff7c2a 0x8669e471f07187f1 0x44334f238f838c3f

def z768 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0x519fc00007fe000c 0x328cfe00003ff000

def z769 : W := mkw 0x0565485a6cbca993 0x482b2a42d365e54c 0x19e7f87e0e0ff991 0xe8cf3fc3f0707fcc

def z770 : W := mkw 0x077d40807d6c5203 0xd03bea0403eb6290 0xf7ffc0007ffe780e 0x3fbffe0003fff3c0

def z771 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x8fe03f807e01fe10 0xcc7f01fc03f00ff0

def z772 : W := mkw 0x05c0368002015600 0x302e01b400100ab0 0xefe03f807001fe16 0xcf7f01fc03800ff0

def z773 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xfffffbfe00000000 0xbfffffdff0000000

def z774 : W := mkw 0x077d52807d6c5203 0xd03bea9403eb6290 0xffffdf807ffe7e1e 0xfffffefc03fff3f0

def z775 : W := mkw 0x056012806e015603 0x302b009403700ab0 0x8e601b807601f804 0x847300dc03b00fc0

def z776 : W := mkw 0x0218894c80000010 0x0010c44a64000000 0xa079c7ff80000001 0xfd03ce3ffc000000

def z777 : W := mkw 0x075d4000356c0001 0xc03aea0001ab6000 0x779fc0003ffe000e 0x3bbcfe0001fff000

def z778 : W := mkw 0x077d48487d6c0013 0xc03bea4243eb6000 0xffffd80e7ffe000e 0xbffffec073fff000

def z779 : W := mkw 0x029d7680136d5600 0xf014ebb4009b6ab0 0x181fff8001fffe18 0xf0c0fffc000ffff0

def z780 : W := mkw 0xc0a2e5b7cabbe7ea 0x2e05172dbe55df3f 0xd1ffe3fe47f7e004 0x868fff1ff23fbf00

def z781 : W := mkw 0x05e536806e015603 0x302f29b403700ab0 0xffe7ff807e01fe16 0xefff3ffc03f00ff0

def z782 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03b807601f816 0xc77f01dc03b00fc0

def z783 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8f8e07ff 0xfffffffffc7c703f

def z784 : W := mkw 0x402040927ff9ffa3 0xba01020493ffcffd 0x000000007ff9fffe 0x0000000003ffcfff

def z785 : W := mkw 0x05e036006c000003 0x002f01b003600000 0xefe03f807e01f816 0xcf7f01fc03f00fc0

def z786 : W := mkw 0x075d4000356c0001 0xc03aea0001ab6000 0xf79fc00077fe000e 0x37bcfe0003bff000

def z787 : W := mkw 0x8fdf3e7913c38d5c 0xa47ef9f3c89e1c6a 0x5f96387037879804 0x02fcb1c381bc3cc0

def z788 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xf1962471cf8fe7ff 0xff8cb1238e7c7f3f

def z789 : W := mkw 0x05c0368026015601 0x302e01b401300ab0 0xef803f807601fe16 0xc77c01fc03b00ff0

def z790 : W := mkw 0x05e576806e2d5603 0x702f2bb403716ab0 0xefe1ff807e01fe16 0xcf7f0ffc03f00ff0

def z791 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xee79ffff80000001 0xd773cffffc000000

def z792 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f81fe09fe76 0xef7f01fc0ff04ff3

def z793 : W := mkw 0x0f7d5a487d6c0017 0xc07bead243eb6000 0xffffd8007ffe000e 0x3ffffec003fff000

def z794 : W := mkw 0x45c0f706a63934a1 0x3a2e07b83531c9a5 0x4f89f80fb67999ed 0x327c4fc07db3cccf

def z795 : W := mkw 0x0882bf6d8000001c 0x004415fb6c000000 0xf9ffffff80000001 0xffcffffffc000000

def z796 : W := mkw 0x0fdfbf6d9140001c 0x807efdfb6c8a0000 0xfffffffff0700001 0xffffffffff838000

def z797 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xfffffffe00000000 0xcffffffff0000000

def z798 : W := mkw 0x075d4000356c0001 0xc03aea0001ab6000 0x579fc00037f60004 0x02bcfe0001bfb000

def z799 : W := mkw 0x05e236a16e01560b 0x302f11b50b700ab0 0xfff63ff1ff8ffe1f 0xffffb1ff8ffc7ff0

def z800 : W := mkw 0x0540120000000000 0x002a009000000000 0xee603b807001f816 0xc77301dc03800fc0

def z801 : W := mkw 0x05c0368026015601 0x302e01b401300ab0 0x0e003f803001fe10 0xc07001fc01800ff0

def z802 : W := mkw 0x8fdfbf6d8203045c 0x247efdfb6c101822 0xffffffff8e0f8677 0xfffffffffc707c33

def z803 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0xfff63f81ff8ffe7e 0xffffb1fc0ffc7ff3

def z804 : W := mkw 0x002000806e015603 0x3001000403700ab0 0xee603f807e01fe16 0xcf7301fc03f00ff0

def z805 : W := mkw 0x0000400000280000 0x0000020000014000 0x719fc0000ffe000e 0x3b8cfe00007ff000

def z806 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519624718f8f87f5 0x6a8cb1238c7c7c3f

def z807 : W := mkw 0x0dc7bf6d8000001c 0x006e3dfb6c000000 0x0861ffff80000001 0xc0430ffffc000000

def z808 : W := mkw 0x021d085a11d4a990 0xc810e842d08ea54c 0xfe1e387e71f7f99f 0xd7f0f1c3f38fbfcc

def z809 : W := mkw 0x0fdfbf6da601141d 0x307efdfb6d3008a0 0xffffffff86000001 0xfffffffffc300000

def z810 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0007ffe601e 0xffbffe0003fff300

def z811 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x7f963c71bf8f9fff 0x7bfcb1e38dfc7cff

def z812 : W := mkw 0x0000001000808100 0x0000000080040408 0x719624718f8f87ff 0x7b8cb1238c7c7c3f

def z813 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xae08387e7071f99b 0xd57041c3f3838fcc

def z814 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0007ffff81e 0x3fbffe0003ffffc0

def z815 : W := mkw 0x0f5f896d8000001c 0x007afc4b6c000000 0xf7ffc7ff80000001 0xffbffe3ffc000000

def z816 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xefe9ffff80000001 0xcf7f4ffffc000000

def z817 : W := mkw 0x023d40007d6c0003 0xc011ea0003eb6000 0x719fc0007ffe000e 0x3b8cfe0003fff000

def z818 : W := mkw 0x05e236a16e01560b 0x302f11b50b700ab0 0xfff63ff07e01fe16 0xcfffb1ff83f00ff0

def z819 : W := mkw 0x0fdfbf6db544001d 0xc07efdfb6daa2000 0xffffffffbf8e000f 0xfffffffffdfc7000

def z820 : W := mkw 0x056012806c005203 0x102b009403600290 0xce603b807001f804 0x867301dc03800fc0

def z821 : W := mkw 0x4218895e91d0a9b0 0x8a10c44af48e854d 0x0018007f81f001e9 0x1000c003fc0f800f

def z822 : W := mkw 0x056540007d6c0003 0xc02b2a0003eb6000 0x11e7c0000ffe0008 0x288f3e00007ff000

def z823 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa869ff8fc879fffb 0xfd434ffc7e43cfff

def z824 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc00077f6000e 0x17bffe0003bfb000

def z825 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8808000b 0xfffffffffc404000

def z826 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xe669c78ff87867ff 0xff334e3c7fc3c33f

def z827 : W := mkw 0x05c0368026015601 0x302e01b401300ab0 0xefe03f803601fe14 0xcf7f01fc01b00ff0

def z828 : W := mkw 0xc882bfff8293e7fc 0x2e4415fffc149f3f 0x08003fff8001e7f1 0xc04001fffc000f3f

def z829 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xfffffffff0000007 0xffffffffff800000

def z830 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x4e18387e71f1f99f 0x1270c1c3f38f8fcc

def z831 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xffffffff86018005 0xfffffffffc300c00

def z832 : W := mkw 0x402040927dfceba3 0xca01020493efe75d 0x000000007ffffffe 0x0000000003ffffff

def z833 : W := mkw 0x05e076806e295603 0x302f03b403714ab0 0xefe9ff81fe79ffff 0xff7f4ffc0ff3cfff

def z834 : W := mkw 0x421dc95e91fca9b0 0xca10ee4af48fe54d 0x101fc07f81fe01e9 0x3080fe03fc0ff00f

def z835 : W := mkw 0x0080360000000000 0x000401b000000000 0xee003f807001f816 0xc77001fc03800fc0

def z836 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fc87807eb 0x3d034e3c7e43c03f

def z837 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x4f803f807e01fe16 0xc27c01fc03f00ff0

def z838 : W := mkw 0x05e036806c005203 0x102f01b403600290 0xefe03f807001f816 0xcf7f01fc03800fc0

def z839 : W := mkw 0xc082a5378293a5e8 0x2e041529bc149d2f 0x0000247f800187f1 0x40000123fc000c3f

def z840 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xffffffff80018611 0xfffffffffc000c30

def z841 : W := mkw 0x0a1f896d8000001c 0x0050fc4b6c000000 0xfe7fffff80000001 0xfff3fffffc000000

def z842 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0xfffffbfe00000001 0xffffffdff0000000

def z843 : W := mkw 0x8fdf3e7937c7855d 0xe47ef9f3c9be3c2a 0x5f96387037878004 0x02fcb1c381bc3c00

def z844 : W := mkw 0x0218894c80000010 0x0010c44a64000000 0xee79fbfe00000001 0xd773cfdff0000000

def z845 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x71962471ff8fffff 0x7b8cb1238ffc7fff

def z846 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0007ffe019f 0x7fbffe0003fff00c

def z847 : W := mkw 0xc21ac97f91faa9f8 0x8e10d64bfc8fd54f 0x101fc07f81fe01e9 0x3080fe03fc0ff00f

def z848 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xf19e2471cfff87ff 0x7f8cf1238e7ffc3f

def z849 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fc87067f3 0xcd034e3c7e43833f

def z850 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc7807ffe000e 0xffbffe3c03fff000

def z851 : W := mkw 0x077d52007d6c0003 0xc03bea9003eb6000 0xffffdb807ffe000e 0xbffffedc03fff000

def z852 : W := mkw 0x056012806c005203 0x102b009403600290 0x8e603b807001f810 0xc47301dc03800fc0

def z853 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xfe1e387e71fff99f 0xf7f0f1c3f38fffcc

def z854 : W := mkw 0x05e076806e295603 0x302f03b403714ab0 0xefe9ff807e71fe16 0xcf7f4ffc03f38ff0

def z855 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x71ffc0000ffe000e 0x3b8ffe00007ff000

def z856 : W := mkw 0x0fdfbf6d9140081c 0x807efdfb6c8a0040 0xffffffffb0001801 0xfffffffffd8000c0

def z857 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8e000007 0xfffffffffc700000

def z858 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0xbe7fdfff80000001 0xfdf3fefffc000000

def z859 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807601f804 0xcf7f01fc03b00fc0

def z860 : W := mkw 0x0020c104c8280002 0x0001060826414000 0xa069c78fc87807fb 0xfd034e3c7e43c03f

def z861 : W := mkw 0x07f83eda7fd1ff93 0xb83fc1f6d3fe8ffc 0x01f807fe0ff00789 0x180fc03ff07f803c

def z862 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8e0e0001 0xfffffffffc707000

def z863 : W := mkw 0x056012806e015603 0x302b009403700ab0 0xee603b807e01fe16 0xc77301dc03f00ff0

def z864 : W := mkw 0x056540007d6c0003 0xc02b2a0003eb6000 0xb1efc0007ffe000e 0x3d8f7e0003fff000

def z865 : W := mkw 0x077d48487d6c0813 0xc03bea4243eb6040 0xffffd8007ffe180e 0x3ffffec003fff0c0

def z866 : W := mkw 0x4f7ddbcefd7c62b7 0xca7beede77ebe315 0x8e69db8e70706000 0x84734edc73838300

def z867 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x57ffc0003ffe000c 0x3abffe0001fff000

def z868 : W := mkw 0x0080368002015600 0x300401b400100ab0 0x8e003f807001fe10 0xc47001fc03800ff0

def z869 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xdffffbff80000001 0xb6ffffdffc000000

def z870 : W := mkw 0x07dfa52580000008 0x003efd292c000000 0xf7ffe7ff80000001 0xffbfff3ffc000000

def z871 : W := mkw 0x40a264a3483862aa 0x0a0513251a41c315 0x71962471c87867fb 0x7b8cb1238e43c33f

def z872 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x4fe03f803e01fe14 0xca7f01fc01f00ff0

def z873 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519624718f8f87fe 0x2a8cb1238c7c7c3f

def z874 : W := mkw 0x05e0368048004202 0x002f01b402400210 0xefe03f807801fe16 0xcf7f01fc03c00ff0

def z875 : W := mkw 0x0a1f896d8000001c 0x0050fc4b6c000000 0x107fc7ff80000001 0x3883fe3ffc000000

def z876 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xd7ffc00077fe000c 0x36bffe0003bff000

def z877 : W := mkw 0x0fdfbf6d8201141c 0x307efdfb6c1008a0 0xffffffff80019801 0xfffffffffc000cc0

def z878 : W := mkw 0x075d4000356c0001 0xc03aea0001ab6000 0xf7ffc00037fe000c 0x3fbffe0001bff000

def z879 : W := mkw 0x077d400048280002 0x003bea0002414000 0xf7ffc0004ffe000e 0x3fbffe00027ff000

def z880 : W := mkw 0x0000000000000000 0x0000000000000000 0xee603f807001f816 0xcf7301fc03800fc0

def z881 : W := mkw 0x056000806c004203 0x002b000403600210 0xefe03f807e01fe16 0xcf7f01fc03f00ff0

def z882 : W := mkw 0x0218084a00102090 0x0810c04250008104 0xee18387e7071f99f 0xd770c1c3f3838fcc

def z883 : W := mkw 0x029aad6d80000018 0x0014d56b6c000000 0xffffffff80000001 0xfffffffffc000000

def z884 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fcffe67ff 0xfd034e3c7e7ff33f

def z885 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x8e08387e7071f800 0x847041c3f3838fc0

def z886 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc07867f9 0xf4034e3c7e03c33f

def z887 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffe0007fff801e 0x7fbfff0003fffc00

def z888 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0xffe63f81fe0fffff 0xffff31fc0ff07fff

def z889 : W := mkw 0x0802896d8000001c 0x0040144b6c000000 0xa069c7ff80000001 0xfd034e3ffc000000

def z890 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xdfffffff80000001 0xc6fffffffc000000

def z891 : W := mkw 0x0082a52580000008 0x000415292c000000 0xa069e7ff80000001 0xfd034f3ffc000000

def z892 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffffc0006013 0xfffffffffe000300

def z893 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xfffffffff0007801 0xffffffffff8003c0

def z894 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x9fefffff80000001 0xecff7ffffc000000

def z895 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc001fffe01ef 0x3fbffe000ffff00f

def z896 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0xffe63f807e07fe16 0xcfff31fc03f03ff0

def z897 : W := mkw 0x05e236a16e01560b 0x302f11b50b700ab0 0xefe03ff1fe01fe17 0xcf7f01ff8ff00ff0

def z898 : W := mkw 0x0080368002015600 0x300401b400100ab0 0xef803f807e01fe16 0xcf7c01fc03f00ff0

def z899 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee08387e7071f997 0xc77041c3f3838fcc

def z900 : W := mkw 0x002040007d6c0003 0xc001020003eb6000 0xf1ffc0007ffe000e 0x3f8ffe0003fff000

def z901 : W := mkw 0x05e536806e055603 0x702f29b403702ab0 0xffe63f807e07fe16 0xcfff31fc03f03ff0

def z902 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xae69df8ff8787ffb 0xfd734efc7fc3c3ff

def z903 : W := mkw 0x0fdfbf6d9140001c 0x807efdfb6c8a0000 0xffffffff81f00009 0xfffffffffc0f8000

def z904 : W := mkw 0x05e236a16e01560b 0x302f11b50b700ab0 0xffe63f81fe01fe16 0xefff31fc0ff00ff0

def z905 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xae69ffff80000001 0xfd734ffffc000000

def z906 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee183c7ff1f1f99f 0xff70c1e3ff8f8fcc

def z907 : W := mkw 0x056012806e015603 0x302b009403700ab0 0xefe01b807e01fe16 0x8f7f00dc03f00ff0

def z908 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x9fffdfff80000001 0xbcfffefffc000000

def z909 : W := mkw 0x021d4000116c0000 0xc010ea00008b6000 0xf79fc0007ffe000e 0x3fbcfe0003fff000

def z910 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0x8e69dbff80000001 0x84734edffc000000

def z911 : W := mkw 0x0238400059680002 0x8011c20002cb4000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z912 : W := mkw 0x056012806c005203 0x102b009403600290 0xee603f807801fe16 0xcf7301fc03c00ff0

def z913 : W := mkw 0x0fdfbf6da400001d 0x007efdfb6d200000 0xffffffffb6000005 0xfffffffffdb00000

def z914 : W := mkw 0x8fdfbf6d8203045c 0x247efdfb6c101822 0xffffffff86060001 0xfffffffffc303000

def z915 : W := mkw 0x0218084811400010 0x8010c042408a0000 0xee18387e71f1f81f 0xd770c1c3f38f8fc0

def z916 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e7071f991 0xd770c1c3f3838fcc

def z917 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519624718f8f87ff 0x428cb1238c7c7c3f

def z918 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x79963c718f8fffff 0xfbccb1e38c7c7fff

def z919 : W := mkw 0xc02040927fffe7e3 0xee01020493ffff3f 0x000000007fffe7fe 0x0000000003ffff3f

def z920 : W := mkw 0x075d4000116c0000 0xc03aea00008b6000 0xf7ffc0000ffe000e 0x3fbffe00007ff000

def z921 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e79f9f99f 0xff70c1c3f3cfcfcc

def z922 : W := mkw 0x0000008000004200 0x0000000400000210 0xee003f807001fe16 0xc77001fc03800ff0

def z923 : W := mkw 0x002040927ffdff83 0xf801020493ffeffc 0x000000007fffff9e 0x0000000003fffffc

def z924 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x5ff7ffff80000001 0xeaffbffffc000000

def z925 : W := mkw 0x8fdfbf6d8203045c 0x247efdfb6c101822 0xffffffff8f8e066f 0xfffffffffc7c7033

def z926 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff800007f1 0xfffffffffc00003f

def z927 : W := mkw 0x056540007d6c0003 0xc02b2a0003eb6000 0xf7e7c0007ffe000e 0x2fbf3e0003fff000

def z928 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8001f811 0xfffffffffc000fc0

def z929 : W := mkw 0x0fddbf4c80000014 0x007eedfa64000000 0xeff9fffe00000001 0xdf7fcffff0000000

def z930 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x319604718f8e07fb 0x798cb0238c7c703f

def z931 : W := mkw 0x056540006c2c0003 0x402b2a0003616000 0xf1ffc0004ffe000e 0x3f8ffe00027ff000

def z932 : W := mkw 0x8000811482838540 0x24000408a4141c2a 0xa069c78f8f8f87ff 0xfd034e3c7c7c7c3f

def z933 : W := mkw 0x0000810480000000 0x0000040824000000 0xe079e7ff80000001 0xff03cf3ffc000000

def z934 : W := mkw 0x4020c186ec3872a3 0x1a01060c3761c395 0xa069c78ff8787ffb 0xfd034e3c7fc3c3ff

def z935 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xcfe03f807601fe14 0xc67f01fc03b00ff0

def z936 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x8e69fbfe00000000 0x84734fdff0000000

def z937 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xee603f807001fe16 0xc77301fc03800ff0

def z938 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x11ffc0007ffe000e 0x388ffe0003fff000

def z939 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xff9e387e77f7f99f 0xd7fcf1c3f3bfbfcc

def z940 : W := mkw 0x4020409248b8eba2 0x0a0102049245c75d 0x000000004879fffa 0x000000000243cfff

def z941 : W := mkw 0x077d52807d6c5203 0xd03bea9403eb6290 0xf7ffc3807ffe000e 0x3fbffe1c03fff000

def z942 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x8e603f807e01fe16 0xc47301fc03f00ff0

def z943 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xff9e3c7fffffffff 0xfffcf1e3ffffffff

def z944 : W := mkw 0xc5e2f7a5ee2b566b 0x362f17bd2f715ab3 0x11e7c7818e0e0660 0x288f3e3c0c707033

def z945 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x719604718f8e07ef 0x3b8cb0238c7c703f

def z946 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xffe63f807e0ffe16 0xefff31fc03f07ff0

def z947 : W := mkw 0x0a9fad6d8000001c 0x0054fd6b6c000000 0xf1ffe7ff80000001 0xff8fff3ffc000000

def z948 : W := mkw 0x0fdfbf6db544001d 0xc07efdfb6daa2000 0xffffffffb0000001 0xfffffffffd800000

def z949 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f81fe01fe17 0xff7f01fc0ff00ff0

def z950 : W := mkw 0x0fdfbf6da400101d 0x107efdfb6d200080 0xffffffffb0001801 0xfffffffffd8000c0

def z951 : W := mkw 0x05e076806e2d5603 0x702f03b403716ab0 0xefe03f807e0ffe16 0xcf7f01fc03f07ff0

def z952 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xfffffffffe01fe17 0xfffffffffff00ff0

def z953 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78ff879ffff 0xfd034e3c7fc3cfff

def z954 : W := mkw 0x0fdfbf6da404001d 0x407efdfb6d202000 0xffffffff86060001 0xfffffffffc303000

def z955 : W := mkw 0x477d40807d6c4223 0xc23bea0403eb6211 0xf7ffc0007ffe066e 0x3fbffe0003fff033

def z956 : W := mkw 0x077d52007d6c1003 0xd03bea9003eb6080 0xffffd8007ffe180e 0x3ffffec003fff0c0

def z957 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee79f87e71f1f99f 0xff73cfc3f38f8fcc

def z958 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee183c7e79f1ff9f 0xdf70c1e3f3cf8ffc

def z959 : W := mkw 0x0882bf6d8000001c 0x004415fb6c000000 0x8869ffff80000001 0xc4434ffffc000000

def z960 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0069c78f887867f9 0xf8034e3c7c43c33f

def z961 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xb1ffc7ff80000001 0xfd8ffe3ffc000000

def z962 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x4e10387e71f1f99f 0xc27081c3f38f8fcc

def z963 : W := mkw 0x0082242100000008 0x0004112108000000 0x719624718f8e07ff 0x7b8cb1238c7c703f

def z964 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff87860005 0xfffffffffc3c3000

def z965 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xb07fc78fc9fe67fb 0xfd83fe3c7e4ff33f

def z966 : W := mkw 0x8882bf7f8293addc 0x2c4415fbfc149d6e 0x08003fff8001fff1 0xc04001fffc000fff

def z967 : W := mkw 0x077d48487d6c0013 0xc03bea4243eb6000 0xfffff8707ffe000e 0x3fffffc383fff000

def z968 : W := mkw 0x45e076806e295623 0x322f03b403714ab1 0xefe03f807e09fe76 0xcf7f01fc03f04ff3

def z969 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x8e08387e71f1f99f 0xc47041c3f38f8fcc

def z970 : W := mkw 0x00a036804a015602 0x300501b402500ab0 0xee603f807801fe16 0xcf7301fc03c00ff0

def z971 : W := mkw 0x077d40807d6c4203 0xc03bea0403eb6210 0xffffff807ffffe1e 0xfffffffc03fffff0

def z972 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x9e7fffff80000001 0xf4f3fffffc000000

def z973 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffffb0019805 0xfffffffffd800cc0

def z974 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff80018017 0xfffffffffc000c00

def z975 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0xee79ffff80000001 0xff73cffffc000000

def z976 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe83f807e71fe1e 0xdf7f41fc03f38ff0

def z977 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e71f1f816 0xc770c1c3f38f8fc0

def z978 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xeff03f807f81fe1e 0xdf7f81fc03fc0ff0

def z979 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0x8e18387e71f1f999 0xd470c1c3f38f8fcc

def z980 : W := mkw 0x0de7f7a5ee2d560f 0x706f3fbd2f716ab0 0x11e7c7818e0e0600 0x288f3e3c0c707030

def z981 : W := mkw 0x8082363102839548 0x340411b188141caa 0x79963c718f8f9fff 0x7bccb1e38c7c7cff

def z982 : W := mkw 0x85e776a16e2f564b 0x742f3bb50b717ab2 0xffe7ff81fe0ffe76 0xefff3ffc0ff07ff3

def z983 : W := mkw 0x077d52807d6c5203 0xd03bea9403eb6290 0xfffffb807ffff81e 0xffffffdc03ffffc0

def z984 : W := mkw 0x05e076806e295603 0x302f03b403714ab0 0xefe03f807e79fe1e 0xcf7f01fc03f3cff0

def z985 : W := mkw 0x8082243102838548 0x2404112188141c2a 0xf7962471ff8f87ff 0x7fbcb1238ffc7c3f

def z986 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff800801e9 0xfffffffffc00400f

def z987 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc00077f60004 0x3fbffe0003bfb000

def z988 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x8fe01f807e01fe16 0x8c7f00fc03f00ff0

def z989 : W := mkw 0x05e576806e2d5603 0x702f2bb403716ab0 0xffefff807e7ffe1e 0xffff7ffc03f3fff0

def z990 : W := mkw 0x4a1fc97f91f8a9bc 0x8a50fe4bfc8fc54d 0x101fc07f81f801e9 0x3080fe03fc0fc00f

def z991 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fc07067f1 0xfd034e3c7e03833f

def z992 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x119604718f8f87ff 0x388cb0238c7c7c3f

def z993 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xe079c78fc9f867ff 0xff03ce3c7e4fc33f

def z994 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0x9e7fdbfe00000000 0x84f3fedff0000000

def z995 : W := mkw 0x0dc7bf6d8000001c 0x006e3dfb6c000000 0xffe7ffff80000001 0xefff3ffffc000000

def z996 : W := mkw 0x056012806e015603 0x302b009403700ab0 0x8e601b807001fe10 0x847300dc03800ff0

def z997 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03b807e01f806 0x8f7f01dc03f00fc0

def z998 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8000019b 0xfffffffffc00000c

def z999 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xe1e9c78fce7867ff 0xff0f4e3c7e73c33f

def z1000 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0x8e69fbfe00000001 0xc4734fdff0000000

def z1001 : W := mkw 0x077d40807d6c4203 0xc03bea0403eb6210 0xf7ffc0007ffe661e 0x3fbffe0003fff330

def z1002 : W := mkw 0x0fdfbf6d9144001c 0xc07efdfb6c8a2000 0xffffffff81860001 0xfffffffffc0c3000

def z1003 : W := mkw 0x477dc9cefd7c6ab3 0xca3bee4e77ebe355 0x8e69db8e70707800 0x84734edc738383c0

def z1004 : W := mkw 0x0dc2bf6d8000001c 0x006e15fb6c000000 0xefe9ffff80000001 0xff7f4ffffc000000

def z1005 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee183c7ff1f1ffff 0xd770c1e3ff8f8fff

def z1006 : W := mkw 0x4000c106803820a0 0x0a0006083401c105 0xa069c78f887807fb 0xfd034e3c7c43c03f

def z1007 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xf7ffc7ff80000001 0x3fbffe3ffc000000

def z1008 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x4fe03f807e01fe16 0x0a7f01fc03f00ff0

def z1009 : W := mkw 0x0dc7bf6d8000001c 0x006e3dfb6c000000 0xb9efffff80000001 0xfdcf7ffffc000000

def z1010 : W := mkw 0x0fdfbf6da601141d 0x307efdfb6d3008a0 0xffffffffbe019e17 0xfffffffffdf00cf0

def z1011 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0x8e79dbfe00000001 0x9473cedff0000000

def z1012 : W := mkw 0x8218085a11d2a9d0 0x8c10c042d08e954e 0xee18387e71fff9ff 0xd770c1c3f38fffcf

def z1013 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e79f9ffff 0xd770c1c3f3cfcfff

def z1014 : W := mkw 0x075d894c80000010 0x003aec4a64000000 0xffffffff80000001 0xfffffffffc000000

def z1015 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc00e7ffe000f 0xffbffe0073fff000

def z1016 : W := mkw 0x0dc7bf6d8000001c 0x006e3dfb6c000000 0x11e7c7ff80000001 0x288f3e3ffc000000

def z1017 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78fc07067fb 0xd5034e3c7e03833f

def z1018 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387e71f1f80e 0x9770c1c3f38f8fc0

def z1019 : W := mkw 0x4020409259f8eba2 0x8a01020492cfc75d 0x0000000049f867fa 0x00000000024fc33f

def z1020 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff8180000f 0xfffffffffc0c0000

def z1021 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe83f8e7e01fe17 0xdf7f41fc73f00ff0

def z1022 : W := mkw 0x05c0368026015601 0x302e01b401300ab0 0x4f803b803601f804 0x827c01dc01b00fc0

def z1023 : W := mkw 0x05c2b72580000008 0x002e15b92c000000 0xffffffff80000001 0xfffffffffc000000

def z1024 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc401fffe000f 0x7fbffe200ffff000

def z1025 : W := mkw 0x077d40807d6c4203 0xc03bea0403eb6210 0xf7ffc7807ffe060e 0x3fbffe3c03fff030

def z1026 : W := mkw 0x0000085a0090a990 0x08000042d004854c 0xee08387e7071f99f 0xd77041c3f3838fcc

def z1027 : W := mkw 0x023d4000596c0002 0xc011ea0002cb6000 0xf1ffc0004ffe000e 0x3f8ffe00027ff000

def z1028 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0x7196078f8f8e67ff 0xfb8cb03c7c7c733f

def z1029 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xffffffff818e0009 0xfffffffffc0c7000

def z1030 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0007ffe07fe 0x3fbffe0003fff03f

def z1031 : W := mkw 0x0a1f896d8000001c 0x0050fc4b6c000000 0x907fc3ff80000001 0xb483fe1ffc000000

def z1032 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x19ffffff80000001 0xf8cffffffc000000

def z1033 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x71ffe7ff80000001 0x7b8fff3ffc000000

def z1034 : W := mkw 0x8fdfbf6d8203045c 0x247efdfb6c101822 0xffffffff80000661 0xfffffffffc000033

def z1035 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xe069e78fc879e7ff 0xff034f3c7e43cf3f

def z1036 : W := mkw 0x0dc7bf6d8000001c 0x006e3dfb6c000000 0x79f7ffff80000001 0xfbcfbffffc000000

def z1037 : W := mkw 0x0000894c80000010 0x0000044a64000000 0xa869ffff80000001 0xfd434ffffc000000

def z1038 : W := mkw 0x40008186801062a0 0x0a00040c34008315 0xa069c78fc07067fb 0xfd034e3c7e03833f

def z1039 : W := mkw 0x0fdfbf6da601141d 0x307efdfb6d3008a0 0xfffffffff601f817 0xffffffffffb00fc0

def z1040 : W := mkw 0x4000c186803862a0 0x0a00060c3401c315 0xa069c78f807867f9 0xfd034e3c7c03c33f

def z1041 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xfff63f81ff8fffff 0xffffb1fc0ffc7fff

def z1042 : W := mkw 0x4020409248b8e3a2 0x0a0102049245c71d 0x0000000049f9e7fe 0x00000000024fcf3f

def z1043 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x97efc0007ffe000e 0x2cbf7e0003fff000

def z1044 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xd7ffc0007ffe000e 0x06bffe0003fff000

def z1045 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xffffffff8e0987ff 0xfffffffffc704c3f

def z1046 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xce18387e71f1f99e 0x8670c1c3f38f8fcc

def z1047 : W := mkw 0x0fdfbf6db544001d 0xc07efdfb6daa2000 0xfffffffff7f6000f 0xffffffffffbfb000

def z1048 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xfffffbfe00000001 0xd7ffffdff0000000

def z1049 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807f8ffe1e 0xcf7f01fc03fc7ff0

def z1050 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807e09fffe 0xcf7f01fc03f04fff

def z1051 : W := mkw 0x0fdfbf6d9140001c 0x807efdfb6c8a0000 0xffffffffb1800005 0xfffffffffd8c0000

def z1052 : W := mkw 0x056012806c005203 0x102b009403600290 0x8e601b807001f816 0x847300dc03800fc0

def z1053 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee783ffe71f1f99f 0xdf73c1fff38f8fcc

def z1054 : W := mkw 0xc020409248bae3e2 0x0e0102049245d71f 0x0000000049fe67fa 0x00000000024ff33f

def z1055 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0xefe03f81fe01fe76 0xcf7f01fc0ff00ff3

def z1056 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xfff63f807f87fe16 0xcfffb1fc03fc3ff0

def z1057 : W := mkw 0x0fdfbf6d9140001c 0x807efdfb6c8a0000 0xfffffffffffe000f 0xfffffffffffff000

def z1058 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc0007ff60006 0x0fbffe0003ffb000

def z1059 : W := mkw 0x07d8bf4c80000010 0x003ec5fa64000000 0xeff9ffff80000001 0xff7fcffffc000000

def z1060 : W := mkw 0x8082363102838548 0x240411b188141c2a 0x79963ff18f8f87ff 0xfbccb1ff8c7c7c3f

def z1061 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x519620718f8f87ff 0x328cb1038c7c7c3f

def z1062 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xee18387ff1f9f9ff 0xf770c1c3ff8fcfcf

def z1063 : W := mkw 0x0000128000005200 0x1000009400000290 0xee003b807001f816 0xc77001dc03800fc0

def z1064 : W := mkw 0x0a1fc97f91fca99c 0xc850fe4bfc8fe54c 0x101fc07f81fe0189 0x3080fe03fc0ff00c

def z1065 : W := mkw 0x075d000035440001 0xc03ae80001aa2000 0xf7ffc00077f6000e 0x3fbffe0003bfb000

def z1066 : W := mkw 0xc082adff8293eff8 0x2e04156ffc149f7f 0x08003fff8001fff1 0xc04001fffc000fff

def z1067 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xffffd8007ffe780e 0xbffffec003fff3c0

def z1068 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x579fc0007ffe000e 0x32bcfe0003fff000

def z1069 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xae603f807801fe12 0xcd7301fc03c00ff0

def z1070 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x719624718f8e07e9 0x7b8cb1238c7c703f

def z1071 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xb1efc78fce7e67fb 0xfd8f7e3c7e73f33f

def z1072 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x57f7c0007ffe000e 0x2abfbe0003fff000

def z1073 : W := mkw 0x00a024804a014602 0x2005012402500a30 0xefe03f807e01fe16 0xcf7f01fc03f00ff0

def z1074 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x2069c78f887807fb 0x79034e3c7c43c03f

def z1075 : W := mkw 0x077d48487d6c0013 0xc03bea4243eb6000 0xfffff87e7ffff81f 0xffffffc3f3ffffc0

def z1076 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc4007ffe061e 0x7fbffe2003fff030

def z1077 : W := mkw 0x85e236a16e03564b 0x342f11b50b701ab2 0xfff63ff1fe0ffe77 0xffffb1ff8ff07ff3

def z1078 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xcfe03b807e01fe16 0x867f01dc03f00ff0

def z1079 : W := mkw 0x0a9abf6d8000001c 0x0054d5fb6c000000 0xee79ffff80000001 0xff73cffffc000000

def z1080 : W := mkw 0x8002003102838548 0x2400100188141c2a 0x719600718f8f87ff 0x3b8cb0038c7c7c3f

def z1081 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xf1ffc78fc87867fb 0xff8ffe3c7e43c33f

def z1082 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xa069c78f887807e9 0xfd034e3c7c43c03f

def z1083 : W := mkw 0x056540007d6c0003 0xc02b2a0003eb6000 0x71f7c0007ffe000e 0x3b8fbe0003fff000

def z1084 : W := mkw 0x0de736a16e01560f 0x306f39b50b700ab0 0xffe63f807e01fe16 0xcfff31fc03f00ff0

def z1085 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0x8e603b807001f800 0x847301dc03800fc0

def z1086 : W := mkw 0x0a9fbf6d8000001c 0x0054fdfb6c000000 0xb87fffff80000001 0xfdc3fffffc000000

def z1087 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xee69ff8fc87867fb 0xff734ffc7e43c33f

def z1088 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0x5fffffff80000001 0x3afffffffc000000

def z1089 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xff9e387e71f1f99f 0xfffcf1c3f38f8fcc

def z1090 : W := mkw 0x05e236a16e01560b 0x302f11b50b700ab0 0xfff63ff1fe09ffff 0xffffb1ff8ff04fff

def z1091 : W := mkw 0x05c0360026011401 0x302e01b0013008a0 0xefe03f807601f816 0xcf7f01fc03b00fc0

def z1092 : W := mkw 0x075d000011400000 0x803ae800008a0000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z1093 : W := mkw 0x0882bf6d8000001c 0x004415fb6c000000 0x0861ffff80000001 0xe8430ffffc000000

def z1094 : W := mkw 0x05e576806e2d5603 0x702f2bb403716ab0 0xfff7ff807f8ffe1e 0xffffbffc03fc7ff0

def z1095 : W := mkw 0x000000120090a180 0x080000009004850c 0xee18387e71f1f99f 0xd770c1c3f38f8fcc

def z1096 : W := mkw 0x0218895e91d0a990 0x8810c44af48e854c 0x0019c07f81f00189 0x3000ce03fc0f800c

def z1097 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffe0707ffe000f 0x7fbfff0383fff000

def z1098 : W := mkw 0x056040006c280003 0x002b020003614000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z1099 : W := mkw 0x0f5f9b6d8000001c 0x007afcdb6c000000 0xfe7ffbff80000001 0xf7f3ffdffc000000

def z1100 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc87867f1 0xec034e3c7e43c33f

def z1101 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xffffffff8f8f861f 0xfffffffffc7c7c30

def z1102 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x0069c78fc87867fb 0x38034e3c7e43c33f

def z1103 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe03f807e01ff9f 0xdf7f01fc03f00ffc

def z1104 : W := mkw 0x0fdfbf6d8000001c 0x007efdfb6c000000 0xdfffffff80000000 0xaefffffffc000000

def z1105 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xce18387e71f1f98d 0x9670c1c3f38f8fcc

def z1106 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xb1ffc0004ffe000a 0x3d8ffe00027ff000

def z1107 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xd7ffc0007ffe0004 0x2ebffe0003fff000

def z1108 : W := mkw 0x077d40807d6c4203 0xc03bea0403eb6210 0xf7ffc781fffe67ff 0xffbffe3c0ffff33f

def z1109 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0x8069c78fc87867e9 0xbc034e3c7e43c33f

def z1110 : W := mkw 0x0000810680102080 0x0800040834008104 0xa069c78fc87867fb 0xfd034e3c7e43c33f

def z1111 : W := mkw 0x0fdfbf6d8201041c 0x207efdfb6c100820 0xffffffff8e000601 0xfffffffffc700030

def z1112 : W := mkw 0x0218085a11d0a990 0x8810c042d08e854c 0xef98387e7ff1f99f 0xdf7cc1c3f3ff8fcc

def z1113 : W := mkw 0x8082243102838548 0x2404112188141c2a 0x119624718f8f87f9 0x788cb1238c7c7c3f

def z1114 : W := mkw 0x8a1f897f91d2a9dc 0x8c50fc4bfc8e954e 0x101fc07f81fe01e9 0x3080fe03fc0ff00f

def z1115 : W := mkw 0x0f5d9b4c80000014 0x007aecda64000000 0xce79fbfe00000000 0x8673cfdff0000000

def z1116 : W := mkw 0x8002003100828148 0x040010018804140a 0x719604718f8e07ff 0x7b8cb0238c7c703f

def z1117 : W := mkw 0x4218c95e91f8a9b0 0x8a10c64af48fc54d 0x0019c07e01f00189 0x1000ce03f00f800c

def z1118 : W := mkw 0x05c0368026015601 0x302e01b401300ab0 0x6f803f803e01fe16 0xcb7c01fc01f00ff0

def z1119 : W := mkw 0x4020c186ec3c62a3 0x4a01060c3761e315 0xa069c78fce7e67fb 0xfd034e3c7e73f33f

def z1120 : W := mkw 0x07dd3e4800000010 0x003ee9f240000000 0xfffffffe00000001 0xfffffffff0000000

def z1121 : W := mkw 0x4020c186c83862a2 0x0a01060c3641c315 0xe079e7ffc87867fb 0xff03cf3ffe43c33f

def z1122 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0xf7ffc401fffe066e 0x3fbffe200ffff033

def z1123 : W := mkw 0x0000085a11d0a990 0x88000042d08e854c 0xee00387e71f1f99f 0xc77001c3f38f8fcc

def z1124 : W := mkw 0x077d40007d6c0003 0xc03bea0003eb6000 0x97ffc0007ffe0008 0x3cbffe0003fff000

def z1125 : W := mkw 0x0218084a11502890 0x8810c042508a8144 0xee18387e7071f817 0xd770c1c3f3838fc0

def z1126 : W := mkw 0x0a1d895e91d0a994 0x8850ec4af48e854c 0x0019c07e01f00189 0x1000ce03f00f800c

def z1127 : W := mkw 0x05c0360002010400 0x202e01b000100820 0xefe03f807e01fe16 0xcf7f01fc03f00ff0

def z1128 : W := mkw 0x0dc7b7258000000c 0x006e3db92c000000 0xf1ffe7ff80000001 0xff8fff3ffc000000

def z1129 : W := mkw 0x05e036806e015603 0x302f01b403700ab0 0xefe9ff807e01fe16 0xff7f4ffc03f00ff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z8,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z10]),(0,[z11,z1,z12,z3,z4,z5,z6])],[(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z6]),(0,[z1,z2,z3,z15,z16,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z18,z6,z19]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z22,z1,z23,z3,z4,z5,z6])],[(0,[z1,z2,z3,z24,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z5,z6])],[(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z6]),(0,[z1,z28,z2,z3,z4,z5,z6]),(0,[z1,z29,z30,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z31,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z32])],[(0,[z33,z1,z2,z3,z4,z5,z6]),(1,[z34,z2,z3,z16,z5,z6])],[(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z38,z1,z12,z3,z4,z5,z6]),(0,[z1,z2,z39,z3,z4,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z6]),(0,[z1,z2,z41,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z1,z2,z3,z4,z5,z6,z43])],[(0,[z1,z2,z3,z44,z5,z45,z6]),(0,[z1,z2,z3,z4,z5,z46,z36]),(0,[z1,z2,z3,z4,z5,z47,z6]),(0,[z1,z2,z3,z48,z49,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z51,z1,z2,z3,z4,z5,z52]),(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z54,z5,z6]),(0,[z1,z2,z3,z55,z4,z5,z6])],[(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z1,z12,z3,z4,z5,z6,z19]),(0,[z56,z1,z57,z3,z4,z5,z6]),(0,[z56,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z3,z59,z5,z60,z6])],[(0,[z1,z2,z3,z4,z61,z18,z6]),(0,[z1,z2,z3,z4,z62,z5,z6]),(0,[z1,z2,z3,z4,z63,z5,z6]),(0,[z1,z2,z3,z64,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z65])],[(0,[z1,z2,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z4,z5,z67,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z68,z1,z2,z3,z4,z5,z36]),(0,[z1,z2,z69,z3,z4,z5,z6]),(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z6])],[(0,[z71,z1,z2,z3,z4,z5,z10]),(0,[z72,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z75])],[(0,[z1,z2,z58,z76,z4,z5,z6]),(0,[z1,z2,z77,z4,z8,z5,z6]),(0,[z1,z2,z3,z78,z4,z5,z6]),(0,[z22,z25,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z79,z5,z6]),(0,[z1,z2,z3,z77,z27,z5,z6]),(0,[z1,z2,z3,z4,z80,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z81])],[(0,[z71,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z82,z5,z6]),(0,[z1,z2,z3,z4,z83,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z84]),(0,[z85,z1,z2,z3,z4,z5,z86])],[(0,[z87,z1,z2,z3,z4,z5,z6])],[(0,[z88,z1,z89,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z90,z6]),(1,[z1,z2,z3,z4,z91,z6]),(0,[z92,z1,z2,z3,z4,z5,z6])],[(0,[z71,z2,z3,z93,z4,z5,z6]),(0,[z1,z2,z94,z3,z4,z5,z6]),(0,[z1,z2,z76,z4,z5,z86,z6]),(0,[z1,z95,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z96,z4,z5,z6]),(0,[z1,z2,z97,z3,z4,z5,z98]),(0,[z99,z1,z2,z3,z4,z5,z6]),(0,[z100,z1,z2,z3,z4,z5,z6])],[(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z1,z102,z2,z3,z4,z5,z6]),(0,[z51,z2,z3,z4,z5,z6,z52]),(0,[z103,z1,z3,z4,z5,z6,z19]),(0,[z1,z2,z3,z59,z104,z5,z6])],[(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z6]),(0,[z22,z1,z108,z3,z4,z5,z6])],[(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z110,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z6]),(0,[z112,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z113,z1,z2,z3,z4,z5,z114]),(0,[z22,z1,z2,z115,z4,z5,z6])]],
   [[(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z58,z3,z117,z5,z6])],[(0,[z118,z1,z2,z3,z4,z5,z6])],[(0,[z71,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z88,z1,z2,z7,z4,z5,z6]),(0,[z113,z1,z2,z3,z5,z6,z114])],[(0,[z1,z2,z3,z120,z4,z5,z6]),(0,[z1,z121,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z122,z6]),(0,[z1,z123,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z124,z5,z6]),(1,[z1,z2,z125,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z18,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z20,z1,z2,z3,z4,z60,z6])],[(0,[z1,z2,z3,z4,z5,z127,z6]),(0,[z1,z128,z129,z2,z4,z5,z6]),(0,[z1,z2,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z131,z6]),(1,[z1,z2,z3,z132,z5,z6])],[(0,[z1,z2,z3,z4,z5,z133,z6]),(0,[z1,z2,z3,z4,z5,z134,z6]),(0,[z1,z2,z58,z3,z4,z5,z6])],[(0,[z1,z2,z3,z135,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(0,[z38,z1,z2,z137,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z6])],[(0,[z139,z1,z2,z3,z4,z5,z6]),(1,[z71,z3,z93,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z141,z1,z142,z3,z4,z5,z6]),(0,[z1,z2,z58,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z83,z6,z65])]],
   [[(0,[z109,z1,z2,z3,z143,z5,z6]),(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z145,z1,z2,z3,z4,z5,z6]),(0,[z1,z146,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z147,z5,z6])],[(0,[z1,z148,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z103,z1,z2,z3,z150,z5,z6])],[(0,[z1,z151,z2,z3,z4,z5,z6]),(0,[z152,z1,z2,z3,z4,z5,z6])],[(0,[z153,z1,z2,z3,z4,z5,z6]),(1,[z1,z29,z2,z4,z5,z6]),(0,[z1,z2,z3,z154,z4,z5,z6]),(0,[z1,z2,z3,z4,z81,z6,z65])],[(1,[z1,z2,z3,z155,z5,z6]),(1,[z149,z2,z3,z4,z45,z6]),(0,[z1,z2,z3,z4,z156,z5,z6]),(1,[z11,z1,z128,z4,z5,z6]),(0,[z1,z3,z4,z80,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z157,z6])],[(0,[z1,z128,z89,z2,z4,z5,z6]),(0,[z11,z1,z129,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z159]),(0,[z1,z2,z3,z4,z5,z6,z160])],[(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z163])],[(0,[z1,z164,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z165,z6]),(0,[z1,z2,z3,z166,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z167]),(0,[z1,z168,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z5,z6])]],
   [[(0,[z1,z2,z169,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z170,z5,z6]),(0,[z1,z2,z3,z16,z48,z5,z6]),(0,[z1,z2,z3,z59,z48,z5,z6]),(0,[z1,z2,z3,z171,z4,z5,z6])],[(0,[z71,z1,z2,z3,z4,z66,z6]),(0,[z1,z2,z3,z4,z5,z6,z172]),(0,[z51,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z97,z4,z5,z86]),(0,[z1,z2,z3,z4,z5,z6,z173])],[(0,[z71,z1,z174,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z175,z6]),(0,[z1,z2,z3,z4,z5,z6,z176]),(0,[z1,z2,z3,z177,z4,z5,z6]),(0,[z1,z178,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z179]),(0,[z180,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z181,z6]),(0,[z1,z2,z3,z4,z5,z6,z182]),(0,[z1,z2,z3,z4,z183,z5,z6])],[(0,[z71,z1,z2,z3,z184,z5,z6]),(0,[z185,z89,z2,z3,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z6]),(0,[z1,z2,z3,z187,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z6]),(0,[z22,z1,z2,z188,z4,z5,z6])],[(0,[z189,z1,z3,z4,z5,z45,z6]),(0,[z1,z2,z3,z4,z5,z190,z6]),(0,[z191,z1,z2,z3,z4,z5,z6])],[(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z193,z4,z5,z6]),(0,[z1,z194,z2,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z19]),(0,[z1,z2,z3,z4,z5,z6,z195])],[(0,[z1,z2,z196,z3,z4,z5,z6]),(0,[z1,z2,z3,z197,z4,z5,z6]),(0,[z1,z128,z2,z4,z5,z86,z6]),(0,[z1,z2,z23,z3,z4,z5,z6])]],
   [[(0,[z198,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z199,z6]),(0,[z51,z68,z2,z3,z4,z5,z6]),(0,[z200,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z201,z6]),(0,[z1,z2,z3,z4,z5,z202,z6]),(0,[z1,z2,z3,z4,z5,z203,z6])],[(0,[z1,z2,z3,z4,z5,z6,z204]),(0,[z1,z2,z3,z48,z5,z6,z114]),(0,[z103,z1,z30,z3,z4,z5,z6]),(0,[z103,z1,z2,z3,z205,z5,z6]),(0,[z56,z1,z206,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z207,z6])],[(0,[z208,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z80,z61,z6]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6])],[(0,[z1,z2,z3,z211,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z212,z6]),(0,[z1,z2,z3,z213,z4,z5,z6]),(0,[z214,z1,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z215,z6])],[(0,[z1,z2,z169,z4,z8,z5,z6]),(0,[z1,z216,z3,z4,z27,z5,z6]),(0,[z1,z2,z3,z4,z80,z45,z6]),(0,[z1,z2,z3,z217,z4,z5,z6]),(1,[z1,z2,z3,z218,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z219])],[(0,[z68,z2,z3,z169,z4,z5,z6]),(0,[z1,z220,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z221,z4,z5,z6]),(0,[z1,z2,z3,z76,z4,z5,z6]),(0,[z1,z2,z3,z59,z8,z5,z6]),(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z223,z65]),(0,[z1,z2,z3,z224,z4,z5,z6])],[(0,[z225,z1,z2,z3,z4,z5,z6]),(0,[z11,z226,z1,z3,z4,z5,z6]),(0,[z149,z227,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z228,z4,z5,z6]),(1,[z1,z2,z3,z147,z5,z6])],[(0,[z71,z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6])]],
   [[(0,[z71,z1,z3,z4,z5,z6,z19]),(0,[z1,z2,z3,z4,z5,z6,z232]),(0,[z1,z2,z3,z4,z233,z5,z6]),(0,[z1,z2,z3,z234,z4,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z1,z236,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z237,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z238])],[(0,[z1,z239,z2,z3,z4,z5,z6]),(0,[z240,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z241,z4,z5,z6])],[(0,[z38,z226,z1,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z85,z1,z244,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z246,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z247,z4,z5,z6]),(0,[z227,z2,z3,z4,z5,z6,z52]),(0,[z1,z2,z248,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z5,z6]),(0,[z85,z56,z1,z2,z4,z5,z6]),(0,[z113,z1,z2,z3,z59,z5,z6])],[(0,[z1,z2,z3,z4,z5,z250,z6]),(0,[z1,z251,z2,z3,z4,z5,z6])],[(1,[z26,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z252,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z253]),(0,[z1,z2,z3,z4,z5,z254,z6]),(0,[z20,z113,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z44,z5,z6]),(1,[z1,z2,z3,z255,z5,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z113,z1,z257,z3,z4,z5,z6]),(0,[z1,z258,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z259,z6]),(0,[z109,z1,z89,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z260,z6]),(0,[z149,z2,z3,z4,z5,z45,z6]),(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z6])],[(0,[z1,z2,z3,z262,z4,z5,z6]),(0,[z1,z2,z3,z4,z263,z5,z6]),(0,[z1,z2,z3,z4,z5,z264,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z265,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z266,z5,z6]),(0,[z1,z2,z58,z4,z5,z6,z98]),(1,[z267,z1,z2,z3,z5,z6])],[(0,[z1,z2,z268,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z269]),(0,[z270,z1,z2,z3,z5,z6,z114]),(0,[z189,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z271,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z56,z1,z2,z4,z5,z273,z6]),(0,[z1,z2,z3,z4,z274,z5,z6]),(1,[z1,z2,z3,z59,z5,z275])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z276,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z277,z5,z6]),(0,[z1,z2,z3,z4,z278,z5,z6]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z49,z6])],[(0,[z1,z279,z2,z3,z4,z5,z6]),(0,[z141,z1,z2,z3,z48,z5,z6]),(0,[z1,z2,z3,z280,z4,z5,z6]),(0,[z1,z2,z3,z4,z281,z5,z6]),(0,[z1,z2,z3,z282,z4,z5,z6]),(0,[z283,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z284,z6]),(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z1,z129,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z286,z6]),(0,[z1,z2,z3,z4,z5,z6,z287])]],
   [[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z128,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z117,z5,z6])],[(0,[z185,z1,z2,z169,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z1,z290,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z292,z1,z2,z3,z4,z5,z6]),(1,[z38,z1,z3,z4,z18,z6]),(0,[z1,z2,z97,z4,z5,z273,z6])],[(0,[z1,z293,z2,z3,z4,z5,z6]),(0,[z1,z2,z58,z3,z294,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z296])],[(0,[z1,z2,z3,z4,z297,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z20,z1,z2,z3,z5,z275,z6]),(0,[z1,z2,z3,z5,z275,z6,z114]),(0,[z298,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z104,z49,z5,z6])],[(0,[z85,z299,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z65])]],
   [[],[(0,[z1,z2,z3,z4,z5,z6,z300]),(0,[z1,z129,z3,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z301]),(0,[z1,z2,z3,z4,z5,z302,z6]),(1,[z20,z1,z2,z3,z60,z6]),(0,[z1,z2,z3,z49,z5,z60,z6])],[(0,[z1,z2,z3,z4,z5,z6,z303]),(1,[z1,z244,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z304,z6]),(0,[z305,z1,z2,z3,z4,z5,z6])],[(1,[z270,z2,z3,z27,z5,z6]),(0,[z2,z3,z4,z61,z5,z45,z6]),(0,[z1,z2,z3,z306,z4,z5,z6]),(0,[z1,z2,z97,z3,z4,z5,z86])],[(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z308,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z45,z6,z52]),(0,[z1,z128,z2,z58,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z309]),(0,[z1,z2,z3,z4,z5,z310,z6])],[(0,[z1,z2,z3,z4,z5,z6,z311]),(0,[z1,z129,z2,z3,z4,z5,z6]),(0,[z1,z3,z76,z4,z5,z18,z6]),(0,[z1,z2,z3,z312,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z275,z6])],[(0,[z1,z2,z3,z4,z5,z313,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z315,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z3,z4,z5,z6,z19]),(0,[z1,z2,z317,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z77,z16,z5,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z77,z4,z5,z6]),(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z321,z6])],[(0,[z1,z2,z3,z4,z322,z5,z6]),(0,[z1,z2,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z323,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z324])],[(0,[z1,z2,z4,z5,z86,z6,z98]),(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z6]),(0,[z327,z1,z2,z3,z4,z5,z6])],[(0,[z328,z1,z2,z3,z4,z5,z6]),(0,[z226,z1,z142,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z329,z6]),(0,[z1,z2,z3,z4,z5,z330,z6]),(0,[z331,z1,z2,z3,z4,z5,z6]),(0,[z85,z315,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z332,z5,z6]),(0,[z185,z109,z2,z3,z4,z5,z6]),(0,[z2,z3,z16,z4,z27,z5,z6]),(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z334,z65])],[(0,[z335,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z336,z4,z5,z6]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z27,z48,z5,z6]),(0,[z34,z2,z3,z16,z4,z5,z6]),(0,[z1,z338,z2,z3,z4,z5,z6])],[(0,[z89,z2,z3,z169,z4,z5,z6]),(0,[z1,z279,z2,z3,z5,z45,z6]),(0,[z68,z227,z2,z3,z4,z5,z6]),(0,[z339,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z273,z6]),(0,[z22,z1,z2,z3,z4,z6,z65])],[(0,[z341,z1,z2,z3,z4,z5,z6]),(0,[z270,z1,z2,z3,z49,z5,z6]),(0,[z1,z2,z3,z342,z5,z36,z6]),(0,[z1,z2,z3,z205,z4,z5,z6]),(1,[z1,z257,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z343])]],
   [[(0,[z20,z270,z1,z2,z3,z5,z6]),(0,[z34,z1,z2,z3,z49,z5,z6]),(0,[z1,z2,z3,z344,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z345,z6])],[(0,[z346,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z347,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z348,z6])],[(0,[z1,z2,z3,z349,z4,z5,z6]),(0,[z1,z2,z3,z342,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z350,z6]),(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z351,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z352]),(0,[z1,z128,z2,z169,z4,z5,z6]),(0,[z353,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z354,z5,z6]),(0,[z1,z142,z3,z4,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z223])],[(1,[z1,z2,z120,z4,z5,z6]),(0,[z1,z2,z355,z3,z4,z5,z6]),(0,[z1,z2,z356,z3,z4,z5,z6]),(0,[z141,z1,z2,z3,z15,z5,z6])],[(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z1,z2,z3,z4,z5,z45,z6]),(1,[z299,z2,z3,z4,z5,z6])],[(1,[z1,z216,z3,z4,z5,z6]),(0,[z358,z1,z2,z3,z4,z5,z6]),(0,[z88,z1,z2,z3,z77,z5,z6])],[(0,[z71,z38,z1,z3,z4,z5,z6])]],
   [[(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z360,z3,z4,z5,z6]),(0,[z361,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z247,z4,z27,z5,z6]),(0,[z1,z2,z3,z4,z5,z46,z52]),(0,[z1,z3,z4,z5,z46,z6,z19]),(0,[z1,z2,z3,z4,z5,z6,z98]),(0,[z1,z362,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z323,z5,z6])],[(0,[z1,z2,z3,z27,z8,z5,z6]),(0,[z1,z2,z3,z4,z363,z5,z6])],[(0,[z364,z1,z2,z3,z4,z5,z6]),(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z366,z3,z4,z5,z6]),(0,[z1,z2,z3,z367,z4,z5,z6]),(0,[z141,z1,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z368,z6])],[(0,[z1,z2,z3,z369,z4,z5,z6]),(0,[z1,z2,z3,z370,z4,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z275])],[(0,[z1,z2,z3,z4,z371,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z373,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z374]),(0,[z68,z1,z2,z3,z4,z5,z52]),(0,[z1,z142,z2,z3,z15,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z375]),(0,[z1,z2,z3,z4,z5,z6,z376]),(0,[z56,z1,z2,z3,z4,z83,z6]),(0,[z113,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z377,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z379,z1,z2,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z381,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z382,z5,z6])],[(0,[z1,z2,z3,z383,z4,z5,z6]),(1,[z1,z3,z4,z5,z127,z6]),(0,[z1,z2,z3,z255,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z143,z4,z5,z6]),(0,[z227,z2,z3,z4,z61,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z384]),(0,[z1,z2,z3,z4,z5,z6,z385]),(0,[z386,z1,z2,z3,z4,z5,z6])],[(0,[z26,z1,z89,z3,z4,z5,z6]),(0,[z1,z387,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z388]),(0,[z1,z2,z3,z4,z5,z389,z6]),(0,[z1,z2,z3,z390,z4,z5,z6]),(1,[z315,z2,z3,z4,z5,z6])],[(0,[z226,z1,z3,z4,z80,z5,z6]),(0,[z1,z2,z76,z4,z5,z273,z6]),(0,[z1,z2,z3,z391,z4,z5,z6]),(0,[z1,z2,z392,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z393,z6])],[(1,[z113,z1,z2,z3,z5,z114])],[(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z395,z6]),(0,[z1,z2,z396,z3,z4,z5,z6]),(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z398,z5,z6])],[(0,[z1,z2,z3,z4,z399,z5,z6]),(0,[z1,z2,z3,z4,z5,z400,z6]),(0,[z1,z2,z206,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z401,z6])],[(0,[z1,z3,z4,z5,z36,z6,z73]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z5,z6,z114]),(0,[z1,z2,z3,z4,z403,z5,z6])],[(0,[z1,z2,z3,z4,z150,z5,z6]),(0,[z1,z2,z3,z4,z5,z404,z6]),(0,[z1,z2,z3,z4,z5,z86,z6])]],
   [[(0,[z405,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z197,z4,z5,z6]),(0,[z1,z2,z3,z16,z8,z5,z6]),(0,[z406,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z97,z4,z5,z6])],[(0,[z407,z1,z2,z3,z4,z5,z6]),(0,[z1,z408,z2,z3,z4,z5,z6])],[(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z410,z3,z4,z5,z36,z6]),(0,[z1,z411,z2,z3,z4,z5,z6])],[(0,[z1,z2,z412,z3,z4,z5,z6]),(0,[z413,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z414,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z415]),(0,[z22,z246,z2,z3,z4,z5,z6])],[(0,[z1,z416,z2,z3,z4,z5,z6])],[(0,[z417,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z36,z6,z52]),(0,[z1,z2,z3,z4,z5,z418,z6]),(0,[z1,z2,z419,z3,z4,z5,z6]),(0,[z1,z2,z3,z294,z4,z5,z6])],[(0,[z1,z2,z420,z3,z4,z5,z6]),(0,[z1,z2,z421,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z4,z49,z6])],[(0,[z109,z1,z2,z169,z4,z5,z6]),(1,[z1,z2,z3,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z422,z6]),(0,[z1,z2,z7,z3,z77,z5,z6]),(0,[z20,z1,z2,z3,z77,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z423,z5,z6]),(1,[z1,z2,z3,z4,z5,z10])],[(0,[z1,z424,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z425,z5,z6]),(1,[z185,z89,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z426,z5,z6]),(0,[z1,z12,z3,z4,z80,z5,z6]),(0,[z1,z427,z2,z3,z4,z5,z6])],[(0,[z1,z89,z2,z76,z4,z5,z6]),(1,[z1,z23,z3,z4,z5,z6])],[(0,[z428,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z429,z5,z6]),(0,[z1,z2,z3,z430,z4,z5,z6]),(0,[z1,z2,z3,z4,z431,z5,z6]),(0,[z432,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z433])],[(0,[z2,z3,z169,z4,z5,z6,z52]),(0,[z1,z2,z434,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z19]),(0,[z435,z1,z2,z3,z4,z5,z6])],[(1,[z1,z164,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z436,z5,z6]),(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z438,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z439,z6])],[(0,[z1,z440,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z61,z6]),(0,[z1,z2,z3,z441,z4,z5,z6])],[(0,[z1,z2,z3,z184,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z423,z6]),(0,[z1,z2,z3,z15,z49,z5,z6]),(0,[z1,z2,z442,z3,z4,z5,z6]),(1,[z1,z2,z3,z117,z5,z6]),(0,[z85,z1,z2,z4,z83,z5,z6]),(0,[z1,z2,z3,z4,z5,z443,z6])]],
   [[(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z5,z6,z114]),(0,[z149,z1,z2,z3,z4,z45,z6]),(0,[z1,z2,z3,z4,z5,z46,z6])],[(0,[z56,z1,z2,z3,z4,z273,z6])],[(0,[z1,z2,z3,z445,z4,z5,z6]),(0,[z185,z2,z3,z4,z5,z6,z52]),(0,[z1,z2,z3,z4,z5,z446,z6]),(0,[z447,z1,z2,z3,z4,z5,z6]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z450])],[(0,[z226,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z451,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z452]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z2,z454,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z455])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z456,z2,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z457,z5,z6]),(0,[z1,z2,z3,z59,z5,z275,z6])],[(0,[z1,z128,z2,z4,z5,z273,z6]),(0,[z458,z1,z2,z3,z4,z5,z6])],[(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z460,z5,z6]),(0,[z1,z89,z2,z4,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z461]),(0,[z1,z2,z3,z4,z5,z462,z6]),(1,[z25,z2,z3,z4,z5,z6]),(0,[z1,z2,z463,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z464]),(0,[z1,z2,z3,z4,z5,z6,z465]),(0,[z1,z2,z3,z4,z49,z5,z6]),(0,[z466,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z71,z226,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z6]),(1,[z1,z3,z247,z4,z5,z6]),(0,[z467,z1,z2,z3,z4,z5,z6])],[(0,[z1,z468,z2,z3,z4,z5,z6]),(0,[z68,z2,z3,z4,z5,z36,z6]),(0,[z1,z469,z2,z3,z4,z5,z6]),(1,[z1,z12,z3,z4,z80,z6])],[(0,[z270,z1,z2,z3,z27,z5,z6]),(0,[z1,z142,z2,z3,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6])],[(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z1,z2,z3,z4,z471,z5,z6]),(0,[z1,z472,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z126,z6]),(0,[z1,z2,z473,z3,z4,z5,z6])],[(0,[z88,z1,z2,z169,z4,z5,z6]),(0,[z227,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z36,z19]),(0,[z1,z2,z474,z3,z4,z5,z6]),(0,[z11,z1,z128,z2,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z475,z6])],[(1,[z1,z2,z3,z143,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z476]),(0,[z1,z12,z2,z3,z218,z5,z6]),(1,[z1,z108,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z52,z19]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z478,z5,z6]),(0,[z479,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z480,z6]),(1,[z1,z2,z115,z4,z5,z6])],[(0,[z71,z1,z142,z3,z4,z5,z6]),(0,[z226,z1,z3,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z481,z5,z6]),(0,[z1,z3,z15,z4,z48,z5,z6]),(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z1,z2,z3,z4,z483,z5,z6]),(0,[z267,z1,z2,z3,z5,z6,z65])]],
   [[(0,[z1,z2,z3,z4,z5,z484,z6]),(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z1,z486,z2,z3,z4,z5,z6]),(0,[z1,z2,z487,z3,z4,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z275])],[(0,[z1,z2,z3,z488,z4,z5,z6]),(0,[z141,z1,z30,z3,z4,z5,z6]),(0,[z1,z489,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z104,z49,z6])],[(0,[z490,z1,z2,z3,z4,z5,z6]),(0,[z1,z491,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z492,z4,z5,z6]),(0,[z38,z1,z2,z125,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z493])],[(1,[z1,z2,z3,z4,z66,z6]),(0,[z109,z1,z2,z3,z79,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(1,[z85,z1,z2,z4,z5,z98])],[(0,[z1,z2,z3,z4,z5,z495,z6]),(0,[z1,z2,z3,z4,z5,z6,z496]),(0,[z1,z497,z2,z3,z4,z5,z6]),(0,[z1,z30,z3,z4,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z498,z6]),(0,[z85,z1,z2,z4,z5,z6,z98])],[(0,[z1,z30,z3,z76,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z132,z5,z6])],[(1,[z1,z2,z3,z184,z5,z6]),(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z501,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z502]),(0,[z1,z2,z3,z4,z5,z6,z503])],[(0,[z504,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z137,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z505])]],
   [[(0,[z506,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z58,z4,z83,z6]),(0,[z507,z1,z2,z3,z4,z5,z6])],[(0,[z226,z1,z3,z93,z4,z5,z6]),(0,[z1,z12,z2,z3,z255,z5,z6]),(0,[z1,z2,z3,z8,z49,z5,z6]),(0,[z1,z2,z3,z4,z508,z5,z6])],[(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z510,z4,z5,z6]),(0,[z1,z511,z2,z3,z4,z5,z6]),(0,[z1,z257,z2,z3,z4,z5,z6])],[(0,[z512,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z513])],[(0,[z185,z68,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z514,z4,z5,z6]),(1,[z1,z30,z3,z4,z5,z46]),(0,[z1,z515,z2,z3,z4,z5,z6]),(1,[z92,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z516,z4,z5,z6]),(0,[z1,z517,z2,z3,z4,z5,z6])],[(0,[z226,z1,z3,z15,z4,z5,z6]),(0,[z518,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z519,z4,z5,z6]),(0,[z520,z1,z2,z3,z4,z5,z6])]],
   [[],[(0,[z1,z2,z3,z4,z5,z6,z521]),(1,[z1,z2,z3,z4,z126,z6])],[(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z270,z1,z2,z3,z59,z5,z6]),(0,[z523,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z169,z4,z5,z6]),(0,[z1,z216,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z59,z5,z6]),(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z76,z4,z5,z6]),(0,[z1,z142,z2,z3,z4,z5,z6]),(0,[z525,z1,z2,z3,z4,z5,z6]),(0,[z526,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z188,z4,z5,z6])],[(0,[z174,z2,z3,z93,z4,z5,z6]),(0,[z527,z1,z2,z3,z4,z5,z6]),(0,[z68,z2,z3,z4,z5,z45,z6]),(1,[z51,z2,z3,z4,z5,z52]),(0,[z1,z410,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z529]),(0,[z1,z2,z3,z4,z5,z530,z6]),(0,[z1,z2,z3,z4,z5,z6,z334])],[(0,[z1,z2,z531,z3,z4,z5,z6])],[(0,[z71,z1,z3,z4,z80,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z2,z3,z4,z5,z533,z6])],[(0,[z1,z534,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z5,z6,z114]),(0,[z535,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z268,z4,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z2,z537,z3,z4,z5,z6])],[(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z36,z6,z388]),(0,[z1,z539,z2,z3,z4,z5,z6]),(1,[z1,z2,z7,z8,z5,z6]),(0,[z1,z2,z58,z3,z4,z273,z6]),(0,[z1,z2,z3,z540,z4,z5,z6]),(0,[z541,z1,z2,z3,z4,z5,z6])],[(0,[z71,z1,z2,z3,z155,z5,z6]),(1,[z109,z2,z169,z4,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z218,z5,z6]),(1,[z103,z1,z3,z4,z5,z19]),(0,[z1,z2,z543,z3,z4,z5,z6])],[(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z545,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z80,z6]),(0,[z1,z2,z547,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z548,z6]),(0,[z1,z2,z549,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z550,z5,z6]),(0,[z1,z551,z2,z3,z4,z5,z6])],[(0,[z552,z1,z2,z3,z4,z5,z6]),(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z554,z6]),(0,[z11,z1,z3,z4,z5,z18,z6]),(1,[z1,z2,z3,z4,z215,z81])],[(1,[z1,z2,z3,z150,z5,z6])],[(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z1,z556,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z557]),(0,[z1,z2,z3,z4,z5,z6,z114])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z558]),(0,[z1,z57,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z83,z5,z86,z6]),(0,[z1,z2,z97,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z559,z6])],[(0,[z1,z2,z3,z4,z5,z560,z6]),(1,[z1,z410,z3,z4,z5,z6])],[(0,[z1,z561,z2,z3,z4,z5,z6]),(1,[z88,z1,z2,z77,z5,z6])],[(0,[z1,z2,z3,z562,z4,z5,z6]),(0,[z1,z2,z3,z4,z563,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z73]),(0,[z38,z1,z3,z4,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z6,z564])],[(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z81,z6])],[(0,[z1,z2,z3,z4,z566,z5,z6]),(0,[z1,z2,z3,z567,z4,z5,z6])],[(0,[z1,z3,z4,z5,z127,z45,z6]),(0,[z1,z2,z568,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z1,z570,z2,z3,z4,z5,z6])],[(0,[z571,z1,z2,z3,z4,z5,z6]),(0,[z572,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z573,z5,z6]),(0,[z1,z574,z2,z3,z4,z5,z6])]],
   [[(0,[z109,z2,z3,z169,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z575,z6]),(0,[z141,z1,z3,z4,z5,z6,z19]),(0,[z1,z576,z2,z3,z4,z5,z6])],[(0,[z577,z1,z2,z3,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6])],[(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z77,z5,z6,z114])],[(0,[z1,z2,z3,z580,z4,z5,z6]),(1,[z227,z2,z3,z4,z61,z6]),(0,[z1,z3,z76,z4,z5,z6,z19]),(0,[z1,z30,z2,z3,z4,z5,z46])],[(0,[z1,z2,z3,z581,z4,z5,z6]),(0,[z1,z2,z3,z4,z45,z18,z6]),(1,[z189,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z582,z6]),(0,[z20,z1,z2,z3,z15,z5,z6]),(0,[z583,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z584,z4,z5,z6])],[(0,[z270,z1,z2,z197,z4,z5,z6]),(1,[z1,z2,z3,z205,z5,z6]),(0,[z1,z2,z3,z4,z585,z5,z6])],[(0,[z1,z2,z3,z4,z5,z586,z6]),(0,[z1,z2,z3,z4,z587,z5,z6]),(1,[z1,z168,z3,z4,z5,z6]),(0,[z113,z1,z473,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z588,z4,z5,z6]),(0,[z185,z1,z89,z2,z4,z5,z6]),(0,[z1,z589,z2,z3,z4,z5,z6]),(1,[z1,z206,z3,z4,z5,z6]),(0,[z1,z2,z590,z3,z4,z5,z6])],[(0,[z591,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z114]),(0,[z1,z2,z3,z104,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z5,z65])],[(0,[z1,z592,z2,z3,z4,z5,z6]),(0,[z593,z1,z2,z3,z4,z5,z6]),(0,[z34,z20,z1,z2,z3,z5,z6]),(0,[z1,z3,z4,z48,z5,z6,z19]),(0,[z1,z2,z3,z4,z5,z594,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z5,z6])],[(0,[z1,z2,z3,z4,z5,z596,z6]),(0,[z1,z2,z3,z4,z597,z5,z6])],[(0,[z598,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z599,z4,z5,z6]),(1,[z1,z2,z430,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z600,z6]),(0,[z20,z1,z2,z3,z5,z60,z6])],[(0,[z1,z2,z3,z4,z601,z5,z6]),(0,[z1,z2,z3,z602,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z603,z6]),(0,[z1,z2,z3,z4,z5,z604,z6]),(0,[z1,z2,z3,z4,z215,z5,z81])],[(0,[z605,z1,z2,z3,z4,z5,z6]),(1,[z1,z279,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z606]),(0,[z1,z2,z3,z4,z5,z6,z607])]],
   [[(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z2,z3,z609,z4,z5,z6]),(0,[z1,z2,z3,z610,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z611])],[(0,[z1,z2,z3,z4,z79,z5,z6]),(0,[z38,z1,z2,z3,z4,z80,z6]),(0,[z612,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z613,z5,z6]),(0,[z614,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z59,z5,z6]),(0,[z1,z2,z3,z125,z4,z5,z6]),(0,[z1,z615,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z98]),(0,[z1,z2,z3,z49,z5,z275,z6])],[(0,[z71,z1,z3,z76,z4,z5,z6]),(0,[z1,z2,z3,z616,z4,z5,z6]),(0,[z270,z1,z164,z2,z4,z5,z6]),(0,[z1,z617,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z83,z5,z273,z6]),(0,[z1,z2,z3,z4,z5,z618,z6])],[(0,[z619,z1,z2,z3,z4,z5,z6]),(0,[z620,z1,z2,z3,z4,z5,z6]),(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z622])],[(0,[z226,z1,z30,z3,z4,z5,z6]),(1,[z1,z2,z3,z342,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z623]),(0,[z624,z1,z2,z3,z4,z5,z6])],[(0,[z34,z1,z2,z3,z27,z5,z6]),(0,[z11,z1,z128,z3,z4,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z46]),(0,[z20,z1,z2,z3,z104,z5,z6])],[(0,[z625,z1,z2,z3,z4,z5,z6]),(1,[z1,z434,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z626,z6]),(0,[z1,z2,z3,z4,z5,z627,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z628,z6]),(0,[z1,z2,z58,z3,z4,z83,z6]),(0,[z1,z2,z3,z4,z5,z6,z629])],[(0,[z1,z2,z3,z4,z5,z6,z630]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z273,z6,z65])],[(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z270,z1,z2,z3,z16,z5,z6]),(0,[z1,z632,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z633,z5,z6]),(0,[z634,z1,z2,z3,z4,z5,z6])],[(0,[z1,z89,z434,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z16,z5,z6]),(0,[z1,z2,z4,z5,z273,z6,z98]),(0,[z1,z299,z2,z3,z4,z5,z6]),(0,[z635,z1,z2,z3,z4,z5,z6])],[(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z92,z1,z2,z4,z5,z6,z65])],[(0,[z71,z1,z3,z93,z4,z5,z6]),(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z270,z2,z3,z4,z27,z5,z6]),(1,[z141,z1,z3,z15,z5,z6]),(0,[z88,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z77,z49,z5,z6]),(0,[z1,z108,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z132,z5,z6])],[(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z638,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z5,z6]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z306,z5,z6])],[(0,[z640,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z11,z1,z3,z4,z5,z6,z19]),(0,[z1,z2,z3,z641,z4,z5,z6]),(0,[z1,z30,z12,z3,z4,z5,z6])],[(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z642,z6]),(1,[z1,z129,z76,z4,z5,z6]),(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z644,z4,z5,z6]),(0,[z1,z30,z2,z430,z4,z5,z6]),(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z646,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z104,z4,z60,z6])],[(0,[z71,z1,z3,z15,z4,z5,z6]),(0,[z647,z1,z2,z3,z4,z5,z6])],[(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z649,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z650,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z651,z6])],[(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z2,z3,z4,z5,z652,z6]),(0,[z1,z2,z3,z77,z59,z5,z6]),(1,[z1,z57,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z223])],[(0,[z56,z1,z2,z4,z5,z86,z6]),(0,[z653,z1,z2,z3,z4,z5,z6]),(1,[z1,z473,z3,z4,z5,z6])],[(0,[z654,z1,z2,z3,z4,z5,z6]),(1,[z56,z1,z2,z4,z273,z6])]],
   [[(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z656,z4,z5,z6]),(0,[z657,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z323,z5,z6])],[(0,[z1,z2,z3,z658,z4,z5,z6]),(0,[z1,z12,z3,z76,z4,z5,z6]),(0,[z20,z1,z2,z3,z48,z5,z6]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z659,z4,z5,z6]),(0,[z1,z660,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z661,z6])],[(0,[z34,z270,z2,z3,z4,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z663,z6]),(0,[z1,z2,z3,z4,z5,z6,z664]),(0,[z1,z2,z3,z5,z60,z6,z114])],[(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z666]),(0,[z1,z2,z667,z3,z4,z5,z6]),(0,[z1,z2,z58,z4,z83,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z114])],[(0,[z668,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z4,z5,z669,z6]),(0,[z1,z2,z97,z4,z5,z86,z6])],[(0,[z51,z1,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z4,z5,z670,z6]),(0,[z1,z12,z2,z3,z4,z5,z6])],[(0,[z226,z1,z174,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z52]),(0,[z1,z2,z3,z671,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z672,z6])],[(0,[z1,z2,z3,z4,z5,z6,z388]),(0,[z1,z2,z3,z673,z4,z5,z6]),(0,[z674,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z675,z6])]],
   [[(1,[z1,z142,z3,z48,z5,z6]),(0,[z1,z30,z3,z4,z5,z46,z6]),(0,[z1,z2,z3,z4,z5,z676,z6]),(0,[z1,z2,z3,z4,z5,z81,z6])],[(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z1,z678,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z679,z6]),(0,[z1,z2,z3,z4,z48,z5,z6]),(0,[z1,z2,z3,z680,z4,z5,z6]),(0,[z681,z1,z2,z3,z4,z5,z6])],[(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z71,z1,z2,z120,z4,z5,z6]),(0,[z1,z682,z2,z3,z4,z5,z6]),(0,[z113,z1,z2,z3,z49,z5,z6])],[],[(0,[z683,z1,z2,z3,z4,z5,z6]),(0,[z1,z684,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z83,z215,z6]),(0,[z85,z1,z168,z3,z4,z5,z6]),(1,[z1,z2,z3,z306,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z685]),(0,[z56,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z334])],[(0,[z1,z2,z3,z686,z4,z5,z6]),(0,[z38,z1,z2,z3,z4,z18,z6]),(0,[z1,z2,z7,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z8,z5,z6]),(0,[z1,z687,z2,z3,z4,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z689,z3,z4,z5,z6]),(0,[z11,z1,z2,z76,z4,z5,z6]),(0,[z1,z128,z3,z76,z4,z5,z6]),(0,[z1,z2,z3,z690,z4,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z691,z5,z6]),(0,[z1,z2,z3,z4,z147,z5,z6])]],
   [[(0,[z1,z2,z692,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z1,z2,z3,z4,z5,z6,z694]),(1,[z22,z1,z2,z3,z4,z65])],[(1,[z1,z2,z3,z4,z423,z6]),(0,[z1,z2,z3,z4,z5,z695,z6]),(0,[z227,z1,z2,z3,z4,z61,z6]),(0,[z1,z2,z3,z4,z696,z5,z6]),(0,[z1,z2,z3,z697,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z698]),(0,[z1,z2,z3,z4,z5,z699,z6]),(1,[z246,z2,z3,z4,z5,z6])],[(0,[z71,z1,z2,z268,z4,z5,z6]),(0,[z227,z1,z2,z3,z4,z45,z6]),(0,[z1,z128,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z700])],[(0,[z1,z2,z3,z93,z4,z5,z6]),(0,[z226,z1,z3,z4,z5,z6,z19]),(0,[z1,z2,z701,z3,z4,z5,z6]),(0,[z11,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z702,z4,z5,z6])],[(0,[z1,z2,z3,z15,z27,z5,z6]),(1,[z1,z2,z3,z294,z5,z6]),(0,[z85,z1,z2,z3,z4,z91,z6]),(0,[z1,z2,z703,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z88,z1,z2,z77,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z704])],[(0,[z71,z11,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z705,z4,z5,z6]),(0,[z1,z2,z3,z706,z4,z5,z6]),(0,[z1,z2,z244,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z707,z5,z6]),(0,[z2,z3,z4,z5,z708,z6]),(0,[z523,z1,z2,z4,z273,z6])],[(0,[z1,z2,z4,z126,z6,z98])],[(0,[z1,z3,z155,z5,z6,z19]),(0,[z1,z2,z3,z709,z5,z6]),(0,[z1,z2,z3,z4,z710,z6]),(0,[z25,z2,z3,z132,z5,z6]),(0,[z1,z2,z5,z6,z223,z334])],[(0,[z1,z2,z3,z4,z5,z711]),(0,[z339,z89,z2,z4,z5,z6]),(0,[z583,z2,z3,z4,z5,z36]),(0,[z1,z712,z3,z4,z5,z6])],[(0,[z71,z268,z93,z4,z5,z6]),(0,[z1,z2,z713,z4,z5,z6]),(0,[z141,z1,z3,z15,z5,z6]),(0,[z1,z2,z3,z4,z714,z6])],[(0,[z1,z715,z3,z4,z5,z6]),(0,[z716,z1,z2,z3,z5,z6]),(0,[z1,z206,z58,z4,z5,z6]),(0,[z1,z2,z3,z4,z717,z6]),(0,[z718,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z115,z4,z65])],[(0,[z1,z2,z719,z4,z5,z6]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z721]),(0,[z85,z1,z2,z4,z91,z98])],[(0,[z1,z29,z2,z4,z5,z6]),(0,[z1,z2,z3,z722,z5,z6])]],
   [[(0,[z1,z2,z3,z723,z5,z6]),(0,[z1,z129,z76,z4,z5,z6])],[(0,[z1,z2,z724,z4,z5,z6]),(0,[z1,z2,z197,z5,z6,z114]),(0,[z1,z2,z3,z4,z725,z6]),(0,[z1,z2,z3,z5,z695,z114]),(0,[z1,z726,z3,z4,z5,z6]),(0,[z1,z108,z3,z132,z5,z6])],[(0,[z1,z2,z727,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z229]),(0,[z1,z2,z4,z5,z6,z728]),(0,[z22,z1,z2,z3,z223,z65])],[(0,[z1,z2,z590,z77,z5,z6]),(0,[z1,z168,z3,z4,z126,z6])],[(0,[z729,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z730])],[(0,[z1,z473,z3,z4,z5,z6]),(0,[z1,z2,z97,z4,z5,z86]),(0,[z731,z1,z3,z4,z5,z6])],[(0,[z71,z40,z3,z4,z5,z6]),(0,[z1,z732,z3,z4,z5,z6]),(0,[z56,z1,z2,z4,z273,z6]),(0,[z1,z2,z3,z733,z5,z6])],[(0,[z38,z1,z3,z4,z66,z6]),(0,[z1,z2,z3,z734,z5,z6]),(0,[z299,z244,z3,z4,z5,z6]),(0,[z1,z2,z3,z323,z5,z6]),(0,[z1,z735,z3,z4,z5,z6])]],
   [[(0,[z1,z121,z76,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z736]),(0,[z1,z2,z3,z5,z6,z737])],[(0,[z738,z1,z3,z4,z5,z6]),(0,[z578,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z4,z739,z6]),(0,[z1,z2,z3,z4,z5,z740]),(0,[z1,z3,z741,z4,z5,z6])],[(0,[z71,z3,z93,z4,z66,z6]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z1,z2,z7,z743,z5,z6])],[(0,[z1,z2,z3,z4,z5,z744]),(0,[z1,z2,z3,z5,z6,z745]),(0,[z1,z3,z4,z5,z6,z746]),(0,[z1,z2,z3,z747,z5,z6])],[(0,[z1,z3,z15,z155,z5,z6]),(0,[z1,z2,z3,z4,z423,z10]),(0,[z1,z2,z3,z4,z5,z748]),(0,[z749,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z750]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z2,z3,z59,z5,z752])],[(0,[z2,z3,z753,z27,z5,z6]),(0,[z1,z754,z410,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z755]),(0,[z1,z756,z3,z4,z5,z6]),(0,[z1,z757,z3,z4,z5,z6])],[(0,[z758,z1,z3,z4,z5,z6]),(0,[z11,z1,z29,z4,z5,z6]),(0,[z1,z2,z759,z4,z5,z6]),(0,[z760,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z761,z5,z6]),(0,[z2,z3,z4,z61,z762,z6]),(0,[z1,z2,z3,z218,z5,z6]),(0,[z1,z763,z3,z4,z5,z6]),(0,[z1,z2,z58,z4,z710,z6])],[(0,[z68,z2,z3,z4,z5,z271]),(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z765,z3,z4,z5,z6])],[(0,[z109,z2,z169,z79,z5,z6]),(0,[z1,z2,z3,z5,z6,z766]),(0,[z85,z1,z2,z4,z5,z767]),(0,[z1,z768,z2,z4,z5,z6])],[(0,[z89,z769,z2,z4,z5,z6]),(0,[z299,z128,z2,z4,z5,z6]),(0,[z1,z2,z770,z4,z5,z6]),(0,[z1,z2,z3,z306,z5,z6]),(0,[z315,z244,z3,z4,z5,z6])],[(0,[z1,z771,z3,z4,z5,z6]),(0,[z1,z772,z3,z4,z5,z6]),(0,[z1,z2,z3,z773,z5,z6]),(0,[z22,z1,z2,z3,z132,z65])],[(0,[z1,z12,z3,z218,z80,z6]),(0,[z1,z2,z4,z83,z6,z493])],[(1,[z769,z2,z4,z5,z6]),(0,[z1,z469,z76,z4,z5,z6]),(0,[z1,z2,z3,z59,z5,z210]),(0,[z1,z2,z774,z4,z5,z6])],[(0,[z1,z775,z3,z4,z5,z6]),(0,[z1,z2,z188,z132,z5,z6]),(0,[z22,z1,z2,z3,z4,z65])]],
   [[(0,[z1,z2,z3,z4,z423,z6]),(0,[z1,z776,z2,z3,z5,z6]),(0,[z85,z1,z206,z4,z5,z6])],[(0,[z246,z2,z3,z4,z5,z6]),(0,[z1,z2,z777,z4,z5,z6]),(0,[z56,z1,z57,z4,z273,z6])],[(0,[z1,z2,z778,z4,z5,z6]),(0,[z1,z779,z2,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z780])],[(0,[z1,z2,z120,z155,z5,z6]),(0,[z26,z1,z3,z4,z5,z6]),(0,[z1,z781,z3,z4,z5,z6]),(0,[z270,z2,z197,z27,z5,z6]),(0,[z1,z782,z3,z4,z5,z6]),(0,[z1,z206,z4,z5,z86,z6]),(0,[z1,z2,z3,z783,z5,z6]),(0,[z22,z25,z2,z3,z4,z65]),(0,[z1,z2,z3,z4,z780,z65])],[(0,[z1,z2,z3,z784,z5,z6]),(0,[z226,z1,z430,z4,z5,z6]),(0,[z1,z785,z3,z4,z5,z6]),(0,[z1,z2,z3,z255,z5,z6]),(0,[z1,z2,z3,z743,z5,z6])],[(0,[z1,z216,z3,z155,z5,z6]),(0,[z1,z2,z786,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z787]),(0,[z1,z2,z3,z217,z49,z6]),(0,[z1,z29,z30,z4,z5,z46]),(1,[z1,z2,z3,z5,z752]),(0,[z92,z1,z2,z5,z6,z223])],[(0,[z1,z2,z3,z4,z5,z788]),(0,[z1,z789,z3,z4,z5,z6]),(0,[z1,z790,z3,z4,z5,z6])],[(0,[z1,z2,z3,z791,z5,z6]),(0,[z1,z792,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z5,z6])]],
   [[(1,[z1,z3,z4,z5,z755]),(0,[z1,z2,z793,z4,z5,z6])],[(0,[z189,z1,z279,z3,z5,z6]),(0,[z1,z3,z4,z5,z794,z6]),(0,[z1,z12,z3,z255,z80,z6]),(0,[z1,z2,z3,z795,z5,z6]),(0,[z85,z1,z2,z147,z5,z98]),(0,[z1,z2,z3,z5,z275,z415])],[(0,[z1,z410,z3,z4,z5,z19])],[(0,[z1,z2,z3,z796,z5,z6]),(0,[z1,z2,z3,z797,z5,z6]),(0,[z1,z2,z798,z4,z5,z6]),(0,[z1,z799,z3,z4,z5,z6]),(0,[z1,z800,z3,z4,z5,z6]),(0,[z92,z1,z801,z4,z5,z6])],[(0,[z1,z2,z3,z5,z6,z802]),(0,[z1,z3,z4,z5,z6,z803]),(0,[z1,z2,z197,z59,z5,z6]),(0,[z222,z1,z2,z3,z60,z6])],[(0,[z71,z178,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z600,z6])],[(0,[z185,z89,z434,z4,z5,z6]),(0,[z804,z1,z3,z4,z5,z6]),(0,[z1,z408,z3,z48,z5,z6]),(0,[z38,z1,z3,z4,z18,z6]),(0,[z805,z1,z2,z4,z5,z6])],[]],
   [[(0,[z1,z2,z3,z4,z5,z806]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z808,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z809,z5,z6]),(0,[z1,z216,z3,z48,z5,z6]),(0,[z1,z2,z4,z5,z6,z767]),(0,[z22,z1,z2,z4,z334,z65])],[(0,[z1,z2,z3,z184,z423,z6]),(0,[z541,z1,z2,z77,z5,z6]),(0,[z1,z168,z3,z4,z91,z6])],[(0,[z1,z128,z168,z4,z5,z6])],[(0,[z1,z2,z810,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z812,z1,z2,z3,z4,z5]),(0,[z813,z2,z3,z4,z5,z6]),(0,[z1,z801,z3,z4,z5,z6])],[(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z815,z5,z6]),(0,[z1,z2,z3,z816,z5,z6]),(0,[z1,z817,z2,z4,z5,z6]),(0,[z1,z818,z3,z4,z5,z6]),(0,[z1,z2,z3,z819,z5,z6])],[(0,[z1,z820,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z821,z6])],[(0,[z1,z2,z3,z79,z5,z6]),(0,[z270,z2,z3,z753,z5,z6]),(0,[z624,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z147,z126,z6])]],
   [[(0,[z2,z3,z4,z5,z762,z6]),(0,[z1,z822,z2,z4,z5,z6])],[(0,[z1,z2,z77,z743,z5,z6]),(0,[z22,z1,z2,z188,z4,z65])],[(0,[z1,z2,z3,z4,z823,z6]),(0,[z71,z3,z93,z4,z5,z10]),(0,[z1,z3,z44,z5,z127,z6]),(0,[z1,z2,z824,z4,z5,z6]),(0,[z1,z2,z3,z825,z5,z6]),(0,[z20,z1,z473,z3,z5,z6]),(0,[z20,z1,z2,z3,z480,z6]),(0,[z246,z2,z3,z323,z5,z6])],[(0,[z1,z2,z3,z4,z826,z6]),(0,[z270,z3,z247,z27,z5,z6]),(0,[z1,z29,z76,z4,z5,z6]),(0,[z299,z2,z76,z4,z5,z6]),(0,[z1,z3,z4,z80,z794,z6]),(0,[z1,z827,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z828])],[(0,[z1,z2,z3,z4,z762,z6])],[(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z2,z3,z4,z423,z229]),(0,[z11,z1,z779,z4,z5,z6]),(0,[z85,z315,z2,z4,z5,z98])],[(0,[z149,z2,z3,z44,z45,z6]),(0,[z189,z1,z720,z4,z5,z6]),(0,[z830,z2,z3,z4,z5,z6]),(0,[z1,z12,z125,z4,z5,z6]),(0,[z1,z2,z3,z831,z5,z6]),(0,[z1,z206,z4,z5,z273,z6])],[(0,[z1,z2,z3,z155,z5,z10]),(0,[z1,z2,z3,z832,z5,z6]),(0,[z1,z833,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z834,z6]),(0,[z835,z1,z3,z4,z5,z6]),(0,[z1,z2,z58,z4,z183,z6])],[(0,[z1,z2,z3,z4,z836,z6]),(0,[z38,z1,z137,z4,z18,z6]),(0,[z1,z837,z3,z4,z5,z6])],[(0,[z1,z2,z94,z8,z5,z6]),(0,[z1,z838,z3,z4,z5,z6]),(0,[z1,z2,z125,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z839])],[(0,[z1,z257,z3,z4,z5,z6]),(0,[z1,z2,z97,z4,z5,z676]),(0,[z1,z2,z4,z5,z767,z98]),(0,[z1,z2,z3,z132,z5,z6])],[(0,[z1,z2,z268,z4,z423,z6]),(0,[z1,z489,z76,z4,z5,z6]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z22,z92,z1,z2,z4,z65])],[(0,[z1,z2,z3,z841,z5,z6]),(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z2,z3,z4,z6,z843]),(0,[z1,z2,z4,z273,z6,z43]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z1,z844,z2,z3,z5,z6])],[(0,[z71,z3,z93,z4,z5,z6])],[(0,[z26,z1,z268,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z2,z846,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z847])]],
   [[(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z4,z849,z6]),(0,[z1,z2,z850,z4,z5,z6]),(0,[z1,z2,z851,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z752])],[(0,[z299,z2,z3,z4,z5,z6]),(0,[z1,z852,z3,z4,z5,z6]),(0,[z853,z2,z3,z4,z5,z6]),(0,[z1,z854,z3,z4,z5,z6])],[(0,[z149,z279,z2,z3,z45,z6]),(0,[z1,z3,z342,z5,z6,z73])],[(0,[z1,z2,z3,z155,z5,z6]),(0,[z1,z2,z855,z4,z5,z6]),(0,[z109,z769,z2,z4,z5,z6]),(0,[z149,z2,z3,z4,z45,z6]),(0,[z2,z3,z4,z762,z45,z6]),(0,[z1,z2,z3,z856,z5,z6]),(0,[z11,z1,z128,z4,z5,z6])],[(0,[z1,z2,z3,z857,z5,z6]),(0,[z1,z2,z3,z858,z5,z6]),(0,[z1,z859,z3,z4,z5,z6])],[(0,[z553,z2,z3,z4,z45,z6]),(0,[z1,z2,z262,z4,z5,z86]),(0,[z860,z1,z2,z3,z4,z6]),(0,[z1,z2,z115,z132,z5,z6])],[(0,[z507,z1,z2,z3,z5,z114])],[(0,[z71,z3,z861,z4,z5,z6]),(0,[z1,z216,z3,z15,z5,z6]),(0,[z1,z473,z3,z49,z5,z6])]],
   [[],[(0,[z1,z2,z3,z862,z5,z6]),(0,[z1,z863,z3,z4,z5,z6]),(0,[z227,z2,z3,z4,z762,z6])],[(0,[z1,z2,z3,z49,z330,z6]),(0,[z1,z456,z3,z4,z80,z6]),(0,[z1,z30,z3,z218,z5,z6])],[(0,[z1,z3,z4,z5,z127,z6]),(0,[z1,z864,z2,z4,z5,z6]),(0,[z1,z2,z865,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z244,z3,z4,z126,z6])],[(0,[z1,z2,z867,z4,z5,z6]),(0,[z270,z216,z3,z27,z5,z6]),(0,[z51,z2,z3,z4,z5,z751]),(0,[z868,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z869,z5,z6]),(0,[z56,z1,z2,z4,z126,z6]),(0,[z1,z2,z3,z870,z5,z6])],[(0,[z315,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z388]),(0,[z1,z2,z3,z5,z871,z6])],[(0,[z1,z3,z4,z80,z66,z6]),(0,[z1,z872,z3,z4,z5,z6]),(0,[z1,z779,z76,z4,z5,z6]),(0,[z1,z168,z3,z306,z5,z6])],[(0,[z1,z2,z197,z27,z5,z6]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z874,z3,z4,z5,z6]),(0,[z1,z2,z3,z875,z5,z6])]],
   [[(0,[z71,z3,z93,z184,z5,z6]),(0,[z185,z769,z2,z4,z5,z6]),(0,[z26,z1,z76,z4,z5,z6]),(0,[z162,z1,z3,z4,z5,z19]),(0,[z144,z1,z2,z3,z5,z114]),(0,[z1,z2,z876,z4,z5,z6])],[(0,[z22,z267,z1,z2,z3,z65])],[(0,[z1,z2,z3,z155,z66,z6]),(0,[z1,z515,z3,z15,z5,z6])],[(0,[z1,z2,z3,z877,z5,z6]),(0,[z1,z2,z878,z4,z5,z6]),(0,[z1,z2,z879,z4,z5,z6])],[(0,[z1,z2,z197,z4,z5,z6]),(0,[z1,z2,z197,z16,z5,z6])],[(0,[z1,z2,z3,z147,z5,z6]),(0,[z880,z1,z3,z4,z5,z6])],[(0,[z1,z881,z3,z4,z5,z6]),(0,[z2,z3,z753,z4,z5,z6]),(0,[z882,z2,z3,z4,z5,z6])],[(0,[z1,z220,z2,z8,z5,z6]),(0,[z1,z883,z2,z3,z5,z6]),(0,[z1,z128,z2,z4,z126,z6]),(0,[z1,z2,z3,z4,z884,z6]),(0,[z885,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z306,z91,z6])]],
   [[(0,[z92,z1,z2,z4,z273,z6])],[(0,[z1,z89,z2,z79,z5,z6]),(1,[z1,z779,z4,z5,z6]),(0,[z85,z1,z2,z4,z5,z43])],[(0,[z1,z2,z3,z4,z886,z6])],[(0,[z1,z2,z887,z4,z5,z6]),(0,[z71,z3,z93,z4,z5,z229]),(0,[z1,z3,z4,z5,z6,z888]),(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z2,z3,z890,z5,z6]),(0,[z891,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z892,z5,z6]),(0,[z1,z2,z3,z893,z5,z6]),(0,[z1,z2,z3,z894,z5,z6]),(0,[z1,z779,z3,z4,z5,z6]),(0,[z144,z1,z3,z4,z5,z19]),(0,[z1,z2,z895,z4,z5,z6])],[(0,[z71,z682,z3,z4,z5,z6]),(0,[z185,z89,z2,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z896]),(1,[z1,z3,z764,z5,z6]),(0,[z1,z897,z3,z4,z5,z6])],[(0,[z898,z1,z3,z4,z5,z6]),(0,[z406,z1,z3,z4,z18,z6]),(0,[z299,z2,z3,z4,z126,z6])],[(0,[z899,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z767])]],
   [[(0,[z1,z2,z3,z155,z5,z229]),(0,[z20,z1,z2,z197,z5,z6]),(0,[z900,z1,z2,z4,z5,z6]),(0,[z25,z23,z3,z4,z5,z6])],[(0,[z428,z2,z3,z4,z5,z52]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z20,z1,z2,z3,z42,z6]),(0,[z1,z3,z4,z794,z18,z6]),(0,[z1,z2,z97,z4,z5,z767])],[(0,[z1,z2,z3,z4,z902,z6]),(0,[z1,z2,z3,z903,z5,z6])],[(0,[z226,z3,z4,z5,z569,z6]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z1,z904,z3,z4,z5,z6]),(0,[z1,z2,z3,z905,z5,z6]),(0,[z1,z2,z3,z59,z5,z275]),(0,[z22,z1,z23,z3,z4,z65])],[(0,[z70,z1,z2,z4,z273,z6]),(0,[z906,z2,z3,z4,z5,z6])],[(0,[z1,z268,z76,z4,z5,z6]),(0,[z1,z362,z3,z48,z5,z6])],[(0,[z1,z907,z3,z4,z5,z6]),(0,[z246,z2,z3,z132,z5,z6])],[(0,[z1,z2,z268,z155,z5,z6]),(0,[z1,z2,z3,z908,z5,z6]),(0,[z1,z909,z2,z4,z5,z6]),(0,[z192,z2,z169,z4,z5,z6]),(0,[z1,z2,z3,z910,z5,z6])]],
   [[(0,[z1,z911,z2,z4,z5,z6]),(0,[z1,z912,z3,z4,z5,z6]),(0,[z1,z754,z2,z4,z5,z6]),(0,[z1,z2,z3,z913,z5,z6]),(0,[z1,z23,z115,z4,z5,z6])],[(0,[z1,z2,z3,z5,z6,z914]),(0,[z915,z2,z3,z4,z5,z6]),(0,[z916,z2,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z65]),(1,[z1,z2,z4,z5,z767])],[(0,[z25,z2,z3,z4,z5,z6]),(0,[z447,z1,z3,z4,z18,z6]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z315,z2,z3,z4,z126,z6])],[(0,[z1,z2,z3,z4,z5,z918]),(0,[z226,z1,z125,z4,z5,z6]),(0,[z270,z164,z2,z27,z5,z6]),(0,[z1,z2,z3,z59,z5,z389]),(0,[z1,z2,z3,z5,z6,z919])],[(0,[z1,z2,z920,z4,z5,z6])],[(0,[z103,z1,z3,z4,z5,z755]),(0,[z113,z1,z473,z3,z5,z114])],[(0,[z921,z2,z3,z4,z5,z6]),(0,[z922,z1,z3,z4,z5,z6])],[(0,[z923,z1,z2,z3,z5,z6]),(0,[z1,z473,z3,z5,z6,z114])]],
   [[(0,[z397,z1,z3,z4,z5,z19]),(0,[z1,z2,z3,z107,z49,z6]),(0,[z20,z1,z2,z3,z60,z6])],[(0,[z1,z2,z3,z924,z5,z6]),(0,[z1,z2,z3,z5,z6,z925]),(0,[z1,z244,z3,z4,z5,z6]),(0,[z1,z108,z3,z4,z5,z6]),(0,[z1,z2,z3,z926,z5,z6])],[(0,[z1,z927,z2,z4,z5,z6]),(0,[z270,z2,z3,z27,z5,z6]),(0,[z1,z2,z537,z4,z83,z6])],[(0,[z1,z3,z76,z4,z66,z6]),(0,[z25,z108,z3,z4,z5,z6])],[(0,[z25,z2,z115,z4,z5,z6])],[(0,[z1,z125,z4,z5,z18,z6])],[(0,[z1,z2,z3,z928,z5,z6]),(0,[z71,z1,z430,z4,z5,z6]),(0,[z1,z2,z3,z929,z5,z6])],[(0,[z1,z120,z4,z5,z6,z19]),(0,[z1,z2,z120,z4,z5,z10]),(0,[z1,z3,z861,z4,z5,z6]),(0,[z1,z2,z58,z117,z83,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z930]),(0,[z270,z2,z3,z453,z5,z6]),(0,[z1,z3,z48,z5,z6,z606])],[(0,[z1,z2,z196,z8,z5,z6]),(0,[z1,z931,z2,z4,z5,z6]),(0,[z113,z1,z2,z3,z5,z503])],[(0,[z1,z410,z3,z5,z6,z388]),(0,[z1,z2,z3,z5,z932,z6]),(0,[z1,z2,z3,z49,z6,z455]),(0,[z113,z1,z2,z3,z5,z752])],[(0,[z769,z2,z3,z4,z5,z6]),(0,[z933,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z934,z6]),(0,[z1,z935,z3,z4,z5,z6]),(0,[z1,z2,z3,z717,z60,z6]),(0,[z1,z108,z115,z4,z5,z6])],[(0,[z1,z2,z58,z4,z83,z6]),(0,[z1,z2,z3,z936,z5,z6]),(0,[z299,z168,z3,z4,z5,z6])],[(0,[z1,z30,z3,z155,z5,z6]),(0,[z1,z937,z3,z4,z5,z6]),(0,[z85,z299,z2,z4,z5,z98]),(0,[z1,z23,z188,z4,z5,z6])],[(0,[z1,z2,z938,z4,z5,z6]),(0,[z939,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z940,z5,z6]),(0,[z92,z1,z2,z4,z83,z6])]],
   [[(0,[z1,z2,z268,z4,z5,z10]),(0,[z1,z2,z941,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z596]),(0,[z1,z942,z3,z4,z5,z6]),(0,[z943,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z59,z5,z122]),(0,[z579,z2,z3,z4,z61,z6]),(0,[z1,z76,z4,z5,z554,z6]),(0,[z20,z1,z2,z3,z652,z6]),(0,[z2,z3,z4,z5,z6,z944]),(0,[z1,z30,z3,z4,z5,z46])],[(1,[z2,z3,z4,z762,z6]),(0,[z1,z2,z3,z49,z717,z6])],[(0,[z1,z2,z120,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z684,z76,z4,z5,z6]),(0,[z1,z2,z3,z947,z5,z6]),(0,[z1,z2,z743,z8,z5,z6]),(0,[z1,z2,z3,z948,z5,z6]),(0,[z1,z949,z3,z4,z5,z6])],[(0,[z34,z2,z3,z5,z675,z6]),(0,[z149,z189,z3,z4,z45,z6]),(0,[z1,z2,z3,z4,z215,z530])],[(0,[z1,z216,z3,z4,z5,z6]),(0,[z1,z2,z3,z950,z5,z6]),(0,[z1,z2,z3,z5,z752,z114])],[(0,[z1,z951,z3,z4,z5,z6]),(0,[z1,z2,z3,z952,z5,z6])],[(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z2,z3,z954,z5,z6]),(0,[z1,z2,z4,z5,z955,z6]),(0,[z1,z2,z956,z4,z5,z6]),(0,[z957,z2,z3,z4,z5,z6]),(0,[z1,z2,z188,z4,z5,z6]),(0,[z1,z2,z97,z4,z126,z6])]],
   [[(0,[z315,z168,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z275,z752])],[(0,[z958,z2,z3,z4,z5,z6]),(0,[z25,z2,z188,z4,z5,z6]),(0,[z1,z2,z3,z959,z5,z6])],[(0,[z1,z2,z3,z4,z960,z6]),(0,[z1,z2,z3,z961,z5,z6]),(0,[z0,z2,z3,z4,z5,z52]),(0,[z962,z2,z3,z4,z5,z6])],[(0,[z26,z1,z128,z4,z5,z6]),(0,[z963,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z964,z5,z6])],[(0,[z1,z2,z268,z4,z5,z6])],[(0,[z88,z1,z2,z221,z5,z6]),(0,[z2,z3,z4,z5,z751,z52]),(0,[z318,z2,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z1,z2,z7,z8,z5,z6])],[(0,[z1,z3,z4,z66,z6,z19]),(0,[z1,z2,z4,z5,z6,z966]),(0,[z1,z142,z3,z764,z5,z6]),(0,[z103,z1,z3,z4,z5,z19]),(1,[z1,z2,z3,z4,z780])],[(0,[z1,z2,z967,z4,z5,z6]),(0,[z1,z3,z4,z5,z968,z6]),(0,[z969,z2,z3,z4,z5,z6]),(0,[z1,z2,z743,z4,z5,z6])]],
   [[(0,[z970,z1,z3,z4,z5,z6]),(0,[z1,z168,z3,z147,z5,z6]),(0,[z1,z108,z188,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z780])],[(0,[z270,z411,z2,z3,z5,z6]),(0,[z1,z2,z971,z4,z5,z6]),(0,[z1,z2,z3,z972,z5,z6]),(0,[z22,z1,z108,z3,z4,z65]),(0,[z1,z2,z3,z4,z215,z81])],[(0,[z1,z2,z120,z4,z66,z6]),(0,[z1,z2,z3,z973,z5,z6]),(0,[z1,z2,z3,z974,z5,z6]),(0,[z1,z3,z764,z48,z5,z6]),(0,[z1,z473,z3,z59,z5,z6]),(0,[z113,z1,z2,z3,z5,z114])],[(0,[z1,z2,z4,z5,z86,z767])],[(0,[z1,z3,z15,z371,z5,z6]),(0,[z1,z2,z3,z975,z5,z6]),(0,[z85,z1,z2,z4,z126,z98])],[(0,[z1,z2,z120,z184,z5,z6]),(0,[z1,z976,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z403,z6])],[(0,[z88,z1,z2,z77,z5,z6]),(0,[z1,z2,z4,z83,z126,z6]),(0,[z1,z244,z3,z306,z5,z6])],[(0,[z1,z3,z4,z80,z313,z6]),(0,[z1,z2,z169,z79,z5,z6]),(0,[z977,z2,z3,z4,z5,z6])]],
   [[(0,[z92,z267,z1,z2,z5,z6])],[(0,[z1,z978,z3,z4,z5,z6]),(0,[z979,z2,z3,z4,z5,z6]),(0,[z2,z3,z980,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z2,z3,z147,z91,z6]),(0,[z1,z3,z4,z5,z6,z982])],[],[(0,[z1,z2,z268,z4,z66,z6]),(0,[z1,z3,z76,z4,z5,z10]),(0,[z1,z2,z983,z4,z5,z6]),(0,[z1,z12,z3,z4,z794,z6]),(0,[z1,z984,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z687,z76,z4,z5,z6]),(0,[z1,z2,z3,z986,z5,z6]),(0,[z1,z3,z150,z5,z6,z19]),(0,[z1,z2,z987,z4,z5,z6])],[(0,[z1,z988,z3,z4,z5,z6]),(0,[z1,z989,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z990,z6]),(0,[z1,z2,z3,z44,z5,z6]),(0,[z1,z2,z3,z4,z991,z6])],[(0,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z992]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z95,z3,z48,z5,z6]),(0,[z1,z2,z3,z4,z794,z6]),(0,[z1,z2,z3,z4,z81,z780])]],
   [[(0,[z1,z2,z120,z4,z5,z229]),(0,[z141,z1,z3,z764,z5,z6]),(0,[z1,z2,z3,z994,z5,z6]),(0,[z1,z2,z4,z5,z86,z84])],[(0,[z1,z2,z3,z995,z5,z6]),(0,[z1,z23,z3,z4,z5,z6]),(0,[z1,z996,z3,z4,z5,z6]),(0,[z1,z997,z3,z4,z5,z6])],[(0,[z1,z2,z41,z8,z5,z6])],[(0,[z1,z2,z3,z998,z5,z6]),(0,[z1,z2,z3,z4,z999,z6])],[(0,[z1,z164,z2,z4,z5,z6]),(0,[z113,z1,z257,z3,z5,z114])],[(0,[z1,z2,z3,z1000,z5,z6]),(0,[z1,z2,z1001,z4,z5,z6])],[(0,[z1,z2,z3,z1002,z5,z6]),(0,[z1,z2,z3,z117,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1003]),(0,[z1,z2,z3,z1004,z5,z6]),(0,[z1005,z2,z3,z4,z5,z6])]],
   [[(0,[z149,z2,z3,z4,z762,z6]),(0,[z1,z2,z430,z4,z5,z6]),(0,[z1,z2,z3,z4,z1006,z6]),(1,[z1,z3,z4,z794,z6]),(0,[z1,z3,z4,z5,z6,z755]),(0,[z267,z1,z2,z5,z6,z334])],[(0,[z189,z1,z3,z4,z80,z6]),(0,[z1,z427,z3,z48,z5,z6]),(0,[z299,z2,z3,z306,z5,z6]),(0,[z85,z1,z244,z4,z5,z98]),(0,[z20,z1,z2,z3,z717,z6])],[(0,[z1,z2,z3,z1007,z5,z6]),(0,[z1,z1008,z3,z4,z5,z6]),(0,[z1,z279,z2,z3,z5,z6]),(0,[z149,z3,z4,z127,z45,z6]),(0,[z1,z2,z58,z294,z83,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z71,z3,z93,z4,z423,z6]),(0,[z1,z2,z3,z1009,z5,z6]),(0,[z85,z1,z168,z4,z5,z98])],[(0,[z380,z1,z2,z4,z5,z98])],[(0,[z1,z2,z188,z4,z215,z6]),(0,[z1,z2,z3,z4,z5,z780])],[(0,[z1,z2,z3,z4,z66,z10]),(0,[z2,z3,z861,z4,z5,z6]),(0,[z1,z308,z76,z4,z5,z6]),(0,[z1,z2,z3,z5,z717,z6])],[(0,[z1,z3,z247,z4,z5,z6]),(0,[z448,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z1010,z5,z6])]],
   [[(0,[z1,z2,z3,z155,z423,z6]),(0,[z1,z2,z3,z1011,z5,z6]),(0,[z34,z2,z3,z5,z6,z629]),(0,[z1,z12,z3,z4,z80,z6])],[(0,[z1,z2,z3,z184,z5,z10]),(0,[z1,z30,z3,z4,z66,z6]),(0,[z1,z2,z3,z342,z5,z6]),(1,[z2,z3,z753,z5,z6]),(0,[z2,z3,z4,z5,z6,z1012]),(0,[z1013,z2,z3,z4,z5,z6])],[(0,[z71,z3,z546,z4,z5,z6]),(0,[z1,z2,z1014,z3,z5,z6])],[(0,[z1,z3,z4,z5,z229,z19]),(0,[z1,z2,z1015,z4,z5,z6]),(0,[z1,z2,z3,z1016,z5,z6])],[(0,[z11,z1,z268,z4,z5,z6]),(0,[z1,z2,z3,z143,z5,z6]),(0,[z1,z2,z3,z4,z1017,z6])],[(0,[z38,z1,z125,z4,z18,z6]),(0,[z1,z2,z115,z4,z5,z6]),(0,[z1,z2,z4,z5,z710,z6]),(0,[z1018,z2,z3,z4,z5,z6]),(0,[z315,z2,z3,z306,z5,z6]),(0,[z1,z244,z3,z4,z91,z6])],[],[(0,[z1,z2,z3,z1019,z5,z6]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z1021,z3,z4,z5,z6]),(0,[z1,z410,z3,z4,z5,z46]),(0,[z1,z1022,z3,z4,z5,z6]),(0,[z1,z2,z3,z59,z5,z401])]],
   [[(0,[z1,z1023,z2,z3,z5,z6]),(0,[z103,z1,z3,z150,z5,z19]),(0,[z1,z2,z3,z104,z49,z6]),(0,[z1,z2,z1024,z4,z5,z6])],[(0,[z1,z2,z1025,z4,z5,z6]),(0,[z578,z2,z169,z4,z5,z6]),(0,[z1026,z2,z3,z4,z5,z6]),(0,[z1,z2,z58,z4,z249,z6]),(0,[z1,z1027,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z66,z6]),(0,[z1,z2,z76,z4,z126,z6]),(0,[z85,z1,z2,z4,z5,z98]),(0,[z1,z23,z3,z323,z5,z6])],[(0,[z1,z2,z4,z1028,z5,z6])],[(0,[z1,z2,z3,z1029,z5,z6]),(0,[z1,z2,z3,z4,z6,z780])],[(0,[z1,z2,z3,z184,z5,z6]),(0,[z1,z30,z120,z4,z5,z6]),(0,[z1,z2,z1030,z4,z5,z6]),(0,[z1,z2,z3,z1031,z5,z6])],[(0,[z1,z2,z3,z1032,z5,z6]),(0,[z1,z2,z3,z1033,z5,z6]),(0,[z1,z2,z137,z4,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1034])]],
   [[(0,[z1,z142,z3,z155,z5,z6]),(0,[z1,z2,z3,z4,z1035,z6]),(0,[z1,z2,z3,z1036,z5,z6]),(0,[z56,z1,z206,z4,z273,z6])],[(0,[z1037,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1038,z6]),(0,[z1,z2,z3,z1039,z5,z6]),(0,[z1,z2,z3,z4,z1040,z6]),(0,[z1,z57,z3,z4,z5,z6]),(0,[z1,z30,z430,z4,z5,z46]),(1,[z1,z2,z4,z710,z6]),(0,[z56,z1,z2,z4,z710,z6]),(0,[z1,z1041,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z223])],[(0,[z141,z1,z3,z213,z5,z6])],[(0,[z319,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z1042,z5,z6])],[(0,[z1,z2,z1043,z4,z5,z6]),(0,[z438,z1,z128,z4,z5,z6]),(0,[z92,z1,z2,z4,z5,z6]),(0,[z1,z2,z1044,z4,z5,z6])],[(0,[z71,z1,z125,z4,z5,z6])],[(0,[z520,z1,z3,z4,z5,z19]),(0,[z1,z2,z3,z1045,z5,z6]),(0,[z25,z2,z3,z323,z5,z6])],[(0,[z11,z1,z3,z4,z5,z10]),(0,[z1046,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z229]),(0,[z1,z769,z2,z4,z5,z6]),(0,[z1,z2,z3,z1047,z5,z6]),(0,[z1,z2,z3,z1048,z5,z6]),(0,[z1,z410,z983,z4,z5,z6]),(0,[z103,z1,z3,z205,z5,z19]),(0,[z1,z2,z3,z4,z126,z6]),(0,[z1,z2,z4,z83,z710,z6]),(0,[z299,z2,z3,z4,z91,z6])],[(0,[z72,z1,z3,z15,z5,z6]),(0,[z189,z1,z971,z4,z5,z6]),(0,[z1,z1049,z3,z4,z5,z6]),(0,[z1,z1050,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z1052,z3,z4,z5,z6]),(0,[z1053,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1054])],[(0,[z1,z3,z4,z5,z6,z1055]),(0,[z51,z2,z3,z4,z5,z52]),(0,[z1,z1056,z3,z4,z5,z6])],[(0,[z1,z2,z3,z184,z66,z6]),(0,[z1,z142,z3,z48,z5,z6]),(0,[z1,z30,z3,z4,z5,z348]),(0,[z1,z30,z3,z150,z5,z6]),(0,[z246,z23,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z1058,z4,z5,z6]),(0,[z88,z1,z2,z743,z5,z6]),(0,[z1,z108,z3,z323,z5,z6])],[(0,[z1,z2,z3,z1059,z5,z6]),(0,[z189,z1,z3,z4,z18,z6]),(0,[z1,z2,z3,z4,z5,z1060]),(0,[z1,z2,z3,z4,z5,z1061]),(0,[z1,z2,z115,z323,z5,z6])],[(0,[z1062,z2,z3,z4,z5,z6])]],
   [[(0,[z240,z2,z169,z4,z5,z6]),(0,[z1,z30,z3,z4,z5,z462])],[(0,[z109,z2,z169,z4,z5,z6]),(0,[z447,z1,z2,z4,z273,z6]),(0,[z1,z2,z4,z5,z6,z334]),(0,[z1063,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z717,z6])],[(0,[z1,z3,z1064,z4,z5,z6]),(0,[z1,z2,z1065,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1066]),(0,[z92,z1,z735,z4,z5,z6])],[(0,[z1,z2,z1067,z4,z5,z6]),(0,[z1,z2,z1068,z4,z5,z6]),(0,[z1,z1069,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1070]),(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z2,z703,z8,z5,z6]),(0,[z315,z2,z3,z4,z91,z6])],[(0,[z1,z2,z1072,z4,z5,z6]),(0,[z1073,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z751]),(0,[z1,z2,z3,z150,z5,z6])],[(0,[z71,z3,z93,z155,z5,z6]),(0,[z1,z2,z3,z4,z1074,z6]),(0,[z189,z1,z3,z44,z5,z6]),(0,[z1,z2,z1075,z4,z5,z6]),(0,[z214,z1,z3,z15,z5,z6]),(0,[z1,z2,z1076,z4,z5,z6])],[(0,[z1,z2,z3,z4,z66,z229]),(0,[z1,z3,z5,z6,z73,z388]),(0,[z1,z146,z76,z4,z5,z6])]],
   [[(0,[z1,z410,z3,z4,z5,z6]),(0,[z3,z861,z93,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1077]),(0,[z1,z168,z76,z4,z5,z6]),(0,[z1,z244,z3,z147,z5,z6]),(0,[z1,z1078,z3,z4,z5,z6]),(0,[z1,z2,z188,z4,z6,z65])],[(0,[z1,z3,z4,z5,z133,z19]),(0,[z1,z2,z3,z1079,z5,z6]),(0,[z1,z2,z197,z49,z5,z6]),(0,[z1,z2,z3,z4,z5,z1080]),(0,[z1,z2,z3,z294,z5,z6]),(0,[z1,z2,z3,z4,z1081,z6])],[(0,[z1,z2,z3,z4,z1082,z6]),(0,[z1,z2,z3,z184,z5,z229]),(0,[z109,z2,z169,z143,z5,z6]),(0,[z1,z3,z15,z764,z5,z6]),(0,[z1,z2,z487,z8,z5,z6]),(0,[z1,z2,z4,z710,z273,z6])],[(0,[z1,z1083,z2,z4,z5,z6]),(0,[z1,z3,z1084,z4,z5,z6])],[(0,[z227,z2,z3,z4,z633,z6]),(0,[z1,z1085,z3,z4,z5,z6])],[(0,[z34,z2,z3,z753,z5,z6]),(0,[z1,z123,z2,z77,z5,z6]),(0,[z1,z2,z3,z1086,z5,z6]),(1,[z1,z2,z3,z717,z6])],[(0,[z1,z2,z3,z4,z1087,z6]),(0,[z1,z2,z3,z1088,z5,z6]),(0,[z1,z410,z3,z342,z5,z6]),(0,[z1,z128,z779,z4,z5,z6])],[(0,[z85,z1,z2,z306,z5,z98]),(0,[z246,z108,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z46,z755]),(0,[z1089,z2,z3,z4,z5,z6]),(0,[z1,z1090,z3,z4,z5,z6]),(0,[z246,z2,z115,z4,z5,z6])],[(0,[z1,z2,z268,z184,z5,z6]),(0,[z1,z1091,z3,z4,z5,z6]),(0,[z92,z1,z2,z4,z126,z6])],[(0,[z11,z1,z3,z4,z66,z6]),(0,[z185,z524,z2,z4,z5,z6]),(0,[z34,z2,z3,z16,z5,z6]),(0,[z1,z2,z1092,z4,z5,z6]),(0,[z227,z2,z3,z4,z61,z6]),(0,[z1,z2,z3,z1093,z5,z6])],[(0,[z189,z1,z3,z4,z5,z6]),(0,[z769,z2,z169,z4,z5,z6]),(1,[z1,z2,z743,z5,z6]),(0,[z1,z2,z188,z323,z5,z6])],[(0,[z1,z1094,z3,z4,z5,z6]),(0,[z1095,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z755,z19]),(0,[z1,z1096,z3,z4,z5,z6])],[(0,[z68,z2,z3,z4,z5,z575]),(0,[z1,z2,z1097,z4,z5,z6]),(0,[z2,z3,z16,z753,z5,z6]),(0,[z1,z279,z3,z5,z127,z6]),(0,[z1,z779,z129,z4,z5,z6]),(0,[z1,z2,z3,z205,z5,z6]),(0,[z1,z1098,z2,z4,z5,z6])],[(0,[z1,z2,z3,z1099,z5,z6]),(0,[z1,z2,z3,z4,z1100,z6]),(0,[z1,z168,z3,z4,z5,z6]),(0,[z1,z2,z3,z1101,z5,z6])],[(0,[z1,z206,z3,z4,z5,z6]),(0,[z1,z12,z430,z4,z5,z6])]],
   [[(0,[z643,z89,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1102,z6])],[(0,[z1,z1103,z3,z4,z5,z6]),(0,[z1,z2,z3,z1104,z5,z6]),(0,[z1105,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1106,z4,z5,z6]),(0,[z1,z2,z1107,z4,z5,z6]),(0,[z499,z2,z3,z4,z45,z6]),(0,[z1,z2,z1108,z4,z5,z6]),(0,[z299,z2,z3,z147,z5,z6]),(0,[z22,z246,z2,z3,z4,z65])],[(0,[z71,z120,z93,z4,z5,z6]),(0,[z1,z2,z268,z4,z5,z229]),(0,[z38,z1,z3,z4,z794,z6])],[(0,[z1,z2,z3,z4,z1109,z6]),(0,[z1110,z1,z2,z3,z4,z6]),(0,[z1,z12,z3,z4,z696,z6]),(0,[z11,z1,z574,z4,z5,z6]),(0,[z1,z2,z3,z306,z126,z6])],[(0,[z1,z2,z3,z1111,z5,z6]),(0,[z1112,z2,z3,z4,z5,z6]),(0,[z1,z3,z764,z4,z5,z6]),(0,[z1,z23,z3,z132,z5,z6])],[(0,[z1,z2,z3,z4,z91,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z120,z4,z423,z6]),(0,[z1,z3,z4,z5,z6,z1114]),(0,[z1,z2,z3,z1115,z5,z6]),(0,[z1,z2,z3,z4,z5,z1116]),(0,[z1,z29,z168,z4,z5,z6]),(0,[z1,z3,z4,z5,z1117,z6])],[(0,[z1,z3,z218,z5,z6,z19]),(0,[z1,z1118,z3,z4,z5,z6])],[(0,[z189,z1,z3,z4,z66,z6]),(0,[z1,z2,z3,z4,z1119,z6]),(0,[z525,z1,z2,z3,z5,z114])],[(0,[z1,z2,z3,z1120,z5,z6]),(0,[z1,z2,z3,z4,z1121,z6]),(0,[z1,z2,z1122,z4,z5,z6]),(0,[z1123,z2,z3,z4,z5,z6]),(0,[z1,z12,z3,z4,z597,z6])],[(0,[z1,z2,z1124,z4,z5,z6]),(0,[z1125,z2,z3,z4,z5,z6])],[(0,[z1,z410,z3,z4,z5,z229]),(0,[z185,z26,z89,z4,z5,z6]),(0,[z85,z1,z2,z4,z5,z513]),(0,[z1,z3,z1126,z4,z5,z6]),(0,[z246,z2,z188,z4,z5,z6])],[(0,[z1,z434,z3,z4,z5,z6]),(0,[z1,z1127,z3,z4,z5,z6]),(0,[z1,z2,z3,z1128,z5,z6])],[(0,[z1,z430,z4,z5,z18,z6]),(0,[z1,z1129,z3,z4,z5,z6]),(0,[z315,z2,z3,z147,z5,z6]),(0,[z22,z1,z2,z3,z323,z65])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1088)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 544] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 150).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 150).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [150, 106] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_37851

theorem PEqualNP.Outside.L_meta_37851 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4243388552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4243388552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37851.solve