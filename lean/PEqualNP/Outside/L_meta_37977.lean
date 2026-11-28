import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37977

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
  Nat.testBit (4277075688 * 2 ^ 32 + 4277074088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x480040c282048964#64 ++ 0x112001030a081225#64 ++ 0xf414c1c7864c9ffe#64 ++ 0xf7d053071e19327f#64 : BitVec 256),
   (0x3001061908931480#64 ++ 0x00c0041864224c52#64 ++ 0xef2b0e3999b31cfd#64 ++ 0xefbcac38e666cc73#64 : BitVec 256),
   (0x204c102c21c12609#64 ++ 0x20813040b0870498#64 ++ 0x5ecc303e61c3e72b#64 ++ 0xdd7b30c0f9870f9c#64 : BitVec 256),
   (0x40b02b405e02d832#64 ++ 0x4502c0ad01780b60#64 ++ 0x3ff03fc07e03f827#64 ++ 0xbcffc0ff01f80fe0#64 : BitVec 256),
   (0x80fe800075680003#64 ++ 0x8603fa0001d5a000#64 ++ 0xfcffc0007ffc001f#64 ++ 0x83f3ff0001fff000#64 : BitVec 256),
   (0x01fffdb780000003#64 ++ 0xf807fff6de000000#64 ++ 0xfdffffff80000000#64 ++ 0x7ff7fffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [7, 9]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80000000 0x7ff7fffffe000000

def z1 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e61c3e72b 0xdd7b30c0f9870f9c

def z2 : W := mkw 0x214fd4bfa1c12609 0xb8853f52fe870498 0xc00fc03f81c00708 0x43003f00fe07001c

def z3 : W := mkw 0x21fffdbfa1c1260b 0xf887fff6fe870498 0xffffffffe1c3e72b 0xffffffffff870f9c

def z4 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3999b31cfd 0xefbcac38e666cc73

def z5 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c7864c9ffe 0xf7d053071e19327f

def z6 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc001f 0x83f3ff0001fff000

def z7 : W := mkw 0x014ed0a680000001 0xb8053b429a000000 0x0004c00600000000 0x0000130018000000

def z8 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e03f827 0xbcffc0ff01f80fe0

def z9 : W := mkw 0x30ff861908931483 0x80c3fe1864224c52 0xffffce3999b31cfd 0xefffff38e666cc73

def z10 : W := mkw 0x81fef9a6f5680003 0xfe07fbe69bd5a000 0x10d4f1c6664c0002 0x104353c719993000

def z11 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffffffc001f 0xfff7fffffffff000

def z12 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xa033c0001e3c0014 0x0280cf000078f000

def z13 : W := mkw 0x004c102421402209 0x2001304090850088 0x10c430066040e302 0x104310c01981038c

def z14 : W := mkw 0xa0fe902c75e9260b 0xa683fa40b1d7a498 0xfefff03e7fffe73f 0xdffbffc0f9ffff9c

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc3fc0001ffc001f 0x83f0ff00007ff000

def z16 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0xff3fcfff9fff9fff 0xfffcff3ffe7ffe7f

def z17 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x13d03fc06603f822 0x3c4f40ff01980fe0

def z18 : W := mkw 0x00b0000054000002 0x0402c00001500000 0x3cf000007e000007 0x80f3c00001f80000

def z19 : W := mkw 0x804e800021680001 0x82013a000085a000 0xc00fc00001fc0018 0x03003f000007f000

def z20 : W := mkw 0x0000020008021000 0x0000000800200840 0xef2b0e0019b3183d 0xafbcac380066cc60

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c000064c001e 0x83d0530000193000

def z22 : W := mkw 0xc8fec0c2f76c8967 0x9723fb030bddb225 0xfcffc1c7fffc9fff 0xf7f3ff071ffff27f

def z23 : W := mkw 0x004c000000000001 0x0001300000000000 0x5ccc000000000000 0x0173300000000000

def z24 : W := mkw 0x21017dbf80812608 0x788405f6fe020498 0x03003fff8003e720 0x7c0c00fffe000f9c

def z25 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x2fe03e0078037825 0xacbf80f801e00de0

def z26 : W := mkw 0x004c102400000001 0x2001304090000000 0x400c003e00000000 0x41003000f8000000

def z27 : W := mkw 0x3000020808931480 0x00c0000820224c52 0x0200000019b31cfd 0x800800000066cc73

def z28 : W := mkw 0x4800004002048964 0x0120000100081225 0x00000000064c9ffe 0x800000000019327f

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000001cfc 0x8000000000000073

def z30 : W := mkw 0xc0feab407f6ad833 0xc703faad01fdab60 0xffffffc07ffff83f 0xbfffffff01ffffe0

def z31 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xb1f7ffc780000000 0x32c7dfff1e000000

def z32 : W := mkw 0x2000000800810400 0x0080000020020410 0xee2b003819b3043d 0xcfb8ac00e066cc10

def z33 : W := mkw 0x01017db780000000 0x780405f6de000000 0x01003fff80000000 0x7c0400fffe000000

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b000019b0001d 0x83b0ac000066c000

def z35 : W := mkw 0x480040c282048964 0x112001030a081225 0x1014c1c7864c9fe2 0x744053071e19327f

def z36 : W := mkw 0x88fec082f56c0147 0x9623fb020bd5b005 0xfcffc007fffc07df 0xc3f3ff001ffff01f

def z37 : W := mkw 0x48b069c282048966 0x5122c1a70a081225 0xfdf4ffc7864c9ffe 0xfff7d3ff1e19327f

def z38 : W := mkw 0x0001041100000000 0x0000041044000000 0xed2b0e3999b0001d 0xefb4ac38e666c000

def z39 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x0be03e0078036001 0x082f80f801e00d80

def z40 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x21300fc01e001804 0x2084c03f00780060

def z41 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x10d031c06600e002 0x104340c701980380

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ec030006003e023 0x9c7b00c001800f80

def z43 : W := mkw 0xa0fe902c75e9260b 0xa683fa40b1d7a498 0xfcffc03e7ffc071f 0xc3f3ff00f9fff01c

def z44 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x0200303e0003e720 0x5c0800c0f8000f9c

def z45 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x0ac8303861836001 0x082b20c0e1860d80

def z46 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0x10d4f006664ce302 0x104353c01999338c

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0xe40000000000001c 0x8390000000000000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x5ec430066043e72b 0xdd7b10c019810f9c

def z49 : W := mkw 0xc1fffff7ff6ad833 0xff07ffffdffdab60 0xfffffffffffff83f 0xffffffffffffffe0

def z50 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc00000000000 0x03f3ff0000000000

def z51 : W := mkw 0x010154b780000000 0x38040552de000000 0x0000003f80000000 0x40000000fe000000

def z52 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x400c003e01c00708 0x41003000f807001c

def z53 : W := mkw 0x40b02b400a02d832 0x4102c0ad00280b60 0x3ff03fc00003f820 0x3cffc0ff00000fe0

def z54 : W := mkw 0x4000004002008820 0x0100000100080220 0x341001c006009826 0xb4d0400700180260

def z55 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x08eb000079b00001 0x0023ac0001e6c000

def z56 : W := mkw 0x0000408280000000 0x100001020a000000 0xa010c1c180000000 0x2280430706000000

def z57 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x12d031c07e03f827 0x904b40c701f80fe0

def z58 : W := mkw 0x2000000821c12608 0x0080000020870498 0x4e08003861c3e72b 0xcd382000e1870f9c

def z59 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xffffffffe003e023 0xffffffffff800f80

def z60 : W := mkw 0x31fffdbf80910483 0xf8c7fff6fe024412 0xfdffffff81b004d8 0x7ff7fffffe06c013

def z61 : W := mkw 0x804e800021680001 0x82013a000085a000 0xec2fc00019fc001d 0x83b0bf000067f000

def z62 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1acc303e61c3e303 0x186b30c0f9870f8c

def z63 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x0b2b0e3819b30001 0x082cac38e066cc00

def z64 : W := mkw 0x480040c282048964 0x112001030a081225 0x1014c1c6064c8302 0x104053071819320c

def z65 : W := mkw 0xb0ff86197dfb1483 0x86c3fe1865f7ec52 0xffffce39ffff1cff 0xefffff38e7fffc73

def z66 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0xf714cfff864f9ffe 0xffdc533ffe193e7f

def z67 : W := mkw 0x1001061108121080 0x0040041844204842 0xa1230e01983018d4 0x22848c380660c063

def z68 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x420c003e61c3e72b 0xc1083000f9870f9c

def z69 : W := mkw 0x480040c282048964 0x112001030a081225 0x000001c780009fe0 0x740000071e00027f

def z70 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x0200303800036000 0x080800c0e0000d80

def z71 : W := mkw 0x0000408280000000 0x100001020a000000 0xf414c1c7864c001e 0xf7d053071e193000

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0xa023000018300014 0x02808c000060c000

def z73 : W := mkw 0x00fea90000000003 0xc003faa400000000 0xfdffffc000000000 0x3ff7ffff00000000

def z74 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xa133cfc180000000 0x2284cf3f06000000

def z75 : W := mkw 0x00fe800021400003 0x8003fa0000850000 0xfcffc00061c0000b 0x83f3ff0001870000

def z76 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ac0300060036001 0x082b00c001800d80

def z77 : W := mkw 0x014d7db780000001 0x780535f6de000000 0x5dcc3fff80000000 0x7d7730fffe000000

def z78 : W := mkw 0x0800408280040144 0x102001020a001005 0x0004c006004c0300 0x000013001801300c

def z79 : W := mkw 0x204c000821c10401 0x0081300020870410 0x5ecc003861c3042b 0xcd7b3000e1870c10

def z80 : W := mkw 0x81fffdb7a1680003 0xfa07fff6de85a000 0xfdffffff81fc0018 0x7ff7fffffe07f000

def z81 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffff9b00001 0x7ff7ffffffe6c000

def z82 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0x08eb000000000000 0x0023ac0000000000

def z83 : W := mkw 0x580146d38a1699e4 0x1160051b4e285a67 0xf537cfc79e7c9ffe 0xf7d4df3f1e79f27f

def z84 : W := mkw 0x480040c282048964 0x112001030a081225 0xa010c1c1860c18d4 0x2280430706183063

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x3410000006000006 0x80d0400000180000

def z86 : W := mkw 0x284c50aea1c5274d 0x30a13142ba87149d 0xc00cc03f81cc07d8 0x43003300fe07301f

def z87 : W := mkw 0x0001041100000000 0x0000041044000000 0x01000e3980000000 0x6c040038e6000000

def z88 : W := mkw 0x014fd4b780000001 0xb8053f52de000000 0xdccff03f80000000 0x5f733fc0fe000000

def z89 : W := mkw 0x304d163d08931481 0x20c13458f4224c52 0xffef3e3f99b31cfd 0xffffbcf8fe66cc73

def z90 : W := mkw 0x31ffffbf88931483 0xf8c7fffefe224c52 0xffffffff99b30001 0x7ffffffffe66cc00

def z91 : W := mkw 0x01fef9a6a140220b 0xf807fbe69a850088 0x10d4f1c66040e302 0x104353c71981038c

def z92 : W := mkw 0x70b12f595e93dcb2 0x45c2c4bd657a4f72 0xfffb3ff9ffb3fcff 0xffffecffe7fecff3

def z93 : W := mkw 0xc80040c2f76c8964 0x172001030bddb225 0xf414c1c7fffc9fff 0xf7d053071ffff27f

def z94 : W := mkw 0x3001163d08933688 0x20c00458f4224cda 0x03003e3f8003ffe0 0x7c0c00f8fe000fff

def z95 : W := mkw 0xa0fe902c75e9260b 0xa683fa40b1d7a498 0x5edcf03e67cfe72b 0xdd7b73c0f99f3f9c

def z96 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff4ffc07e4ff83f 0xbfffd3ff01f93fe0

def z97 : W := mkw 0x01fef9a680000003 0xf807fbe69a000000 0x10d4f1c600000000 0x104353c718000000

def z98 : W := mkw 0x780042ca8a979de4 0x11e0010b2a2a5e77 0xf614c1c79fff9fff 0xf7d853071e7ffe7f

def z99 : W := mkw 0x304d163d29d33689 0x20c13458f4a74cda 0xffef3e3ff9f3ffff 0xffffbcf8ffe7cfff

def z100 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xf437c0001e7c001e 0x83d0df000079f000

def z101 : W := mkw 0x48b06bc2de06d976 0x5522c1af0b781b65 0xfff4ffc7fe4fffff 0xffffd3ff1ff93fff

def z102 : W := mkw 0x4800004002048964 0x0120000100081225 0x341001c0064c9ffe 0xb4d040070019327f

def z103 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80001cfc 0xfff7fffffe000073

def z104 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x3dfb3ff800000000 0x3cf7ecffe0000000

def z105 : W := mkw 0x31ffffbf88931483 0xf8c7fffefe224c52 0xffffffff99b31cfd 0xfffffffffe66cc73

def z106 : W := mkw 0x400002405e02d830 0x0500000901780b60 0x020000007e03f827 0x8008000001f80fe0

def z107 : W := mkw 0x00b0000000000002 0x0002c00000000000 0x3cf0000000000000 0x00f3c00000000000

def z108 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xed3bcff980000000 0x6fb4ef3fe6000000

def z109 : W := mkw 0x780002480a979de4 0x01e00009202a5e77 0x020000001fff9fff 0x80080000007ffe7f

def z110 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xffeb3e39f9b3fcff 0xffffacf8e7e6cff3

def z111 : W := mkw 0xa04e902c21e92609 0xa2813a40b087a498 0xc00fc03e01fc0718 0x43003f00f807f01c

def z112 : W := mkw 0x780144db82958de4 0x11e005136e0a5637 0xf41fc1ff87fc9ffe 0xf7d07f07fe1ff27f

def z113 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c7860c18d4 0x77d053071e183063

def z114 : W := mkw 0x484c50e6a344ab6d 0x312131439a8d12ad 0x10d4f1c6664ce302 0x104353c71999338c

def z115 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0xc10fffff80000000 0x7f043ffffe000000

def z116 : W := mkw 0x0000408280000000 0x100001020a000000 0xc004c00780000000 0x430013001e000000

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x540400060040872a 0xd55010001801021c

def z118 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xa3230e3998331cf4 0x6e8c8c38e660cc73

def z119 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x10d4c000664c0002 0x0043530001993000

def z120 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x0be03fc07803f821 0x3c2f80ff01e00fe0

def z121 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x5604303e0043e72a 0xdd5810c0f8010f9c

def z122 : W := mkw 0x0001041100000000 0x0000041044000000 0xed2b0e3980000000 0x6fb4ac38e6000000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z124 : W := mkw 0x01fef9a680000003 0xf807fbe69a000000 0x5cdcf1fe00000000 0x5d7373c7f8000000

def z125 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x11d4ffff80000000 0x7c4753fffe000000

def z126 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303861c3600b 0x897b30c0e1870d80

def z127 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc000664c0002 0x03f3ff0001993000

def z128 : W := mkw 0x004c102400000001 0x2001304090000000 0x5ecc303e6003e023 0xdd7b30c0f9800f80

def z129 : W := mkw 0x014f943500000001 0xa8053e50d4000000 0x000b003800000000 0x00002c00e0000000

def z130 : W := mkw 0x0000408280000000 0x100001020a000000 0xf414c1c780000000 0x77d053071e000000

def z131 : W := mkw 0x3000020808931480 0x00c0000820224c52 0x2f200e0019b31cfd 0xacbc80380066cc73

def z132 : W := mkw 0xc0b02b407f6ad832 0x4702c0ad01fdab60 0x3ff03fc07ffff83f 0xbcffc0ff01ffffe0

def z133 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x31f03fc07e00f806 0x30c7c0ff01f803e0

def z134 : W := mkw 0x3001041900910480 0x00c0041064024412 0xc00b003981b004d8 0x43002c00e606c013

def z135 : W := mkw 0x304d143d21d12689 0x20c13450f487449a 0xc00f003f81f007d8 0x43003c00fe07c01f

def z136 : W := mkw 0x00b0000054000002 0x0402c00001500000 0xfcf4c0007e4c001f 0x83f3d30001f93000

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400000180001cfc 0xe790000006000073

def z138 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x19fffffe00000000 0x1867fffff8000000

def z139 : W := mkw 0x60fc3b6c7fc3fe3b 0x6583f0edb1ff0ff8 0x7ffc3ffe7fc3ff2f 0xfdfff0fff9ff0ffc

def z140 : W := mkw 0x684c50eea3c5af6d 0x31a13143ba8f16bd 0xfedcf1ffe7cfffff 0xfffb73c7ff9f3fff

def z141 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3df00fc07e001807 0xa0f7c03f01f80060

def z142 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc001fffc1cff 0xe7f3ff0007fff073

def z143 : W := mkw 0x80feab007d6a5013 0xc603faac01f5a940 0x0beb3e0079b36001 0x082facf801e6cd80

def z144 : W := mkw 0x0000000021400000 0x0000000000850000 0x0000000061c0000b 0x8000000001870000

def z145 : W := mkw 0xa0fe800875e9260b 0x8683fa0021d7a498 0xfeffc0007fffe73f 0x83fbff0001ffff9c

def z146 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x3df03fc000000000 0x3cf7c0ff00000000

def z147 : W := mkw 0x49fffdf782048967 0xf927fff7de081225 0xfdffffff864c9ffe 0xfff7fffffe19327f

def z148 : W := mkw 0x80fe800054280003 0x8603fa000150a000 0xfcffc0001e3c0014 0x03f3ff000078f000

def z149 : W := mkw 0x804e800075680001 0x86013a0001d5a000 0xc00fc0007ffc001f 0x83003f0001fff000

def z150 : W := mkw 0x4000004002008820 0x0100000100080220 0x201001c006001804 0x2080400700180060

def z151 : W := mkw 0xa000000875e92608 0x0680000021d7a498 0x020000007fffe73f 0x8008000001ffff9c

def z152 : W := mkw 0x004c102400000001 0x2001304090000000 0x5ccc303e00000000 0x5d7330c0f8000000

def z153 : W := mkw 0x480040c282048964 0x112001030a081225 0x000001c1800018c0 0x2000000706000063

def z154 : W := mkw 0xc0b2ab405e2ad832 0xc702caad0178ab60 0xa133cfc01e3c1814 0x2284cf3f0078f060

def z155 : W := mkw 0x204d143d21c12609 0x20813450f4870498 0xffef3e3fe1c3e72b 0xffffbcf8ff870f9c

def z156 : W := mkw 0x0800408280040144 0x102001020a001005 0x8000c001800c00d0 0x0200030006003003

def z157 : W := mkw 0xa04e902c21e92609 0xa2813a40b087a498 0xdecff03e61ffe73b 0xdf7b3fc0f987ff9c

def z158 : W := mkw 0xb04f861929fb1481 0x82c13e1864a7ec52 0xef2fce3999ff1cfd 0xefbcbf38e667fc73

def z159 : W := mkw 0xc0feab407f6ad833 0xc703faad01fdab60 0x3ffb3fc07fb3f827 0xbcffecff01fecfe0

def z160 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xa8fbc0007fbc0015 0x02a3ef0001fef000

def z161 : W := mkw 0xa0fe902c75e9260b 0xa683fa40b1d7a498 0xfefff0387fff601f 0x8bfbffc0e1fffd80

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c006064c873e 0xd7d053001819321c

def z163 : W := mkw 0x014fd4b780000001 0xb8053f52de000000 0xc00fc03f80000000 0x43003f00fe000000

def z164 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x5def3e3e00000000 0x5d77bcf8f8000000

def z165 : W := mkw 0x00b12d1100000002 0x4002c4b444000000 0xfdfb3ff980000000 0x7ff7ecffe6000000

def z166 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xa9fbfff980000000 0x2aa7efffe6000000

def z167 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfdfffffffe000007 0xfff7fffffff80000

def z168 : W := mkw 0x40feab405e02d833 0xc503faad01780b60 0xffffffc07e03f827 0xbfffffff01f80fe0

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000180001ce0 0x6400000006000073

def z170 : W := mkw 0x0001449380000000 0x100005124e000000 0xfd3fcfff80000000 0x7ff4ff3ffe000000

def z171 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x540c003e01c0872a 0xd5503000f807021c

def z172 : W := mkw 0xc9fffdf7f76c8967 0xff27fff7dfddb225 0xfdfffffffffc9fff 0xfff7fffffffff27f

def z173 : W := mkw 0x484c50e6a344ab6d 0x312131439a8d12ad 0xf4d4f1c7e64cfffe 0xf7d353c71f9933ff

def z174 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x09eb3e3800000000 0x0827acf8e0000000

def z175 : W := mkw 0x3000020808931480 0x00c0000820224c52 0x0200000000031ce0 0x0008000000000c73

def z176 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xbdf3ffc180000000 0x3ef7cfff06000000

def z177 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010c000060c0014 0x0280430000183000

def z178 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff804c07d8 0x7ff7fffffe01301f

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400000180000000 0x6790000006000000

def z180 : W := mkw 0x80fe800021680003 0x8203fa000085a000 0xfcffc00001fc0018 0x03f3ff000007f000

def z181 : W := mkw 0x480040c282048964 0x112001030a081225 0xe410c1c1860c1cfc 0xe790430706183073

def z182 : W := mkw 0x684c50eea3c5af6d 0x31a13143ba8f16bd 0xf41cc1ff87cc9ffe 0xf7d07307fe1f327f

def z183 : W := mkw 0x60b03b6c5e83fe3a 0x6582c0edb17a0ff8 0x3ff03ffe7e03ff27 0xfcffc0fff9f80ffc

def z184 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x7ff43fc67e43ff2f 0xfdffd0ff19f90ffc

def z185 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x03000e3980031ce0 0x6c0c0038e6000c73

def z186 : W := mkw 0x3001061929d33688 0x00c0041864a74cda 0xef2b0e39f9f3ffff 0xefbcac38e7e7cfff

def z187 : W := mkw 0x8000000075680000 0x0600000001d5a000 0x0000000079b00001 0x0000000001e6c000

def z188 : W := mkw 0x4800004002048964 0x0120000100081225 0x0000000000009fe0 0x000000000000027f

def z189 : W := mkw 0x81ffbd3575680003 0xee07fef4d5d5a000 0x09eb3e3879b00001 0x0827acf8e1e6c000

def z190 : W := mkw 0x480040c282048964 0x112001030a081225 0x540401c780409fea 0xf55010071e01027f

def z191 : W := mkw 0x78b16fdbde97ddf6 0x55e2c5bf6f7a5f77 0xffffffffffffffff 0xffffffffffffffff

def z192 : W := mkw 0x0800408280040144 0x102001020a001005 0xc004c007804c07d8 0x430013001e01301f

def z193 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3819b3001d 0x8bbcac38e066cc00

def z194 : W := mkw 0x3000020808931480 0x00c0000820224c52 0x4e08003819b31cfd 0xcd382000e066cc73

def z195 : W := mkw 0x2000000821c12608 0x0080000020870498 0x1ec0300061c3e72b 0x9c7b00c001870f9c

def z196 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff99b0001d 0xfff7fffffe66c000

def z197 : W := mkw 0x3001041900910480 0x00c0041064024412 0xec2b003999b004dd 0xc3b0ac00e666c013

def z198 : W := mkw 0x31ffffbfa9d3368b 0xf8c7fffefea74cda 0xfffffffff9f3ffff 0xffffffffffe7cfff

def z199 : W := mkw 0x8000000075680000 0x0600000001d5a000 0x000000007ffc001f 0x8000000001fff000

def z200 : W := mkw 0x214d7dbfa1c12609 0x788535f6fe870498 0x5fcc3fffe1c3e72b 0xfd7f30ffff870f9c

def z201 : W := mkw 0x0103c49380000000 0x98040f124e000000 0x8003c00180000000 0x02000f0006000000

def z202 : W := mkw 0x400002405e02d830 0x0500000901780b60 0x1ec030007e03f827 0x9c7b00c001f80fe0

def z203 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x12c4300661c3e72b 0x904b10c019870f9c

def z204 : W := mkw 0x804e800021680001 0x82013a000085a000 0xf41fc00007fc001e 0x83d07f00001ff000

def z205 : W := mkw 0x2000000800810400 0x0080000020020410 0x0a08003801830001 0x08282000e0060c00

def z206 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0067ffc873f 0xd7f3ff0019fff21c

def z207 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x4e0c003e01c30729 0xcd383000f8070c1c

def z208 : W := mkw 0x0000020008021000 0x0000000800200840 0xef200e0198031cfd 0xefbc803806600c73

def z209 : W := mkw 0x0001041100000000 0x0000041044000000 0xc00b003980000000 0x43002c00e6000000

def z210 : W := mkw 0x604c126c7fc3fe39 0x25813049b1ff0ff8 0x5ecc303e7fc3ff2f 0xdd7b30c0f9ff0ffc

def z211 : W := mkw 0x684c106c23c5af6d 0x21a13041b08f16bd 0x5ecc303e67cfffff 0xdd7b30c0f99f3fff

def z212 : W := mkw 0x1001061108121080 0x0040041844204842 0xaf230e01983318f5 0xaebc8c380660cc63

def z213 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x50cc303e61c0e70a 0x514330c0f987039c

def z214 : W := mkw 0x01017db780000000 0x780405f6de000000 0xed2b3fff80000000 0x7fb4acfffe000000

def z215 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x1bf03fc07e03e003 0x186fc0ff01f80f80

def z216 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xc9effe3f80000000 0x4b27bff8fe000000

def z217 : W := mkw 0x1001061108121080 0x0040041844204842 0xed2b0e39983018d4 0x6fb4ac38e660c063

def z218 : W := mkw 0x41ffbf755e02d833 0xed07fefdd5780b60 0x3ffb3ff87e03f827 0xbcffecffe1f80fe0

def z219 : W := mkw 0x70b12f595e93dcb2 0x45c2c4bd657a4f72 0x3ffb3ff87fb3f827 0xbcffecffe1fecfe0

def z220 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x12c4303e6043e722 0x5c4b10c0f9810f9c

def z221 : W := mkw 0x0800408280040144 0x102001020a001005 0xf414c007864c07de 0xc3d053001e19301f

def z222 : W := mkw 0x01b17db780000002 0x7806c5f6de000000 0x3df03fff80000000 0x7cf7c0fffe000000

def z223 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x23300fc07e03f827 0xa08cc03f01f80fe0

def z224 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x1fc03fc06003f823 0xbc7f00ff01800fe0

def z225 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x5cdcc00067cc000b 0x81737300019f3000

def z226 : W := mkw 0x480040c282048964 0x112001030a081225 0xfed4f1c7e64fffff 0xfffb53c71f993fff

def z227 : W := mkw 0x2000000821c12608 0x0080000020870498 0x0200000061c3e72b 0x8008000001870f9c

def z228 : W := mkw 0x01b2e98280000002 0xd806cba60a000000 0x0010c1c000000000 0x0000430700000000

def z229 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3980031ce0 0x6fbcac38e6000c73

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000006003e023 0x8008000001800f80

def z231 : W := mkw 0x400000405600c830 0x0500000101580320 0x000000006600e002 0x0000000001980380

def z232 : W := mkw 0x494fd4f782048965 0xb9253f53de081225 0xf41fc1ff864c9ffe 0xf7d07f07fe19327f

def z233 : W := mkw 0xb1ffffbffdfb1483 0xfec7fffefff7ec52 0xffffffffffff1cff 0xfffffffffffffc73

def z234 : W := mkw 0x00fc000075400003 0x0403f00001d50000 0x7cfc00007fc0000f 0x81f3f00001ff0000

def z235 : W := mkw 0x480040c282048964 0x112001030a081225 0xa010c1c7860c9ff4 0x768043071e18327f

def z236 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x00c0000060000000 0x0003000001800000

def z237 : W := mkw 0x41fffff7de02d833 0xfd07ffffdf780b60 0xfffffffffe03f827 0xfffffffffff80fe0

def z238 : W := mkw 0x3001041900910480 0x00c0041064024412 0x000b003801b00000 0x00002c00e006c000

def z239 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x0b2b0e3999b31ce1 0x6c2cac38e666cc73

def z240 : W := mkw 0x680040caa3c5af6c 0x11a001032a8f16bd 0xf614c1c7e7cfffff 0xf7d853071f9f3fff

def z241 : W := mkw 0x004c102421400001 0x2001304090850000 0x5ccc303e61c0000b 0xdd7330c0f9870000

def z242 : W := mkw 0x480040c282048964 0x112001030a081225 0xe014c1c7864c1fdc 0x638053071e19307f

def z243 : W := mkw 0x600002487fc3fe38 0x0580000921ff0ff8 0x020000007fc3ff2f 0x8008000001ff0ffc

def z244 : W := mkw 0x480040c282048964 0x112001030a081225 0x3414c1c6064c9b26 0xb4d053071819326c

def z245 : W := mkw 0x01017db780000000 0x780405f6de000000 0xf514ffff80000000 0x7fd453fffe000000

def z246 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x3ff03fc06003e023 0xbcffc0ff01800f80

def z247 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c7864c8302 0x77d053071e19320c

def z248 : W := mkw 0x6800004823c5af6c 0x01a00001208f16bd 0x0200000067cfffff 0x80080000019f3fff

def z249 : W := mkw 0x4800004002048964 0x0120000100081225 0xe4000001864c9ffe 0xe79000000619327f

def z250 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x2f203fc01803f825 0xbcbc80ff00600fe0

def z251 : W := mkw 0x0800000000040144 0x0020000000001005 0x00000000004c07d8 0x000000000001301f

def z252 : W := mkw 0x0001041100000000 0x0000041044000000 0xed2b0e3980001cfc 0xefb4ac38e6000073

def z253 : W := mkw 0x81fffdb7d4280003 0xfe07fff6df50a000 0xfdffffff9e3c0014 0x7ff7fffffe78f000

def z254 : W := mkw 0x010079a680000000 0x780401e69a000000 0x000031c600000000 0x100000c718000000

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0000060000003 0x8073000001800000

def z256 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffe64c0002 0x7ff7ffffff993000

def z257 : W := mkw 0x01b3ad1100000002 0xc806ceb444000000 0x01230e0000000000 0x00048c3800000000

def z258 : W := mkw 0x60fc396c77c1ee3b 0x6583f0e5b1df07b8 0x5edc31fe67c3e72b 0xdd7b70c7f99f0f9c

def z259 : W := mkw 0x41017ff78a02d830 0x790405ffde280b60 0x03003fff8003f820 0x7c0c00fffe000fe0

def z260 : W := mkw 0xa04c102c75e92609 0x26813040b1d7a498 0x5ecc303e7fffe73f 0xdd7b30c0f9ffff9c

def z261 : W := mkw 0x80fe82007d6a1003 0x8603fa0801f5a840 0xffffce007fff183f 0xafffff3801fffc60

def z262 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x03003fc00003f820 0x3c0c00ff00000fe0

def z263 : W := mkw 0x0000020008021000 0x0000000800200840 0x2f200e0018031825 0xacbc803800600c60

def z264 : W := mkw 0x480040c282048964 0x112001030a081225 0xfc3fc1c79ffc9fff 0xf7f0ff071e7ff27f

def z265 : W := mkw 0x604c106c23c1ae29 0x21813041b08f06b8 0x7edc31fe67c3ff2f 0xfdfb70c7f99f0ffc

def z266 : W := mkw 0x3001041900910480 0x00c0041064024412 0xed2b0e3981b004d8 0x6fb4ac38e606c013

def z267 : W := mkw 0x400002400a02d830 0x0100000900280b60 0x020000000003f820 0x0008000000000fe0

def z268 : W := mkw 0x3000020808931480 0x00c0000820224c52 0xee2b000019b31cfd 0x83b8ac000066cc73

def z269 : W := mkw 0x00fc392400000003 0x6003f0e490000000 0x7dfc3ffe00000000 0x7df7f0fff8000000

def z270 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdffffffe1c0000b 0xfff7ffffff870000

def z271 : W := mkw 0x30b12f195c935492 0x44c2c4bc65724d52 0x0beb3e3879b36001 0x082facf8e1e6cd80

def z272 : W := mkw 0xc0b2ab405e2ad832 0xc702caad0178ab60 0xbff3ffc07e3ff837 0xbeffcfff01f8ffe0

def z273 : W := mkw 0x700106595e93dcb0 0x05c00419657a4f72 0xef2b0e39ffb3fcff 0xefbcac38e7fecff3

def z274 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x2bf03fc07e037805 0x28afc0ff01f80de0

def z275 : W := mkw 0x60fc3b6c7fc3fe3b 0x6583f0edb1ff0ff8 0x3ff83ff87f83f827 0xbcffe0ffe1fe0fe0

def z276 : W := mkw 0x21fffdbf8081260b 0xf887fff6fe020498 0xffffffff8003e720 0x7ffffffffe000f9c

def z277 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfffb3fc07fb3f83f 0xbfffecff01fecfe0

def z278 : W := mkw 0x01fef9a680000003 0xf807fbe69a000000 0xfcfff1c600000000 0x13f3ffc718000000

def z279 : W := mkw 0x0000290000000000 0x400000a400000000 0x01003fc000000000 0x3c0400ff00000000

def z280 : W := mkw 0x20fc3b2c7dc3761b 0x6483f0ecb1f70dd8 0x5fec3e3e79c3e72b 0xdd7fb0f8f9e70f9c

def z281 : W := mkw 0x90ff86117d7a1083 0x8643fe1845f5e842 0xfdffce01fffc18df 0xa3f7ff3807fff063

def z282 : W := mkw 0x60003b6c0a83fe38 0x618000edb02a0ff8 0x03003ffe0003ff20 0x7c0c00fff8000ffc

def z283 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff2f0e3f99f39fff 0xfffcbc38fe67ce7f

def z284 : W := mkw 0x00fe902400000003 0xa003fa4090000000 0xfcfff03e00000000 0x5ff3ffc0f8000000

def z285 : W := mkw 0x0800408280040144 0x102001020a001005 0xe404c007804c1ffc 0xe79013001e01307f

def z286 : W := mkw 0x30b12f195c935492 0x44c2c4bc65724d52 0xefeb3e39f9b37cfd 0xefbfacf8e7e6cdf3

def z287 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0xfcfff0067ffce31f 0x93f3ffc019fff38c

def z288 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfefff0007fffe03f 0x9ffbffc001ffff80

def z289 : W := mkw 0x480040c282048964 0x112001030a081225 0xb410c1c1860c98f6 0xb6d0430706183263

def z290 : W := mkw 0x70b12f595e93dcb2 0x45c2c4bd657a4f72 0x3ff03ff9fe03fce7 0xfcffc0ffe7f80ff3

def z291 : W := mkw 0xc0fe804077688823 0x8703fa0101dda220 0xfcffc1c07ffc983f 0xb7f3ff0701fff260

def z292 : W := mkw 0x480040c282048964 0x112001030a081225 0x341001c786009fe6 0xf4d040071e18027f

def z293 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfedcf03e67cfe73f 0xdffb73c0f99f3f9c

def z294 : W := mkw 0x80fe902475680003 0xa603fa4091d5a000 0xfcfff03e7ffc001f 0xdff3ffc0f9fff000

def z295 : W := mkw 0x21ffbd3d21c1260b 0xe887fef4f4870498 0x5fef3e3e61c3e72b 0xdd7fbcf8f9870f9c

def z296 : W := mkw 0x2001041900810400 0x0080041064020410 0xef2b0e3981830429 0xefbcac38e6060c10

def z297 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c1864c18de 0xa3d0530706193063

def z298 : W := mkw 0x20fc102c75c1260b 0x2483f040b1d70498 0x7efc303e7fc3e72f 0xddfbf0c0f9ff0f9c

def z299 : W := mkw 0x01feb92400000003 0xe807fae490000000 0x00c0300000000000 0x000300c000000000

def z300 : W := mkw 0x49fffff7de06d977 0xfd27ffffdf781b65 0xfffffffffe4fffff 0xfffffffffff93fff

def z301 : W := mkw 0xe0febb6c7febfe3b 0xe783faedb1ffaff8 0xfffffffe7fffff3f 0xfffffffff9fffffc

def z302 : W := mkw 0x004c000021400001 0x0001300000850000 0x10c4000060400002 0x0043100001810000

def z303 : W := mkw 0x40fc39647740ea3b 0x6503f0e591dd03a8 0x10d431c66640e302 0x104350c71999038c

def z304 : W := mkw 0x00b0000054000002 0x0402c00001500000 0x10d0000066000002 0x0043400001980000

def z305 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x1ec0303e6003e723 0xdc7b00c0f9800f9c

def z306 : W := mkw 0x684c50eea3c5af6d 0x31a13143ba8f16bd 0x5ecc31ffe1c3ffeb 0xfd7b30c7ff870fff

def z307 : W := mkw 0x004c102400000001 0x2001304090000000 0x5ccc303e0040872a 0xdd7330c0f801021c

def z308 : W := mkw 0x81ffbd3575680003 0xee07fef4d5d5a000 0xfdfffe387ffc001f 0x8bf7fff8e1fff000

def z309 : W := mkw 0x2000000800810400 0x0080000020020410 0x5ec830386183e42b 0xdd7b20c0e1860f90

def z310 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0x03000fff80039fe0 0x7c0c003ffe000e7f

def z311 : W := mkw 0xc8fec0c2f76c8967 0x9723fb030bddb225 0xf4d4c1c7e64c9ffe 0xf7d353071f99327f

def z312 : W := mkw 0x48006bc28a06d974 0x512001af0a281b65 0xf714ffc7864ffffe 0xffdc53ff1e193fff

def z313 : W := mkw 0x0000000000000000 0x0000000000000000 0x020030000003e020 0x1c0800c000000f80

def z314 : W := mkw 0x3000020829d33688 0x00c0000820a74cda 0x0200000079f3ffff 0x8008000001e7cfff

def z315 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0x3ff03fc07e4fffff 0xbcffc0ff01f93fff

def z316 : W := mkw 0x2000102c21c12608 0x20800040b0870498 0x0200303e61c3e72b 0xdc0800c0f9870f9c

def z317 : W := mkw 0x00b02b0008021002 0x4002c0ac00200840 0x3ff03fc018031825 0xbcffc0ff00600c60

def z318 : W := mkw 0x49fef9e682048967 0xf927fbe79a081225 0xf4d4f1c7864c9ffe 0xf7d353c71e19327f

def z319 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xe13fcfff80000000 0x6384ff3ffe000000

def z320 : W := mkw 0x004e800000000001 0x80013a0000000000 0xc00fc00000000000 0x03003f0000000000

def z321 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ccc303e01c00708 0x5d7330c0f807001c

def z322 : W := mkw 0x48b040c2d6048966 0x1522c1030b581225 0xfcf4c1c7fe4c9fff 0xf7f3d3071ff9327f

def z323 : W := mkw 0x0000408280000000 0x100001020a000000 0xf414c1c780001cfc 0xf7d053071e000073

def z324 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x3ff03fc078036001 0x3cffc0ff01e00d80

def z325 : W := mkw 0x4800004002048964 0x0120000100081225 0xf414c000064c9ffe 0x83d053000019327f

def z326 : W := mkw 0x804e800021680001 0x82013a000085a000 0xdccfc00061fc001b 0x83733f000187f000

def z327 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff3fce399fff1cff 0xeffcff38e67ffc73

def z328 : W := mkw 0x884ec082a16c0145 0x92213b020a85b005 0xc00fc00781fc07d8 0x43003f001e07f01f

def z329 : W := mkw 0x00002b0008025010 0x400000ac00200940 0x03003e0000036000 0x080c00f800000d80

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0300000000000 0x1c7300c000000000

def z331 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x0b2b0e3819b31cfd 0x882cac38e066cc73

def z332 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e61836001 0x5d7b30c0f9860d80

def z333 : W := mkw 0x1001061108121080 0x0040041844204842 0xe5230e0198301cfc 0xe7948c380660c073

def z334 : W := mkw 0x0000102400000000 0x2000004090000000 0x0000303e00000000 0x5c0000c0f8000000

def z335 : W := mkw 0x400002405e02d830 0x0500000901780b60 0x000000001e001804 0x0000000000780060

def z336 : W := mkw 0x400002405e02d830 0x0500000901780b60 0x2f200e007e03f827 0xacbc803801f80fe0

def z337 : W := mkw 0x0000020008021000 0x0000000800200840 0x0200000018031825 0x8008000000600c60

def z338 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc00079b00001 0x03f3ff0001e6c000

def z339 : W := mkw 0x480040c282048964 0x112001030a081225 0xb014c1c7864c9bd6 0x32c053071e19326f

def z340 : W := mkw 0x1001041100100080 0x0040041044004002 0x80030001803000d0 0x02000c000600c003

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00b000001b00018 0x03002c000006c000

def z342 : W := mkw 0xc84ec0c2a36c8965 0x93213b030a8db225 0xf41fc1c787fc9ffe 0xf7d07f071e1ff27f

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c00000000000 0x03d0530000000000

def z344 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x10d4c0007ffc001f 0x8043530001fff000

def z345 : W := mkw 0x000002005c025010 0x0400000801700940 0x0200000078036001 0x0008000001e00d80

def z346 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x01000fc000001800 0x2004003f00000060

def z347 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff8040872a 0xfff7fffffe01021c

def z348 : W := mkw 0x81b3ed93d4280002 0xde06cfb64f50a000 0xa133cfc19e3c0014 0x2284cf3f0678f000

def z349 : W := mkw 0x40fc2b407f42d833 0x4503f0ad01fd0b60 0x7ffc3fc07fc3f82f 0xbdfff0ff01ff0fe0

def z350 : W := mkw 0x50b12f515e12d8b2 0x4542c4bd45784b62 0xa1330fc19e3018d4 0x2284cc3f0678c063

def z351 : W := mkw 0x400029400200c830 0x410000a500080320 0x000031c00000e000 0x100000c700000380

def z352 : W := mkw 0x1001061108121080 0x0040041844204842 0x01230e0018300000 0x00048c380060c000

def z353 : W := mkw 0x41fffff7de02d833 0xfd07ffffdf780b60 0xfdffffff9e001804 0x7ff7fffffe780060

def z354 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x09eb3fff80000000 0x7c27acfffe000000

def z355 : W := mkw 0x700002485e93dcb0 0x05c00009217a4f72 0x020000007fb3fcff 0x8008000001fecff3

def z356 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x3cf031c07e00e007 0x90f3c0c701f80380

def z357 : W := mkw 0x00fec08280000003 0x9003fb020a000000 0xfcffc1c780000000 0x77f3ff071e000000

def z358 : W := mkw 0x49b3edd382048966 0xd926cfb74e081225 0xf537cfc7864c9ffe 0xf7d4df3f1e19327f

def z359 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c780009fe0 0x77d053071e00027f

def z360 : W := mkw 0xa0fe800875e90403 0x8683fa0021d7a410 0xfeffc0387fff043f 0xcffbff00e1fffc10

def z361 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x18ffc0007ffc0003 0x0063ff0001fff000

def z362 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff864c001e 0xfff7fffffe193000

def z363 : W := mkw 0x70fd3f7d7fd3febb 0x65c3f4fdf5ff4ffa 0xffff3ffffff3ffff 0xfffffcffffffcfff

def z364 : W := mkw 0xc8fec0c2f76c8967 0x9723fb030bddb225 0xfcffc1c1fffc18df 0xa3f3ff0707fff063

def z365 : W := mkw 0x680050ee8285af6c 0x31a00143ba0a16bd 0xf614f1ff864ffffe 0xffd853c7fe193fff

def z366 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xd0dff1ff80000000 0x53437fc7fe000000

def z367 : W := mkw 0x80fea90075680003 0xc603faa401d5a000 0xfdffffc07ffc001f 0xbff7ffff01fff000

def z368 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc000064c001e 0x83f3ff0000193000

def z369 : W := mkw 0x00b0000054000002 0x0402c00001500000 0x3ef030007e03e027 0x9cfbc0c001f80f80

def z370 : W := mkw 0xf8ffc6dbffff9de7 0x97e3ff1b6ffffe77 0xffffcfffffff9fff 0xffffff3ffffffe7f

def z371 : W := mkw 0x00b2800000000002 0x8002ca0000000000 0xa033c00000000000 0x0280cf0000000000

def z372 : W := mkw 0x11ffffb788121083 0xf847fffede204842 0xfdffffff983018d4 0x7ff7fffffe60c063

def z373 : W := mkw 0xb0ff841975f90483 0x86c3fe1065d7e412 0xfcffc039fffc04df 0xc3f3ff00e7fff013

def z374 : W := mkw 0x70012f590a93dcb0 0x41c004bd642a4f72 0x03003ff98003fce0 0x7c0c00ffe6000ff3

def z375 : W := mkw 0x700106590a939ca0 0x01c00419642a4e72 0xff3b0ff99fb39cff 0xfffcec3fe67ece73

def z376 : W := mkw 0x80b2800075680002 0x8602ca0001d5a000 0xa033c0007ffc001f 0x8280cf0001fff000

def z377 : W := mkw 0x2000000800810400 0x0080000020020410 0xee08003981831cfd 0xefb82000e6060c73

def z378 : W := mkw 0x004c102421402209 0x2001304090850088 0x54c430066040e72a 0xd55310c01981039c

def z379 : W := mkw 0xb00002087dfb1480 0x06c0000821f7ec52 0x020000007fff1cff 0x8008000001fffc73

def z380 : W := mkw 0x41fef9e6d600c833 0xfd07fbe79b580320 0x10d4f1c66600e002 0x104353c719980380

def z381 : W := mkw 0x204c50aea1c12609 0x30813142ba870498 0xfedcf1ffe1c3e72b 0xfffb73c7ff870f9c

def z382 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x0ac8303861c3e72b 0x882b20c0e1870f9c

def z383 : W := mkw 0x004c000021400001 0x0001300000850000 0x5ccc000061c0000b 0x8173300001870000

def z384 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x3ff03e007e036007 0x88ffc0f801f80d80

def z385 : W := mkw 0x480040c282048964 0x112001030a081225 0xa010c1c1864c9ffe 0xa28043070619327f

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000040872a 0x800000000001021c

def z387 : W := mkw 0x3801449b809505c4 0x10e005126e025417 0xc00fc03f81fc07d8 0x43003f00fe07f01f

def z388 : W := mkw 0x014fd4b780000001 0xb8053f52de000000 0xf41fc1ff80000000 0x77d07f07fe000000

def z389 : W := mkw 0x48b06bc2de06d976 0x5522c1af0b781b65 0x3ff4ffc67e4ffb27 0xbcffd3ff19f93fec

def z390 : W := mkw 0x0000020008021000 0x0000000800200840 0x21200e0018001804 0x2084803800600060

def z391 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0xa133ffff80000000 0x7e84cffffe000000

def z392 : W := mkw 0x00b0000054000002 0x0402c00001500000 0xfcfb00007fb0001f 0x83f3ec0001fec000

def z393 : W := mkw 0x8000000075680000 0x0600000001d5a000 0xec2b00007ffc001f 0x83b0ac0001fff000

def z394 : W := mkw 0x2000020808831400 0x0080000820220c50 0x6f280e3819831c2d 0xedbca038e0660c70

def z395 : W := mkw 0x2000000800810400 0x0080000020020410 0x4e08003801830429 0xcd382000e0060c10

def z396 : W := mkw 0x004c102421402209 0x2001304090850088 0x00c0300060006000 0x000300c001800180

def z397 : W := mkw 0x0800408280040144 0x102001020a001005 0xd404c007804c87fa 0xd75013001e01321f

def z398 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x4e08303e0183e729 0xdd3820c0f8060f9c

def z399 : W := mkw 0x004c000021400001 0x0001300000850000 0x5ccc000661c0872b 0xd57330001987021c

def z400 : W := mkw 0x0000408280000000 0x100001020a000000 0x000001c780000000 0x740000071e000000

def z401 : W := mkw 0x60b02b485e83dc32 0x4582c0ad217a0f70 0x7ff83ff87f83fc2f 0xfdffe0ffe1fe0ff0

def z402 : W := mkw 0x3001041900910480 0x00c0041064024412 0xce0b003981b304f9 0xcf382c00e606cc13

def z403 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x03000e3800030000 0x080c0038e0000c00

def z404 : W := mkw 0x684c50eea3c5af6d 0x31a13143ba8f16bd 0x5edcf1fe67cfe72b 0xdd7b73c7f99f3f9c

def z405 : W := mkw 0x4000004002008820 0x0100000100080220 0x0000000006009826 0x8000000000180260

def z406 : W := mkw 0x0800408280040144 0x102001020a001005 0xf414c1c7804c07d8 0x77d053071e01301f

def z407 : W := mkw 0x2000000800812608 0x0080000020020498 0x020000000003e720 0x0008000000000f9c

def z408 : W := mkw 0x00b0290054000002 0x4402c0a401500000 0x3df03fc07e000007 0xbcf7c0ff01f80000

def z409 : W := mkw 0x3001041900910480 0x00c0041064024412 0x00000039800004c0 0x40000000e6000013

def z410 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x3cfb00007fb00007 0x80f3ec0001fec000

def z411 : W := mkw 0x204c102c00810401 0x20813040b0020410 0x5ecc303e01830429 0xdd7b30c0f8060c10

def z412 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xab2b0e3999b318d5 0x2aacac38e666cc63

def z413 : W := mkw 0xc8fec0c2f76c8967 0x9723fb030bddb225 0xfcffc1c67ffc831f 0x93f3ff0719fff20c

def z414 : W := mkw 0x31b3ef9b88931482 0xd8c6cfbe6e224c52 0xef3bcff999b31cfd 0xefbcef3fe666cc73

def z415 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x2f2b0e3819b31825 0xacbcac38e066cc60

def z416 : W := mkw 0x2000000821c12608 0x0080000020870498 0x0000000001c00708 0x000000000007001c

def z417 : W := mkw 0x004c000021400001 0x0001300000850000 0x08c8000061800001 0x0023200001860000

def z418 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0xfdfffe3800000000 0x0bf7fff8e0000000

def z419 : W := mkw 0x004c102400000001 0x2001304090000000 0x10c4300600000000 0x104310c018000000

def z420 : W := mkw 0x004c102421402209 0x2001304090850088 0x0004000600400300 0x000010001801000c

def z421 : W := mkw 0xb04f841921f90481 0x82c13e106487e412 0xc00fc03981fc04d8 0x43003f00e607f013

def z422 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0x0023000018300000 0x00008c000060c000

def z423 : W := mkw 0x2000000821c12608 0x0080000020870498 0x0200000061836001 0x0008000001860d80

def z424 : W := mkw 0xb0b386195cbb1482 0x86c2ce186572ec52 0xef3bce399fbf1cfd 0xefbcef38e67efc73

def z425 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xeceb000079b0001d 0x83b3ac0001e6c000

def z426 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x09e03e0000000000 0x082780f800000000

def z427 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff03fc1fe03fcff 0xffffc0ff07f80ff3

def z428 : W := mkw 0x48b06bc2de06d976 0x5522c1af0b781b65 0xa130cfc19e0c18d4 0x2284c33f06783063

def z429 : W := mkw 0x0000020008021000 0x0000000800200840 0x0b200e0018030001 0x082c803800600c00

def z430 : W := mkw 0x480040c282048964 0x112001030a081225 0x000001c600008300 0x100000071800020c

def z431 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x4acc303e61c36709 0x492b30c0f9870d9c

def z432 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x0ac8303e6183e721 0x5c2b20c0f9860f9c

def z433 : W := mkw 0x3001041900910480 0x00c0041064024412 0xe40b003981b01cfc 0xe7902c00e606c073

def z434 : W := mkw 0x1000020008121080 0x0040000800204842 0x00000000183018d4 0x000000000060c063

def z435 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xe12b0e3999b01cdc 0x6384ac38e666c073

def z436 : W := mkw 0x014fd4b780000001 0xb8053f52de000000 0xed2fce3f80000000 0x6fb4bf38fe000000

def z437 : W := mkw 0x2000000800810400 0x0080000020020410 0x5e0c003e01c3872b 0xdd783000f8070e1c

def z438 : W := mkw 0xc0feab407f6ad833 0xc703faad01fdab60 0x3ff4ffc07e4ff827 0xbcffd3ff01f93fe0

def z439 : W := mkw 0x49017df782048964 0x792405f7de081225 0xf514ffff864c9ffe 0xffd453fffe19327f

def z440 : W := mkw 0x68fc7beeffc7ff7f 0x75a3f1efbbff1ffd 0xfffcffffffcfffff 0xfffff3ffffff3fff

def z441 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x37103fc00603f826 0xbcdc40ff00180fe0

def z442 : W := mkw 0x3000020808931480 0x00c0000820224c52 0xe600000199b31cfd 0xe79800000666cc73

def z443 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xe03fc0001ffc001c 0x0380ff00007ff000

def z444 : W := mkw 0x60b02b487fc3fe3a 0x4582c0ad21ff0ff8 0x3ff03fc07fc3ff2f 0xbcffc0ff01ff0ffc

def z445 : W := mkw 0x400002405e02d830 0x0500000901780b60 0x361001c07e03f827 0xb4d8400701f80fe0

def z446 : W := mkw 0x01fffdb7a140220b 0xf807fff6de850088 0xfdffffffe040e302 0x7ff7ffffff81038c

def z447 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400000000008022 0x9450000000000200

def z448 : W := mkw 0x304d061929d31481 0x00c1341864a74c52 0xffef0e39f9f31cff 0xefffbc38e7e7cc73

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c20000018000005 0x80b0800000600000

def z450 : W := mkw 0x31017fbf88931480 0x78c405fefe224c52 0xef2b3fff99b31cfd 0xffbcacfffe66cc73

def z451 : W := mkw 0x0000020008021000 0x0000000800200840 0x3fe03e007803f827 0xbcff80f801e00fe0

def z452 : W := mkw 0x31ffbf3d08931483 0xe8c7fefcf4224c52 0x0beb3e3819b30001 0x082facf8e066cc00

def z453 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0xedeb3e3980000000 0x6fb7acf8e6000000

def z454 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xcb2b0e3999b304d9 0x4b2cac38e666cc13

def z455 : W := mkw 0x2000000821c12608 0x0080000020870498 0x5604000661c3e72b 0xd558100019870f9c

def z456 : W := mkw 0x01013d3500000000 0x680404f4d4000000 0x01003e3800000000 0x080400f8e0000000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000600008720 0x540000001800021c

def z458 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x4f2b0e3819b30429 0xcd3cac38e066cc10

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001800004d8 0x4300000006000013

def z460 : W := mkw 0xa0fe902c75e9260b 0xa683fa40b1d7a498 0x0aeb303879b36001 0x082bacc0e1e6cd80

def z461 : W := mkw 0x01ffffb788021003 0xf807fffede200840 0xffffffff98031825 0xfffffffffe600c60

def z462 : W := mkw 0x480002405e06d974 0x0520000901781b65 0x020000007e4fffff 0x8008000001f93fff

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b000199b01cfd 0xe7b0ac000666c073

def z464 : W := mkw 0xa1fffdbff5e9260b 0xfe87fff6ffd7a498 0xffffffffffffe73f 0xffffffffffffff9c

def z465 : W := mkw 0x11b3ef9388121082 0xd846cfbe4e204842 0xa133cfc1983018d4 0x2284cf3f0660c063

def z466 : W := mkw 0x31ffbf3d08931483 0xe8c7fefcf4224c52 0xefeb3e3999b31cfd 0xefbfacf8e666cc73

def z467 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x34d031c06600f826 0xb4d340c7019803e0

def z468 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1ec830386183e023 0x9c7b20c0e1860f80

def z469 : W := mkw 0x0001041100000000 0x0000041044000000 0x092b0e3800000000 0x0824ac38e0000000

def z470 : W := mkw 0xc8fec0c2f76c8967 0x9723fb030bddb225 0x10d4c1c6664c8302 0x104353071999320c

def z471 : W := mkw 0x21fffdbfa1c1260b 0xf887fff6fe870498 0xffffffffe1836001 0x7fffffffff860d80

def z472 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xd0dfc00067fc001a 0x03437f00019ff000

def z473 : W := mkw 0x004c102421402209 0x2001304090850088 0x1ec430066043e323 0x9c7b10c019810f8c

def z474 : W := mkw 0xb0ff86197dfb1483 0x86c3fe1865f7ec52 0xffffce387fff001f 0x8bffff38e1fffc00

def z475 : W := mkw 0xc8feebc2ff6ed977 0xd723fbaf0bfdbb65 0xffffffc7ffffffff 0xffffffff1fffffff

def z476 : W := mkw 0x8002800000280000 0x82000a000000a000 0x8003c000003c0010 0x02000f000000f000

def z477 : W := mkw 0x3801469b889715c4 0x10e0051a6e225c57 0xef2fce3f99ff1ffd 0xefbcbf38fe67fc7f

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x4400000000000428 0xc510000000000010

def z479 : W := mkw 0x580146d38a1699e4 0x1160051b4e285a67 0xa133cfc19e3c18d4 0x2284cf3f0678f063

def z480 : W := mkw 0x40002b405e02d830 0x450000ad01780b60 0x03003fc07e03f827 0xbc0c00ff01f80fe0

def z481 : W := mkw 0x00b0000054000002 0x0402c00001500000 0x203000001e000004 0x0080c00000780000

def z482 : W := mkw 0xa0fe902c75e9260b 0xa683fa40b1d7a498 0x5eef303e79f3e72b 0xdd7bbcc0f9e7cf9c

def z483 : W := mkw 0x4000004002008820 0x0100000100080220 0x741401c606409f2e 0xf5d050071819027c

def z484 : W := mkw 0x0001061108021000 0x0000041844200840 0xef2b0e3998031825 0xefbcac38e6600c60

def z485 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xf537cfc780000000 0x77d4df3f1e000000

def z486 : W := mkw 0x804e800021680001 0x82013a000085a000 0x000b000001b00000 0x00002c000006c000

def z487 : W := mkw 0x80fec082f5680003 0x9603fb020bd5a000 0xfcffc1c7fffc001f 0xf7f3ff071ffff000

def z488 : W := mkw 0x784d56ffabd7bfed 0x31e1355bfeaf5eff 0xffffffffffffffff 0xffffffffffffffff

def z489 : W := mkw 0x48b06bc2de06d976 0x5522c1af0b781b65 0x3ff03fc7fe03ffe7 0xfcffc0ff1ff80fff

def z490 : W := mkw 0x21fef9aea1c1260b 0xf887fbe6ba870498 0x5edcf1fe61c3e72b 0xdd7b73c7f9870f9c

def z491 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x03000e3999b31cfd 0xec0c0038e666cc73

def z492 : W := mkw 0x2000000800810400 0x0080000020020410 0x0200000001830429 0x8008000000060c10

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0xf404000780409ffe 0xf7d010001e01027f

def z494 : W := mkw 0x004c102400000001 0x2001304090000000 0x08c8303800000000 0x082320c0e0000000

def z495 : W := mkw 0x20fc392c21c1260b 0x6083f0e4b0870498 0x7ffc3ffe61c3e72b 0xfdfff0fff9870f9c

def z496 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfeef303e79f3e73f 0xdffbbcc0f9e7cf9c

def z497 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0x10d4c00000000000 0x0043530000000000

def z498 : W := mkw 0x2000000800810400 0x0080000020020410 0x4008003801800408 0x41002000e0060010

def z499 : W := mkw 0x3000000800910480 0x00c0000020024412 0x0000000001b004d8 0x000000000006c013

def z500 : W := mkw 0xc0fe82407f6ad833 0x8703fa0901fdab60 0xfeffc0007ffff83f 0x83fbff0001ffffe0

def z501 : W := mkw 0x20fe902c21c1260b 0xa083fa40b0870498 0xfefff03e61c3e72b 0xdffbffc0f9870f9c

def z502 : W := mkw 0x31017fbf88931480 0x78c405fefe224c52 0x03003fff80031ce0 0x7c0c00fffe000c73

def z503 : W := mkw 0x01ffffb7dc025013 0xfc07fffedf700940 0xfffffffff8036001 0x7fffffffffe00d80

def z504 : W := mkw 0xc00002407f6ad830 0x0700000901fdab60 0x020000007ffff83f 0x8008000001ffffe0

def z505 : W := mkw 0x4800004002048964 0x0120000100081225 0x00000000060c18d4 0x0000000000183063

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000001800018d4 0x2280000006000063

def z507 : W := mkw 0x480042c2de06d974 0x1520010b0b781b65 0xf614c1c7fe4fffff 0xf7d853071ff93fff

def z508 : W := mkw 0x0000020008021000 0x0000000800200840 0x03000e0000031820 0x2c0c003800000c60

def z509 : W := mkw 0x00b0290054004012 0x4402c0a401500100 0x00c0300060006000 0x000300c001800180

def z510 : W := mkw 0x01fef9a680000003 0xf807fbe69a000000 0xf4d4f1c780000000 0x77d353c71e000000

def z511 : W := mkw 0x204c000821c12609 0x0081300020870498 0x5ecc000061c3e72b 0x817b300001870f9c

def z512 : W := mkw 0x0000000000000000 0x0000000000000000 0x1004000600408302 0x104010001801020c

def z513 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x1ed031c06603e023 0x9c7b40c701980f80

def z514 : W := mkw 0x40b06bc2de02d832 0x5502c1af0b780b60 0xfff4ffc7fe03f827 0xffffd3ff1ff80fe0

def z515 : W := mkw 0x284c50aea1c5274d 0x30a13142ba87149d 0xdeccf03fe1cfe7fb 0xdf7b33c0ff873f9f

def z516 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3999b30001 0x6fbcac38e666cc00

def z517 : W := mkw 0x61ffffffffc3fe3b 0xfd87ffffffff0ff8 0xffffffffffc3ff2f 0xffffffffffff0ffc

def z518 : W := mkw 0x0000408280000000 0x100001020a000000 0x1014c1c600000000 0x1040530718000000

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x2400000000001824 0xa490000000000060

def z520 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x3cf4c0007e4c0007 0x80f3d30001f93000

def z521 : W := mkw 0x304d163d29d33689 0x20c13458f4a74cda 0x5fef3e3e79f3e72b 0xdd7fbcf8f9e7cf9c

def z522 : W := mkw 0x4800004002048964 0x0120000100081225 0x54040006064c9ffe 0xd55010001819327f

def z523 : W := mkw 0x70b02b485e93dcb2 0x45c2c0ad217a4f72 0x3ff03fc07fb3fcff 0xbcffc0ff01fecff3

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x540400000040000a 0x8150100000010000

def z525 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfecc303fe1c3ffff 0xfffb30c0ff870fff

def z526 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x23303fc01e03f824 0x3c8cc0ff00780fe0

def z527 : W := mkw 0x00fe800054000003 0x8403fa0001500000 0xfcffc0007e000007 0x83f3ff0001f80000

def z528 : W := mkw 0x680040ca82858d64 0x11a001032a0a1635 0xfe1cc1ff87cf9fff 0xfff87307fe1f3e7f

def z529 : W := mkw 0x304d143d21d12689 0x20c13450f487449a 0xdecf303fe1f3e7fb 0xdf7b3cc0ff87cf9f

def z530 : W := mkw 0x304d163d29d33689 0x20c13458f4a74cda 0x5fcc3e3fe1c3ffeb 0xfd7f30f8ff870fff

def z531 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xc8efc00079fc0019 0x0323bf0001e7f000

def z532 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x10d031c000000000 0x104340c700000000

def z533 : W := mkw 0xb0fe82087dfb1483 0x86c3fa0821f7ec52 0xfeffc0007fff1cff 0x83fbff0001fffc73

def z534 : W := mkw 0x40b0294002008822 0x4102c0a500080220 0x3df03fc006009826 0xbcf7c0ff00180260

def z535 : W := mkw 0xb00106197dfb1480 0x06c0041865f7ec52 0xef2b0e39ffff1cff 0xefbcac38e7fffc73

def z536 : W := mkw 0x48b069c2d604c976 0x5522c1a70b581325 0x10d4f1c6664ce302 0x104353c71999338c

def z537 : W := mkw 0x70012f590a93dcb0 0x41c004bd642a4f72 0xef2b3ff999b3fcfd 0xffbcacffe666cff3

def z538 : W := mkw 0x814fd4b7a1680001 0xba053f52de85a000 0xc00fc03f81fc0018 0x43003f00fe07f000

def z539 : W := mkw 0x480040c282048964 0x112001030a081225 0x0010c1c0060c0000 0x0000430700183000

def z540 : W := mkw 0x004c102421402209 0x2001304090850088 0x5ccc300661c0e30b 0x917330c01987038c

def z541 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xa3230e0199b31cfd 0xa28c8c380666cc73

def z542 : W := mkw 0x314fd6bf88931481 0xb8c53f5afe224c52 0xef2fce3f99b31cfd 0xefbcbf38fe66cc73

def z543 : W := mkw 0xf0ffaf597ffbdcb3 0xc7c3febd65ffef72 0xfffffff9fffffcff 0xffffffffe7fffff3

def z544 : W := mkw 0x4000004002008820 0x0100000100080220 0x3ed031c06603f827 0xbcfb40c701980fe0

def z545 : W := mkw 0x0800408280040144 0x102001020a001005 0x00000007800007c0 0x400000001e00001f

def z546 : W := mkw 0x40b0004056008822 0x0502c00101580220 0x3cf001c07e009827 0xb4f3c00701f80260

def z547 : W := mkw 0x41b17ff7de02d832 0x7d06c5ffdf780b60 0x3ff03ffffe03f827 0xfcffc0fffff80fe0

def z548 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0x0010c000060c0000 0x0000430000183000

def z549 : W := mkw 0x004d143500000001 0x20013450d4000000 0xfdef3e3f80000000 0x7ff7bcf8fe000000

def z550 : W := mkw 0x004c000021400001 0x0001300000850000 0xfcef000079f0001f 0x83f3bc0001e7c000

def z551 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xbcf3c0007e3c0017 0x82f3cf0001f8f000

def z552 : W := mkw 0x30b106195c931482 0x04c2c41865724c52 0xfffb0e39ffb31cff 0xefffec38e7fecc73

def z553 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0xef2b0fff99b39ffd 0xffbcac3ffe66ce7f

def z554 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e00000000030021 0x8c38000000000c00

def z555 : W := mkw 0x484c40c2a3448965 0x112131030a8d1225 0xfcdcc1c7e7cc9fff 0xf7f373071f9f327f

def z556 : W := mkw 0x90b386115c3a1082 0x8642ce184570e842 0xa133ce019e3c18d4 0x2284cf380678f063

def z557 : W := mkw 0x21ffbd3d21c1260b 0xe887fef4f4870498 0x0beb3e3861836001 0x082facf8e1860d80

def z558 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x3df03fc06600e002 0x3cf7c0ff01980380

def z559 : W := mkw 0x204c102c00812609 0x20813040b0020498 0x5ecc303e0003e720 0x5d7b30c0f8000f9c

def z560 : W := mkw 0x41b3efd3de02d832 0xdd06cfbf4f780b60 0xa133cfc19e001804 0x2284cf3f06780060

def z561 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x4f080e3981831ce9 0xed3c2038e6060c73

def z562 : W := mkw 0x48006bc28a06d974 0x512001af0a281b65 0x03003fc78003ffe0 0x7c0c00ff1e000fff

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x341001c000000000 0x34d0400700000000

def z564 : W := mkw 0xc0feab407f6ad833 0xc703faad01fdab60 0xfdffcfc07ffc181f 0xa3f7ff3f01fff060

def z565 : W := mkw 0x80feab007d6a5013 0xc603faac01f5a940 0xfffffe007fff601f 0x8bfffff801fffd80

def z566 : W := mkw 0x804c000075680001 0x0601300001d5a000 0x5ccc00007ffc001f 0x8173300001fff000

def z567 : W := mkw 0xb0ff86197dfb1483 0x86c3fe1865f7ec52 0xefeb0e39f9b31cfd 0xefbfac38e7e6cc73

def z568 : W := mkw 0x3001163d08933688 0x20c00458f4224cda 0xef2b3e3f99b3fffd 0xffbcacf8fe66cfff

def z569 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xe7000e3980031cfc 0xef9c0038e6000c73

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000064c001e 0x8000000000193000

def z571 : W := mkw 0x480040c282048964 0x112001030a081225 0x5414c1c6064c872a 0xd55053071819321c

def z572 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x420c303e01c3e728 0x5d0830c0f8070f9c

def z573 : W := mkw 0x70b12f595e93dcb2 0x45c2c4bd657a4f72 0xef3b0ff99fb31cfd 0xefbcec3fe67ecc73

def z574 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc00019b0001d 0x83f3ff000066c000

def z575 : W := mkw 0x01ffbf355c025013 0xec07fefcd5700940 0x0beb3e3878036001 0x082facf8e1e00d80

def z576 : W := mkw 0x0000000054000000 0x0400000001500000 0x000000007e000007 0x8000000001f80000

def z577 : W := mkw 0x48b069c2d604c976 0x5522c1a70b581325 0xf4d4f1c7e64cfffe 0xf7d353c71f9933ff

def z578 : W := mkw 0x48fec0c282048967 0x9123fb030a081225 0xfcffc1c7864c9ffe 0xf7f3ff071e19327f

def z579 : W := mkw 0x480040c282048964 0x112001030a081225 0x000001c7864c9ffe 0xf40000071e19327f

def z580 : W := mkw 0x40fc3b647f42fa3b 0x6503f0ed91fd0be8 0x3ff43fc67e43fb27 0xbcffd0ff19f90fec

def z581 : W := mkw 0xc0fea9407768c833 0xc703faa501dda320 0xfcfff1c07ffce01f 0x93f3ffc701fff380

def z582 : W := mkw 0x0000408280000000 0x100001020a000000 0xf414c1c78040872a 0xf7d053071e01021c

def z583 : W := mkw 0x004c102421402209 0x2001304090850088 0x5ccc303e6040e302 0x5d7330c0f981038c

def z584 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xc20b003999b31cfd 0xc3082c00e666cc73

def z585 : W := mkw 0x41fffdf7d600c833 0xfd07fff7df580320 0xfdffffffe600e002 0x7ff7ffffff980380

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0xf414c001864c1cfe 0xe7d0530006193073

def z587 : W := mkw 0x79ffffff8a979de7 0xf9e7fffffe2a5e77 0xffffffff9fff9fff 0xfffffffffe7ffe7f

def z588 : W := mkw 0x4800004002048964 0x0120000100081225 0x00000000064c8302 0x000000000019320c

def z589 : W := mkw 0x81ffd4b7f5680003 0xbe07ff52dfd5a000 0xfcffc03ffffc001f 0xc3f3ff00fffff000

def z590 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x35300fc01e009826 0xb4d4c03f00780260

def z591 : W := mkw 0x00b0000054000002 0x0402c00001500000 0x08e0000078000001 0x0023800001e00000

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004c000004c0018 0x0300130000013000

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x5404000600000000 0x5550100018000000

def z594 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x08eb00007ffc001f 0x8023ac0001fff000

def z595 : W := mkw 0x8000000075680000 0x0600000001d5a000 0xf414c0007ffc001f 0x83d0530001fff000

def z596 : W := mkw 0x0000102400002208 0x2000004090000088 0x000030060000e300 0x100000c01800038c

def z597 : W := mkw 0x804e800021680001 0x82013a000085a000 0x0004c000004c0000 0x0000130000013000

def z598 : W := mkw 0x1001061108121080 0x0040041844204842 0x01000e01800018c0 0x2004003806000063

def z599 : W := mkw 0x4000004002008820 0x0100000100080220 0x101001c006008002 0x1040400700180200

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x2d200e0000000000 0x2cb4803800000000

def z601 : W := mkw 0x680050ee8285af6c 0x31a00143ba0a16bd 0x020031ff8003ffe0 0x7c0800c7fe000fff

def z602 : W := mkw 0x71ffffffde93dcb3 0xfdc7ffffff7a4f72 0xffffffffffb3fcff 0xfffffffffffecff3

def z603 : W := mkw 0x01016d9380000000 0x580405b64e000000 0x01000fc180000000 0x2004003f06000000

def z604 : W := mkw 0x4000004002008820 0x0100000100080220 0xf41001c186009cfe 0xf7d0400706180273

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x1014c000064c0002 0x0040530000193000

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000019b0001d 0x800000000066c000

def z607 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x01200e0018000000 0x0004803800600000

def z608 : W := mkw 0x1001061108121080 0x0040041844204842 0xed2b0e0199b018dd 0xa3b4ac380666c063

def z609 : W := mkw 0x01ffd4b780000003 0xb807ff52de000000 0xfcffc03f80000000 0x43f3ff00fe000000

def z610 : W := mkw 0x21fffdbfa1c1260b 0xf887fff6fe870498 0xfdffffff81c00708 0x7ff7fffffe07001c

def z611 : W := mkw 0xc8b2c0c2d62c8966 0x9722cb030b58b225 0xa033c1c19e3c18d4 0x2280cf070678f063

def z612 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x001001c006000000 0x0000400700180000

def z613 : W := mkw 0x004c000021400001 0x0001300000850000 0xfcdcc00067cc001f 0x83f37300019f3000

def z614 : W := mkw 0x604c3b6c2bc3fe39 0x618130edb0af0ff8 0x5fcc3ffe61c3ff2b 0xfd7f30fff9870ffc

def z615 : W := mkw 0x00b0698280000002 0x5002c1a60a000000 0xfdf4ffc780000000 0x7ff7d3ff1e000000

def z616 : W := mkw 0x0001041100000000 0x0000041044000000 0xa1230e0180000000 0x22848c3806000000

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0xec2b000000000000 0x03b0ac0000000000

def z618 : W := mkw 0x314fd4bf80910481 0xb8c53f52fe024412 0xc00fc03f81b004d8 0x43003f00fe06c013

def z619 : W := mkw 0x40b002405e02d832 0x0502c00901780b60 0x3ef000007e03f827 0x80fbc00001f80fe0

def z620 : W := mkw 0x01ffed9380000003 0xd807ffb64e000000 0xfdffcfc180000000 0x23f7ff3f06000000

def z621 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xf4d4c000664c001e 0x83d3530001993000

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c08000001800009 0x8130200000060000

def z623 : W := mkw 0x50b12f515e12d8b2 0x4542c4bd45784b62 0xbff33fc1fe33f8f7 0xbeffccff07f8cfe3

def z624 : W := mkw 0x49fffdf782048967 0xf927fff7de081225 0xfdffffff80009fe0 0x7ff7fffffe00027f

def z625 : W := mkw 0x00ff841100000003 0x8003fe1044000000 0xfdffce3980000000 0x6ff7ff38e6000000

def z626 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3df03fc01e001804 0x3cf7c0ff00780060

def z627 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x0008003801800000 0x00002000e0060000

def z628 : W := mkw 0xc8b2c0c2d62c8966 0x9722cb030b58b225 0xf437c1c79e7c9ffe 0xf7d0df071e79f27f

def z629 : W := mkw 0x480040c282048964 0x112001030a081225 0xc004c1c7804c9ff8 0x770013071e01327f

def z630 : W := mkw 0xc0fea9407768c833 0xc703faa501dda320 0x10d4f1c0664ce002 0x104353c701993380

def z631 : W := mkw 0x480040c282048964 0x112001030a081225 0x1014c1c6064c9ffe 0x904053071819327f

def z632 : W := mkw 0x30b12f1908931482 0x40c2c4bc64224c52 0xfffb3ff999b31cfd 0xffffecffe666cc73

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x082b000019b00001 0x0020ac000066c000

def z634 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x21300fc000000000 0x2084c03f00000000

def z635 : W := mkw 0x80b0000075680002 0x0602c00001d5a000 0x3cf000007ffc001f 0x80f3c00001fff000

def z636 : W := mkw 0x49fffdf782048967 0xf927fff7de081225 0xfdffffff860c18d4 0x7ff7fffffe183063

def z637 : W := mkw 0x480040c282048964 0x112001030a081225 0xd014c1c7864c87da 0x534053071e19321f

def z638 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xc30b0e3981b31cf8 0x6f0c2c38e606cc73

def z639 : W := mkw 0x204c122c29c33609 0x20813048b0a70cd8 0x7fec3e3e79c3ff2f 0xfdffb0f8f9e70ffc

def z640 : W := mkw 0x484c50e682048965 0x312131439a081225 0xfcdcf1ff864c9ffe 0xfff373c7fe19327f

def z641 : W := mkw 0x41fefbe6de02d833 0xfd07fbef9b780b60 0x3ff4ffc67e03f827 0xbcffd3ff19f80fe0

def z642 : W := mkw 0x214fd4bfa1c12609 0xb8853f52fe870498 0xdecff03fe1c3e72b 0xdf7b3fc0ff870f9c

def z643 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x0000003e00000700 0x40000000f800001c

def z644 : W := mkw 0x0000000021402208 0x0000000000850088 0x000000006040e302 0x000000000181038c

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x10c030006000e002 0x104300c001800380

def z646 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x0be03e007e03f827 0x882f80f801f80fe0

def z647 : W := mkw 0xb0ff963d7dfb368b 0xa6c3fe58f5f7ecda 0xfffffe3fffffffff 0xfffffff8ffffffff

def z648 : W := mkw 0x004c000021400001 0x0001300000850000 0x400c000001c00008 0x0100300000070000

def z649 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x1fe03e007803e023 0x9c7f80f801e00f80

def z650 : W := mkw 0x4000004002008820 0x0100000100080220 0xf414c1c0064c983e 0xb7d0530700193260

def z651 : W := mkw 0x49b3edd382048966 0xd926cfb74e081225 0xa133cfc1860c18d4 0x2284cf3f06183063

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c08003800000000 0x4d302000e0000000

def z653 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xec3bc0001fbc001d 0x83b0ef00007ef000

def z654 : W := mkw 0x81fef9a6f5680003 0xfe07fbe69bd5a000 0xfcfff1c67ffc001f 0x93f3ffc719fff000

def z655 : W := mkw 0x49017df782048964 0x792405f7de081225 0x01003fff80009fe0 0x7c0400fffe00027f

def z656 : W := mkw 0x480042c28a069964 0x1120010b0a281a65 0xff34cfc79e4f9fff 0xfffcd33f1e793e7f

def z657 : W := mkw 0x49fffdf782048967 0xf927fff7de081225 0xfdffffff864c8302 0x7ff7fffffe19320c

def z658 : W := mkw 0x69fffdffa3c5af6f 0xf9a7fff7fe8f16bd 0xffffffffe7cfffff 0xffffffffff9f3fff

def z659 : W := mkw 0x400002400a029820 0x0100000900280a60 0x3f300fc01e039827 0xbcfcc03f00780e60

def z660 : W := mkw 0x480144d382048964 0x112005134e081225 0xfd3fcfff864c9ffe 0xfff4ff3ffe19327f

def z661 : W := mkw 0x8000000075680000 0x0600000001d5a000 0x00000000664c0002 0x0000000001993000

def z662 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ccc003e61c0070b 0xc1733000f987001c

def z663 : W := mkw 0x40fc3b645e02d833 0x6503f0ed91780b60 0x7ffc3ffe7e03f827 0xfdfff0fff9f80fe0

def z664 : W := mkw 0x004c50a680000001 0x300131429a000000 0xfcdcf1ff80000000 0x7ff373c7fe000000

def z665 : W := mkw 0x41b3efd3de02d832 0xdd06cfbf4f780b60 0xbff3ffc1fe03f827 0xbeffcfff07f80fe0

def z666 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0xef3bcff99fbf1cfd 0xefbcef3fe67efc73

def z667 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c6064c831e 0x93d053071819320c

def z668 : W := mkw 0x094fd4b780040145 0xb8253f52de001005 0xc00fc03f804c07d8 0x43003f00fe01301f

def z669 : W := mkw 0x41fffdf782008823 0xf907fff7de080220 0xfdffffff86009826 0xfff7fffffe180260

def z670 : W := mkw 0x41fffff78a02d833 0xf907ffffde280b60 0xffffffff8003f820 0x7ffffffffe000fe0

def z671 : W := mkw 0x8000000054280000 0x060000000150a000 0x000000001e3c0014 0x000000000078f000

def z672 : W := mkw 0x304d163d29d33689 0x20c13458f4a74cda 0x0beb3e3879b36001 0x082facf8e1e6cd80

def z673 : W := mkw 0x31ffffbf88931483 0xf8c7fffefe224c52 0xffffffff80031ce0 0x7ffffffffe000c73

def z674 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x2f300fc01e031825 0xacbcc03f00780c60

def z675 : W := mkw 0x4000004002008820 0x0100000100080220 0x000001c000009820 0x3400000700000260

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004000600400708 0x410010001801001c

def z677 : W := mkw 0x48b06bc2de06d976 0x5522c1af0b781b65 0xbff0ffc1fe0ff8f7 0xbeffc3ff07f83fe3

def z678 : W := mkw 0x21fffdbf80810403 0xf887fff6fe020410 0xffffffff81830429 0xfffffffffe060c10

def z679 : W := mkw 0x304d163d29d33689 0x20c13458f4a74cda 0xefeb3e39f9b37cfd 0xefbfacf8e7e6cdf3

def z680 : W := mkw 0x81ffed93f5680003 0xde07ffb64fd5a000 0xfdffcfc1fffc001f 0xa3f7ff3f07fff000

def z681 : W := mkw 0x20fc3b2c7dc3761b 0x6483f0ecb1f70dd8 0x0be83e3879836001 0x082fa0f8e1e60d80

def z682 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x2f200e3998031ce5 0xecbc8038e6600c73

def z683 : W := mkw 0x00b002005c021002 0x0402c00801700840 0x3ff00e007e031827 0xacffc03801f80c60

def z684 : W := mkw 0xb0ff86197dfb1483 0x86c3fe1865f7ec52 0x0beb0e3879b30001 0x082fac38e1e6cc00

def z685 : W := mkw 0x304c122c29d33689 0x20c13048b0a74cda 0x5ecc303e79f3ffff 0xdd7b30c0f9e7cfff

def z686 : W := mkw 0x004c000021400001 0x0001300000850000 0x5ecc300061c3e02b 0x9d7b30c001870f80

def z687 : W := mkw 0x480040c282048964 0x112001030a081225 0xe40001c780009ffc 0xf79000071e00027f

def z688 : W := mkw 0x8000000021680000 0x020000000085a000 0x0000000001fc0018 0x000000000007f000

def z689 : W := mkw 0x3000020808931480 0x00c0000820224c52 0x0200000019b30001 0x000800000066cc00

def z690 : W := mkw 0x304d163d29d33689 0x20c13458f4a74cda 0xef2f0e3f99f31ffd 0xefbcbc38fe67cc7f

def z691 : W := mkw 0x48b06bc2de06d976 0x5522c1af0b781b65 0xf534cfc79e4c9ffe 0xf7d4d33f1e79327f

def z692 : W := mkw 0xe8fed0eef7edaf6f 0xb7a3fb43bbdfb6bd 0xfefff1ffffffffff 0xfffbffc7ffffffff

def z693 : W := mkw 0x40b12f515e02d832 0x4502c4bd45780b60 0xfffb3ff9fe03f827 0xffffecffe7f80fe0

def z694 : W := mkw 0x780106590a979de4 0x01e00419642a5e77 0xef2b0e399fff9fff 0xefbcac38e67ffe7f

def z695 : W := mkw 0x3001469b88931480 0x10c0051a6e224c52 0xff3fcfff99b31cfd 0xfffcff3ffe66cc73

def z696 : W := mkw 0x01fef9a680000003 0xf807fbe69a000000 0x3df4ffc600000000 0x3cf7d3ff18000000

def z697 : W := mkw 0xc8fe8040776c8967 0x8723fa0101ddb225 0xfcffc0007ffc9fff 0x83f3ff0001fff27f

def z698 : W := mkw 0x80ff841175680003 0x8603fe1045d5a000 0xfdffce39fffc001f 0xeff7ff38e7fff000

def z699 : W := mkw 0x400040c282008820 0x110001030a080220 0xf414c1c786009826 0xf7d053071e180260

def z700 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xb0f7c0007e7c0016 0x02c3df0001f9f000

def z701 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x5cef000079f0000b 0x8173bc0001e7c000

def z702 : W := mkw 0xc8000040776c8964 0x0720000101ddb225 0x000000007ffc9fff 0x8000000001fff27f

def z703 : W := mkw 0x2000000800810400 0x0080000020020410 0x0200003800030420 0x4c080000e0000c10

def z704 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x4ec8303861836429 0xcd3b20c0e1860d90

def z705 : W := mkw 0x480040c282048964 0x112001030a081225 0xc004c007864c9ffe 0xc30013001e19327f

def z706 : W := mkw 0x49fef9e682048967 0xf927fbe79a081225 0x10d4f1c6064c8302 0x104353c71819320c

def z707 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xefeb3e39f9b37cfd 0xefbfacf8e7e6cdf3

def z708 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0xf51fffff80000000 0x7fd47ffffe000000

def z709 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0x1b3fcffe1fff8303 0x186cff3ff87ffe0c

def z710 : W := mkw 0x0000290000000000 0x400000a400000000 0x1fc03fc06003e023 0xbc7f00ff01800f80

def z711 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ffb3fc07fb3f827 0xbcffecff01fecfe0

def z712 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1ec8303e6183e723 0xdc7b20c0f9860f9c

def z713 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x2ff03fc07e037825 0xacbfc0ff01f80de0

def z714 : W := mkw 0x81fffdb7d4280003 0xfe07fff6df50a000 0xfdfffffffe3c0017 0xfff7fffffff8f000

def z715 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2f0e3f99f31ffd 0xefbcbc38fe67cc7f

def z716 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xbcfbc0007fbc0017 0x82f3ef0001fef000

def z717 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff3fce3999b31cfd 0xeffcff38e666cc73

def z718 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80001824 0xfff7fffffe000060

def z719 : W := mkw 0x214fd4bfa1c12609 0xb8853f52fe870498 0xc00fc03f81800000 0x43003f00fe060000

def z720 : W := mkw 0x70b002485e93dcb2 0x05c2c009217a4f72 0xfefb00007fb3fcff 0x83fbec0001fecff3

def z721 : W := mkw 0x204e902c21c12609 0xa0813a40b0870498 0xdecff03e61c3e72b 0xdf7b3fc0f9870f9c

def z722 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3f99b39ffd 0xffbcac38fe66ce7f

def z723 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x7ff83ff87e03f827 0xfdffe0ffe1f80fe0

def z724 : W := mkw 0x70b12d595691ccb2 0x45c2c4b5655a4732 0xd0db31f9e7b0e4da 0x53436cc7e79ec393

def z725 : W := mkw 0x780002480a979de4 0x01e00009202a5e77 0x0200000000039fe0 0x0008000000000e7f

def z726 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xf5d4ffff80000000 0x7fd753fffe000000

def z727 : W := mkw 0x80b2800075680002 0x8602ca0001d5a000 0xa033c0001ffc001c 0x0280cf00007ff000

def z728 : W := mkw 0x480040c282048964 0x112001030a081225 0xf4d4f1c7e64cfffe 0xf7d353c71f9933ff

def z729 : W := mkw 0x01017db780000000 0x780405f6de000000 0x01003fff80008720 0x7c0400fffe00021c

def z730 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff4ffc1fe4ffcff 0xffffd3ff07f93ff3

def z731 : W := mkw 0x414fd6f7de02d831 0xbd053f5bdf780b60 0xc20fc03ffe03f827 0xc3083f00fff80fe0

def z732 : W := mkw 0xc0b2ab405e2ad832 0xc702caad0178ab60 0xfffbffc07fbff83f 0xbfffefff01feffe0

def z733 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0xfff03fc1fe4fffff 0xffffc0ff07f93fff

def z734 : W := mkw 0x81017db7f5680000 0x7e0405f6dfd5a000 0x01003ffffffc001f 0xfc0400fffffff000

def z735 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdffffff81c00008 0x7ff7fffffe070000

def z736 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3999f39fff 0xefbcac38e667ce7f

def z737 : W := mkw 0x00012d1100000000 0x400004b444000000 0x01003ff980000000 0x7c0400ffe6000000

def z738 : W := mkw 0x01fffdb7d4004013 0xfc07fff6df500100 0xfdffffffe0006000 0x7ff7ffffff800180

def z739 : W := mkw 0x01017db780000000 0x780405f6de000000 0x01003ffe00000000 0x180400fff8000000

def z740 : W := mkw 0xb0ff86197dfb1483 0x86c3fe1865f7ec52 0x13d4ce39e64f1ce2 0x6c4f5338e7993c73

def z741 : W := mkw 0x01b17db780000002 0x7806c5f6de000000 0x11d03fff80000000 0x7c4740fffe000000

def z742 : W := mkw 0xc04eab402b6ad831 0xc3013aad00adab60 0xc30fffc001fff838 0x3f0c3fff0007ffe0

def z743 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff99b01cfd 0xfff7fffffe66c073

def z744 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xed2b0e3999b01cdd 0xe3b4ac38e666c073

def z745 : W := mkw 0x314fd4bfa1d12689 0xb8c53f52fe87449a 0xc00fc03f81f007d8 0x43003f00fe07c01f

def z746 : W := mkw 0x004c102421402209 0x2001304090850088 0x5ecc303e6043e323 0xdd7b30c0f9810f8c

def z747 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xe32b0e3999b31cfc 0x6f8cac38e666cc73

def z748 : W := mkw 0x80feb92475680003 0xe603fae491d5a000 0xfdfffffe7ffc001f 0xfff7fffff9fff000

def z749 : W := mkw 0x08b06b82dc065156 0x5422c1ae0b701945 0xcbe4fe07f84f67d9 0x4b2f93f81fe13d9f

def z750 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xa12b0e3999b018d4 0x2284ac38e666c063

def z751 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e399fff1cff 0xefbcac38e67ffc73

def z752 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfeef303ff9f3ffff 0xfffbbcc0ffe7cfff

def z753 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x3cffc0007ffc0007 0x80f3ff0001fff000

def z754 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xa83bc0001fbc0015 0x02a0ef00007ef000

def z755 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x4acc303e61c3e72b 0xc92b30c0f9870f9c

def z756 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffffffc873f 0xfff7fffffffff21c

def z757 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xfcfbc0007fbc001f 0x83f3ef0001fef000

def z758 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xffffffffe043e72b 0xffffffffff810f9c

def z759 : W := mkw 0x804e800075680001 0x86013a0001d5a000 0xc00fc0001ffc001c 0x03003f00007ff000

def z760 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e03fcff 0xbcffc0ff01f80ff3

def z761 : W := mkw 0x684c50eea3c5af6d 0x31a13143ba8f16bd 0xaad8f1f9e78f78d5 0x2aab63c7e79e3de3

def z762 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xdecf303e61f3e73b 0xdf7b3cc0f987cf9c

def z763 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffe7fc001a 0x7ff7ffffff9ff000

def z764 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff81800009 0xfff7fffffe060000

def z765 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0xfdfb3ff980000000 0x7ff7ecffe6000000

def z766 : W := mkw 0x49ffbd7502048967 0xe927fef5d4081225 0x09eb3e38064c9ffe 0x8827acf8e019327f

def z767 : W := mkw 0x01b17db7d4000002 0x7c06c5f6df500000 0x3df03ffffe000007 0xfcf7c0fffff80000

def z768 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff81b00018 0x7ff7fffffe06c000

def z769 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdfffffe00000000 0x1bf7fffff8000000

def z770 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfecc303fe1c3e72b 0xfffb30c0ff870f9c

def z771 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xe52b0e3999b01cfc 0xe794ac38e666c073

def z772 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5edcf03e67cfe72b 0xdd7b73c0f99f3f9c

def z773 : W := mkw 0x80b2800075680002 0x8602ca0001d5a000 0xec3bc0007ffc001f 0x83b0ef0001fff000

def z774 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff03fc1fe03f827 0xffffc0ff07f80fe0

def z775 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x33f03fc07e03f826 0x3ccfc0ff01f80fe0

def z776 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x7eec303e79c3e72f 0xddfbb0c0f9e70f9c

def z777 : W := mkw 0x804e800021680001 0x82013a000085a000 0xfc3fc0001ffc001f 0x83f0ff00007ff000

def z778 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc1fe03fce7 0xfcffc0ff07f80ff3

def z779 : W := mkw 0x0000392400000000 0x600000e490000000 0x01003ffe00000000 0x7c0400fff8000000

def z780 : W := mkw 0x89fffdb7a16c0147 0xfa27fff6de85b005 0xfdffffff81fc07d8 0x7ff7fffffe07f01f

def z781 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfedcf03e61c3e72b 0xdffb73c0f9870f9c

def z782 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffcffffffc001f 0xe3f7ff3ffffff000

def z783 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1ec4303e6043e723 0xdc7b10c0f9810f9c

def z784 : W := mkw 0x2000000800810400 0x0080000020020410 0x5ecc303e61c3e72b 0xdd7b30c0f9870f9c

def z785 : W := mkw 0x600002480a83fe38 0x01800009202a0ff8 0x020000000003ff20 0x0008000000000ffc

def z786 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffffffc0003 0x7ff7fffffffff000

def z787 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdffffffe7cc001f 0xfff7ffffff9f3000

def z788 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0xed2fffff80000000 0x7fb4bffffe000000

def z789 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x09eb3ff980000000 0x2827acffe6000000

def z790 : W := mkw 0x480040c282048964 0x112001030a081225 0xec2b01c799b09ffd 0xf7b0ac071e66c27f

def z791 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x2bf03fc078036001 0x28afc0ff01e00d80

def z792 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3bf03fc07e03f807 0x38efc0ff01f80fe0

def z793 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x08fbc0007fbc0001 0x0023ef0001fef000

def z794 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x3dfffffe00000000 0x3cf7fffff8000000

def z795 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff43fc67e43fb27 0xbcffd0ff19f90fec

def z796 : W := mkw 0x01017db780000000 0x780405f6de000000 0x4d083fff80000000 0x7d3420fffe000000

def z797 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x03c03fc06003f820 0x3c0f00ff01800fe0

def z798 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffe7ffc001f 0x9bf7fffff9fff000

def z799 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffffbc0015 0x7ff7fffffffef000

def z800 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2fce3999ff1cfd 0xefbcbf38e667fc73

def z801 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff860c0014 0x7ff7fffffe183000

def z802 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x2f2b0e3999b31ce5 0xecbcac38e666cc73

def z803 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x13d03fc06603e002 0x184f40ff01980f80

def z804 : W := mkw 0x80fea90075684013 0xc603faa401d5a100 0xfcfff0007ffc601f 0x83f3ffc001fff180

def z805 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x7ff43fc07e43f82f 0xbdffd0ff01f90fe0

def z806 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xd8ffc0007ffc001b 0x0363ff0001fff000

def z807 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfffffffffe03e027 0xfffffffffff80f80

def z808 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3999b318d5 0x6fbcac38e666cc63

def z809 : W := mkw 0x014fd4b780000001 0xb8053f52de000000 0xfd3fcfff80000000 0x7ff4ff3ffe000000

def z810 : W := mkw 0x004c392400000001 0x600130e490000000 0x5dcc3ffe00000000 0x7d7730fff8000000

def z811 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0xfff4ffc07e4fffff 0xbfffd3ff01f93fff

def z812 : W := mkw 0x79017fff8a979de4 0x79e405fffe2a5e77 0x03003fff80039fe0 0x7c0c00fffe000e7f

def z813 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x13d03fc07e03f827 0xbc4f40ff01f80fe0

def z814 : W := mkw 0x01017db780000000 0x780405f6de000000 0x1fc03fffe003e023 0xfc7f00ffff800f80

def z815 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5acc303e61c3e70b 0x596b30c0f9870f9c

def z816 : W := mkw 0x00b02b0008021002 0x4002c0ac00200840 0x3ff03fc07803f827 0xbcffc0ff01e00fe0

def z817 : W := mkw 0x01017db780002208 0x780405f6de000088 0x01003fff8000e300 0x7c0400fffe00038c

def z818 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff99b00001 0x7ff7fffffe66c000

def z819 : W := mkw 0xa04e902c21e92609 0xa2813a40b087a498 0x5ecf303e61f3e72b 0xdd7b3cc0f987cf9c

def z820 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffff9fffc001f 0xabf7ffffe7fff000

def z821 : W := mkw 0x104d163529523289 0x20413458d4a548ca 0xb1e73e07f870fbd6 0x32c79cf81fe1c3ef

def z822 : W := mkw 0x480040c282048964 0x112001030a081225 0xfcd4f1c7864c9ffe 0xfff353c71e19327f

def z823 : W := mkw 0x480040c282048964 0x112001030a081225 0xd014c1c7864c9ffe 0xd34053071e19327f

def z824 : W := mkw 0xa0b2902c54a9260a 0xa682ca40b152a498 0xa233f03e1e3fe734 0x5e88cfc0f878ff9c

def z825 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xb1f7ffff80000000 0x7ec7dffffe000000

def z826 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e61c3ffff 0xdd7b30c0f9870fff

def z827 : W := mkw 0x01b17db780000002 0x7806c5f6de000000 0x09e03fff80000000 0x7c2780fffe000000

def z828 : W := mkw 0x81fffdb7f568220b 0xfe07fff6dfd5a088 0xfdffffffe64ce302 0x7ff7ffffff99338c

def z829 : W := mkw 0x00ffc49380000003 0x9003ff124e000000 0xfdffcfff80000000 0x7ff7ff3ffe000000

def z830 : W := mkw 0x214d54bfa1c12609 0x38853552fe870498 0x400c003f81c00708 0x41003000fe07001c

def z831 : W := mkw 0x81fffdb7d4280003 0xfe07fff6df50a000 0xfdffffff860c0000 0x7ff7fffffe183000

def z832 : W := mkw 0x014d7db780000001 0x780535f6de000000 0x410c3fff80000000 0x7d0430fffe000000

def z833 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x0bc03fc06003f821 0x3c2f00ff01800fe0

def z834 : W := mkw 0x20b0290821c1260a 0x4082c0a420870498 0x3ff03fc061c3e72b 0xbcffc0ff01870f9c

def z835 : W := mkw 0x21b3ed9ba1c1260a 0xd886cfb66e870498 0xa333cfc1e1c3e72b 0xa28ccf3f07870f9c

def z836 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffe64c001e 0xfff7ffffff993000

def z837 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0xc10fcfff80000000 0x63043f3ffe000000

def z838 : W := mkw 0x01017db780000000 0x780405f6de000000 0xc104ffff80000000 0x7f0413fffe000000

def z839 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc043f 0xc7f3ff0001fff010

def z840 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3999b318dd 0xabbcac38e666cc63

def z841 : W := mkw 0x81fffdb7a1680003 0xfa07fff6de85a000 0xfdffffff81b00000 0x7ff7fffffe06c000

def z842 : W := mkw 0xf8fe82487fff9de7 0x87e3fa0921fffe77 0xfeffc0007fff9fff 0x83fbff0001fffe7f

def z843 : W := mkw 0x00fe800000000003 0x8003fa0000000000 0xfcffc0001ffc001f 0x83f3ff00007ff000

def z844 : W := mkw 0xf80002487fff9de4 0x07e0000921fffe77 0x020000007fff9fff 0x8008000001fffe7f

def z845 : W := mkw 0x780002485e97ddf4 0x05e00009217a5f77 0x020000007fffffff 0x8008000001ffffff

def z846 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc001fffc001f 0xe7f3ff0007fff000

def z847 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x02c0303e6003e720 0x5c0b00c0f9800f9c

def z848 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff03fc07e03f83f 0xbfffc0ff01f80fe0

def z849 : W := mkw 0x8002800075680000 0x86000a0001d5a000 0x8003c0007ffc001f 0x82000f0001fff000

def z850 : W := mkw 0x80fe800054280003 0x8603fa000150a000 0xfcffc0001fbc001d 0x83f3ff00007ef000

def z851 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc06603f822 0x3cffc0ff01980fe0

def z852 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xf43fc0001ffc001e 0x83d0ff00007ff000

def z853 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x52cc303e61c3e72a 0x5d4b30c0f9870f9c

def z854 : W := mkw 0x01017db780000000 0x780405f6de000000 0x1dc03fff80000000 0x7c7700fffe000000

def z855 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfeffc0007fff003f 0x8ffbff0001fffc00

def z856 : W := mkw 0x80fea90075680003 0xc603faa401d5a000 0xfdfffe007ffc001f 0x8bf7fff801fff000

def z857 : W := mkw 0x004d54b780000001 0x30013552de000000 0xfdffffff80000000 0x7ff7fffffe000000

def z858 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffffe4c0007 0xfff7fffffff93000

def z859 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0xfdfffff800000000 0x3ff7ffffe0000000

def z860 : W := mkw 0x00b0290054000002 0x4402c0a401500000 0x3ff03fc07e03e027 0xbcffc0ff01f80f80

def z861 : W := mkw 0xc0b2ab405e2ad832 0xc702caad0178ab60 0x3ff33fc07e33f827 0xbcffccff01f8cfe0

def z862 : W := mkw 0x780002480a979de4 0x01e00009202a5e77 0x0200000019b39ffd 0x800800000066ce7f

def z863 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x1bf03fc078036001 0x186fc0ff01e00d80

def z864 : W := mkw 0x00fd3d3500000003 0x6003f4f4d4000000 0xfdff3fff80000000 0x7ff7fcfffe000000

def z865 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x7dff3ffe00000000 0x7df7fcfff8000000

def z866 : W := mkw 0x01017db780000000 0x780405f6de000000 0x35103fff80000000 0x7cd440fffe000000

def z867 : W := mkw 0x31fefbae88931483 0xf8c7fbeeba224c52 0x12d4f1c619b31cfd 0x904b53c71866cc73

def z868 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07fb3f83f 0xbcffc0ff01fecfe0

def z869 : W := mkw 0x294fd4bfa1c5274d 0xb8a53f52fe87149d 0xc00fc03f81cc07d8 0x43003f00fe07301f

def z870 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0xf537ffff80000000 0x7fd4dffffe000000

def z871 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xffffffc07ffff83f 0xbfffffff01ffffe0

def z872 : W := mkw 0xc8fec0c2f76c8967 0x9723fb030bddb225 0x08eb01c7f9b09fe1 0x7423ac071fe6c27f

def z873 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff9ffc001f 0xfff7fffffe7ff000

def z874 : W := mkw 0x81b3ed93d4280002 0xde06cfb64f50a000 0xed3bcff99fbc001d 0xefb4ef3fe67ef000

def z875 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xe9ffffff80000000 0x6ba7fffffe000000

def z876 : W := mkw 0x01fef9a680000003 0xf807fbe69a000000 0x7dfcfffe00000000 0x7df7f3fff8000000

def z877 : W := mkw 0x00fc79a680000003 0x7003f1e69a000000 0xfdfcffff80000000 0x7ff7f3fffe000000

def z878 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x7edc303e67c3e72f 0xddfb70c0f99f0f9c

def z879 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x1fd03fc06603f823 0xbc7f40ff01980fe0

def z880 : W := mkw 0x01017db780000000 0x780405f6de000000 0x01000fff80000000 0x6004003ffe000000

def z881 : W := mkw 0x01017db780000000 0x780405f6de000000 0x55043fff80000000 0x7d5410fffe000000

def z882 : W := mkw 0x01017db780000000 0x780405f6de000000 0xe5003fff80000000 0x7f9400fffe000000

def z883 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff804c0018 0x7ff7fffffe013000

def z884 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x12c0303e6003e722 0x5c4b00c0f9800f9c

def z885 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff804c87fa 0xfff7fffffe01321f

def z886 : W := mkw 0x01017db780000000 0x780405f6de000000 0x092b3fff80000000 0x7c24acfffe000000

def z887 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xa93bcff980000000 0x2aa4ef3fe6000000

def z888 : W := mkw 0x014d7db7a1402209 0x780535f6de850088 0x11c43fffe040e302 0x7c4710ffff81038c

def z889 : W := mkw 0x01017db780000000 0x780405f6de000000 0x01003fff80001ce0 0x7c0400fffe000073

def z890 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfdffffffe6000002 0x7ff7ffffff980000

def z891 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e79f3e73f 0xdd7b30c0f9e7cf9c

def z892 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xf53fcfff80000000 0x77d4ff3ffe000000

def z893 : W := mkw 0x01017db780000000 0x780405f6de000000 0x01003ff980000000 0x280400ffe6000000

def z894 : W := mkw 0x480040c282048964 0x112001030a081225 0xfcd4c1c7e64c9fff 0xf7f353071f99327f

def z895 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e037805 0x3cffc0ff01f80de0

def z896 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0067ffc001f 0xd7f3ff0019fff000

def z897 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffff9ffc001c 0x7ff7fffffe7ff000

def z898 : W := mkw 0x81fffdb7d4280003 0xfe07fff6df50a000 0xfdffffff9e7c001e 0xfff7fffffe79f000

def z899 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffffb00007 0xfff7fffffffec000

def z900 : W := mkw 0x0001449380000000 0x100005124e000000 0xf514cfff80000000 0x7fd4533ffe000000

def z901 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffffffc1cff 0xfff7fffffffff073

def z902 : W := mkw 0x01017db780000000 0x780405f6de000000 0x03003fff8003e020 0x7c0c00fffe000f80

def z903 : W := mkw 0x0001041100000000 0x0000041044000000 0xed2b0e3999b01cfd 0xefb4ac38e666c073

def z904 : W := mkw 0x700002487fd3feb8 0x05c0000921ff4ffa 0x020000007ff3ffff 0x8008000001ffcfff

def z905 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x13c03fc06003f822 0x3c4f00ff01800fe0

def z906 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0x010b3fff80000000 0x7c042cfffe000000

def z907 : W := mkw 0x8000000075680000 0x0600000001d5a000 0xfc3fc0007ffc001f 0x83f0ff0001fff000

def z908 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfeffc0007fffe03f 0x83fbff0001ffff80

def z909 : W := mkw 0x00012d1100000000 0x400004b444000000 0xed2b3ff980000000 0x7fb4acffe6000000

def z910 : W := mkw 0x0103fdb780000000 0xf8040ff6de000000 0x8103ffff80000000 0x7e040ffffe000000

def z911 : W := mkw 0x50b02b405e12d8b2 0x4542c0ad01784b62 0x3ff03fc07e33f8f7 0xbcffc0ff01f8cfe3

def z912 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcfff0007ffce01f 0x93f3ffc001fff380

def z913 : W := mkw 0x09017db780040144 0x782405f6de001005 0x01003fff800007c0 0x7c0400fffe00001f

def z914 : W := mkw 0x80fe80007568220b 0x8603fa0001d5a088 0xfcffc0007ffce31f 0x83f3ff0001fff38c

def z915 : W := mkw 0x01b17db780000002 0x7806c5f6de000000 0xfdfb3fff80000000 0x7ff7ecfffe000000

def z916 : W := mkw 0x00b12d1100000002 0x4002c4b444000000 0x3dfb3ff800000000 0x3cf7ecffe0000000

def z917 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xcb2b0e3999b31cf9 0x6f2cac38e666cc73

def z918 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0387ffc001f 0xcff3ff00e1fff000

def z919 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80408302 0x7ff7fffffe01020c

def z920 : W := mkw 0x89fffdb7f56c0147 0xfe27fff6dfd5b005 0xfdfffffffffc07df 0xfff7fffffffff01f

def z921 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0x0110ffff80000000 0x7c0443fffe000000

def z922 : W := mkw 0x700002480a93dcb0 0x01c00009202a4f72 0x020000000003fce0 0x0008000000000ff3

def z923 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x0bf03fc07e036001 0x082fc0ff01f80d80

def z924 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcfff0007ffc001f 0x9ff3ffc001fff000

def z925 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x2fe03fc07803f825 0xbcbf80ff01e00fe0

def z926 : W := mkw 0x0001041100000000 0x0000041044000000 0xfd3b0ff980000000 0x7ff4ec3fe6000000

def z927 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80409ffe 0xfff7fffffe01027f

def z928 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xec3fc0001ffc001d 0x83b0ff00007ff000

def z929 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e03e007 0x98ffc0ff01f80f80

def z930 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x01c03fff80000000 0x7c0700fffe000000

def z931 : W := mkw 0x01017db780000000 0x780405f6de000000 0x2d203fff80000000 0x7cb480fffe000000

def z932 : W := mkw 0x480040c282048964 0x112001030a081225 0xe014c1c7864c9ffc 0x778053071e19327f

def z933 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xd9ffffff80000000 0x5b67fffffe000000

def z934 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xe32b0e3999b31cfd 0xe38cac38e666cc73

def z935 : W := mkw 0x00fc392475400003 0x6403f0e491d50000 0x7dfc3ffe7fc0000f 0xfdf7f0fff9ff0000

def z936 : W := mkw 0x480040c282048964 0x112001030a081225 0xf41fc1c787fc9ffe 0xf7d07f071e1ff27f

def z937 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0xddcfffff80000000 0x7f773ffffe000000

def z938 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xe13bcff980000000 0x6384ef3fe6000000

def z939 : W := mkw 0x700002485e93dcb0 0x05c00009217a4f72 0x020000007fb3f827 0x8008000001fecfe0

def z940 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff3fce3f9fff9fff 0xfffcff38fe7ffe7f

def z941 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x1fe03fc07803f823 0xbc7f80ff01e00fe0

def z942 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xcb2b0e3999b31cfd 0xcb2cac38e666cc73

def z943 : W := mkw 0x81ffbd3575680003 0xee07fef4d5d5a000 0xfdfffff87ffc001f 0xbff7ffffe1fff000

def z944 : W := mkw 0x01017db780000000 0x780405f6de000000 0xed2b3fff99b0001d 0xffb4acfffe66c000

def z945 : W := mkw 0x014d7db780000001 0x780535f6de000000 0x11c43fff80000000 0x7c4710fffe000000

def z946 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007fbc0015 0x03f3ff0001fef000

def z947 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x5ddcffff80000000 0x7d7773fffe000000

def z948 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff2f0e3999f31cff 0xeffcbc38e667cc73

def z949 : W := mkw 0x480040c282048964 0x112001030a081225 0xe414c1c7864c1ffc 0xe79053071e19307f

def z950 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c7864c1fdc 0x77d053071e19307f

def z951 : W := mkw 0x01017db780000000 0x780405f6de000000 0x55043fff8040872a 0xfd5410fffe01021c

def z952 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x19ffffff80000000 0x7c67fffffe000000

def z953 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x09fbfff800000000 0x0827efffe0000000

def z954 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80400708 0x7ff7fffffe01001c

def z955 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffff9fc0019 0x7ff7ffffffe7f000

def z956 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xab2b0e3999b31cfd 0xaaacac38e666cc73

def z957 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff2b0e3999b39cff 0xfffcac38e666ce73

def z958 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x3ff03fc07e036007 0xbcffc0ff01f80d80

def z959 : W := mkw 0x01fffdb7a140220b 0xf807fff6de850088 0xffffffffe043e323 0xffffffffff810f8c

def z960 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc183f 0xa7f3ff0001fff060

def z961 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x09eb3ffe00000000 0x1827acfff8000000

def z962 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff804c0300 0x7ff7fffffe01300c

def z963 : W := mkw 0x3001061908933688 0x00c0041864224cda 0xef2b0e3999b3fffd 0xefbcac38e666cfff

def z964 : W := mkw 0x480040c282048964 0x112001030a081225 0xb014c1c7864c9ff6 0x76c053071e19327f

def z965 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xa9fbfff9ffbc0015 0x2aa7efffe7fef000

def z966 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x09eb3ff800000000 0x3c27acffe0000000

def z967 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xa9fbffff80000000 0x7ea7effffe000000

def z968 : W := mkw 0x81fffdb7a1680003 0xfa07fff6de85a000 0xfdffffff87fc001e 0xfff7fffffe1ff000

def z969 : W := mkw 0x80ffad1175680003 0xc603feb445d5a000 0xfdfffff9fffc001f 0xfff7ffffe7fff000

def z970 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff4ffc67e4fff3f 0xffffd3ff19f93ffc

def z971 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0067ffc831f 0x93f3ff0019fff20c

def z972 : W := mkw 0x78016fdb8a97ddf4 0x51e005bf6e2a5f77 0x03003fff8003ffe0 0x7c0c00fffe000fff

def z973 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff804c1ffc 0xfff7fffffe01307f

def z974 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfefff03e7fffe73f 0xdffbffc0f9ffff9c

def z975 : W := mkw 0x80b2800075680002 0x8602ca0001d5a000 0xbcf3c0007ffc001f 0x82f3cf0001fff000

def z976 : W := mkw 0x40b0294002008822 0x4102c0a500080220 0x3ff03fc06603f827 0xbcffc0ff01980fe0

def z977 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xbff33fc07e33f837 0xbeffccff01f8cfe0

def z978 : W := mkw 0x40b02b400a02d832 0x4102c0ad00280b60 0x3ff03fc06003f823 0xbcffc0ff01800fe0

def z979 : W := mkw 0x700002480a939ca0 0x01c00009202a4e72 0x020000001fb39cff 0x80080000007ece73

def z980 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffffe000e002 0x7ff7ffffff800380

def z981 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfffb3fc1ffb3fcff 0xffffecff07fecff3

def z982 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc873f 0x83f3ff0001fff21c

def z983 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x7df83ff800000000 0x7df7e0ffe0000000

def z984 : W := mkw 0xa04e902c21e92609 0xa2813a40b087a498 0x5eccf03e61cfe72b 0xdd7b33c0f9873f9c

def z985 : W := mkw 0x01b13d3500000002 0x6806c4f4d4000000 0x3df03ff800000000 0x3cf7c0ffe0000000

def z986 : W := mkw 0x480040c282048964 0x112001030a081225 0xfc1cc1c787cc9fff 0xf7f073071e1f327f

def z987 : W := mkw 0x700002485e93dcb0 0x05c00009217a4f72 0x020000001fb31cfd 0x80080000007ecc73

def z988 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1ecc303e61c3e323 0x9c7b30c0f9870f8c

def z989 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x12c4303e6043e302 0x184b10c0f9810f8c

def z990 : W := mkw 0x80b2800075680002 0x8602ca0001d5a000 0xf437c0007ffc001f 0x83d0df0001fff000

def z991 : W := mkw 0xa14fd4bfa1e92609 0xba853f52fe87a498 0xc00fc03f81fc0718 0x43003f00fe07f01c

def z992 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0xfcfff0067ffce73f 0xd7f3ffc019fff39c

def z993 : W := mkw 0x01016d9380000000 0x580405b64e000000 0x01000ff980000000 0x6c04003fe6000000

def z994 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffffe7c0016 0x7ff7fffffff9f000

def z995 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xb8ffc0007ffc0017 0x02e3ff0001fff000

def z996 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e39f9b3fcff 0xefbcac38e7e6cff3

def z997 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x4acc303e61c3e729 0x5d2b30c0f9870f9c

def z998 : W := mkw 0x480040c282048964 0x112001030a081225 0x1014c1c7864c9ffe 0xf44053071e19327f

def z999 : W := mkw 0x00b0000054000002 0x0402c00001500000 0xfcffc0007ffc001f 0x83f3ff0001fff000

def z1000 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xab2b0e3999b31cf5 0x6eacac38e666cc73

def z1001 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xd0dfc0007ffc001f 0x83437f0001fff000

def z1002 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c79ffc9fff 0xf7d053071e7ff27f

def z1003 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xdeccf03e61cfe73b 0xdf7b33c0f9873f9c

def z1004 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff2f0e3f99b31cfd 0xfffcbc38fe66cc73

def z1005 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0xed3bffff80000000 0x7fb4effffe000000

def z1006 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc0003 0x03f3ff0001fff000

def z1007 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc67e03ff27 0xfcffc0ff19f80ffc

def z1008 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xbff0ffc07e0ff837 0xbeffc3ff01f83fe0

def z1009 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfdffffffffb0001f 0xfff7fffffffec000

def z1010 : W := mkw 0xf0fe82487ffbdcb3 0x87c3fa0921ffef72 0xfeffc0007ffffcff 0x83fbff0001fffff3

def z1011 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xc8efc0007ffc001f 0x8323bf0001fff000

def z1012 : W := mkw 0xf00002487ffbdcb0 0x07c0000921ffef72 0x020000007ffffcff 0x8008000001fffff3

def z1013 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x0ac8303e6183e301 0x182b20c0f9860f8c

def z1014 : W := mkw 0x60fc02487fc3fe3b 0x0583f00921ff0ff8 0x7efc00007fc3ff2f 0x81fbf00001ff0ffc

def z1015 : W := mkw 0x01fffdb7a140220b 0xf807fff6de850088 0xfdffffffe040e72a 0xfff7ffffff81039c

def z1016 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5eef303e79f3e72b 0xdd7bbcc0f9e7cf9c

def z1017 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x7ff03fc07e03fc2f 0xfdffc0ff01f80ff0

def z1018 : W := mkw 0x0001449380000000 0x100005124e000000 0xfd3fcfff9ffc001f 0xfff4ff3ffe7ff000

def z1019 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x0be03fc07e03f827 0xbc2f80ff01f80fe0

def z1020 : W := mkw 0x60fc3b6c7fc3fe3b 0x6583f0edb1ff0ff8 0x613c0ffe1fc01f0c 0x6184f03ff87f007c

def z1021 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07803f821 0x3cffc0ff01e00fe0

def z1022 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff86000006 0xfff7fffffe180000

def z1023 : W := mkw 0x81fffdb7a1680003 0xfa07fff6de85a000 0xfdffffffe1fc001b 0xfff7ffffff87f000

def z1024 : W := mkw 0xc0b2ab405e2ad832 0xc702caad0178ab60 0x3ff0ffc07e0ff827 0xbcffc3ff01f83fe0

def z1025 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xe03bc0001fbc001c 0x0380ef00007ef000

def z1026 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xffffffffe0036001 0x7fffffffff800d80

def z1027 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x0ac0303e6003e721 0x5c2b00c0f9800f9c

def z1028 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef3bce399fbf1cfd 0xefbcef38e67efc73

def z1029 : W := mkw 0xe0fe82487febfe3b 0x8783fa0921ffaff8 0xfeffc0007fffff3f 0x83fbff0001fffffc

def z1030 : W := mkw 0x480040c282048964 0x112001030a081225 0xb014c1c7864c9ffe 0xb2c053071e19327f

def z1031 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0001ffc001c 0x03f3ff00007ff000

def z1032 : W := mkw 0xe00002487febfe38 0x0780000921ffaff8 0x020000007fffff3f 0x8008000001fffffc

def z1033 : W := mkw 0x58b16fd3de16d9f6 0x5562c5bf4f785b67 0xa133cfc19e3c18d4 0x2284cf3f0678f063

def z1034 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xa033c0001fbc001d 0x8280cf00007ef000

def z1035 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0x3ff03fc07e03ffe7 0xbcffc0ff01f80fff

def z1036 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xdecc303fe1c3e7fb 0xdf7b30c0ff870f9f

def z1037 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x56c4303e6043e72a 0xdd5b10c0f9810f9c

def z1038 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdffffffe1c0872b 0xfff7ffffff87021c

def z1039 : W := mkw 0x814ffdb7a1680001 0xfa053ff6de85a000 0xc10fffff81fc0018 0x7f043ffffe07f000

def z1040 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0xfcfff0007ffc601f 0x83f3ffc001fff180

def z1041 : W := mkw 0x40b029405600c832 0x4502c0a501580320 0x3ff03fc06603e023 0xbcffc0ff01980f80

def z1042 : W := mkw 0x81fffdb7f568220b 0xfe07fff6dfd5a088 0xfdfffffffffce31f 0xfff7fffffffff38c

def z1043 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0x01233fff80000000 0x7c048cfffe000000

def z1044 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffff9f0000b 0xfff7ffffffe7c000

def z1045 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff4ffc07e4ff827 0xbcffd3ff01f93fe0

def z1046 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e6043e722 0x5d7b30c0f9810f9c

def z1047 : W := mkw 0x780146db8a979de4 0x11e0051b6e2a5e77 0x03000ff980031ce0 0x6c0c003fe6000c73

def z1048 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e037807 0xa8ffc0ff01f80de0

def z1049 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80008720 0x7ff7fffffe00021c

def z1050 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0x11d4ffffe64c0002 0x7c4753ffff993000

def z1051 : W := mkw 0x80fea90075680003 0xc603faa401d5a000 0xfcfff1c07ffc001f 0x93f3ffc701fff000

def z1052 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff43fc7fe43ffff 0xffffd0ff1ff90fff

def z1053 : W := mkw 0x400002400a029820 0x0100000900280a60 0x3ff03fc07e03f827 0xbcffc0ff01f80fe0

def z1054 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdfffffff9b0001d 0xfff7ffffffe6c000

def z1055 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xb9ffffff80000000 0x3ae7fffffe000000

def z1056 : W := mkw 0x01fffdb7f5400003 0xfc07fff6dfd50000 0xfdffffffffc0000f 0xfff7ffffffff0000

def z1057 : W := mkw 0x00ffad1100000003 0xc003feb444000000 0xfdfffff980000000 0x7ff7ffffe6000000

def z1058 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x4ec8303e6183e729 0xdd3b20c0f9860f9c

def z1059 : W := mkw 0x80fea90075680003 0xc603faa401d5a000 0xffffffc07fffe03f 0xbfffffff01ffff80

def z1060 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfdfffffff8000001 0x7ff7ffffffe00000

def z1061 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xa03bc0001fbc0014 0x0280ef00007ef000

def z1062 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303fe1c3ffeb 0xfd7b30c0ff870fff

def z1063 : W := mkw 0x80ffc493f5680003 0x9603ff124fd5a000 0xfdffcffffffc001f 0xfff7ff3ffffff000

def z1064 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfdffffff9e000004 0x7ff7fffffe780000

def z1065 : W := mkw 0x014d7db7a1400001 0x780535f6de850000 0x5dcc3fffe1c0000b 0xfd7730ffff870000

def z1066 : W := mkw 0x80fe902475680003 0xa603fa4091d5a000 0xfefff03e7fffe03f 0xdffbffc0f9ffff80

def z1067 : W := mkw 0x680002487fc7ff7c 0x05a0000921ff1ffd 0x020000007fcfffff 0x8008000001ff3fff

def z1068 : W := mkw 0x81fffdb7d4280003 0xfe07fff6df50a000 0xfdffffff9fbc001d 0xfff7fffffe7ef000

def z1069 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x5def3fff80000000 0x7d77bcfffe000000

def z1070 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x0b2b0e3999b31cfd 0xec2cac38e666cc73

def z1071 : W := mkw 0x09017db780040144 0x782405f6de001005 0xc104ffff804c07d8 0x7f0413fffe01301f

def z1072 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdffffffe0400002 0x7ff7ffffff810000

def z1073 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0xfcfff03e7ffce31f 0xdff3ffc0f9fff38c

def z1074 : W := mkw 0x49b3efd3de06d976 0xdd26cfbf4f781b65 0xa133cfc19e0c18d4 0x2284cf3f06783063

def z1075 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x3df4ffff80000000 0x7cf7d3fffe000000

def z1076 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0x19fffffe7ffc0003 0x1867fffff9fff000

def z1077 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xecfbc0007fbc001d 0x83b3ef0001fef000

def z1078 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xe03fc0007ffc001f 0x8380ff0001fff000

def z1079 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0x3ff03fc07e0ff8f7 0xbcffc0ff01f83fe3

def z1080 : W := mkw 0x0001449380000000 0x100005124e000000 0x01000fff80000000 0x7c04003ffe000000

def z1081 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xedfbfff980000000 0x6fb7efffe6000000

def z1082 : W := mkw 0x00b0290000000002 0x4002c0a400000000 0x3ff03fc060036001 0x3cffc0ff01800d80

def z1083 : W := mkw 0x01016d9380000000 0x580405b64e000000 0xed2b0ff980000000 0x6fb4ac3fe6000000

def z1084 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0xfefff0067fffe33f 0x9ffbffc019ffff8c

def z1085 : W := mkw 0x01017db780000000 0x780405f6de000000 0xf514ffff864c001e 0xffd453fffe193000

def z1086 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0x3ff03fc07e4ffb27 0xbcffc0ff01f93fec

def z1087 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x0ac8303e61c3e72b 0xdc2b20c0f9870f9c

def z1088 : W := mkw 0x480040c282048964 0x112001030a081225 0x3414c1c7864c9fe6 0xf4d053071e19327f

def z1089 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xedeb3fff80000000 0x7fb7acfffe000000

def z1090 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfedcf03fe7cfffff 0xfffb73c0ff9f3fff

def z1091 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfdffce007ffc001f 0xaff7ff3801fff000

def z1092 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e67cfe73f 0xdd7b30c0f99f3f9c

def z1093 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b3e3999b3fcfd 0xffbcacf8e666cff3

def z1094 : W := mkw 0x00feb92400000003 0xe003fae490000000 0xfdfffffe00000000 0x7ff7fffff8000000

def z1095 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfefff0067fffe73f 0xdffbffc019ffff9c

def z1096 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xbff03fc1fe03f8f7 0xbeffc0ff07f80fe3

def z1097 : W := mkw 0x01017db780000000 0x780405f6de000000 0x1114ffff80000000 0x7c4453fffe000000

def z1098 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffffe0000003 0xfff7ffffff800000

def z1099 : W := mkw 0x81ffed93f5680003 0xde07ffb64fd5a000 0xfdffcff9fffc001f 0xeff7ff3fe7fff000

def z1100 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xaf2b0e3999b318f5 0xaebcac38e666cc63

def z1101 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfecc303e61c3e73f 0xdffb30c0f9870f9c

def z1102 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff864c873e 0xfff7fffffe19321c

def z1103 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x5ec8303e6183e72b 0xdd7b20c0f9860f9c

def z1104 : W := mkw 0x404c12645e02d831 0x2501304991780b60 0x5ecc303e7e03f827 0xdd7b30c0f9f80fe0

def z1105 : W := mkw 0x80fe90247568220b 0xa603fa4091d5a088 0xfcffc0067ffc031f 0x83f3ff0019fff00c

def z1106 : W := mkw 0x480040c282048964 0x112001030a081225 0xfc1cc1ff864c9ffe 0xfff07307fe19327f

def z1107 : W := mkw 0x780002480a979de4 0x01e00009202a5e77 0xfe3fc0001fff9fff 0x83f8ff00007ffe7f

def z1108 : W := mkw 0x01017db780000000 0x780405f6de000000 0xc10b3fff80000000 0x7f042cfffe000000

def z1109 : W := mkw 0x80b2800054280002 0x8602ca000150a000 0xfc3fc0001ffc001f 0x83f0ff00007ff000

def z1110 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x2bf03fc07e03f825 0x3cafc0ff01f80fe0

def z1111 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc001fffc04df 0xc3f3ff0007fff013

def z1112 : W := mkw 0x3000428a88931480 0x10c0010a2a224c52 0xf614c1c799b31cfd 0xf7d853071e66cc73

def z1113 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e61c3e303 0x5d7b30c0f9870f8c

def z1114 : W := mkw 0x01013d3500000000 0x680404f4d4000000 0x01003ff800000000 0x3c0400ffe0000000

def z1115 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xe13fffff80000000 0x7f84fffffe000000

def z1116 : W := mkw 0x480040c282048964 0x112001030a081225 0xf614f1c7864ffffe 0xffd853c71e193fff

def z1117 : W := mkw 0x01017db780000000 0x780405f6de000000 0xa110ffff80000000 0x7e8443fffe000000

def z1118 : W := mkw 0xc9fef9e6f76c8967 0xff27fbe79bddb225 0x10d4f1c6664c8302 0x104353c71999320c

def z1119 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xfdfbfff980000000 0x7ff7efffe6000000

def z1120 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0067ffc071f 0xc3f3ff0019fff01c

def z1121 : W := mkw 0x01fffdb7a140220b 0xf807fff6de850088 0xfdffffffe1c0e30b 0xfff7ffffff87038c

def z1122 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xf1ffffff80000000 0x73c7fffffe000000

def z1123 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80001ce0 0x7ff7fffffe000073

def z1124 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff800018d4 0x7ff7fffffe000063

def z1125 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xe13fcfff9ffc001c 0x6384ff3ffe7ff000

def z1126 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x0be03fc07803e001 0x182f80ff01e00f80

def z1127 : W := mkw 0x01fffdb78000220b 0xf807fff6de000088 0xfdffffff8000e300 0x7ff7fffffe00038c

def z1128 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x7ecc303e61c3ff2f 0xfdfb30c0f9870ffc

def z1129 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x1bf03fc07e03f823 0x3c6fc0ff01f80fe0

def z1130 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x18ffc0007ffc001f 0x8063ff0001fff000

def z1131 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xffffffffe1c3e02b 0xffffffffff870f80

def z1132 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e6183e721 0x5d7b30c0f9860f9c

def z1133 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x3ff03fc07803e023 0xbcffc0ff01e00f80

def z1134 : W := mkw 0x00b12d1154000002 0x4402c4b445500000 0xfdfb3ff9ffb0001f 0xfff7ecffe7fec000

def z1135 : W := mkw 0x600002485e83fe38 0x05800009217a0ff8 0x020000007e03ff27 0x8008000001f80ffc

def z1136 : W := mkw 0x480040c282048964 0x112001030a081225 0xd014c1c7864c9ffa 0x774053071e19327f

def z1137 : W := mkw 0x40b2ab405e02d832 0xc502caad01780b60 0xbff3ffc07e03f827 0xbeffcfff01f80fe0

def z1138 : W := mkw 0xa04c102c21e92609 0x22813040b087a498 0x5ecc303e61ffe73b 0xdd7b30c0f987ff9c

def z1139 : W := mkw 0x384d54bfa1d527cd 0x30e13552fe87549f 0xc00fc03f81fc07d8 0x43003f00fe07f01f

def z1140 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xa8fbc0007ffc001f 0x82a3ef0001fff000

def z1141 : W := mkw 0xa04e902c21e92609 0xa2813a40b087a498 0xfedff03e67ffe73f 0xdffb7fc0f99fff9c

def z1142 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xffffffff8003e020 0x7ffffffffe000f80

def z1143 : W := mkw 0x014d7db780000001 0x780535f6de000000 0xfddcffff80000000 0x7ff773fffe000000

def z1144 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff800004d8 0x7ff7fffffe000013

def z1145 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0x5cffc0007ffc000b 0x8173ff0001fff000

def z1146 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff3b0ff999b31cfd 0xfffcec3fe666cc73

def z1147 : W := mkw 0x600002482bc3fe38 0x0180000920af0ff8 0x0200000061c3ff2b 0x8008000001870ffc

def z1148 : W := mkw 0x80b2800075680002 0x8602ca0001d5a000 0xa033c0007fbc0015 0x0280cf0001fef000

def z1149 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0x09eb3ffff9b00001 0x7c27acffffe6c000

def z1150 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff800c00d0 0x7ff7fffffe003003

def z1151 : W := mkw 0x780002480a979de4 0x01e00009202a5e77 0x02000000064f9ffe 0x8008000000193e7f

def z1152 : W := mkw 0x01fffdb7a140220b 0xf807fff6de850088 0xfdffffff80400300 0x7ff7fffffe01000c

def z1153 : W := mkw 0x11fffdb780100083 0xf847fff6de004002 0xfdffffff803000d0 0x7ff7fffffe00c003

def z1154 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x12c4303e61c3e72b 0xdc4b10c0f9870f9c

def z1155 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfefff0007fff601f 0x8bfbffc001fffd80

def z1156 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xffffffffffffe03f 0xffffffffffffff80

def z1157 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x29fb3ff800000000 0x28a7ecffe0000000

def z1158 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x5ecc303e61c3e30b 0x997b30c0f9870f8c

def z1159 : W := mkw 0x81b3fdb7d4280002 0xfe06cff6df50a000 0xa133ffff9e3c0014 0x7e84cffffe78f000

def z1160 : W := mkw 0x80fe902475680003 0xa603fa4091d5a000 0xfcfff03e7ffc873f 0xdff3ffc0f9fff21c

def z1161 : W := mkw 0x00fc392400000003 0x6003f0e490000000 0x3df83ff800000000 0x3cf7e0ffe0000000

def z1162 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xed2b0e3999b01cdc 0x6fb4ac38e666c073

def z1163 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x3ff03fc078037825 0xbcffc0ff01e00de0

def z1164 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0xa133fff980000000 0x2a84cfffe6000000

def z1165 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x7ff83fc07f83f82f 0xbdffe0ff01fe0fe0

def z1166 : W := mkw 0x81fffdb7a1680003 0xfa07fff6de85a000 0xfdffffff99fc001d 0xfff7fffffe67f000

def z1167 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x7edc31fe61c3e72b 0xfdfb70c7f9870f9c

def z1168 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x52cc303e61c3e72b 0xd14b30c0f9870f9c

def z1169 : W := mkw 0x81ffbd3575680003 0xee07fef4d5d5a000 0x3dfb3ff87fb00007 0xbcf7ecffe1fec000

def z1170 : W := mkw 0x40002b405e02d830 0x450000ad01780b60 0x1fc03fc07e03f827 0xbc7f00ff01f80fe0

def z1171 : W := mkw 0x2000102c00812608 0x20800040b0020498 0x5ec4303e6043e72b 0xdd7b10c0f9810f9c

def z1172 : W := mkw 0x80fe902475680003 0xa603fa4091d5a000 0xfcffc03e7ffc001f 0xc3f3ff00f9fff000

def z1173 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x37d03fc06603f826 0xbcdf40ff01980fe0

def z1174 : W := mkw 0x01017db780000000 0x780405f6de000000 0xe5003fff80001cfc 0xff9400fffe000073

def z1175 : W := mkw 0x004c000021400001 0x0001300000850000 0xfcffc0007ffc001f 0x83f3ff0001fff000

def z1176 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xa13bcff980000000 0x2284ef3fe6000000

def z1177 : W := mkw 0xc0b02b405e2ad832 0x4702c0ad0178ab60 0x3ff03fc07e3ff837 0xbcffc0ff01f8ffe0

def z1178 : W := mkw 0x600002487fc3fe38 0x0580000921ff0ff8 0x020000007f83f827 0x8008000001fe0fe0

def z1179 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdfffff980000000 0x2bf7ffffe6000000

def z1180 : W := mkw 0x80fe902475680003 0xa603fa4091d5a000 0xfcfff0067ffc001f 0x93f3ffc019fff000

def z1181 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff8040000a 0xfff7fffffe010000

def z1182 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xffffffff80030021 0xfffffffffe000c00

def z1183 : W := mkw 0x0000000000000000 0x0000000000000000 0xec3bc0001fbc001d 0x83b0ef00007ef000

def z1184 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x11d4fffe00000000 0x184753fff8000000

def z1185 : W := mkw 0x480040c282048964 0x112001030a081225 0xf614c1c7e64fffff 0xf7d853071f993fff

def z1186 : W := mkw 0x00b02b005c025012 0x4402c0ac01700940 0x0be03fc078036001 0x3c2f80ff01e00d80

def z1187 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0xa133cfff80000000 0x6284cf3ffe000000

def z1188 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xd1dfffff80000000 0x7f477ffffe000000

def z1189 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc007fffc9fff 0xf7f3ff001ffff27f

def z1190 : W := mkw 0x304c102c21d12689 0x20c13040b087449a 0x5ecc303e61f3e7fb 0xdd7b30c0f987cf9f

def z1191 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x1ff03fc07e03e023 0x9c7fc0ff01f80f80

def z1192 : W := mkw 0x01fffdb7d4000003 0xfc07fff6df500000 0xfdfffffffe4c001f 0xfff7fffffff93000

def z1193 : W := mkw 0x480040c282048964 0x112001030a081225 0xfd34cfc7864c9ffe 0xfff4d33f1e19327f

def z1194 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffe0000000 0x7ff7ffffff800000

def z1195 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e43ff2f 0xbcffc0ff01f90ffc

def z1196 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xffef3e3ff9f3ffff 0xffffbcf8ffe7cfff

def z1197 : W := mkw 0x81fffdb7f5680003 0xfe07fff6dfd5a000 0xfdffffffe7cc000b 0xfff7ffffff9f3000

def z1198 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x7ff43fc67e03f827 0xfdffd0ff19f80fe0

def z1199 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x7fec3e3e61c3e72b 0xfdffb0f8f9870f9c

def z1200 : W := mkw 0x00b12d1100000002 0x4002c4b444000000 0x3df03ff980000000 0x7cf7c0ffe6000000

def z1201 : W := mkw 0x80fe902475680003 0xa603fa4091d5a000 0xfcfff0387ffc001f 0x8bf3ffc0e1fff000

def z1202 : W := mkw 0x204c102c00812609 0x20813040b0020498 0x5ecc303e6003e723 0xdd7b30c0f9800f9c

def z1203 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xed3fcfff80000000 0x6fb4ff3ffe000000

def z1204 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x3fd03fc06603f827 0xbcff40ff01980fe0

def z1205 : W := mkw 0x780002482bd7bfec 0x01e0000920af5eff 0x020000007fffffff 0x8008000001ffffff

def z1206 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80008022 0xfff7fffffe000200

def z1207 : W := mkw 0x00b16d9380000002 0x5002c5b64e000000 0xfdffffff80000000 0x7ff7fffffe000000

def z1208 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x33f03fc07e03f827 0xb0cfc0ff01f80fe0

def z1209 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdfffffff9f0001f 0xfff7ffffffe7c000

def z1210 : W := mkw 0x480040c282048964 0x112001030a081225 0xe014c1c7864c9ffe 0xe38053071e19327f

def z1211 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffcfff80000000 0x63f7ff3ffe000000

def z1212 : W := mkw 0x1001061108121080 0x0040041844204842 0xed2b0e3999b018dd 0xefb4ac38e666c063

def z1213 : W := mkw 0x480040c282048964 0x112001030a081225 0xf014c1c7864c9fde 0x73c053071e19327f

def z1214 : W := mkw 0x01fffdb7a140220b 0xf807fff6de850088 0xfdffffffe0006000 0x7ff7ffffff800180

def z1215 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xa133cff980000000 0x6e84cf3fe6000000

def z1216 : W := mkw 0x804e800075680001 0x86013a0001d5a000 0xdccfc0007ffc001f 0x83733f0001fff000

def z1217 : W := mkw 0x01ffbd3500000003 0xe807fef4d4000000 0x19fb3ff800000000 0x1867ecffe0000000

def z1218 : W := mkw 0x81feb92475680003 0xee07fae491d5a000 0xfcfff0007ffc001f 0x83f3ffc001fff000

def z1219 : W := mkw 0x004c102400000001 0x2001304090000000 0x5ecc303e6043e72b 0xdd7b30c0f9810f9c

def z1220 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfff4ffc07e03f827 0xbfffd3ff01f80fe0

def z1221 : W := mkw 0xc0b2ab405e2ad832 0xc702caad0178ab60 0xfff7ffc07e7ff83f 0xbfffdfff01f9ffe0

def z1222 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff98300014 0x7ff7fffffe60c000

def z1223 : W := mkw 0x780156ff8a97bfec 0x31e0055bfe2a5eff 0x03003fff8003ffe0 0x7c0c00fffe000fff

def z1224 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c7864c9fe2 0x77d053071e19327f

def z1225 : W := mkw 0x780002480a979de4 0x01e00009202a5e77 0x020000001fbf1cfd 0x80080000007efc73

def z1226 : W := mkw 0x80fea90075680003 0xc603faa401d5a000 0xfdffcfc07ffc001f 0xa3f7ff3f01fff000

def z1227 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xffeb0e39f9b31cff 0xefffac38e7e6cc73

def z1228 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff800007c0 0x7ff7fffffe00001f

def z1229 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc1c07ffc001f 0xb7f3ff0701fff000

def z1230 : W := mkw 0x480040c282048964 0x112001030a081225 0xf414c1c7864c1fde 0xe3d053071e19307f

def z1231 : W := mkw 0x480040c282048964 0x112001030a081225 0xf437c1c79e7c9ffe 0xf7d0df071e79f27f

def z1232 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1acc303e61c3e723 0x5c6b30c0f9870f9c

def z1233 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff864c0002 0x7ff7fffffe193000

def z1234 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc1cff 0x83f3ff0001fff073

def z1235 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0xfeef303e61c3e72b 0xdffbbcc0f9870f9c

def z1236 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xeb2b0e3999b31cdd 0x6bacac38e666cc73

def z1237 : W := mkw 0x00b0392400000002 0x6002c0e490000000 0x3df03ffe00000000 0x7cf7c0fff8000000

def z1238 : W := mkw 0x01b3ed9380000002 0xd806cfb64e000000 0xfd3fcfff80000000 0x7ff4ff3ffe000000

def z1239 : W := mkw 0x01ffed9380000003 0xd807ffb64e000000 0xfdffcff980000000 0x6ff7ff3fe6000000

def z1240 : W := mkw 0x81fffdb780280003 0xfa07fff6de00a000 0xfdffffff803c0010 0x7ff7fffffe00f000

def z1241 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x5dfffffe00000000 0x5d77fffff8000000

def z1242 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc001fffc18df 0xa3f3ff0007fff063

def z1243 : W := mkw 0x01fffdb7a1400003 0xf807fff6de850000 0xfdffffffe1800001 0x7ff7ffffff860000

def z1244 : W := mkw 0x48b02b405e06d976 0x4522c0ad01781b65 0x7ff43fc67e4fffff 0xfdffd0ff19f93fff

def z1245 : W := mkw 0x600002485e83dc30 0x05800009217a0f70 0x020000007f83fc2f 0x8008000001fe0ff0

def z1246 : W := mkw 0x0001449380000000 0x100005124e000000 0xed3bcff980000000 0x6fb4ef3fe6000000

def z1247 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff80000428 0xfff7fffffe000010

def z1248 : W := mkw 0x01017db780000000 0x780405f6de000000 0xa1233fff80000000 0x7e848cfffe000000

def z1249 : W := mkw 0xa04e902c21e92609 0xa2813a40b087a498 0xfeeff03e79ffe73f 0xdffbbfc0f9e7ff9c

def z1250 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff864c1cfe 0xfff7fffffe193073

def z1251 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff8000001c 0xfff7fffffe000000

def z1252 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xffeb3e3999b31cfd 0xffffacf8e666cc73

def z1253 : W := mkw 0x0001449380000000 0x100005124e000000 0xed2b0fff80000000 0x7fb4ac3ffe000000

def z1254 : W := mkw 0x00b12d1100000002 0x4002c4b444000000 0xed3b0ff980000000 0x6fb4ec3fe6000000

def z1255 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xf714ce39864f1cfe 0xefdc5338e6193c73

def z1256 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e4ff83f 0xbcffc0ff01f93fe0

def z1257 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x0be03fc078037801 0x282f80ff01e00de0

def z1258 : W := mkw 0x014d7db780000001 0x780535f6de000000 0x09c83fff80000000 0x7c2720fffe000000

def z1259 : W := mkw 0x01b17db780000002 0x7806c5f6de000000 0x21303fff80000000 0x7c84c0fffe000000

def z1260 : W := mkw 0x81fffdb7d4280003 0xfe07fff6df50a000 0xfdffffff98300000 0x7ff7fffffe60c000

def z1261 : W := mkw 0x4801045102048964 0x0120041144081225 0xed2b0e39864c9ffe 0xefb4ac38e619327f

def z1262 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xc9efffff80000000 0x7f27bffffe000000

def z1263 : W := mkw 0x2000102c21c12608 0x20800040b0870498 0x1ec0303e61c3e72b 0xdc7b00c0f9870f9c

def z1264 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xfcffc0007ffc803f 0x97f3ff0001fff200

def z1265 : W := mkw 0x480040c282048964 0x112001030a081225 0x5414c1c7864c9fea 0xf55053071e19327f

def z1266 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xff3b0e399fb31cff 0xeffcec38e67ecc73

def z1267 : W := mkw 0x480040c282048964 0x112001030a081225 0xfe14c1c7864f9fff 0xfff853071e193e7f

def z1268 : W := mkw 0x01017db780000000 0x780405f6de000000 0xfd3fffff80000000 0x7ff4fffffe000000

def z1269 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x0b2b0e3999b318c1 0x282cac38e666cc63

def z1270 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x1bf03fc07e03f827 0x986fc0ff01f80fe0

def z1271 : W := mkw 0x204c102c21c12609 0x20813040b0870498 0x1acc303e61c3e72b 0x986b30c0f9870f9c

def z1272 : W := mkw 0x014d7db780000001 0x780535f6de000000 0xfdef3fff80000000 0x7ff7bcfffe000000

def z1273 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xf0ffc0007ffc001e 0x03c3ff0001fff000

def z1274 : W := mkw 0x700002485e93dcb0 0x05c00009217a4f72 0x020000007e03fce7 0x8008000001f80ff3

def z1275 : W := mkw 0x40002b400a02d830 0x410000ad00280b60 0x3fe03fc07803f827 0xbcff80ff01e00fe0

def z1276 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0xfffb3fc07e03f827 0xbfffecff01f80fe0

def z1277 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x2bf03fc07e03f827 0xa8afc0ff01f80fe0

def z1278 : W := mkw 0x09fffdb780040147 0xf827fff6de001005 0xfdffffff864c07de 0xfff7fffffe19301f

def z1279 : W := mkw 0x014ffdb780000001 0xf8053ff6de000000 0x0104ffff80000000 0x7c0413fffe000000

def z1280 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xb0f7c0007ffc001f 0x82c3df0001fff000

def z1281 : W := mkw 0x01fd7db780000003 0x7807f5f6de000000 0x7dfc3fff80000000 0x7df7f0fffe000000

def z1282 : W := mkw 0x80fe800075680003 0x8603fa0001d5a000 0xe8ffc0007ffc001d 0x03a3ff0001fff000

def z1283 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xbdfbfff980000000 0x3ef7efffe6000000

def z1284 : W := mkw 0x3001061908931480 0x00c0041864224c52 0x4f2b0e3999b31ce9 0xed3cac38e666cc73

def z1285 : W := mkw 0x804e800075680001 0x86013a0001d5a000 0xf41fc0007ffc001f 0x83d07f0001fff000

def z1286 : W := mkw 0x01b17db780000002 0x7806c5f6de000000 0xfdf4ffff80000000 0x7ff7d3fffe000000

def z1287 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0x3dfb3fff80000000 0x7cf7ecfffe000000

def z1288 : W := mkw 0x3001061908931480 0x00c0041864224c52 0xef2b0e3999b31ce1 0x6fbcac38e666cc73

def z1289 : W := mkw 0x700002480a93dcb0 0x01c00009202a4f72 0x0200000019b3fcfd 0x800800000066cff3

def z1290 : W := mkw 0x804e800075680001 0x86013a0001d5a000 0xec2fc0007ffc001f 0x83b0bf0001fff000

def z1291 : W := mkw 0x81fffdb7a1680003 0xfa07fff6de85a000 0xfdffffff804c0000 0x7ff7fffffe013000

def z1292 : W := mkw 0x480040c282048964 0x112001030a081225 0xfc3fc1c7864c9ffe 0xf7f0ff071e19327f

def z1293 : W := mkw 0x01b3fdb780000002 0xf806cff6de000000 0xbdf3ffff80000000 0x7ef7cffffe000000

def z1294 : W := mkw 0x01fffdb780000003 0xf807fff6de000000 0xfdffffff98000005 0xfff7fffffe600000

def z1295 : W := mkw 0x480040c282048964 0x112001030a081225 0xfc34c1c79e4c9fff 0xf7f0d3071e79327f

def z1296 : W := mkw 0x40b02b405e02d832 0x4502c0ad01780b60 0x3ff03fc07e03e003 0x3cffc0ff01f80f80

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z9,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z10,z11]),(0,[z0,z1,z4,z8,z5,z12,z11]),(0,[z13,z0,z4,z8,z5,z6,z14]),(0,[z15,z0,z1,z4,z8,z5,z16]),(1,[z0,z1,z4,z17,z5,z6]),(0,[z18,z0,z1,z4,z8,z5,z19]),(0,[z20,z0,z1,z4,z8,z5,z6]),(0,[z21,z0,z1,z4,z8,z6,z22])],[(0,[z23,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z24,z4,z8,z5,z6]),(0,[z25,z0,z1,z4,z8,z5,z6])],[(0,[z26,z0,z1,z4,z8,z5,z6]),(0,[z1,z27,z4,z8,z28,z5,z6]),(0,[z29,z0,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z11,z30]),(0,[z31,z0,z1,z4,z8,z5,z6]),(0,[z0,z32,z1,z4,z8,z5,z6])],[(0,[z33,z1,z4,z8,z5,z6,z14]),(0,[z34,z0,z1,z4,z8,z35,z6]),(0,[z0,z1,z4,z8,z5,z6,z36])],[(0,[z0,z1,z4,z8,z5,z37,z6]),(0,[z38,z0,z1,z4,z8,z5,z6]),(0,[z39,z0,z1,z4,z40,z5,z6])],[(0,[z1,z4,z41,z8,z5,z6,z11]),(0,[z42,z0,z1,z4,z5,z6,z30]),(0,[z0,z1,z4,z8,z5,z6,z43]),(0,[z0,z44,z45,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z46]),(0,[z47,z0,z1,z4,z8,z5,z6]),(0,[z48,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z49]),(0,[z50,z1,z4,z8,z5,z6,z11]),(0,[z51,z33,z1,z4,z8,z5,z6]),(0,[z33,z52,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z53,z8,z5,z6]),(0,[z0,z52,z4,z40,z8,z5,z6]),(0,[z39,z0,z1,z4,z54,z5,z6]),(0,[z0,z1,z4,z8,z55,z6,z22])],[(0,[z56,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z57,z8,z5,z6]),(0,[z0,z58,z1,z4,z8,z5,z6]),(0,[z42,z59,z1,z4,z8,z5,z6]),(1,[z0,z44,z4,z8,z5,z12]),(0,[z0,z1,z4,z60,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z61,z6]),(0,[z0,z62,z1,z4,z8,z5,z6]),(0,[z0,z1,z63,z4,z8,z64,z6]),(0,[z0,z1,z63,z8,z5,z6,z65]),(0,[z0,z1,z4,z8,z5,z66,z6])]],
   [[(0,[z33,z67,z1,z4,z8,z5,z6])],[(0,[z0,z1,z3,z4,z8,z5,z6]),(0,[z0,z68,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z69,z5,z6]),(0,[z0,z70,z1,z4,z8,z5,z6])],[(0,[z71,z0,z1,z4,z8,z5,z6]),(0,[z72,z0,z1,z4,z8,z5,z6]),(0,[z73,z0,z1,z4,z8,z5,z6])],[(0,[z74,z0,z3,z4,z8,z5,z6]),(0,[z75,z0,z1,z4,z8,z5,z6]),(1,[z33,z1,z4,z8,z5,z11]),(0,[z76,z0,z1,z4,z8,z5,z6]),(0,[z77,z1,z4,z8,z5,z12,z6]),(0,[z0,z78,z1,z4,z8,z5,z6]),(0,[z0,z79,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z80]),(0,[z0,z1,z4,z8,z5,z6,z81])],[(0,[z82,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z83,z6]),(0,[z0,z45,z4,z8,z84,z5,z6]),(0,[z85,z0,z1,z4,z8,z5,z6]),(0,[z21,z0,z1,z4,z8,z5,z22])],[(1,[z59,z1,z4,z8,z5,z6]),(0,[z0,z4,z40,z8,z5,z6,z14]),(0,[z0,z1,z86,z4,z8,z5,z6])],[(1,[z50,z1,z4,z8,z5,z11]),(0,[z87,z33,z1,z4,z8,z5,z6]),(0,[z88,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z89,z8,z5,z6]),(0,[z0,z1,z4,z90,z8,z5,z6])]],
   [[(0,[z91,z0,z1,z4,z8,z5,z6]),(1,[z1,z4,z8,z5,z19,z11]),(0,[z33,z1,z4,z8,z5,z92,z6]),(0,[z0,z1,z4,z8,z5,z6,z93]),(0,[z0,z1,z4,z94,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z95]),(0,[z21,z0,z1,z4,z96,z5,z6])],[(0,[z97,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z98,z6]),(0,[z0,z1,z63,z99,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z100,z6]),(0,[z0,z1,z4,z54,z5,z101,z6])],[(0,[z0,z1,z4,z8,z102,z5,z6]),(0,[z0,z1,z4,z8,z5,z19,z14]),(0,[z0,z103,z1,z4,z8,z5,z6]),(0,[z104,z0,z1,z4,z8,z5,z6])],[(0,[z97,z0,z1,z105,z8,z5,z6]),(0,[z0,z1,z4,z106,z8,z5,z6]),(0,[z107,z0,z1,z4,z8,z5,z6]),(1,[z108,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z109,z6])],[(0,[z0,z67,z1,z8,z5,z92,z6]),(1,[z0,z1,z110,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z111]),(0,[z0,z1,z4,z8,z5,z112,z6])],[(0,[z0,z1,z4,z8,z113,z5,z6]),(0,[z13,z108,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z114,z6]),(0,[z115,z0,z1,z4,z8,z5,z6])],[(0,[z116,z0,z1,z4,z8,z5,z6]),(0,[z117,z0,z1,z4,z8,z84,z6]),(0,[z0,z1,z118,z4,z8,z5,z6]),(0,[z34,z0,z1,z4,z8,z5,z119]),(0,[z0,z1,z4,z120,z8,z5,z6]),(0,[z0,z121,z1,z4,z8,z5,z6])],[(0,[z122,z0,z1,z4,z8,z5,z6]),(0,[z123,z1,z4,z8,z5,z6,z11]),(0,[z124,z0,z1,z4,z8,z5,z6]),(0,[z125,z0,z1,z4,z8,z5,z6]),(0,[z0,z126,z1,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z5,z127,z6]),(0,[z128,z0,z1,z4,z8,z5,z6]),(0,[z129,z0,z1,z4,z8,z5,z6]),(0,[z130,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z119,z6])],[(0,[z122,z0,z1,z105,z8,z5,z6]),(0,[z0,z1,z131,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z132]),(0,[z0,z1,z4,z133,z8,z5,z6]),(0,[z0,z1,z134,z99,z8,z5,z6]),(0,[z0,z1,z4,z135,z8,z5,z6]),(0,[z136,z0,z1,z4,z8,z5,z6])],[(0,[z33,z1,z3,z4,z8,z5,z6]),(0,[z137,z138,z1,z4,z8,z5,z6])],[(0,[z42,z0,z4,z8,z5,z139,z6]),(0,[z117,z0,z1,z4,z8,z140,z6]),(0,[z0,z1,z4,z141,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z142]),(0,[z0,z1,z4,z8,z5,z6,z143])],[(0,[z144,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z145]),(0,[z146,z1,z4,z8,z5,z147,z6]),(0,[z18,z33,z1,z4,z8,z5,z6]),(0,[z21,z33,z1,z4,z8,z5,z6]),(0,[z42,z0,z52,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z12,z30])],[(0,[z0,z1,z4,z8,z5,z148,z6]),(0,[z146,z0,z1,z4,z8,z5,z149]),(0,[z0,z1,z4,z150,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z151])],[(0,[z152,z0,z3,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z11,z30]),(0,[z0,z1,z4,z8,z153,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z154])],[(0,[z122,z97,z1,z4,z8,z5,z6]),(0,[z0,z1,z155,z4,z8,z5,z6]),(0,[z0,z156,z1,z4,z8,z5,z6]),(1,[z0,z4,z8,z5,z6,z157]),(0,[z0,z1,z4,z8,z5,z6,z158]),(0,[z0,z1,z4,z8,z5,z6,z159])]],
   [[(0,[z0,z1,z4,z8,z5,z160,z6]),(0,[z0,z1,z4,z8,z5,z6,z161]),(0,[z162,z0,z1,z4,z8,z5,z6])],[(0,[z146,z39,z0,z1,z4,z5,z6]),(0,[z39,z163,z0,z1,z4,z5,z6]),(0,[z13,z0,z45,z4,z8,z5,z6]),(0,[z164,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z14,z30]),(1,[z165,z1,z4,z8,z5,z6])],[(0,[z33,z163,z1,z4,z8,z5,z6]),(0,[z166,z0,z1,z4,z8,z5,z6]),(0,[z0,z167,z1,z4,z8,z5,z6])],[],[(0,[z122,z146,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z106,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z5,z6]),(0,[z0,z1,z4,z8,z168,z5,z6]),(0,[z169,z0,z1,z4,z8,z5,z6]),(0,[z170,z1,z4,z8,z5,z16,z6]),(0,[z0,z1,z4,z54,z8,z5,z6]),(0,[z0,z171,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z172]),(0,[z0,z1,z4,z8,z5,z173,z6]),(1,[z125,z1,z4,z8,z5,z6])],[(0,[z33,z174,z1,z4,z8,z5,z6]),(0,[z1,z175,z4,z8,z5,z6,z11]),(0,[z33,z1,z4,z8,z5,z139,z6]),(0,[z176,z0,z1,z4,z8,z5,z6]),(0,[z177,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z35,z5,z6]),(0,[z0,z178,z1,z4,z8,z5,z6])],[(0,[z179,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z180,z6]),(0,[z33,z1,z4,z8,z5,z147,z6]),(0,[z0,z1,z4,z8,z181,z5,z6]),(0,[z0,z1,z4,z8,z5,z182,z6]),(0,[z0,z1,z4,z8,z5,z183,z6])]],
   [[(0,[z1,z27,z4,z106,z8,z5,z6]),(0,[z0,z1,z4,z8,z184,z5,z6]),(1,[z0,z1,z185,z8,z5,z119])],[(0,[z0,z1,z4,z186,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z187,z6]),(0,[z0,z1,z4,z8,z188,z5,z6]),(0,[z1,z4,z8,z5,z6,z189,z11]),(0,[z1,z4,z8,z5,z6,z11,z11]),(0,[z34,z33,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z119,z6]),(0,[z0,z1,z4,z8,z190,z5,z6]),(0,[z0,z1,z4,z8,z5,z191,z6]),(0,[z0,z192,z1,z4,z54,z8,z6]),(0,[z0,z1,z193,z4,z8,z5,z6])],[(0,[z0,z1,z194,z4,z8,z5,z6]),(0,[z0,z195,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z12,z6,z11]),(0,[z0,z1,z4,z5,z92,z6,z30]),(1,[z196,z1,z4,z8,z5,z6]),(0,[z0,z1,z197,z4,z8,z5,z6])],[(0,[z0,z1,z4,z198,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z199,z6]),(0,[z33,z1,z200,z4,z8,z5,z6])],[(0,[z201,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z202,z8,z5,z6]),(0,[z0,z203,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z204,z6])],[(0,[z1,z4,z8,z5,z147,z6,z11]),(0,[z42,z1,z4,z8,z5,z6,z11]),(0,[z0,z205,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z206]),(0,[z0,z207,z1,z4,z8,z5,z6]),(0,[z15,z0,z1,z4,z8,z5,z6]),(0,[z208,z0,z1,z4,z8,z5,z6]),(0,[z0,z192,z1,z4,z5,z101,z6])],[(0,[z209,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z210,z6]),(0,[z1,z4,z8,z28,z5,z147,z6])],[(0,[z0,z1,z4,z8,z5,z211,z6]),(0,[z0,z1,z4,z5,z101,z139,z6]),(0,[z0,z212,z1,z4,z8,z5,z6]),(0,[z0,z213,z1,z4,z8,z5,z6]),(1,[z214,z1,z4,z8,z5,z6])]],
   [[(0,[z1,z3,z4,z8,z5,z147,z6]),(0,[z130,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z215,z8,z5,z6])],[(0,[z216,z0,z1,z4,z8,z5,z6])],[(0,[z0,z217,z1,z4,z8,z5,z6]),(0,[z130,z0,z1,z4,z8,z28,z6]),(0,[z0,z1,z4,z8,z218,z5,z6]),(0,[z174,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z219,z6]),(0,[z34,z0,z220,z4,z8,z5,z6]),(0,[z0,z221,z1,z4,z8,z5,z6]),(1,[z222,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z223,z8,z5,z6]),(0,[z74,z174,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z224,z5,z12,z6]),(0,[z192,z178,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z22])],[(0,[z0,z1,z4,z8,z5,z225,z6]),(0,[z42,z0,z1,z4,z8,z226,z6]),(0,[z21,z0,z1,z4,z8,z5,z6])],[(0,[z227,z1,z3,z4,z8,z5,z6]),(0,[z228,z0,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z69,z5,z6,z11]),(0,[z33,z1,z4,z54,z8,z5,z6]),(0,[z0,z1,z229,z4,z8,z5,z6])],[(0,[z230,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z231,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z232,z6]),(0,[z1,z4,z8,z5,z6,z11,z233]),(0,[z42,z0,z1,z4,z5,z139,z6]),(0,[z234,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z235,z5,z6]),(0,[z0,z1,z4,z8,z5,z236,z6])],[(0,[z1,z4,z8,z237,z5,z6,z11]),(0,[z0,z1,z238,z4,z8,z5,z6]),(0,[z0,z4,z8,z5,z19,z6,z157]),(1,[z0,z1,z239,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z5,z240,z6]),(0,[z0,z1,z27,z4,z8,z5,z6]),(0,[z241,z1,z4,z8,z5,z6,z11]),(0,[z34,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z242,z5,z6])],[(0,[z122,z74,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z243,z6]),(0,[z0,z1,z4,z8,z244,z5,z6]),(0,[z0,z1,z4,z54,z8,z101,z6]),(1,[z245,z1,z4,z8,z5,z6])],[(1,[z246,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z8,z247,z5,z6]),(0,[z0,z1,z4,z8,z5,z199,z19]),(1,[z0,z1,z4,z8,z226,z6]),(0,[z0,z1,z4,z8,z5,z248,z6])],[(0,[z0,z1,z4,z8,z249,z5,z6]),(0,[z33,z1,z185,z4,z8,z5,z6]),(0,[z42,z0,z4,z8,z5,z6,z14]),(0,[z0,z1,z4,z250,z8,z5,z6]),(0,[z39,z0,z1,z4,z8,z5,z6])],[(0,[z0,z251,z1,z4,z8,z5,z6]),(0,[z252,z0,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z199,z6]),(0,[z0,z1,z4,z8,z5,z6,z253]),(0,[z137,z0,z1,z4,z8,z64,z6])],[(0,[z174,z0,z1,z4,z8,z28,z6]),(0,[z1,z4,z8,z5,z19,z6,z11]),(0,[z0,z1,z4,z8,z5,z12,z55])],[(0,[z254,z33,z1,z4,z8,z5,z6]),(0,[z255,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z256])],[(0,[z257,z0,z1,z4,z8,z5,z6]),(0,[z227,z1,z4,z106,z8,z5,z6]),(1,[z0,z1,z4,z8,z5,z149]),(0,[z0,z1,z4,z8,z5,z258,z6]),(0,[z137,z0,z1,z8,z5,z16,z6])]],
   [[(0,[z0,z1,z4,z8,z259,z5,z6]),(0,[z1,z4,z8,z5,z119,z6,z11]),(0,[z0,z1,z4,z8,z5,z6,z260]),(0,[z0,z1,z4,z110,z8,z5,z6]),(0,[z117,z0,z45,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z261]),(0,[z0,z192,z1,z4,z8,z5,z6])],[(0,[z163,z0,z52,z1,z4,z5,z6]),(0,[z42,z0,z1,z4,z262,z5,z6]),(0,[z263,z0,z1,z4,z8,z5,z6]),(1,[z138,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z264,z6]),(0,[z0,z1,z4,z8,z5,z265,z6])],[(0,[z137,z0,z1,z4,z215,z5,z6]),(1,[z170,z1,z4,z8,z5,z6]),(0,[z0,z1,z185,z4,z8,z5,z119])],[(0,[z0,z1,z266,z4,z8,z5,z6]),(0,[z1,z4,z267,z8,z5,z6,z11]),(0,[z0,z1,z268,z4,z8,z5,z6]),(1,[z269,z1,z4,z8,z5,z6]),(0,[z0,z52,z1,z4,z262,z5,z6]),(0,[z0,z270,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z271,z8,z5,z6])],[(0,[z71,z1,z4,z8,z5,z6,z11]),(0,[z33,z1,z4,z8,z5,z6,z22]),(1,[z0,z1,z4,z5,z6,z272])],[(0,[z0,z1,z4,z8,z5,z273,z6]),(0,[z0,z1,z4,z274,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z275,z6]),(0,[z0,z1,z276,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z277,z5,z6]),(0,[z278,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z2,z4,z8,z5,z6]),(0,[z279,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z280,z4,z8,z5,z6]),(0,[z18,z0,z1,z4,z5,z6,z30])],[(0,[z0,z1,z4,z8,z5,z6,z281]),(0,[z0,z1,z4,z8,z5,z282,z6]),(0,[z0,z1,z4,z283,z8,z5,z6]),(0,[z284,z0,z1,z4,z8,z5,z6]),(0,[z0,z285,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z286,z8,z5,z6])]],
   [[(1,[z0,z1,z4,z8,z5,z287]),(0,[z0,z1,z4,z8,z5,z6,z288]),(0,[z0,z1,z4,z8,z289,z5,z6]),(0,[z34,z0,z1,z4,z17,z5,z6]),(0,[z0,z1,z4,z8,z5,z290,z6]),(0,[z0,z1,z4,z8,z5,z6,z291]),(0,[z0,z1,z4,z8,z292,z5,z6]),(0,[z21,z0,z293,z4,z8,z5,z6])],[(1,[z0,z1,z4,z8,z5,z294]),(0,[z33,z1,z27,z4,z8,z5,z6]),(0,[z0,z1,z295,z4,z8,z5,z6]),(0,[z0,z45,z4,z99,z8,z5,z6]),(0,[z0,z1,z4,z262,z8,z5,z6])],[(0,[z0,z296,z1,z4,z8,z5,z6]),(0,[z13,z0,z1,z4,z8,z5,z287]),(0,[z0,z52,z1,z4,z5,z6,z30]),(0,[z0,z1,z4,z8,z297,z5,z6]),(0,[z0,z1,z298,z4,z8,z5,z6])],[(0,[z0,z0,z1,z4,z8,z5,z6]),(0,[z299,z0,z1,z4,z8,z5,z6]),(0,[z97,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z300,z6]),(0,[z0,z1,z4,z8,z5,z6,z301])],[(1,[z152,z3,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z8,z5,z6]),(0,[z302,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z303,z5,z6]),(0,[z304,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z65]),(0,[z0,z1,z185,z4,z8,z69,z5]),(0,[z0,z305,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z306,z6])],[(0,[z307,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z308]),(0,[z0,z309,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z5,z310]),(0,[z0,z1,z4,z8,z5,z6,z311]),(0,[z0,z1,z4,z8,z5,z312,z6])],[(0,[z74,z0,z227,z4,z8,z5,z6]),(0,[z1,z4,z106,z8,z5,z147,z6])],[(0,[z313,z0,z1,z4,z8,z5,z6]),(0,[z137,z0,z1,z4,z8,z5,z142]),(0,[z245,z1,z4,z8,z5,z55,z6])]],
   [[(0,[z0,z1,z314,z4,z8,z5,z6]),(0,[z39,z0,z1,z4,z8,z101,z6])],[(0,[z122,z1,z4,z8,z5,z6,z11]),(1,[z0,z1,z4,z5,z315,z6]),(0,[z0,z316,z1,z4,z8,z5,z6]),(0,[z33,z192,z1,z4,z8,z5,z6]),(0,[z42,z0,z1,z110,z8,z5,z6]),(0,[z0,z1,z185,z4,z8,z5,z12])],[(0,[z152,z0,z1,z4,z8,z5,z294]),(0,[z1,z3,z27,z4,z8,z5,z6]),(0,[z163,z1,z3,z4,z8,z5,z6]),(0,[z317,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z318,z6]),(0,[z42,z319,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z69,z55,z6])],[(0,[z320,z0,z1,z4,z8,z5,z6]),(0,[z0,z321,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z11,z14]),(0,[z39,z0,z192,z1,z4,z5,z6]),(0,[z0,z1,z4,z8,z5,z322,z6])],[],[(0,[z323,z0,z1,z4,z8,z5,z6]),(0,[z324,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z325,z5,z6]),(0,[z0,z1,z4,z8,z5,z326,z6]),(0,[z0,z1,z4,z327,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z328])],[(0,[z74,z1,z27,z4,z8,z5,z6]),(0,[z254,z0,z1,z4,z8,z5,z6]),(0,[z1,z63,z4,z8,z5,z6,z11]),(0,[z137,z103,z1,z4,z8,z5,z6]),(0,[z329,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z262,z5,z19])],[(0,[z330,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z331,z4,z8,z5,z6]),(0,[z0,z332,z1,z4,z8,z5,z6]),(0,[z0,z333,z1,z4,z8,z5,z6])]],
   [[(0,[z334,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z335,z8,z5,z6]),(0,[z0,z1,z4,z336,z8,z5,z6]),(0,[z337,z0,z1,z4,z8,z5,z6]),(1,[z319,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z55,z14]),(0,[z34,z0,z1,z185,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z338,z6]),(0,[z0,z1,z4,z8,z339,z5,z6]),(0,[z0,z340,z1,z4,z8,z5,z6]),(0,[z341,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z342])],[(0,[z146,z163,z1,z4,z8,z5,z6]),(0,[z343,z0,z1,z4,z8,z5,z6]),(0,[z0,z45,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z41,z5,z101,z6]),(0,[z0,z1,z63,z4,z8,z5,z6]),(0,[z0,z1,z4,z17,z8,z5,z6]),(1,[z18,z0,z1,z4,z5,z30])],[(0,[z0,z1,z4,z8,z5,z344,z6]),(0,[z345,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z6]),(0,[z0,z1,z4,z346,z8,z5,z6]),(0,[z0,z347,z1,z4,z8,z5,z6])],[(0,[z163,z1,z4,z106,z8,z5,z6]),(0,[z33,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z348]),(0,[z0,z1,z4,z8,z84,z5,z6]),(0,[z0,z1,z4,z8,z349,z5,z6]),(0,[z0,z1,z4,z8,z5,z350,z6]),(0,[z0,z1,z4,z5,z101,z92,z6]),(0,[z0,z1,z4,z351,z8,z5,z6])],[(0,[z33,z1,z4,z8,z5,z6,z65]),(0,[z33,z0,z1,z4,z8,z5,z199]),(0,[z117,z0,z1,z4,z8,z5,z160]),(0,[z214,z1,z4,z8,z5,z119,z6])],[(0,[z279,z0,z1,z4,z8,z5,z6]),(0,[z146,z174,z1,z4,z8,z5,z6]),(0,[z0,z352,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z353,z5,z6]),(1,[z0,z1,z283,z8,z5,z6]),(1,[z354,z1,z4,z8,z5,z6])],[(0,[z0,z59,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z355,z6]),(1,[z0,z1,z63,z8,z64,z6]),(0,[z0,z1,z4,z356,z8,z5,z6]),(0,[z357,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z69,z5,z55])]],
   [[(0,[z0,z1,z4,z8,z5,z358,z6]),(0,[z0,z1,z4,z8,z359,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z360]),(1,[z42,z0,z4,z5,z139,z6]),(0,[z0,z1,z4,z8,z5,z361,z6]),(0,[z0,z1,z185,z8,z5,z119,z6]),(0,[z0,z305,z4,z8,z5,z19,z6]),(0,[z21,z362,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z363,z6]),(0,[z0,z1,z4,z8,z5,z6,z364]),(0,[z0,z1,z4,z8,z5,z365,z6])],[(0,[z366,z0,z1,z4,z8,z5,z6]),(0,[z263,z0,z1,z134,z8,z5,z6]),(0,[z0,z1,z134,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z367]),(0,[z368,z0,z1,z4,z8,z5,z6]),(0,[z369,z0,z1,z4,z8,z5,z6]),(0,[z137,z0,z62,z4,z8,z5,z6]),(0,[z34,z0,z1,z4,z8,z69,z5])],[(0,[z0,z1,z4,z8,z5,z6,z370]),(0,[z0,z1,z63,z8,z64,z5,z6])],[(0,[z371,z0,z1,z4,z8,z5,z6]),(0,[z117,z0,z1,z4,z274,z5,z6]),(1,[z115,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z64,z5,z6,z11]),(0,[z39,z33,z1,z4,z8,z5,z6]),(0,[z117,z0,z1,z4,z8,z5,z206]),(0,[z0,z1,z8,z64,z5,z16,z6]),(0,[z0,z1,z4,z8,z69,z16,z6]),(1,[z0,z1,z4,z120,z5,z6]),(1,[z21,z0,z1,z4,z8,z22])],[(0,[z0,z1,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z11,z49]),(0,[z0,z372,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z373])]],
   [[(0,[z34,z0,z1,z4,z8,z5,z12]),(0,[z0,z1,z4,z8,z5,z374,z6]),(0,[z1,z4,z8,z5,z109,z16,z6]),(0,[z0,z1,z4,z8,z5,z375,z6])],[(0,[z74,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z5,z376]),(0,[z0,z377,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z215,z5,z6]),(0,[z378,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z379])],[(0,[z0,z1,z4,z8,z380,z5,z6]),(0,[z0,z1,z381,z4,z8,z5,z6]),(0,[z0,z382,z1,z4,z8,z5,z6]),(0,[z130,z1,z4,z8,z5,z6,z11]),(0,[z383,z0,z44,z4,z8,z5,z6]),(0,[z384,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z385,z5,z6]),(0,[z386,z0,z1,z4,z8,z5,z6]),(1,[z1,z4,z8,z5,z12,z11]),(0,[z1,z4,z262,z8,z5,z6,z11]),(0,[z33,z45,z1,z4,z8,z5,z6]),(0,[z383,z33,z1,z4,z8,z5,z6]),(0,[z33,z1,z63,z4,z8,z5,z6]),(0,[z0,z1,z4,z387,z8,z5,z6]),(0,[z388,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z96,z5,z6])],[(0,[z67,z1,z4,z8,z5,z6,z11]),(0,[z33,z1,z4,z8,z5,z6,z6]),(0,[z263,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z389,z6]),(1,[z0,z1,z4,z277,z5,z6]),(1,[z0,z1,z327,z8,z5,z6])],[(0,[z122,z1,z4,z105,z8,z5,z6]),(0,[z33,z1,z4,z8,z84,z5,z6]),(0,[z390,z0,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z243,z139,z6]),(0,[z383,z391,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z41,z8,z5,z6]),(0,[z392,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z310,z6]),(0,[z34,z125,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z393,z6]),(0,[z18,z1,z4,z8,z5,z6,z11]),(0,[z21,z1,z4,z8,z5,z6,z11]),(0,[z0,z394,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z65,z22])],[(0,[z0,z1,z4,z8,z5,z11,z14]),(1,[z0,z395,z99,z8,z5,z6]),(0,[z13,z0,z1,z99,z8,z5,z6]),(0,[z396,z0,z1,z4,z8,z5,z6]),(0,[z0,z397,z1,z4,z8,z5,z6]),(0,[z0,z398,z1,z4,z8,z5,z6]),(0,[z399,z0,z1,z4,z8,z5,z6])]],
   [[(0,[z400,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z401,z6]),(0,[z0,z1,z402,z4,z8,z5,z6]),(0,[z117,z0,z1,z4,z184,z5,z6])],[(0,[z0,z1,z4,z8,z84,z101,z6]),(0,[z0,z1,z403,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z404,z6]),(0,[z39,z0,z192,z1,z4,z8,z6])],[(0,[z152,z0,z1,z4,z8,z5,z376]),(0,[z0,z1,z4,z405,z8,z5,z6]),(0,[z0,z406,z1,z4,z8,z5,z6]),(0,[z407,z1,z4,z8,z5,z6,z11]),(0,[z408,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z41,z8,z5,z92,z6]),(0,[z0,z1,z409,z4,z8,z5,z6]),(0,[z34,z196,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z410,z6])],[(0,[z0,z411,z1,z4,z8,z5,z6]),(0,[z33,z1,z134,z4,z8,z5,z6]),(0,[z0,z1,z412,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z413])],[(0,[z0,z1,z4,z414,z8,z5,z6]),(0,[z0,z1,z415,z4,z8,z5,z6])],[(0,[z0,z416,z1,z4,z8,z5,z6]),(1,[z324,z0,z1,z4,z5,z6]),(0,[z39,z1,z4,z8,z5,z6,z11]),(0,[z13,z0,z1,z4,z8,z5,z6]),(0,[z417,z0,z1,z4,z8,z5,z6]),(0,[z418,z0,z1,z4,z8,z5,z6])],[(0,[z419,z0,z1,z4,z8,z5,z6]),(0,[z122,z1,z4,z8,z28,z5,z6]),(0,[z420,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z5,z142]),(0,[z0,z1,z4,z8,z5,z6,z421]),(1,[z1,z4,z8,z5,z6,z81])],[(0,[z137,z33,z1,z4,z8,z5,z6]),(0,[z13,z0,z395,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z422,z6]),(0,[z0,z362,z1,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z262,z5,z19,z6])],[(0,[z0,z423,z1,z4,z8,z5,z6]),(0,[z42,z0,z1,z4,z40,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z424]),(0,[z0,z1,z4,z8,z5,z425,z6]),(0,[z0,z1,z4,z262,z5,z101,z6])],[(0,[z426,z0,z1,z4,z8,z5,z6]),(0,[z137,z0,z1,z4,z427,z5,z6]),(0,[z0,z1,z4,z8,z427,z5,z6]),(0,[z0,z1,z4,z8,z5,z428,z6]),(0,[z18,z0,z1,z4,z8,z5,z30])],[(0,[z0,z52,z1,z4,z5,z139,z6]),(0,[z383,z270,z1,z4,z8,z5,z6]),(0,[z429,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z430,z5,z6]),(0,[z0,z431,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z19,z6]),(0,[z21,z0,z432,z4,z8,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z1,z4,z8,z5,z139,z6,z11]),(0,[z0,z1,z4,z8,z5,z101,z6]),(0,[z0,z1,z433,z4,z8,z5,z6])],[(0,[z152,z1,z3,z4,z8,z5,z6]),(0,[z0,z434,z1,z4,z8,z5,z6]),(0,[z52,z1,z4,z8,z5,z6,z11]),(0,[z42,z0,z1,z435,z8,z5,z6]),(0,[z436,z0,z1,z4,z8,z5,z6]),(1,[z103,z1,z4,z8,z5,z6]),(0,[z0,z437,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z438])],[(0,[z33,z74,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z41,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z439,z6]),(0,[z0,z1,z185,z4,z8,z5,z14]),(1,[z1,z4,z8,z5,z109,z6])],[(0,[z0,z1,z4,z8,z5,z440,z6]),(1,[z0,z1,z4,z8,z5,z160]),(1,[z34,z0,z1,z8,z5,z65]),(0,[z0,z1,z4,z441,z8,z5,z6])]],
   [[(0,[z0,z1,z442,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z140,z6,z11]),(0,[z1,z4,z8,z5,z55,z6,z11])],[(0,[z146,z1,z27,z4,z8,z5,z6]),(0,[z146,z0,z1,z4,z5,z101,z6]),(0,[z163,z0,z1,z4,z5,z101,z6]),(0,[z38,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z443,z6])],[(0,[z0,z1,z4,z8,z5,z444,z6]),(0,[z0,z1,z4,z445,z8,z5,z6]),(0,[z0,z446,z1,z4,z8,z5,z6]),(0,[z447,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z448,z8,z5,z6]),(0,[z449,z0,z1,z4,z8,z5,z6]),(0,[z18,z0,z1,z4,z262,z5,z6])],[(1,[z122,z1,z105,z8,z5,z6]),(0,[z334,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z450,z8,z5,z6]),(0,[z451,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z435,z8,z5,z6]),(0,[z269,z1,z4,z8,z5,z139,z6]),(0,[z383,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z310,z16]),(1,[z0,z1,z4,z8,z69,z55])],[(0,[z146,z0,z52,z1,z4,z5,z6])],[(0,[z0,z1,z4,z452,z8,z5,z6]),(0,[z0,z1,z4,z28,z5,z315,z6]),(0,[z0,z1,z4,z8,z5,z6,z11]),(0,[z117,z0,z1,z412,z8,z5,z6]),(0,[z453,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z454,z4,z8,z5,z6])],[(0,[z0,z455,z1,z4,z8,z5,z6]),(0,[z456,z0,z1,z4,z8,z5,z6]),(0,[z457,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z458,z4,z8,z5,z6]),(0,[z459,z0,z1,z4,z8,z5,z6])],[(0,[z152,z1,z4,z106,z8,z5,z6]),(0,[z0,z1,z4,z8,z237,z5,z6]),(0,[z33,z33,z1,z4,z8,z5,z6]),(0,[z0,z395,z1,z99,z8,z5,z6]),(1,[z0,z1,z4,z274,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z460]),(0,[z0,z461,z1,z4,z8,z5,z6])]],
   [[(1,[z0,z1,z4,z8,z5,z206]),(0,[z0,z1,z4,z8,z462,z5,z6]),(0,[z463,z0,z1,z4,z8,z5,z6])],[(0,[z0,z227,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z464]),(0,[z0,z465,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z466,z8,z5,z6]),(0,[z50,z0,z1,z4,z8,z5,z6]),(1,[z1,z4,z8,z5,z11,z30]),(0,[z0,z4,z8,z5,z12,z6,z14]),(0,[z0,z1,z4,z467,z8,z5,z6]),(0,[z34,z0,z1,z4,z8,z264,z6]),(0,[z0,z468,z1,z4,z8,z5,z6])],[(0,[z469,z0,z1,z4,z8,z5,z6]),(0,[z50,z0,z1,z4,z8,z5,z199]),(1,[z0,z62,z4,z8,z5,z6])],[(0,[z0,z1,z175,z4,z8,z5,z6]),(0,[z0,z44,z4,z99,z8,z5,z6]),(0,[z137,z0,z1,z63,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z470])],[(0,[z146,z0,z1,z4,z237,z5,z6]),(0,[z163,z0,z1,z4,z237,z5,z6]),(0,[z33,z1,z4,z8,z5,z19,z6]),(0,[z0,z1,z471,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z472,z6]),(0,[z473,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z474]),(0,[z0,z1,z4,z8,z5,z6,z475])],[(0,[z1,z185,z4,z8,z5,z6,z11]),(0,[z33,z1,z4,z8,z5,z101,z6]),(0,[z0,z1,z4,z8,z5,z476,z6]),(0,[z137,z0,z1,z4,z8,z5,z361]),(1,[z15,z0,z1,z4,z8,z5]),(0,[z0,z1,z4,z477,z8,z5,z6]),(1,[z167,z1,z4,z8,z5,z6])],[(0,[z478,z0,z1,z4,z8,z5,z6]),(0,[z319,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z479,z6])],[(0,[z0,z1,z4,z480,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z439,z6]),(0,[z137,z0,z1,z4,z8,z5,z6])]],
   [[(0,[z1,z4,z99,z8,z5,z6,z11]),(0,[z0,z1,z99,z8,z5,z16,z6]),(0,[z481,z0,z1,z4,z8,z5,z6]),(0,[z214,z0,z1,z4,z8,z5,z6]),(0,[z39,z0,z1,z4,z5,z6,z30]),(0,[z0,z1,z4,z8,z5,z6,z482])],[(0,[z174,z1,z4,z105,z8,z5,z6]),(0,[z0,z1,z435,z4,z8,z5,z6]),(0,[z0,z1,z4,z483,z8,z5,z6]),(1,[z39,z0,z192,z1,z4,z6]),(1,[z178,z1,z4,z8,z5,z6])],[(0,[z484,z0,z1,z4,z8,z5,z6]),(0,[z163,z0,z1,z4,z106,z5,z6]),(0,[z192,z1,z4,z8,z5,z6,z11]),(1,[z0,z1,z4,z184,z5,z6]),(0,[z485,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z16,z6]),(0,[z0,z1,z4,z8,z5,z486,z6]),(0,[z222,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z96,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z487]),(0,[z0,z1,z4,z8,z5,z488,z6]),(0,[z0,z1,z4,z8,z5,z12,z6]),(0,[z0,z1,z4,z8,z5,z489,z6])],[(0,[z0,z1,z490,z4,z8,z5,z6]),(0,[z146,z0,z1,z4,z8,z5,z6]),(0,[z163,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z491,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z11,z22]),(0,[z33,z1,z4,z450,z8,z5,z6]),(0,[z117,z0,z1,z4,z8,z5,z6]),(0,[z0,z220,z1,z4,z8,z5,z6])],[(0,[z0,z492,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z199,z12]),(0,[z493,z0,z1,z4,z8,z5,z6]),(0,[z34,z0,z1,z4,z8,z5,z14]),(0,[z0,z1,z8,z5,z16,z6,z65])],[(0,[z494,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z495,z4,z8,z5,z6]),(0,[z42,z163,z0,z1,z4,z5,z6]),(0,[z0,z1,z496,z4,z8,z5,z6]),(1,[z0,z1,z4,z54,z101,z6])],[(0,[z33,z1,z268,z4,z8,z5,z6]),(0,[z117,z166,z1,z4,z8,z5,z6])]],
   [[(0,[z497,z0,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z237,z5,z6]),(0,[z0,z498,z1,z4,z8,z5,z6])],[(0,[z97,z1,z4,z8,z5,z147,z6]),(0,[z0,z1,z499,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z500]),(0,[z0,z1,z501,z4,z8,z5,z6]),(0,[z0,z1,z4,z99,z8,z5,z6]),(0,[z165,z1,z4,z8,z5,z92,z6]),(0,[z21,z354,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z502,z8,z5,z6]),(0,[z174,z1,z4,z8,z28,z5,z6]),(0,[z0,z503,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z504]),(0,[z21,z0,z1,z4,z8,z69,z6])],[(0,[z0,z1,z4,z8,z505,z5,z6]),(0,[z400,z33,z1,z4,z8,z5,z6]),(0,[z506,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z262,z8,z5,z19]),(0,[z21,z0,z1,z4,z8,z5,z55])],[(0,[z146,z0,z1,z4,z8,z5,z367]),(0,[z0,z1,z4,z8,z5,z507,z6]),(0,[z0,z44,z1,z4,z8,z5,z6]),(0,[z508,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z19,z6,z30])],[(0,[z33,z1,z4,z262,z8,z5,z6]),(0,[z42,z0,z1,z4,z8,z5,z288]),(0,[z0,z44,z4,z8,z5,z140,z6]),(0,[z509,z0,z1,z4,z8,z5,z6])],[(0,[z510,z0,z1,z4,z8,z5,z6])],[(0,[z1,z3,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z101,z6,z11]),(0,[z0,z511,z1,z4,z8,z5,z6]),(1,[z33,z1,z4,z8,z5,z199]),(0,[z13,z0,z44,z4,z8,z5,z6])]],
   [[(0,[z13,z33,z1,z4,z8,z5,z6]),(0,[z512,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z513,z8,z5,z6]),(1,[z391,z1,z4,z8,z5,z6]),(0,[z18,z115,z1,z4,z8,z5,z6])],[(0,[z1,z3,z4,z8,z237,z5,z6]),(0,[z0,z1,z4,z8,z514,z5,z6]),(0,[z263,z0,z1,z8,z5,z92,z6]),(0,[z0,z1,z515,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z30])],[(0,[z0,z1,z516,z4,z8,z5,z6]),(0,[z0,z45,z4,z8,z5,z6,z14]),(0,[z0,z1,z4,z8,z5,z19,z12]),(1,[z0,z496,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z517,z6]),(0,[z74,z1,z4,z8,z5,z6,z11]),(0,[z518,z0,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z16,z6]),(1,[z0,z1,z4,z8,z5,z288]),(0,[z519,z0,z1,z4,z8,z5,z6])],[(0,[z152,z0,z227,z4,z8,z5,z6]),(1,[z1,z4,z8,z5,z243,z6]),(0,[z117,z347,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z520,z6]),(0,[z0,z1,z4,z8,z16,z6,z22]),(0,[z0,z1,z4,z521,z8,z5,z6])],[(0,[z74,z1,z4,z8,z237,z5,z6]),(0,[z1,z4,z105,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z19,z11]),(0,[z0,z1,z4,z8,z69,z64,z6])],[(0,[z0,z1,z4,z8,z522,z5,z6])],[(0,[z152,z33,z1,z4,z8,z5,z6]),(0,[z246,z0,z1,z3,z4,z5,z6]),(0,[z74,z227,z1,z4,z8,z5,z6]),(0,[z33,z97,z1,z4,z8,z5,z6]),(0,[z174,z0,z1,z4,z8,z147,z6]),(0,[z0,z67,z1,z8,z5,z16,z6]),(1,[z0,z1,z412,z8,z5,z6]),(1,[z1,z4,z8,z5,z6,z253])]],
   [[(0,[z0,z1,z4,z8,z5,z523,z6]),(0,[z1,z4,z54,z8,z5,z6,z11]),(0,[z0,z4,z99,z8,z5,z140,z6]),(0,[z0,z1,z4,z8,z5,z226,z6]),(0,[z0,z1,z4,z40,z5,z101,z6]),(0,[z524,z0,z1,z4,z8,z5,z6]),(0,[z137,z0,z525,z4,z8,z5,z6])],[(0,[z33,z1,z4,z8,z325,z5,z6]),(0,[z0,z1,z4,z526,z8,z5,z6]),(1,[z1,z4,z8,z5,z6,z256])],[(0,[z527,z0,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z99,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z528,z6]),(0,[z383,z0,z1,z4,z8,z5,z12]),(0,[z0,z1,z4,z529,z8,z5,z6]),(0,[z0,z1,z4,z530,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z531,z6])],[(0,[z532,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z533]),(0,[z0,z1,z4,z534,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z535]),(0,[z0,z1,z4,z8,z5,z140,z6]),(0,[z34,z0,z1,z8,z5,z6,z65]),(0,[z0,z1,z4,z8,z5,z536,z6]),(0,[z0,z1,z4,z8,z5,z537,z6])],[(0,[z1,z4,z8,z5,z6,z538,z11]),(0,[z1,z4,z8,z5,z6,z6,z11]),(0,[z0,z1,z4,z8,z539,z5,z6]),(0,[z13,z446,z1,z4,z8,z5,z6]),(0,[z540,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z541,z4,z8,z5,z6]),(0,[z0,z1,z4,z542,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z11,z65]),(0,[z33,z44,z1,z4,z8,z5,z6]),(0,[z0,z44,z4,z40,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z543])],[(0,[z1,z4,z40,z8,z5,z6,z11]),(0,[z0,z1,z4,z544,z8,z5,z6]),(1,[z270,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z12,z22]),(0,[z0,z545,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z546,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z149,z6]),(0,[z0,z1,z4,z8,z547,z5,z6]),(0,[z0,z1,z4,z8,z5,z548,z6]),(0,[z0,z1,z4,z8,z5,z264,z6])]],
   [[(0,[z549,z0,z1,z4,z8,z5,z6]),(0,[z550,z0,z1,z4,z8,z5,z6]),(0,[z0,z67,z1,z63,z8,z5,z6]),(0,[z42,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z551,z6]),(0,[z0,z1,z4,z552,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z553,z6])],[(0,[z227,z1,z4,z8,z5,z6,z11]),(1,[z130,z1,z4,z8,z147,z6]),(0,[z456,z33,z1,z4,z8,z5,z6]),(0,[z554,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z555,z6]),(0,[z0,z1,z4,z8,z5,z6,z556])],[(0,[z0,z1,z557,z4,z8,z5,z6]),(0,[z0,z1,z4,z558,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z6,z30]),(0,[z0,z559,z1,z4,z8,z5,z6]),(0,[z108,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z55,z65]),(1,[z104,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z560,z5,z6]),(0,[z324,z0,z1,z4,z28,z5,z6]),(0,[z1,z4,z8,z84,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z14,z22]),(0,[z0,z1,z561,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z562,z6])],[(0,[z563,z0,z1,z4,z8,z5,z6]),(0,[z50,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z189]),(0,[z0,z1,z4,z8,z5,z199,z30]),(0,[z0,z67,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z564]),(1,[z0,z1,z4,z8,z5,z361]),(0,[z0,z1,z4,z8,z5,z6,z565])],[(0,[z0,z1,z4,z8,z5,z566,z6]),(0,[z21,z0,z1,z239,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z567])],[(1,[z0,z1,z4,z8,z5,z6]),(0,[z174,z1,z3,z4,z8,z5,z6]),(0,[z163,z74,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z188,z5,z6,z11]),(0,[z0,z1,z4,z568,z8,z5,z6]),(0,[z1,z4,z8,z5,z119,z6,z256]),(0,[z0,z1,z569,z4,z8,z5,z6])],[(0,[z130,z174,z1,z4,z8,z5,z6]),(0,[z570,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z571,z5,z6]),(0,[z0,z572,z1,z4,z8,z5,z6])]],
   [[(0,[z130,z122,z1,z4,z8,z5,z6]),(0,[z130,z1,z4,z8,z5,z147,z6]),(0,[z395,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z573,z6]),(0,[z0,z1,z4,z8,z64,z6,z22])],[(0,[z574,z0,z1,z4,z8,z5,z6]),(0,[z575,z0,z1,z4,z8,z5,z6]),(0,[z13,z0,z4,z8,z5,z140,z6]),(0,[z269,z0,z1,z4,z8,z5,z6]),(1,[z166,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z224,z5,z6]),(1,[z1,z4,z8,z5,z6,z80])],[(0,[z137,z0,z1,z4,z8,z16,z6])],[(0,[z576,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z40,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z577,z6]),(1,[z0,z1,z4,z8,z35,z6])],[(0,[z0,z1,z4,z8,z5,z578,z6]),(0,[z0,z1,z4,z8,z579,z5,z6]),(0,[z1,z134,z4,z8,z5,z6,z11]),(0,[z33,z1,z4,z8,z5,z140,z6]),(0,[z0,z1,z4,z8,z580,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z581])],[(1,[z74,z227,z4,z8,z5,z6]),(1,[z163,z1,z4,z106,z5,z6]),(0,[z1,z4,z106,z8,z5,z6,z11]),(0,[z383,z1,z4,z8,z5,z6,z11]),(0,[z1,z4,z8,z5,z199,z6,z11])],[(0,[z582,z0,z1,z4,z8,z5,z6]),(0,[z583,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z584,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z5,z367]),(0,[z263,z1,z4,z8,z5,z6,z11]),(0,[z0,z52,z1,z4,z40,z5,z6]),(0,[z0,z1,z4,z8,z585,z5,z6]),(0,[z138,z0,z1,z4,z8,z5,z6]),(0,[z586,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z293,z4,z8,z5,z6])],[(0,[z152,z0,z1,z4,z8,z5,z6]),(0,[z146,z33,z1,z4,z8,z5,z6]),(0,[z1,z4,z106,z8,z237,z5,z6]),(0,[z117,z33,z1,z4,z8,z5,z6]),(0,[z0,z395,z4,z99,z8,z5,z6]),(0,[z42,z0,z1,z4,z8,z242,z6]),(0,[z0,z196,z1,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z5,z587,z6]),(0,[z0,z1,z4,z8,z588,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z589]),(0,[z174,z1,z4,z106,z8,z5,z6]),(0,[z33,z1,z4,z8,z547,z5,z6])],[(0,[z39,z0,z1,z4,z5,z139,z6]),(0,[z0,z1,z4,z8,z5,z55,z6])],[(0,[z0,z1,z4,z8,z5,z199,z14]),(0,[z0,z1,z4,z590,z8,z5,z6]),(0,[z0,z192,z1,z4,z8,z84,z6]),(0,[z0,z1,z4,z5,z12,z6,z272]),(0,[z0,z1,z4,z41,z5,z6,z30]),(0,[z591,z0,z1,z4,z8,z5,z6]),(0,[z592,z0,z1,z4,z8,z5,z6]),(0,[z222,z1,z4,z8,z5,z19,z6])],[(0,[z593,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z594,z6]),(0,[z0,z1,z4,z8,z5,z595,z6]),(0,[z596,z0,z1,z4,z8,z5,z6]),(0,[z0,z44,z1,z4,z8,z5,z12]),(0,[z77,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z525,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z19,z6,z80]),(0,[z1,z4,z8,z5,z55,z6,z81])],[(0,[z0,z1,z4,z8,z5,z597,z6]),(0,[z104,z192,z1,z4,z8,z5,z6])],[(1,[z174,z1,z4,z8,z28,z6]),(0,[z123,z33,z1,z4,z8,z5,z6]),(0,[z0,z598,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z242,z6]),(0,[z0,z1,z4,z599,z8,z5,z6])],[(0,[z600,z0,z1,z4,z8,z5,z6]),(1,[z347,z1,z4,z8,z5,z6])],[(0,[z0,z192,z1,z4,z8,z140,z6]),(0,[z0,z1,z4,z8,z5,z601,z6])]],
   [[(0,[z0,z44,z4,z8,z5,z12,z6]),(0,[z0,z1,z63,z4,z8,z16,z6]),(0,[z18,z167,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z602,z6]),(0,[z137,z1,z4,z8,z5,z6,z11]),(0,[z1,z4,z8,z5,z6,z11,z172]),(0,[z33,z0,z1,z4,z8,z5,z11]),(0,[z603,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z604,z8,z5,z6]),(0,[z605,z0,z1,z4,z8,z5,z6])],[(0,[z606,z0,z1,z4,z8,z5,z6]),(0,[z607,z0,z1,z4,z8,z5,z6]),(1,[z383,z0,z4,z8,z5,z14]),(0,[z0,z608,z1,z4,z8,z5,z6]),(1,[z1,z4,z8,z5,z355,z6]),(0,[z609,z0,z1,z4,z8,z5,z6]),(1,[z0,z293,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z92,z6,z11]),(0,[z0,z1,z610,z4,z8,z5,z6]),(0,[z0,z4,z8,z84,z5,z140,z6]),(0,[z383,z0,z4,z8,z5,z6,z14]),(0,[z39,z0,z1,z4,z41,z5,z6]),(0,[z21,z0,z1,z185,z4,z8,z5]),(0,[z0,z1,z4,z8,z5,z6,z611])],[(0,[z152,z146,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z40,z8,z5,z6]),(0,[z0,z1,z4,z612,z8,z5,z6]),(0,[z613,z0,z1,z4,z8,z5,z6]),(0,[z39,z0,z1,z4,z262,z5,z6]),(0,[z0,z1,z4,z8,z5,z614,z6])],[(0,[z0,z1,z4,z267,z8,z5,z6]),(0,[z13,z0,z67,z4,z8,z5,z6]),(0,[z615,z0,z1,z4,z8,z5,z6])],[(0,[z616,z0,z1,z4,z8,z5,z6]),(0,[z617,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z618,z8,z5,z6]),(0,[z146,z1,z4,z8,z5,z6,z11]),(0,[z163,z1,z4,z8,z5,z6,z11]),(0,[z117,z1,z4,z8,z5,z6,z11]),(0,[z354,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z538]),(1,[z263,z0,z1,z5,z92,z6]),(1,[z0,z525,z4,z8,z5,z6])]],
   [[(0,[z146,z1,z4,z8,z237,z5,z6]),(0,[z0,z1,z4,z619,z8,z5,z6]),(0,[z0,z395,z1,z4,z8,z5,z6]),(0,[z620,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z621,z6]),(0,[z0,z1,z4,z8,z5,z6,z157]),(0,[z0,z1,z239,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z69,z5,z22])],[(0,[z0,z1,z4,z8,z5,z376,z6]),(0,[z622,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z623,z6]),(0,[z263,z0,z1,z4,z41,z5,z6]),(0,[z0,z1,z4,z8,z5,z624,z6])],[(0,[z146,z227,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z55,z6]),(0,[z0,z1,z4,z8,z5,z139,z6]),(0,[z0,z1,z134,z4,z5,z92,z6]),(0,[z625,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z262,z8,z5,z30])],[(0,[z0,z1,z4,z8,z5,z147,z6])],[(0,[z0,z1,z4,z626,z8,z5,z6]),(0,[z0,z407,z1,z4,z8,z5,z6]),(0,[z0,z627,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z628]),(0,[z0,z1,z4,z8,z629,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z630]),(1,[z0,z305,z4,z8,z5,z6])],[(0,[z122,z1,z3,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z233]),(1,[z97,z1,z27,z8,z5,z6]),(0,[z146,z0,z1,z4,z106,z5,z6]),(0,[z0,z67,z1,z134,z8,z5,z6]),(0,[z34,z21,z0,z1,z4,z8,z5])],[(0,[z0,z1,z4,z8,z631,z5,z6]),(0,[z0,z1,z4,z632,z8,z5,z6]),(0,[z633,z0,z1,z4,z8,z5,z6])],[(0,[z634,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z635,z6]),(0,[z0,z1,z200,z4,z8,z5,z6]),(0,[z0,z67,z395,z1,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z636,z6]),(0,[z383,z0,z1,z4,z8,z5,z14]),(0,[z0,z1,z4,z8,z637,z5,z6]),(0,[z0,z1,z638,z4,z8,z5,z6])]],
   [[(0,[z117,z0,z4,z8,z5,z140,z6]),(0,[z0,z1,z185,z4,z8,z5,z65])],[(0,[z33,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z639,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z355,z92,z6]),(0,[z0,z1,z4,z262,z41,z5,z6]),(0,[z0,z1,z4,z8,z5,z55,z119]),(0,[z245,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z640,z6]),(0,[z0,z1,z4,z8,z641,z5,z6]),(0,[z130,z1,z27,z4,z8,z5,z6]),(0,[z0,z1,z642,z4,z8,z5,z6]),(1,[z1,z4,z8,z5,z11,z14]),(0,[z42,z0,z44,z4,z8,z5,z6]),(0,[z0,z643,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z272]),(0,[z0,z1,z185,z8,z5,z16,z6])],[(0,[z97,z174,z1,z4,z8,z5,z6]),(0,[z51,z0,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z16,z6,z11]),(0,[z42,z33,z1,z4,z8,z5,z6])],[(0,[z644,z0,z1,z4,z8,z5,z6]),(0,[z45,z1,z4,z8,z5,z6,z11]),(0,[z645,z0,z1,z4,z8,z5,z6]),(0,[z0,z45,z1,z4,z8,z84,z6])],[(0,[z123,z0,z1,z4,z8,z5,z6]),(0,[z33,z227,z1,z4,z8,z5,z6]),(0,[z1,z27,z4,z8,z5,z6,z11]),(0,[z42,z146,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z646,z8,z5,z6]),(0,[z170,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z647])],[(0,[z122,z1,z4,z106,z8,z5,z6]),(0,[z130,z0,z1,z4,z8,z147,z6]),(0,[z648,z0,z1,z4,z8,z5,z6]),(0,[z0,z4,z8,z5,z140,z6,z14])]],
   [[(0,[z1,z4,z8,z28,z5,z6,z11]),(0,[z0,z1,z4,z8,z101,z140,z6]),(0,[z649,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z650,z8,z5,z6])],[(0,[z152,z74,z1,z4,z8,z5,z6]),(0,[z603,z0,z1,z4,z8,z5,z6]),(1,[z33,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z619,z8,z5,z6]),(0,[z33,z395,z1,z4,z8,z5,z6]),(0,[z42,z0,z1,z4,z8,z5,z443]),(0,[z0,z45,z1,z4,z8,z140,z6]),(0,[z1,z4,z8,z5,z12,z6,z253])],[(0,[z0,z1,z4,z8,z5,z651,z6]),(1,[z362,z1,z4,z8,z5,z6])],[(0,[z652,z0,z1,z4,z8,z5,z6]),(0,[z87,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z5,z653]),(0,[z0,z1,z185,z63,z8,z5,z6])],[(0,[z0,z1,z4,z105,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z654]),(0,[z0,z1,z4,z8,z5,z655,z6]),(1,[z0,z45,z4,z8,z84,z6]),(0,[z391,z0,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z427,z5,z6]),(0,[z21,z0,z1,z4,z120,z5,z6])],[(0,[z97,z0,z1,z27,z8,z5,z6]),(0,[z13,z0,z1,z4,z8,z5,z653]),(0,[z0,z1,z4,z8,z5,z656,z6]),(0,[z165,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z657,z6])],[(0,[z0,z67,z4,z99,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z658,z6]),(0,[z0,z1,z4,z8,z5,z315,z6]),(0,[z33,z1,z4,z8,z5,z12,z6]),(1,[z0,z1,z4,z8,z5,z443]),(0,[z0,z1,z4,z659,z8,z5,z6]),(0,[z0,z1,z185,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z5,z660,z6]),(0,[z0,z1,z4,z8,z5,z661,z6]),(0,[z0,z662,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z663,z5,z6]),(0,[z664,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z665,z5,z6]),(0,[z1,z4,z8,z5,z6,z11,z464]),(0,[z0,z1,z4,z8,z5,z666,z6]),(0,[z34,z0,z496,z4,z8,z5,z6]),(1,[z0,z220,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z667,z5,z6]),(0,[z21,z0,z1,z327,z8,z5,z6])],[(0,[z122,z0,z1,z27,z8,z5,z6])],[(0,[z0,z668,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z224,z8,z5,z6]),(0,[z0,z1,z4,z8,z64,z5,z6]),(0,[z0,z1,z4,z8,z669,z5,z6]),(0,[z0,z1,z4,z8,z670,z5,z6])],[(0,[z246,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z671,z6]),(0,[z0,z1,z4,z8,z28,z5,z6]),(0,[z44,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z672,z8,z5,z6]),(1,[z446,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z287]),(0,[z0,z4,z40,z8,z5,z139,z6]),(0,[z0,z1,z134,z41,z8,z5,z6]),(0,[z0,z1,z4,z673,z8,z5,z6]),(0,[z0,z432,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z294]),(0,[z0,z1,z4,z674,z8,z5,z6]),(0,[z13,z0,z67,z1,z8,z5,z6]),(0,[z39,z0,z1,z4,z5,z92,z6]),(0,[z0,z1,z4,z675,z8,z5,z6])],[(0,[z408,z1,z4,z8,z5,z6,z11]),(0,[z0,z4,z99,z8,z5,z6,z14]),(0,[z676,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z677,z6]),(0,[z34,z0,z1,z4,z8,z5,z65])]],
   [[(1,[z1,z4,z8,z5,z6,z11]),(0,[z0,z44,z1,z4,z8,z5,z14]),(1,[z137,z0,z1,z8,z16,z6]),(0,[z0,z1,z4,z8,z5,z119,z22])],[(0,[z74,z1,z4,z8,z5,z147,z6]),(0,[z0,z1,z678,z4,z8,z5,z6]),(0,[z0,z1,z4,z679,z8,z5,z6]),(0,[z18,z0,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z680]),(0,[z13,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z653,z6]),(0,[z0,z1,z681,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z14]),(0,[z0,z1,z134,z4,z41,z5,z6]),(0,[z0,z1,z682,z4,z8,z5,z6])],[(0,[z1,z4,z105,z8,z5,z147,z6]),(0,[z33,z511,z1,z4,z8,z5,z6]),(0,[z683,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z684])],[(0,[z263,z0,z1,z4,z5,z92,z6])],[(0,[z33,z1,z4,z105,z8,z5,z6]),(0,[z0,z1,z4,z685,z8,z5,z6]),(0,[z0,z52,z1,z4,z8,z5,z6]),(0,[z686,z0,z1,z4,z8,z5,z6])],[(0,[z50,z0,z1,z4,z8,z5,z11]),(0,[z1,z4,z8,z5,z6,z348,z11]),(0,[z0,z1,z4,z8,z687,z5,z6])],[(0,[z0,z1,z4,z8,z5,z688,z6]),(1,[z77,z1,z4,z8,z5,z6]),(0,[z34,z0,z1,z4,z277,z5,z6])]],
   [[(0,[z0,z1,z689,z4,z8,z5,z6]),(0,[z174,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z690,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z691,z6]),(0,[z0,z1,z4,z8,z5,z6,z692]),(0,[z0,z1,z4,z8,z69,z5,z6])],[(0,[z152,z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z693,z5,z6]),(0,[z1,z27,z4,z105,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z694,z6]),(0,[z117,z0,z1,z283,z8,z5,z6])],[(0,[z0,z1,z4,z695,z8,z5,z6]),(0,[z696,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z8,z5,z119,z6,z65])],[(0,[z0,z1,z4,z8,z5,z6,z697])],[(0,[z0,z1,z4,z8,z5,z6,z698]),(0,[z0,z1,z4,z699,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z6,z10]),(0,[z0,z1,z4,z8,z5,z700,z6]),(1,[z117,z0,z4,z8,z140,z6]),(0,[z0,z1,z4,z8,z5,z701,z6]),(0,[z0,z1,z4,z262,z5,z92,z6]),(0,[z0,z1,z4,z8,z5,z6,z702])],[(0,[z33,z1,z4,z8,z64,z5,z6]),(0,[z0,z703,z1,z4,z8,z5,z6]),(0,[z0,z1,z99,z8,z5,z92,z6]),(0,[z0,z704,z1,z4,z8,z5,z6]),(1,[z0,z432,z4,z8,z5,z6])],[(0,[z97,z1,z27,z4,z8,z5,z6]),(1,[z146,z1,z4,z237,z5,z6]),(0,[z33,z1,z4,z8,z28,z5,z6]),(0,[z241,z0,z1,z4,z8,z5,z6]),(0,[z34,z0,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z101,z6,z30])],[(0,[z122,z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z705,z5,z6]),(0,[z0,z1,z4,z8,z5,z706,z6]),(0,[z0,z1,z4,z8,z5,z92,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z137,z1,z8,z16,z6,z11]),(0,[z0,z1,z707,z8,z5,z6]),(0,[z170,z1,z4,z8,z5,z310]),(0,[z0,z432,z4,z96,z5,z6]),(0,[z0,z1,z327,z120,z5,z6])],[(0,[z163,z59,z1,z4,z5,z6]),(0,[z220,z4,z8,z5,z6,z11]),(0,[z708,z1,z4,z8,z5,z6])],[(0,[z0,z1,z8,z64,z709,z6])],[(0,[z324,z1,z4,z5,z147,z6]),(0,[z710,z33,z1,z4,z5,z6])],[(0,[z163,z0,z1,z4,z226,z6]),(0,[z4,z8,z5,z348,z11,z14]),(0,[z0,z1,z4,z711,z5,z6]),(0,[z0,z712,z4,z8,z5,z6])],[(0,[z77,z1,z4,z8,z5,z11]),(0,[z0,z1,z4,z713,z5,z6]),(0,[z15,z0,z1,z185,z8,z5])],[(0,[z1,z4,z8,z5,z6,z714])],[(0,[z0,z1,z715,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z716]),(0,[z196,z1,z4,z277,z5,z6])],[(0,[z0,z1,z717,z8,z5,z6]),(0,[z718,z1,z4,z8,z5,z6])],[(0,[z1,z435,z8,z5,z6,z11]),(0,[z0,z1,z719,z4,z5,z6])],[(0,[z0,z1,z4,z8,z5,z653])],[],[(0,[z1,z4,z8,z5,z720,z6]),(0,[z137,z0,z525,z8,z16,z6]),(0,[z0,z1,z185,z8,z5,z119])],[(0,[z0,z721,z4,z8,z5,z6])],[(0,[z174,z1,z4,z8,z249,z6]),(0,[z1,z4,z8,z69,z55,z11])],[(0,[z1,z4,z8,z28,z6,z189]),(0,[z0,z1,z722,z8,z5,z6])]],
   [[],[(0,[z1,z4,z8,z5,z326,z11]),(0,[z0,z220,z4,z8,z5,z6])],[(0,[z0,z1,z4,z723,z5,z6])],[(0,[z71,z1,z4,z8,z6,z172]),(0,[z0,z1,z5,z724,z92,z6]),(0,[z1,z4,z8,z5,z725,z310])],[(0,[z42,z269,z4,z5,z139,z6]),(0,[z0,z1,z283,z8,z5,z206]),(0,[z726,z1,z4,z8,z5,z6])],[(0,[z146,z416,z1,z4,z5,z6]),(0,[z0,z1,z4,z8,z5,z727]),(0,[z1,z4,z8,z5,z338,z11]),(0,[z0,z1,z4,z8,z728,z6]),(0,[z729,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z730,z5,z6])],[(0,[z0,z1,z4,z731,z5,z6]),(0,[z0,z1,z4,z8,z264,z65])],[(0,[z1,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z5,z653,z732]),(0,[z269,z52,z1,z4,z5,z6]),(0,[z39,z0,z285,z1,z4,z6]),(0,[z137,z0,z1,z8,z16,z6]),(0,[z463,z0,z1,z8,z16,z6])],[(0,[z0,z1,z4,z5,z733,z6]),(0,[z1,z4,z8,z5,z6,z734])],[(0,[z735,z1,z4,z8,z5,z6]),(0,[z34,z0,z293,z4,z8,z5])],[(0,[z0,z1,z736,z8,z5,z6])],[(0,[z737,z1,z4,z8,z5,z6]),(0,[z738,z1,z4,z8,z5,z6]),(0,[z739,z1,z4,z8,z5,z142])],[(0,[z1,z185,z8,z5,z119,z11]),(0,[z305,z4,z8,z5,z19,z11]),(0,[z0,z1,z8,z5,z119,z740])],[(0,[z246,z33,z1,z4,z5,z6])],[(0,[z246,z0,z1,z4,z5,z6]),(0,[z0,z1,z283,z184,z5,z6]),(0,[z741,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z19,z742]),(0,[z743,z1,z4,z8,z5,z6])],[(0,[z1,z4,z5,z315,z6,z11])]],
   [[],[(0,[z0,z1,z744,z8,z5,z6])],[(0,[z0,z305,z4,z8,z5,z12])],[(0,[z0,z1,z4,z745,z5,z6]),(0,[z746,z0,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z149]),(0,[z146,z1,z4,z731,z5,z6]),(0,[z1,z4,z8,z5,z531,z11]),(0,[z550,z0,z4,z8,z5,z14]),(0,[z0,z1,z747,z8,z5,z6]),(0,[z1,z4,z8,z5,z139,z748]),(0,[z39,z0,z749,z1,z4,z6])],[(0,[z0,z432,z4,z8,z5,z6]),(0,[z0,z1,z750,z8,z5,z6])],[(0,[z0,z1,z751,z8,z5,z6]),(0,[z1,z4,z17,z5,z6,z11]),(0,[z15,z0,z1,z8,z5,z65]),(0,[z0,z1,z4,z8,z264,z6]),(0,[z0,z752,z4,z8,z5,z6])],[(0,[z0,z1,z4,z224,z5,z30])],[(0,[z603,z1,z4,z8,z5,z11]),(0,[z408,z0,z1,z4,z5,z30]),(0,[z0,z1,z4,z17,z5,z6])],[(0,[z0,z1,z110,z8,z5,z288]),(0,[z0,z1,z4,z8,z5,z753]),(0,[z0,z1,z4,z8,z5,z754])],[(0,[z1,z4,z8,z28,z98,z6]),(0,[z319,z1,z4,z8,z5,z288]),(0,[z269,z1,z4,z8,z5,z748]),(0,[z21,z362,z1,z4,z8,z22])],[(0,[z0,z755,z4,z8,z5,z6]),(0,[z42,z4,z8,z5,z11,z14]),(0,[z1,z4,z8,z5,z6,z756]),(0,[z0,z1,z4,z277,z5,z14])],[(0,[z1,z4,z8,z5,z11,z145]),(0,[z0,z1,z4,z8,z5,z757]),(0,[z1,z4,z224,z5,z6,z253]),(0,[z758,z1,z4,z8,z5,z6])],[(0,[z246,z0,z1,z4,z5,z759]),(0,[z0,z1,z4,z760,z5,z6]),(0,[z1,z4,z8,z5,z11,z360]),(0,[z0,z4,z8,z761,z140,z6]),(0,[z0,z762,z4,z8,z5,z6])],[(0,[z152,z246,z3,z4,z5,z6]),(0,[z1,z27,z8,z5,z273,z6]),(0,[z0,z4,z8,z226,z6,z14]),(0,[z1,z4,z8,z5,z6,z763]),(0,[z245,z1,z4,z8,z69,z55])],[(0,[z1,z3,z4,z8,z5,z294]),(0,[z33,z4,z8,z5,z6,z157]),(0,[z0,z44,z4,z8,z5,z12])],[(0,[z764,z1,z4,z8,z5,z6]),(0,[z765,z1,z4,z8,z5,z6])]],
   [[(0,[z1,z4,z8,z28,z766,z6]),(0,[z767,z1,z4,z8,z5,z6]),(0,[z768,z1,z4,z8,z5,z6]),(0,[z769,z1,z4,z8,z5,z6])],[],[(0,[z0,z770,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z11]),(0,[z0,z1,z4,z8,z5,z742])],[(0,[z0,z1,z771,z8,z5,z6])],[(1,[z1,z4,z731,z5,z6]),(0,[z1,z4,z262,z5,z19,z11]),(0,[z51,z1,z4,z619,z5,z6]),(0,[z0,z44,z4,z8,z5,z653]),(0,[z417,z0,z4,z8,z5,z14]),(0,[z0,z772,z4,z8,z5,z6])],[(0,[z165,z1,z4,z5,z101,z6])],[(0,[z0,z1,z4,z8,z5,z773]),(0,[z0,z1,z4,z774,z5,z6]),(0,[z0,z1,z4,z775,z5,z6])],[(0,[z42,z1,z4,z5,z11,z30]),(0,[z1,z4,z8,z5,z19,z11]),(0,[z0,z776,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z777])],[],[(0,[z246,z1,z4,z237,z5,z6]),(0,[z0,z1,z4,z778,z5,z6])],[(0,[z108,z1,z4,z8,z5,z6]),(0,[z74,z195,z4,z8,z5,z6]),(0,[z779,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z226,z6,z30]),(0,[z0,z1,z8,z5,z709,z6]),(0,[z0,z1,z4,z262,z5,z19]),(0,[z0,z1,z239,z96,z5,z6]),(0,[z1,z4,z8,z5,z6,z780])],[(0,[z0,z781,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z199,z272]),(0,[z0,z1,z110,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z782])],[(0,[z319,z1,z4,z8,z5,z6]),(0,[z0,z783,z4,z8,z5,z6]),(0,[z138,z62,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z109,z310]),(0,[z39,z104,z192,z1,z4,z6])],[(0,[z33,z1,z4,z8,z5,z635]),(0,[z1,z4,z8,z5,z443,z11]),(0,[z18,z33,z1,z4,z5,z30]),(0,[z0,z1,z4,z5,z6,z732]),(0,[z0,z784,z4,z8,z5,z6]),(0,[z196,z496,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z785,z6]),(0,[z18,z167,z1,z4,z5,z30])],[(0,[z0,z1,z8,z5,z740,z65]),(1,[z0,z1,z327,z8,z22])]],
   [[(0,[z307,z3,z4,z8,z5,z6]),(0,[z130,z1,z4,z8,z439,z6]),(0,[z0,z559,z4,z8,z5,z12]),(0,[z1,z4,z8,z5,z6,z786]),(0,[z0,z1,z185,z8,z5,z740])],[(0,[z174,z1,z4,z8,z325,z6]),(0,[z787,z1,z4,z8,z5,z6]),(0,[z788,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z6,z742])],[(0,[z0,z1,z283,z8,z5,z6]),(0,[z789,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z790,z5])],[(0,[z791,z0,z1,z4,z5,z6]),(0,[z42,z33,z4,z5,z139,z6]),(0,[z0,z1,z4,z792,z5,z6]),(0,[z0,z1,z4,z8,z5,z793]),(0,[z369,z0,z1,z4,z5,z30])],[(0,[z0,z1,z4,z5,z551,z30]),(0,[z794,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z795,z5,z6])],[(0,[z796,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z797,z5,z6])],[(0,[z710,z0,z1,z4,z5,z6]),(0,[z1,z4,z8,z5,z6,z798])],[(0,[z1,z239,z8,z5,z6,z11]),(0,[z1,z4,z8,z5,z6,z799]),(0,[z0,z1,z800,z8,z5,z6])],[(0,[z51,z1,z4,z8,z5,z11]),(0,[z33,z1,z4,z8,z226,z6]),(0,[z21,z33,z1,z4,z8,z22]),(0,[z0,z283,z8,z5,z140,z6]),(0,[z801,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z724,z6]),(0,[z0,z1,z802,z8,z5,z6]),(0,[z0,z1,z4,z803,z5,z6])],[(0,[z42,z0,z1,z4,z5,z367]),(0,[z21,z0,z1,z4,z8,z22])],[(0,[z241,z4,z8,z5,z11,z14]),(0,[z0,z1,z4,z215,z5,z361])],[(0,[z125,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z261,z11]),(0,[z117,z166,z4,z8,z140,z6]),(0,[z0,z1,z4,z8,z5,z804]),(0,[z0,z749,z1,z4,z5,z6])],[(0,[z146,z1,z4,z547,z5,z6]),(0,[z0,z1,z4,z805,z5,z6]),(0,[z0,z1,z4,z8,z5,z806])],[],[(0,[z13,z4,z8,z5,z11,z14]),(0,[z0,z45,z4,z8,z761,z6]),(0,[z807,z1,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z808,z8,z5,z6]),(0,[z809,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z215,z5,z142]),(0,[z810,z1,z4,z8,z5,z6]),(0,[z362,z432,z4,z8,z5,z6])],[(0,[z0,z1,z4,z5,z811,z6])],[(0,[z0,z1,z4,z8,z5,z812]),(0,[z34,z0,z496,z8,z5,z65])],[(0,[z0,z1,z4,z813,z5,z6]),(0,[z814,z1,z4,z8,z5,z6]),(0,[z33,z1,z4,z5,z6,z272])],[(0,[z0,z815,z4,z8,z5,z6])],[(0,[z816,z0,z1,z4,z5,z6]),(0,[z1,z501,z4,z8,z5,z11])],[(0,[z214,z1,z4,z8,z5,z6]),(0,[z1,z4,z502,z8,z5,z11]),(0,[z817,z1,z4,z8,z5,z6]),(0,[z196,z1,z4,z8,z35,z6])],[(0,[z33,z1,z4,z8,z5,z287]),(0,[z818,z1,z4,z8,z5,z6]),(0,[z0,z4,z8,z5,z6,z819])],[(0,[z33,z1,z4,z8,z5,z294]),(0,[z324,z33,z1,z4,z5,z6]),(0,[z1,z4,z8,z5,z6,z820]),(0,[z0,z293,z4,z8,z5,z55])],[(0,[z324,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z8,z5,z748])],[(0,[z1,z4,z8,z5,z206,z11]),(0,[z767,z1,z4,z8,z5,z11]),(0,[z0,z821,z395,z8,z5,z6])],[(0,[z0,z1,z4,z8,z822,z6]),(0,[z0,z1,z4,z8,z823,z6]),(0,[z383,z0,z4,z8,z5,z824])],[(0,[z246,z59,z1,z4,z5,z6]),(0,[z33,z1,z4,z8,z5,z310]),(0,[z825,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z262,z5,z443]),(0,[z15,z0,z1,z4,z797,z5]),(0,[z34,z0,z1,z277,z5,z65])],[(0,[z0,z1,z412,z8,z5,z206]),(1,[z0,z4,z8,z761,z6])],[(0,[z0,z826,z4,z8,z5,z6]),(0,[z0,z1,z239,z8,z5,z6]),(0,[z827,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z6,z828]),(0,[z0,z1,z8,z5,z6,z740]),(0,[z0,z1,z327,z8,z6,z22])]],
   [[(0,[z829,z1,z4,z8,z5,z6])],[(0,[z0,z1,z830,z4,z5,z6]),(0,[z1,z4,z8,z5,z6,z831]),(0,[z832,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z833,z5,z6]),(0,[z0,z1,z4,z8,z687,z55])],[(0,[z1,z834,z4,z8,z5,z6]),(0,[z446,z1,z4,z8,z5,z287])],[(0,[z0,z835,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z836])],[(0,[z0,z44,z110,z8,z5,z6]),(0,[z837,z1,z4,z8,z5,z6]),(0,[z838,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z839]),(0,[z166,z1,z4,z8,z5,z160]),(0,[z0,z1,z840,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z841])],[(0,[z583,z3,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z344]),(0,[z0,z1,z412,z184,z5,z6]),(0,[z1,z4,z8,z5,z6,z842]),(0,[z18,z115,z1,z4,z5,z30])],[(0,[z138,z1,z4,z8,z5,z6]),(0,[z843,z0,z1,z4,z8,z5]),(0,[z163,z1,z4,z8,z5,z367]),(0,[z1,z4,z8,z5,z6,z844])],[(0,[z77,z1,z4,z5,z6,z272]),(0,[z1,z4,z8,z5,z845,z6]),(0,[z34,z0,z220,z8,z5,z65])],[(0,[z269,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z846]),(0,[z0,z847,z4,z8,z5,z6])],[(0,[z0,z1,z4,z226,z139,z6]),(0,[z0,z1,z327,z8,z5,z22])],[(0,[z174,z1,z4,z8,z5,z367]),(0,[z0,z1,z4,z848,z5,z6])],[(0,[z1,z4,z8,z5,z147,z367]),(0,[z1,z4,z8,z5,z11,z30]),(0,[z0,z1,z4,z8,z5,z849]),(0,[z1,z4,z8,z5,z206,z756])],[(0,[z0,z1,z4,z8,z5,z850]),(0,[z0,z1,z4,z851,z5,z6]),(0,[z0,z62,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z852]),(0,[z0,z853,z4,z8,z5,z6])]],
   [[(0,[z854,z1,z4,z8,z5,z443]),(1,[z0,z1,z4,z5,z742])],[(0,[z252,z1,z105,z8,z5,z6])],[(0,[z0,z293,z239,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z855]),(0,[z451,z0,z1,z5,z92,z6]),(0,[z0,z1,z185,z8,z5,z553])],[(0,[z39,z33,z192,z1,z4,z6]),(0,[z42,z0,z4,z5,z139,z288])],[(0,[z0,z1,z4,z8,z5,z856]),(0,[z33,z1,z4,z120,z5,z6]),(0,[z59,z1,z4,z8,z226,z6])],[(0,[z0,z1,z435,z8,z242,z6])],[(0,[z857,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z274,z5,z160]),(0,[z1,z4,z8,z5,z6,z858])],[(0,[z33,z1,z4,z8,z5,z376]),(0,[z0,z1,z4,z5,z315,z6]),(0,[z33,z1,z4,z215,z5,z6]),(0,[z103,z62,z4,z8,z5,z6])],[(0,[z859,z1,z4,z8,z5,z6])],[(0,[z246,z1,z4,z5,z6,z11])],[(0,[z33,z1,z327,z8,z5,z6]),(0,[z0,z4,z8,z5,z555,z14])],[(0,[z860,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z861]),(0,[z1,z4,z8,z5,z862,z6])],[(0,[z863,z0,z1,z4,z5,z6]),(0,[z864,z1,z4,z8,z5,z6]),(0,[z865,z1,z4,z8,z5,z6]),(0,[z866,z1,z4,z8,z5,z6])],[(0,[z122,z1,z867,z8,z5,z6]),(0,[z395,z99,z8,z5,z6,z11]),(0,[z33,z395,z99,z8,z5,z6])],[(0,[z0,z1,z4,z868,z5,z6]),(0,[z0,z496,z4,z277,z5,z6]),(0,[z0,z1,z185,z8,z264,z6]),(0,[z21,z0,z432,z4,z8,z22])]],
   [[],[(0,[z0,z1,z869,z4,z5,z6]),(0,[z42,z0,z4,z5,z614,z6]),(0,[z870,z1,z4,z8,z5,z6]),(0,[z15,z0,z1,z4,z871,z5]),(0,[z18,z0,z1,z4,z5,z30])],[(0,[z1,z4,z8,z5,z294,z11]),(1,[z835,z4,z8,z5,z6]),(0,[z0,z32,z99,z8,z5,z6]),(0,[z0,z1,z4,z8,z69,z872])],[(0,[z383,z4,z8,z5,z11,z14]),(0,[z873,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z6,z874]),(0,[z875,z1,z4,z8,z5,z6]),(0,[z399,z0,z4,z8,z5,z14])],[(0,[z1,z4,z8,z264,z6,z11]),(0,[z33,z1,z4,z8,z5,z142]),(0,[z196,z220,z4,z8,z5,z6])],[(0,[z74,z835,z4,z8,z5,z6]),(0,[z0,z1,z63,z8,z64,z6])],[(0,[z128,z3,z4,z8,z5,z6]),(0,[z246,z174,z1,z4,z5,z6]),(0,[z876,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z288]),(0,[z42,z0,z4,z5,z139,z6]),(0,[z877,z1,z4,z8,z5,z6]),(0,[z15,z0,z847,z4,z8,z5]),(0,[z0,z878,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z11,z581]),(0,[z117,z0,z283,z8,z140,z6]),(0,[z0,z1,z4,z427,z5,z142]),(0,[z0,z293,z185,z4,z8,z5])],[],[(0,[z0,z44,z4,z5,z12,z272]),(0,[z362,z1,z239,z8,z5,z6])],[(0,[z1,z4,z8,z5,z6,z253]),(0,[z0,z1,z412,z8,z5,z6]),(0,[z13,z0,z333,z8,z5,z6]),(0,[z0,z1,z4,z879,z5,z6]),(0,[z880,z1,z4,z8,z5,z288]),(0,[z0,z1,z4,z184,z5,z206]),(0,[z881,z1,z4,z8,z5,z160]),(0,[z882,z1,z4,z8,z5,z361]),(0,[z0,z1,z569,z8,z5,z119])],[(0,[z883,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z376,z11]),(0,[z1,z4,z8,z5,z6,z256]),(0,[z0,z884,z4,z8,z5,z6]),(0,[z15,z0,z1,z4,z8,z22])],[(0,[z77,z1,z4,z8,z5,z376]),(0,[z0,z1,z4,z8,z766,z6]),(0,[z33,z1,z4,z8,z5,z160]),(0,[z885,z1,z4,z8,z5,z6]),(0,[z886,z1,z4,z8,z5,z6])],[(0,[z1,z27,z4,z8,z5,z367]),(0,[z0,z4,z8,z5,z6,z824]),(0,[z887,z1,z4,z8,z5,z6])]],
   [[(0,[z603,z1,z4,z8,z5,z294]),(0,[z0,z1,z110,z5,z6,z30]),(0,[z540,z0,z4,z8,z5,z14])],[(0,[z888,z1,z4,z8,z5,z6])],[(0,[z270,z1,z4,z8,z5,z6]),(0,[z33,z1,z435,z8,z5,z6]),(0,[z0,z1,z4,z8,z226,z443]),(0,[z889,z1,z4,z8,z5,z6]),(0,[z1,z185,z8,z5,z119,z256])],[(0,[z408,z1,z4,z5,z11,z30]),(0,[z890,z1,z4,z8,z5,z6])],[],[(0,[z0,z891,z4,z8,z5,z6]),(0,[z892,z1,z4,z8,z5,z6])],[(0,[z152,z1,z4,z8,z5,z367])],[(0,[z146,z1,z4,z693,z5,z6]),(0,[z893,z1,z4,z8,z5,z206])],[(0,[z73,z1,z4,z8,z5,z11]),(0,[z0,z1,z435,z8,z5,z443]),(0,[z0,z1,z4,z8,z894,z6]),(0,[z0,z4,z8,z84,z761,z6]),(0,[z0,z1,z4,z277,z35,z6])],[(0,[z0,z1,z4,z895,z5,z6]),(0,[z0,z1,z4,z483,z101,z6]),(0,[z196,z1,z4,z8,z264,z6]),(0,[z0,z1,z4,z650,z101,z6]),(0,[z21,z0,z1,z4,z120,z22])],[],[(0,[z0,z1,z4,z8,z5,z824]),(0,[z196,z1,z4,z17,z5,z6]),(0,[z0,z1,z8,z5,z264,z65]),(0,[z0,z305,z4,z262,z5,z19])],[(0,[z0,z1,z4,z8,z5,z896]),(0,[z122,z1,z632,z8,z5,z6]),(0,[z1,z4,z8,z5,z11,z157]),(0,[z1,z4,z8,z5,z6,z897])],[(0,[z1,z4,z8,z5,z6,z898]),(0,[z1,z4,z8,z5,z6,z899])],[(0,[z0,z45,z4,z8,z181,z6])],[(0,[z323,z1,z4,z8,z147,z6])]],
   [[(0,[z1,z4,z8,z5,z655,z11]),(0,[z900,z1,z4,z8,z5,z6])],[(0,[z163,z1,z4,z106,z5,z6]),(0,[z633,z0,z1,z8,z5,z65])],[(0,[z163,z1,z610,z4,z5,z6]),(0,[z1,z4,z8,z5,z142,z901]),(0,[z0,z1,z185,z327,z8,z5])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z902,z1,z4,z8,z5,z6])],[(0,[z103,z1,z4,z8,z5,z6]),(0,[z0,z121,z4,z8,z5,z12])],[],[(0,[z903,z0,z1,z8,z5,z6]),(0,[z1,z4,z8,z5,z11,z272]),(0,[z1,z4,z8,z5,z904,z6])],[],[(0,[z0,z1,z4,z8,z5,z759]),(0,[z0,z171,z4,z40,z5,z6]),(0,[z0,z220,z4,z8,z5,z14])],[(0,[z33,z1,z4,z8,z5,z698]),(0,[z0,z1,z4,z905,z5,z653]),(0,[z0,z525,z4,z215,z5,z6]),(0,[z906,z1,z4,z8,z5,z6])],[(0,[z122,z1,z105,z8,z5,z6]),(0,[z130,z1,z4,z8,z660,z6]),(0,[z0,z1,z4,z8,z5,z907])],[(0,[z0,z1,z4,z8,z5,z908]),(0,[z0,z110,z8,z5,z6,z14]),(0,[z1,z4,z8,z5,z19,z253]),(0,[z15,z873,z1,z4,z8,z5]),(0,[z34,z0,z1,z8,z35,z65])],[(0,[z0,z1,z4,z8,z69,z425]),(0,[z909,z1,z4,z8,z5,z6])],[(0,[z383,z33,z4,z8,z5,z14]),(0,[z910,z1,z4,z8,z5,z6]),(0,[z0,z749,z1,z4,z8,z6])],[(0,[z0,z1,z4,z5,z911,z6]),(0,[z146,z1,z4,z237,z5,z149]),(0,[z0,z1,z4,z8,z5,z912]),(0,[z42,z4,z5,z243,z139,z6]),(0,[z0,z192,z749,z1,z4,z6]),(0,[z913,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z914]),(0,[z0,z377,z99,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z206]),(0,[z915,z1,z4,z8,z5,z6]),(0,[z916,z1,z4,z8,z5,z6]),(0,[z0,z1,z917,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z5,z918])],[(0,[z45,z4,z8,z5,z11,z14]),(0,[z33,z496,z4,z8,z5,z6]),(0,[z166,z1,z4,z274,z5,z6])],[(0,[z263,z33,z1,z5,z92,z6]),(0,[z919,z1,z4,z8,z5,z6])],[(0,[z0,z1,z867,z8,z5,z6]),(0,[z686,z0,z4,z8,z5,z14])],[(0,[z152,z246,z1,z4,z5,z6]),(0,[z1,z4,z8,z5,z6,z920]),(0,[z473,z0,z67,z8,z5,z6])],[(0,[z324,z1,z4,z5,z6,z11]),(0,[z4,z8,z5,z6,z11,z157])],[(0,[z347,z1,z4,z8,z5,z160]),(0,[z0,z525,z4,z8,z5,z142]),(0,[z0,z1,z327,z8,z69,z6])],[(0,[z921,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z922,z6]),(0,[z1,z4,z215,z5,z6,z11]),(0,[z87,z1,z450,z8,z5,z6]),(0,[z0,z1,z4,z923,z5,z6]),(0,[z39,z165,z1,z4,z5,z6]),(0,[z39,z0,z192,z1,z4,z6])],[(0,[z0,z1,z4,z8,z5,z924]),(0,[z241,z0,z4,z8,z5,z14]),(0,[z279,z1,z4,z547,z5,z6]),(0,[z0,z1,z4,z184,z5,z6]),(0,[z0,z1,z4,z925,z5,z6]),(0,[z0,z1,z4,z96,z5,z6]),(0,[z0,z1,z4,z8,z55,z872])],[(0,[z284,z1,z4,z8,z5,z11]),(1,[z1,z4,z8,z5,z748])],[(0,[z196,z1,z4,z8,z5,z12]),(0,[z926,z1,z4,z8,z5,z6]),(0,[z21,z0,z1,z327,z8,z22])],[(0,[z1,z4,z427,z5,z6,z11]),(0,[z493,z0,z4,z8,z140,z6]),(0,[z927,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z928]),(0,[z0,z4,z8,z5,z653,z14]),(0,[z0,z1,z4,z8,z264,z14]),(0,[z1,z4,z8,z5,z81,z14]),(0,[z0,z1,z4,z929,z5,z6]),(0,[z930,z1,z4,z8,z5,z6])],[(0,[z152,z495,z4,z8,z5,z6]),(0,[z931,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z54,z101,z6])],[(0,[z1,z4,z106,z5,z523,z6]),(0,[z1,z4,z8,z5,z11,z14]),(0,[z33,z1,z4,z277,z5,z6]),(0,[z0,z437,z99,z8,z5,z6]),(0,[z59,z1,z435,z8,z5,z6]),(0,[z0,z1,z4,z8,z932,z6]),(0,[z347,z1,z4,z274,z5,z6]),(0,[z933,z1,z4,z8,z5,z6]),(0,[z34,z0,z1,z8,z5,z740])],[(0,[z0,z1,z110,z8,z226,z6])]],
   [[(0,[z0,z1,z934,z8,z5,z6]),(0,[z935,z1,z4,z8,z5,z6]),(0,[z21,z1,z4,z8,z11,z22]),(0,[z319,z1,z4,z8,z226,z6])],[(0,[z0,z1,z4,z8,z936,z6]),(1,[z0,z1,z8,z5,z740])],[(0,[z324,z174,z1,z4,z5,z6]),(0,[z1,z4,z8,z5,z443,z897]),(0,[z0,z1,z193,z8,z64,z6])],[(0,[z1,z4,z8,z5,z11,z564]),(0,[z1,z4,z8,z5,z61,z11]),(0,[z39,z192,z1,z4,z6,z11]),(0,[z33,z1,z4,z8,z5,z361]),(0,[z937,z1,z4,z8,z5,z6]),(0,[z39,z192,z178,z1,z4,z6]),(0,[z167,z1,z4,z8,z5,z19]),(0,[z0,z1,z4,z262,z5,z742]),(0,[z354,z1,z239,z8,z5,z6])],[(0,[z456,z1,z4,z8,z325,z6]),(0,[z938,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z939,z6])],[(0,[z893,z1,z4,z8,z5,z6]),(0,[z42,z59,z4,z5,z139,z6]),(0,[z0,z4,z224,z5,z6,z14]),(0,[z0,z1,z940,z8,z5,z6]),(0,[z0,z44,z4,z8,z5,z824])],[(0,[z0,z1,z4,z427,z5,z361]),(0,[z104,z1,z4,z5,z101,z6])],[(0,[z391,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z11,z697]),(0,[z1,z4,z184,z5,z6,z11]),(0,[z0,z220,z4,z277,z5,z6])],[(0,[z33,z1,z4,z224,z5,z6]),(0,[z0,z1,z4,z941,z5,z6]),(0,[z0,z1,z4,z8,z16,z142])],[(0,[z835,z3,z4,z8,z5,z6]),(0,[z0,z1,z942,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z943])],[(0,[z944,z1,z4,z8,z5,z6]),(0,[z1,z4,z5,z101,z11,z30]),(0,[z945,z1,z4,z8,z5,z653]),(0,[z1,z4,z8,z5,z160,z799]),(0,[z137,z0,z1,z215,z16,z6])],[(0,[z1,z4,z8,z5,z243,z6]),(0,[z0,z1,z4,z8,z5,z946]),(0,[z1,z4,z5,z538,z11,z30])],[(0,[z108,z1,z4,z8,z5,z287]),(0,[z0,z1,z110,z262,z5,z6]),(0,[z354,z432,z4,z8,z5,z6])],[(0,[z227,z4,z8,z5,z6,z348]),(0,[z33,z1,z4,z8,z5,z367]),(0,[z1,z4,z8,z5,z100,z11]),(0,[z947,z1,z4,z8,z5,z6]),(0,[z0,z1,z948,z8,z5,z6]),(0,[z0,z293,z4,z96,z5,z6])],[(0,[z0,z1,z4,z8,z949,z6]),(0,[z0,z1,z4,z224,z5,z443]),(0,[z0,z496,z4,z8,z35,z6])],[(0,[z903,z1,z8,z5,z6,z11])]],
   [[(0,[z0,z1,z4,z8,z950,z6]),(0,[z146,z1,z4,z218,z5,z6])],[(1,[z1,z867,z8,z5,z6]),(0,[z1,z4,z8,z5,z11,z43]),(0,[z117,z0,z412,z8,z140,z6])],[(0,[z0,z1,z4,z5,z101,z367]),(0,[z951,z1,z4,z8,z5,z6]),(0,[z952,z1,z4,z8,z5,z6])],[(0,[z953,z1,z4,z8,z5,z6]),(0,[z34,z0,z1,z8,z5,z424]),(1,[z0,z1,z8,z709,z6])],[(0,[z1,z4,z8,z5,z127,z11]),(0,[z33,z1,z4,z8,z242,z6]),(0,[z954,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z955]),(1,[z0,z749,z1,z4,z6]),(0,[z0,z432,z4,z120,z5,z6])],[(0,[z0,z1,z956,z8,z5,z6]),(0,[z407,z4,z8,z5,z6,z348]),(0,[z33,z1,z4,z8,z69,z55]),(0,[z0,z1,z957,z8,z5,z6]),(0,[z1,z4,z8,z5,z12,z81])],[(0,[z958,z0,z1,z4,z5,z6]),(0,[z959,z1,z4,z8,z5,z6])],[(0,[z137,z0,z1,z8,z16,z142])],[(0,[z130,z1,z4,z8,z147,z6]),(0,[z860,z1,z4,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z960]),(0,[z961,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z148,z11]),(0,[z4,z40,z8,z5,z11,z14]),(0,[z39,z1,z4,z5,z11,z30]),(0,[z33,z1,z4,z274,z5,z6]),(0,[z962,z1,z4,z8,z5,z6]),(0,[z586,z0,z1,z8,z16,z6])],[(0,[z130,z1,z4,z8,z766,z6]),(0,[z1,z963,z8,z5,z6,z11]),(0,[z0,z1,z4,z8,z964,z6]),(0,[z0,z1,z4,z8,z242,z443]),(0,[z0,z1,z8,z16,z65,z22]),(0,[z0,z432,z327,z8,z5,z6])],[],[(0,[z371,z1,z4,z8,z5,z11]),(0,[z163,z1,z4,z731,z5,z6]),(0,[z1,z4,z8,z5,z160,z11])],[(0,[z0,z1,z4,z8,z5,z6]),(0,[z463,z0,z1,z8,z5,z65])],[(0,[z1,z4,z8,z237,z5,z367]),(0,[z1,z4,z8,z5,z6,z965]),(0,[z293,z4,z8,z5,z6,z11]),(0,[z33,z525,z4,z8,z5,z6]),(0,[z77,z1,z4,z224,z5,z6]),(0,[z966,z1,z4,z8,z5,z6])],[(0,[z117,z33,z4,z8,z140,z6]),(0,[z383,z391,z4,z8,z5,z14])]],
   [[(0,[z1,z4,z8,z168,z5,z11]),(0,[z967,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z968])],[(0,[z1,z4,z120,z5,z6,z11]),(0,[z880,z1,z4,z8,z5,z6]),(0,[z0,z1,z185,z8,z5,z46]),(0,[z1,z4,z8,z5,z6,z969]),(0,[z0,z525,z4,z427,z5,z6])],[(0,[z227,z4,z8,z5,z210,z6]),(0,[z222,z1,z4,z8,z5,z149]),(0,[z0,z1,z4,z970,z5,z6])],[(0,[z1,z4,z8,z5,z180,z11]),(0,[z0,z1,z4,z8,z5,z971]),(0,[z0,z1,z4,z8,z5,z972]),(0,[z973,z1,z4,z8,z5,z6]),(0,[z15,z0,z974,z4,z8,z5])],[(0,[z74,z227,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z975]),(0,[z0,z1,z4,z976,z5,z6]),(0,[z1,z27,z8,z5,z6,z10]),(0,[z51,z1,z4,z8,z5,z367])],[(0,[z1,z4,z106,z5,z6,z538]),(0,[z0,z1,z4,z8,z190,z55]),(0,[z362,z1,z4,z96,z5,z6])],[],[],[(0,[z1,z4,z8,z242,z6,z11]),(0,[z334,z200,z4,z8,z5,z6]),(0,[z400,z1,z4,z8,z439,z6]),(0,[z1,z4,z8,z5,z199,z734])],[(0,[z0,z1,z4,z977,z5,z6])],[(0,[z75,z1,z4,z8,z5,z11]),(0,[z0,z1,z4,z978,z5,z6]),(0,[z1,z4,z8,z5,z979,z6])],[],[(0,[z1,z4,z8,z5,z11,z161]),(0,[z980,z1,z4,z8,z5,z6])],[(0,[z18,z1,z4,z5,z11,z30])],[(0,[z0,z45,z283,z8,z5,z6]),(0,[z34,z0,z1,z8,z264,z65])],[(1,[z1,z4,z8,z766,z6]),(0,[z1,z4,z224,z5,z12,z11]),(0,[z958,z1,z4,z5,z6,z11]),(0,[z0,z1,z4,z224,z5,z19]),(0,[z0,z1,z4,z981,z5,z6])]],
   [[(0,[z91,z1,z27,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z982]),(0,[z0,z821,z4,z8,z5,z6]),(0,[z15,z170,z1,z4,z8,z5]),(0,[z34,z0,z1,z17,z5,z65])],[(0,[z0,z293,z4,z8,z5,z6]),(0,[z383,z0,z4,z8,z5,z14]),(1,[z0,z1,z8,z264,z65])],[(0,[z163,z1,z4,z202,z5,z6]),(0,[z50,z1,z4,z8,z5,z11]),(0,[z983,z1,z4,z8,z5,z6])],[(0,[z50,z1,z4,z8,z5,z734]),(0,[z33,z1,z4,z427,z5,z6]),(0,[z0,z4,z8,z5,z140,z206])],[(0,[z0,z4,z8,z5,z6,z984]),(0,[z0,z525,z4,z8,z5,z361])],[(0,[z263,z1,z5,z92,z6,z11]),(0,[z117,z0,z4,z8,z140,z206]),(0,[z985,z1,z4,z8,z5,z6])],[(0,[z74,z511,z4,z8,z5,z6]),(0,[z1,z4,z5,z92,z11,z30]),(0,[z33,z1,z4,z8,z5,z443]),(0,[z0,z1,z4,z8,z986,z6]),(0,[z263,z0,z1,z5,z92,z6]),(0,[z0,z1,z8,z5,z724,z6])],[(0,[z1,z4,z8,z5,z987,z6]),(0,[z0,z988,z4,z8,z5,z6]),(0,[z0,z989,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z990]),(0,[z1,z4,z5,z6,z11,z991]),(0,[z383,z270,z4,z8,z5,z14]),(0,[z0,z1,z4,z8,z5,z992])],[(0,[z33,z220,z4,z8,z5,z6]),(0,[z222,z1,z4,z262,z5,z19])],[(0,[z993,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z994]),(0,[z0,z1,z327,z8,z5,z55])],[(0,[z0,z1,z4,z8,z5,z995]),(0,[z0,z305,z4,z8,z5,z6])],[(0,[z0,z1,z996,z8,z5,z6])],[(0,[z1,z4,z8,z5,z565,z11]),(0,[z0,z1,z4,z277,z5,z12]),(0,[z0,z997,z4,z8,z5,z6])],[(0,[z152,z200,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z998,z6]),(0,[z446,z1,z4,z8,z5,z653])],[(0,[z117,z0,z4,z184,z140,z6])]],
   [[(0,[z59,z1,z4,z8,z242,z6]),(0,[z42,z0,z4,z5,z6,z301]),(0,[z999,z0,z1,z4,z8,z5])],[],[(0,[z0,z1,z1000,z8,z5,z6]),(0,[z137,z0,z1,z427,z16,z6]),(0,[z125,z1,z4,z277,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1001]),(0,[z0,z4,z8,z5,z6,z157]),(0,[z0,z45,z4,z8,z297,z6]),(0,[z263,z1,z5,z355,z92,z6])],[(0,[z0,z1,z4,z8,z1002,z6]),(0,[z71,z1,z4,z8,z147,z6]),(0,[z0,z1003,z4,z8,z5,z6])],[(0,[z0,z1,z1004,z8,z5,z6]),(0,[z165,z1,z4,z8,z5,z6]),(0,[z1005,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1006]),(0,[z496,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z1007,z5,z6]),(0,[z0,z1,z4,z1008,z5,z6])],[(0,[z324,z174,z1,z4,z28,z6]),(0,[z1009,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z734]),(0,[z1,z4,z8,z5,z6,z1010]),(0,[z137,z0,z1,z8,z310,z16])],[(0,[z0,z1,z4,z8,z5,z1011]),(0,[z362,z1,z4,z8,z5,z6]),(0,[z319,z1,z435,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z1012])],[(0,[z0,z1013,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z226,z288]),(0,[z0,z1,z283,z8,z5,z160])],[(0,[z1,z4,z8,z5,z1014,z6]),(0,[z1015,z1,z4,z8,z5,z6]),(0,[z0,z1016,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z872,z22])],[(0,[z33,z1,z4,z8,z35,z6]),(0,[z0,z305,z4,z5,z6,z30])],[(0,[z0,z1,z4,z1017,z5,z6]),(0,[z0,z1,z185,z8,z5,z621]),(0,[z0,z1,z239,z120,z5,z6])],[(0,[z1018,z1,z4,z8,z5,z6]),(0,[z38,z1,z8,z5,z6,z233]),(0,[z33,z1,z4,z17,z5,z6])]],
   [[(0,[z0,z1,z4,z5,z6,z991]),(0,[z0,z1,z4,z1019,z5,z6]),(0,[z1,z4,z274,z5,z6,z11]),(0,[z1,z4,z5,z6,z11,z272]),(0,[z34,z196,z1,z8,z5,z65])],[(0,[z1,z2,z4,z5,z6,z11]),(0,[z0,z496,z4,z8,z264,z6])],[(0,[z42,z0,z4,z5,z1020,z6]),(0,[z42,z269,z1,z4,z5,z6]),(0,[z169,z0,z1,z8,z16,z6])],[(0,[z33,z1,z4,z8,z5,z566]),(0,[z0,z1,z283,z274,z5,z6]),(0,[z0,z496,z4,z17,z5,z6]),(0,[z136,z0,z1,z4,z5,z30])],[(0,[z137,z103,z1,z8,z16,z6])],[(0,[z152,z835,z4,z8,z5,z6]),(0,[z1,z327,z8,z5,z6,z11]),(0,[z0,z1,z4,z5,z443,z30]),(0,[z137,z0,z1,z8,z16,z361])],[(0,[z52,z1,z4,z5,z11,z30]),(0,[z33,z44,z4,z8,z5,z12]),(0,[z0,z220,z4,z8,z35,z6])],[(0,[z1,z4,z8,z731,z5,z6]),(0,[z0,z1,z4,z1021,z5,z6]),(0,[z222,z1,z4,z8,z5,z199]),(0,[z1022,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z6,z1023]),(0,[z0,z45,z4,z8,z5,z206]),(0,[z1,z4,z8,z5,z12,z80])],[(0,[z1,z4,z8,z35,z6,z11]),(0,[z0,z1,z4,z5,z6,z1024]),(0,[z0,z1,z4,z8,z5,z1025])],[],[(0,[z1026,z1,z4,z8,z5,z6]),(0,[z138,z1,z4,z215,z5,z6]),(0,[z15,z0,z1,z4,z8,z69]),(0,[z0,z1027,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z361,z11]),(0,[z0,z309,z99,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z872])],[(0,[z245,z1,z4,z8,z5,z6]),(0,[z0,z1,z1028,z8,z5,z6]),(0,[z362,z293,z4,z8,z5,z6])],[(0,[z38,z1,z105,z8,z5,z6]),(0,[z368,z1,z4,z8,z5,z11]),(0,[z1,z4,z8,z5,z6,z1029]),(0,[z0,z1,z4,z277,z264,z6])],[(0,[z0,z1,z4,z8,z1030,z6]),(0,[z0,z1,z4,z8,z5,z1031]),(0,[z1,z4,z8,z226,z6,z11]),(0,[z378,z0,z67,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z1032]),(0,[z0,z4,z8,z5,z326,z14])]],
   [[(0,[z0,z4,z8,z5,z1033,z6]),(0,[z0,z974,z4,z8,z5,z6]),(0,[z34,z0,z1,z327,z8,z5]),(0,[z0,z4,z262,z5,z19,z157])],[(0,[z0,z1,z4,z8,z5,z1034]),(0,[z1,z4,z5,z1035,z6,z11]),(0,[z0,z62,z4,z215,z5,z6])],[(0,[z59,z1,z4,z8,z5,z443]),(0,[z0,z1036,z4,z8,z5,z6])],[(0,[z227,z1,z4,z8,z5,z367]),(0,[z117,z0,z4,z8,z140,z6]),(0,[z0,z1037,z4,z8,z5,z6])],[(0,[z33,z1,z4,z8,z5,z393])],[(0,[z146,z1,z4,z237,z5,z6]),(0,[z1038,z1,z4,z8,z5,z6])],[(1,[z1,z4,z8,z5,z734]),(0,[z1,z4,z8,z5,z6,z1039]),(0,[z0,z1,z4,z8,z5,z1040])],[(0,[z152,z2,z3,z4,z5,z6]),(0,[z0,z1,z4,z1041,z5,z6]),(0,[z0,z205,z99,z8,z5,z6])],[(0,[z241,z3,z4,z8,z5,z6]),(0,[z0,z1,z4,z5,z6,z272]),(0,[z138,z1,z4,z8,z5,z142])],[(0,[z1,z4,z8,z5,z310,z11]),(0,[z1,z4,z8,z5,z287,z1042]),(0,[z1043,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z1044]),(0,[z270,z1,z4,z8,z5,z14])],[(0,[z33,z1,z4,z8,z5,z589]),(0,[z0,z1,z4,z40,z226,z6]),(0,[z0,z1,z4,z1045,z5,z6])],[(0,[z0,z1046,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1047])],[(0,[z0,z1,z4,z1048,z5,z6]),(0,[z77,z44,z4,z8,z5,z12]),(0,[z0,z1,z4,z17,z35,z6])],[(0,[z1049,z1,z4,z8,z5,z6])],[],[(0,[z39,z0,z1,z4,z5,z367]),(0,[z1,z4,z8,z5,z6,z1050])]],
   [[(0,[z152,z3,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1051]),(0,[z0,z1,z4,z1052,z5,z6]),(0,[z0,z1,z4,z8,z69,z66])],[(0,[z0,z1,z4,z1053,z5,z6]),(0,[z42,z319,z4,z5,z139,z6]),(0,[z0,z44,z4,z224,z5,z12]),(0,[z1,z4,z8,z5,z6,z1054])],[(0,[z1055,z1,z4,z8,z5,z6]),(0,[z15,z1,z4,z8,z5,z109])],[(0,[z1056,z1,z4,z8,z5,z6]),(0,[z1057,z1,z4,z8,z5,z6]),(0,[z21,z0,z1,z4,z96,z22])],[],[(0,[z33,z1,z4,z8,z5,z653])],[(0,[z0,z1058,z4,z8,z5,z6])],[(0,[z246,z0,z1,z4,z5,z1059]),(0,[z33,z1,z185,z8,z5,z119]),(0,[z1060,z1,z4,z8,z5,z6])],[(0,[z1,z4,z106,z8,z5,z294]),(0,[z125,z496,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1061])],[(0,[z0,z1,z4,z905,z5,z6]),(0,[z0,z1062,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z1063])],[(0,[z122,z1,z414,z8,z5,z6]),(0,[z146,z503,z1,z4,z5,z6])],[(0,[z1064,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z184,z84,z6]),(0,[z137,z15,z0,z1,z8,z16])],[],[(0,[z1065,z1,z4,z8,z5,z12]),(0,[z0,z1,z4,z8,z264,z119])],[(0,[z174,z1,z4,z8,z705,z6]),(0,[z0,z1,z4,z8,z5,z1066]),(0,[z0,z220,z4,z8,z5,z653]),(0,[z1,z4,z8,z5,z1067,z6]),(0,[z0,z1,z63,z8,z667,z6])],[(0,[z1,z283,z8,z5,z6,z11]),(0,[z767,z1,z4,z8,z5,z19]),(0,[z1,z4,z8,z5,z653,z1068]),(0,[z854,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z184,z5,z160]),(0,[z1069,z1,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z1070,z8,z5,z6]),(0,[z1071,z1,z4,z8,z5,z6]),(0,[z1072,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z184,z140,z6])],[],[(0,[z0,z1,z4,z8,z5,z1073]),(0,[z354,z1,z4,z8,z5,z6])],[],[(0,[z0,z4,z8,z5,z1074,z6]),(0,[z1075,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z6,z1076]),(0,[z0,z1,z4,z8,z5,z1077]),(0,[z166,z1,z283,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1078]),(0,[z0,z1,z4,z5,z1079,z6]),(0,[z4,z8,z5,z19,z11,z157]),(0,[z33,z1,z239,z8,z5,z6])],[],[(0,[z146,z59,z1,z4,z5,z6]),(0,[z1,z4,z8,z5,z472,z11]),(0,[z1080,z1,z4,z8,z5,z6]),(0,[z1081,z1,z4,z8,z5,z6]),(0,[z0,z44,z4,z8,z226,z6]),(0,[z1082,z0,z1,z4,z5,z6]),(0,[z1083,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1084])],[(0,[z122,z1,z450,z8,z5,z6]),(0,[z115,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z476,z11]),(0,[z1085,z1,z4,z8,z5,z6]),(0,[z0,z305,z4,z262,z5,z6])],[(0,[z1,z4,z867,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z901]),(0,[z0,z1,z110,z8,z242,z6]),(0,[z0,z1,z4,z8,z64,z142]),(0,[z0,z1,z4,z120,z5,z6])],[(0,[z0,z1,z4,z5,z1086,z6]),(0,[z1,z4,z8,z188,z6,z189]),(0,[z319,z1,z4,z8,z242,z6]),(0,[z0,z4,z8,z5,z443,z14]),(0,[z0,z4,z5,z1020,z139,z6])],[],[(0,[z0,z1087,z4,z8,z5,z6]),(0,[z0,z1,z4,z215,z5,z6]),(0,[z0,z1,z4,z8,z1088,z6]),(0,[z0,z1,z8,z5,z16,z142]),(0,[z1089,z1,z4,z8,z5,z6]),(0,[z0,z1090,z4,z8,z5,z6])],[(0,[z33,z1,z4,z8,z5,z654]),(0,[z33,z1,z4,z8,z5,z149])],[(0,[z0,z1,z4,z8,z5,z1091]),(0,[z1,z4,z731,z237,z5,z6]),(0,[z1,z4,z8,z5,z12,z11]),(0,[z33,z432,z4,z8,z5,z6]),(0,[z59,z1,z110,z8,z5,z6]),(0,[z0,z305,z4,z8,z5,z14])]],
   [[(0,[z0,z1092,z4,z8,z5,z6]),(0,[z33,z1,z4,z8,z264,z6]),(0,[z0,z1,z327,z8,z5,z6])],[(0,[z196,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z53,z5,z19]),(0,[z125,z1,z4,z8,z35,z6]),(0,[z0,z1,z4,z262,z5,z204])],[(0,[z0,z1,z1093,z8,z5,z6]),(0,[z1094,z1,z4,z8,z5,z6]),(0,[z347,z1,z283,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1095])],[(0,[z138,z1,z4,z427,z5,z6]),(0,[z0,z1,z4,z8,z6,z872])],[(0,[z0,z821,z1,z8,z5,z6]),(0,[z0,z1,z4,z1096,z5,z6]),(0,[z0,z1,z435,z8,z5,z288]),(0,[z42,z0,z435,z5,z139,z6]),(0,[z0,z1,z412,z8,z5,z160])],[(0,[z4,z8,z5,z12,z11,z14]),(1,[z0,z4,z8,z5,z824]),(0,[z1097,z1,z4,z8,z5,z6]),(0,[z0,z749,z1,z4,z54,z6])],[(0,[z1098,z1,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z287,z11]),(0,[z1,z4,z8,z5,z11,z291]),(0,[z1,z4,z8,z5,z6,z1099]),(0,[z269,z1,z4,z5,z101,z6]),(0,[z0,z1,z1100,z8,z5,z6]),(0,[z103,z1,z4,z215,z5,z6]),(0,[z0,z1101,z4,z8,z5,z6]),(0,[z15,z0,z1,z4,z8,z264]),(0,[z21,z0,z1,z4,z8,z264])],[(0,[z174,z1,z4,z8,z766,z6]),(0,[z42,z0,z4,z242,z139,z6]),(0,[z34,z125,z1,z8,z5,z65])],[(0,[z222,z1,z4,z8,z5,z6]),(0,[z1102,z1,z4,z8,z5,z6]),(0,[z0,z1103,z4,z8,z5,z6]),(0,[z0,z220,z4,z8,z264,z6])],[(0,[z1,z4,z1104,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z81]),(0,[z1,z4,z8,z5,z11,z301]),(0,[z432,z4,z8,z5,z6,z11]),(0,[z945,z1,z4,z8,z5,z6])],[(0,[z739,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1105]),(0,[z0,z220,z4,z17,z5,z6])],[(0,[z33,z1,z4,z8,z5,z680]),(0,[z0,z1,z63,z8,z571,z6]),(0,[z21,z354,z1,z4,z8,z22])],[(0,[z0,z1,z4,z8,z1106,z6])],[(0,[z1,z4,z8,z5,z1107,z6]),(0,[z1108,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1109]),(0,[z0,z1,z4,z1110,z5,z6]),(0,[z0,z1,z4,z8,z5,z1111])]],
   [[(0,[z33,z1,z4,z5,z315,z6]),(0,[z0,z4,z8,z5,z761,z6])],[(0,[z1,z1112,z4,z8,z5,z6]),(0,[z0,z1113,z4,z8,z5,z6]),(0,[z1114,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z226,z6]),(0,[z354,z1,z4,z96,z5,z6])],[(0,[z34,z33,z1,z8,z5,z65])],[(0,[z1115,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z1116,z6]),(0,[z0,z1,z4,z8,z5,z160]),(0,[z1117,z1,z4,z8,z5,z6])],[(0,[z0,z1,z8,z5,z6,z1118]),(0,[z1,z4,z8,z5,z734,z11]),(0,[z103,z1,z4,z8,z5,z142]),(0,[z0,z1,z4,z327,z8,z22])],[(0,[z33,z1,z4,z262,z5,z19]),(0,[z1119,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1120]),(0,[z0,z44,z4,z8,z5,z100])],[(0,[z574,z1,z4,z8,z5,z11]),(0,[z33,z1,z110,z8,z5,z6]),(0,[z48,z0,z4,z8,z140,z6]),(0,[z138,z1,z4,z8,z5,z361]),(0,[z1121,z1,z4,z8,z5,z6])],[(0,[z254,z1,z268,z8,z5,z6]),(0,[z1122,z1,z4,z8,z5,z6]),(0,[z0,z1,z435,z8,z5,z6]),(0,[z108,z1,z4,z8,z5,z653]),(0,[z1123,z1,z4,z8,z5,z6])],[(0,[z1,z4,z5,z19,z11,z30])],[(0,[z170,z1,z4,z8,z5,z6]),(0,[z1124,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z748])],[],[(0,[z1,z4,z8,z5,z149,z11]),(0,[z1,z4,z8,z547,z5,z11])],[(0,[z1,z4,z8,z5,z6,z1125]),(0,[z1,z4,z8,z5,z551,z11]),(0,[z0,z1,z110,z8,z5,z443]),(0,[z0,z62,z4,z8,z5,z361]),(0,[z0,z1,z4,z1126,z5,z6])],[(0,[z122,z1,z4,z8,z5,z367]),(0,[z33,z1,z283,z8,z5,z6]),(0,[z319,z1,z4,z8,z5,z443]),(0,[z392,z0,z1,z4,z5,z30])],[(0,[z97,z1,z442,z8,z5,z6]),(0,[z1127,z1,z4,z8,z5,z6]),(0,[z0,z1128,z4,z8,z5,z6]),(0,[z0,z1,z4,z1129,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1130]),(0,[z1,z4,z8,z5,z142,z11]),(0,[z0,z1,z4,z8,z5,z287]),(0,[z0,z1,z4,z17,z264,z6]),(0,[z0,z1,z327,z96,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z5,z294]),(0,[z406,z1,z4,z8,z147,z6]),(0,[z15,z33,z1,z4,z8,z5]),(0,[z0,z1,z185,z8,z69,z16]),(0,[z1131,z1,z4,z8,z5,z6])],[(0,[z0,z1132,z4,z8,z5,z6]),(0,[z0,z62,z4,z8,z5,z142])],[(0,[z1133,z0,z1,z4,z5,z6]),(0,[z1134,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z1135,z6]),(0,[z1,z4,z8,z5,z253,z30]),(0,[z0,z1,z4,z8,z1136,z6])],[(0,[z0,z1,z4,z1137,z5,z6])],[(0,[z0,z4,z8,z5,z6,z1138]),(0,[z62,z4,z8,z5,z6,z11]),(0,[z0,z1,z4,z1139,z5,z6]),(0,[z0,z1,z4,z8,z5,z310])],[(0,[z0,z1,z4,z8,z5,z1140]),(0,[z178,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z102,z101,z6])],[(0,[z0,z4,z8,z5,z6,z1141])],[(0,[z1,z4,z8,z5,z11,z533]),(0,[z222,z305,z4,z8,z5,z6])],[(0,[z246,z1,z27,z4,z5,z6]),(0,[z1142,z1,z4,z8,z5,z6]),(1,[z0,z1,z4,z8,z872])],[(0,[z1143,z1,z4,z8,z5,z6]),(0,[z1144,z1,z4,z8,z5,z6])],[(0,[z1,z175,z8,z5,z6,z10]),(0,[z0,z1,z4,z8,z5,z1145])],[(0,[z0,z1,z1146,z8,z5,z6]),(0,[z408,z1,z4,z5,z6,z49]),(0,[z0,z220,z4,z8,z5,z12])],[(0,[z668,z1,z4,z106,z5,z6]),(0,[z1,z4,z8,z5,z725,z6]),(0,[z33,z1,z4,z5,z811,z6]),(0,[z1,z4,z8,z5,z1147,z6]),(0,[z362,z1,z327,z8,z5,z6])],[(0,[z146,z1,z4,z8,z5,z294])],[(0,[z0,z1,z4,z8,z5,z1148]),(0,[z1,z4,z8,z5,z6,z1149]),(0,[z1150,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z1151,z6])],[(0,[z1152,z1,z4,z8,z5,z6]),(0,[z1153,z1,z4,z8,z5,z6]),(0,[z222,z4,z8,z5,z6,z157])]],
   [[(0,[z1,z835,z4,z8,z5,z6]),(0,[z0,z1154,z4,z8,z5,z6]),(0,[z0,z4,z8,z5,z11,z157]),(0,[z0,z1,z4,z8,z5,z1155]),(0,[z1,z4,z8,z5,z288,z1156]),(0,[z1157,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z274,z5,z206]),(0,[z0,z1158,z4,z8,z5,z6]),(0,[z125,z220,z4,z8,z5,z6])],[(0,[z1,z4,z8,z5,z6,z1159]),(0,[z493,z0,z1,z8,z16,z6]),(0,[z138,z525,z4,z8,z5,z6]),(0,[z4,z8,z5,z6,z80,z157])],[(0,[z305,z4,z8,z5,z6,z80])],[(0,[z0,z1,z4,z8,z5,z1160]),(0,[z222,z1,z4,z8,z5,z11]),(0,[z1161,z1,z4,z8,z5,z6]),(0,[z0,z1,z8,z709,z16,z6])],[(0,[z0,z1,z1162,z8,z5,z6]),(0,[z1163,z0,z1,z4,z5,z6]),(0,[z44,z4,z8,z5,z12,z11]),(0,[z1164,z1,z4,z8,z5,z6])],[],[],[(0,[z146,z1,z4,z663,z5,z6]),(0,[z0,z1,z4,z1165,z5,z6]),(0,[z263,z165,z1,z5,z92,z6]),(0,[z1,z4,z8,z5,z6,z1166]),(0,[z0,z1,z8,z16,z6,z142])],[(0,[z0,z1167,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z361,z786]),(0,[z605,z0,z1,z4,z8,z22])],[],[(0,[z0,z1168,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z1169]),(0,[z1,z4,z8,z5,z80,z14])],[(0,[z122,z246,z1,z4,z5,z6]),(0,[z33,z1,z2,z4,z5,z6])],[(0,[z33,z1,z830,z4,z5,z6]),(0,[z993,z1,z4,z8,z5,z287])],[(0,[z882,z1,z4,z8,z5,z6])],[(0,[z146,z0,z1,z4,z226,z6]),(0,[z1,z4,z5,z12,z11,z272]),(0,[z1,z4,z41,z5,z11,z30]),(0,[z0,z1,z4,z150,z101,z6]),(0,[z166,z1,z412,z8,z5,z6])],[(0,[z42,z0,z4,z226,z139,z6]),(0,[z0,z1,z4,z8,z264,z12]),(0,[z103,z1,z4,z427,z5,z6]),(0,[z21,z0,z1,z239,z8,z22])]],
   [[(0,[z0,z1,z4,z8,z5,z376]),(0,[z0,z1,z4,z1170,z5,z6]),(0,[z0,z4,z8,z5,z1020,z6]),(0,[z18,z0,z1,z4,z5,z742])],[(0,[z0,z1171,z4,z8,z5,z6])],[(0,[z74,z1,z4,z8,z5,z294]),(0,[z0,z52,z1,z4,z5,z367]),(0,[z1,z8,z5,z6,z11,z1118])],[(0,[z1,z200,z4,z8,z5,z11]),(0,[z0,z1,z4,z277,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1172]),(0,[z125,z1,z4,z8,z264,z6]),(0,[z1,z4,z8,z69,z55,z81])],[],[(0,[z0,z395,z99,z8,z5,z6]),(0,[z0,z1,z4,z8,z242,z288]),(0,[z137,z170,z1,z8,z16,z6]),(0,[z0,z1,z4,z1173,z5,z6]),(0,[z125,z1,z4,z17,z5,z6])],[(0,[z33,z1,z4,z8,z5,z206]),(0,[z1174,z1,z4,z8,z5,z6]),(0,[z1175,z0,z1,z4,z8,z5])],[(0,[z1,z4,z106,z5,z444,z6]),(0,[z1176,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1177]),(0,[z33,z62,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z1178,z6]),(0,[z0,z1,z63,z8,z5,z142]),(0,[z354,z293,z4,z8,z5,z6])],[(0,[z1179,z1,z4,z8,z5,z6])],[],[(0,[z1,z867,z105,z8,z5,z6]),(0,[z163,z1,z4,z462,z5,z6]),(0,[z0,z62,z4,z427,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1180]),(0,[z166,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z80]),(0,[z1,z110,z8,z5,z6,z11]),(0,[z1181,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z142])],[(1,[z4,z8,z5,z11,z157])],[(0,[z1,z4,z267,z5,z6,z538]),(0,[z1182,z1,z4,z8,z5,z6]),(0,[z0,z1,z412,z274,z5,z6]),(0,[z1183,z0,z1,z4,z8,z5]),(0,[z1184,z1,z4,z8,z5,z6])]],
   [[(0,[z0,z1,z4,z8,z1185,z6]),(0,[z1,z27,z867,z8,z5,z6]),(0,[z1186,z33,z1,z4,z5,z6]),(0,[z117,z347,z4,z8,z140,z6]),(0,[z1187,z1,z4,z8,z5,z6])],[(0,[z320,z1,z4,z8,z5,z11]),(0,[z33,z1,z4,z184,z5,z6]),(0,[z33,z1,z4,z96,z5,z6]),(0,[z1186,z0,z1,z4,z5,z6]),(0,[z0,z468,z4,z8,z84,z6]),(0,[z0,z293,z4,z120,z5,z6])],[(0,[z227,z835,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z367]),(0,[z33,z1,z4,z8,z5,z595]),(0,[z1188,z1,z4,z8,z5,z6]),(0,[z103,z1,z4,z8,z5,z361])],[(0,[z146,z575,z1,z4,z5,z6]),(0,[z0,z1,z4,z8,z5,z1189]),(0,[z0,z1,z4,z8,z761,z6])],[(0,[z0,z4,z1190,z8,z5,z6]),(0,[z0,z1,z4,z1191,z5,z6]),(0,[z0,z749,z1,z4,z101,z6])],[(0,[z1,z4,z8,z5,z109,z6]),(0,[z42,z0,z495,z4,z5,z6]),(0,[z0,z1,z4,z5,z11,z272]),(0,[z117,z0,z4,z8,z761,z6]),(0,[z0,z432,z239,z8,z5,z6])],[(0,[z0,z525,z8,z5,z16,z6]),(0,[z34,z0,z1,z8,z5,z65]),(0,[z1192,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z1193,z6]),(0,[z1,z4,z8,z5,z6,z1194]),(0,[z0,z293,z327,z8,z5,z6])],[(0,[z0,z1,z4,z1195,z5,z6]),(0,[z1,z4,z8,z5,z11,z500]),(0,[z241,z4,z8,z5,z6,z464]),(0,[z1,z4,z8,z5,z6,z1068]),(0,[z48,z0,z4,z5,z139,z6]),(0,[z0,z1,z1196,z8,z5,z6])],[(0,[z174,z1,z4,z8,z28,z6]),(0,[z117,z0,z4,z8,z140,z160])],[(0,[z246,z227,z1,z4,z5,z6]),(0,[z1,z4,z8,z5,z766,z6]),(0,[z1,z4,z8,z5,z6,z1197]),(0,[z0,z1,z4,z8,z69,z55])],[(0,[z0,z1,z4,z1198,z5,z6]),(0,[z0,z1,z4,z5,z1035,z6]),(0,[z4,z8,z5,z140,z11,z14]),(0,[z0,z1,z4,z5,z1020,z6]),(0,[z39,z104,z1,z4,z5,z6])],[],[],[(0,[z0,z1199,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z355,z6]),(0,[z1,z4,z8,z766,z147,z6]),(0,[z1,z4,z8,z5,z653,z11]),(0,[z0,z1,z4,z274,z5,z6])],[(0,[z0,z1,z4,z262,z226,z6]),(0,[z1200,z1,z4,z8,z5,z6])]],
   [[(0,[z525,z4,z8,z5,z6,z11])],[(0,[z0,z1,z4,z8,z5,z1201]),(0,[z0,z1,z63,z8,z709,z6])],[(0,[z0,z1202,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z288,z11]),(0,[z33,z1,z4,z8,z5,z288]),(0,[z1203,z1,z4,z8,z5,z6]),(0,[z166,z1,z4,z8,z5,z206]),(0,[z0,z1,z4,z1204,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1059]),(0,[z324,z1,z27,z4,z5,z6]),(0,[z1,z4,z8,z5,z1205,z6]),(0,[z0,z4,z8,z5,z140,z287]),(0,[z1206,z1,z4,z8,z5,z6]),(0,[z1207,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z1208,z5,z6]),(0,[z1,z4,z8,z5,z367,z11]),(0,[z167,z1,z4,z8,z5,z6]),(0,[z1209,z1,z4,z8,z5,z6]),(0,[z39,z269,z1,z4,z5,z6]),(0,[z15,z0,z1,z4,z8,z5]),(0,[z21,z0,z293,z4,z8,z22])],[(0,[z0,z1,z4,z8,z709,z6]),(0,[z0,z1,z8,z264,z6,z65])],[(0,[z0,z1,z4,z8,z1210,z6]),(0,[z33,z1,z412,z8,z5,z6]),(0,[z1211,z1,z4,z8,z5,z6])],[(0,[z0,z1212,z1,z8,z5,z6]),(0,[z33,z1,z4,z8,z5,z308]),(0,[z1,z4,z224,z5,z6,z11])],[(0,[z163,z1,z4,z619,z5,z6]),(0,[z1,z4,z8,z5,z700,z11]),(0,[z0,z1,z4,z8,z1213,z6]),(0,[z42,z0,z4,z5,z139,z443])],[(0,[z1214,z1,z4,z8,z5,z6]),(0,[z1215,z1,z4,z8,z5,z6]),(0,[z362,z1,z4,z120,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1216]),(0,[z1217,z1,z4,z8,z5,z6]),(0,[z1,z4,z262,z5,z19,z80])],[(0,[z74,z455,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1218]),(0,[z1219,z0,z4,z8,z5,z6]),(0,[z0,z1,z4,z1220,z5,z6]),(0,[z4,z99,z8,z5,z11,z14]),(0,[z0,z1,z4,z5,z6,z1221])],[(0,[z0,z1,z963,z8,z5,z6]),(0,[z1222,z1,z4,z8,z5,z6]),(0,[z166,z1,z4,z184,z5,z6])],[(0,[z1,z24,z4,z8,z5,z11]),(0,[z42,z4,z5,z139,z6,z11]),(0,[z0,z1,z4,z8,z5,z1223]),(0,[z103,z525,z4,z8,z5,z6])],[(0,[z39,z0,z1,z4,z705,z6])],[(0,[z39,z0,z397,z1,z4,z6]),(0,[z347,z1,z4,z8,z5,z206])]],
   [[(0,[z122,z1,z695,z8,z5,z6]),(0,[z122,z324,z1,z4,z5,z6])],[(0,[z0,z1,z4,z8,z1224,z6]),(0,[z1,z4,z8,z5,z1225,z6])],[(0,[z881,z1,z4,z8,z5,z6])],[(0,[z152,z3,z4,z8,z5,z294]),(1,[z1,z4,z5,z11,z272])],[(0,[z137,z0,z1,z8,z709,z6]),(0,[z586,z0,z1,z4,z8,z22]),(0,[z0,z1,z4,z101,z265,z6])],[(0,[z33,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z544,z101,z6]),(0,[z137,z0,z62,z8,z16,z6])],[(0,[z0,z1,z4,z8,z5,z1226]),(0,[z33,z1,z4,z8,z5,z199]),(0,[z0,z1,z1227,z8,z5,z6]),(0,[z1228,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1229]),(0,[z0,z4,z8,z5,z12,z824]),(0,[z0,z44,z4,z224,z5,z6])],[(0,[z246,z1,z4,z5,z147,z6]),(0,[z174,z1,z4,z28,z315,z6]),(0,[z0,z1,z4,z8,z1230,z6]),(0,[z0,z45,z4,z8,z84,z6]),(0,[z0,z1,z4,z427,z5,z6]),(0,[z214,z1,z185,z8,z5,z119])],[(0,[z527,z1,z4,z8,z5,z11]),(0,[z0,z496,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z1231,z6]),(0,[z347,z1,z4,z184,z5,z6]),(0,[z0,z293,z4,z8,z5,z22])],[(0,[z74,z203,z4,z8,z5,z6])],[(0,[z1,z4,z277,z5,z6,z11]),(0,[z0,z1,z4,z8,z5,z443]),(0,[z0,z1232,z4,z8,z5,z6])],[(0,[z1233,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1234]),(0,[z128,z146,z1,z4,z5,z6])],[(0,[z0,z1235,z4,z8,z5,z6]),(0,[z0,z1,z1236,z8,z5,z6]),(0,[z1237,z1,z4,z8,z5,z6])],[(0,[z1238,z1,z4,z8,z5,z6]),(0,[z1239,z1,z4,z8,z5,z6]),(0,[z1,z4,z8,z5,z6,z1240]),(0,[z137,z138,z1,z8,z16,z6])]],
   [[(0,[z1241,z1,z4,z8,z5,z6]),(0,[z137,z1,z8,z109,z16,z6])],[(0,[z446,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1242])],[(0,[z1243,z1,z4,z8,z5,z6]),(0,[z1,z4,z5,z6,z253,z272])],[(0,[z0,z1,z4,z5,z1244,z6]),(0,[z1065,z1,z4,z8,z5,z6]),(0,[z1,z4,z96,z5,z6,z11]),(0,[z137,z33,z1,z8,z16,z6]),(0,[z0,z4,z8,z5,z199,z157]),(0,[z1,z4,z8,z5,z1245,z6])],[(0,[z1246,z1,z4,z8,z5,z6])],[(0,[z1247,z1,z4,z8,z5,z6]),(0,[z1248,z1,z4,z8,z5,z6])],[(0,[z42,z0,z4,z5,z14,z30]),(0,[z0,z4,z8,z5,z6,z1249]),(0,[z1250,z1,z4,z8,z5,z6])],[(0,[z1251,z1,z4,z8,z5,z6])],[(0,[z0,z45,z4,z8,z5,z287])],[(0,[z0,z1,z1252,z8,z5,z6]),(0,[z104,z1,z4,z8,z5,z6]),(0,[z33,z293,z4,z8,z5,z6]),(0,[z1253,z1,z4,z8,z5,z6])],[(0,[z1254,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z1255,z8,z5])],[(0,[z77,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z1256,z5,z6]),(0,[z0,z99,z8,z5,z528,z6]),(0,[z0,z1,z4,z8,z5,z361])],[(0,[z246,z163,z1,z4,z5,z6]),(0,[z77,z1,z4,z8,z5,z199]),(0,[z42,z0,z4,z5,z183,z6]),(0,[z0,z1,z4,z1257,z5,z6])],[(0,[z319,z1,z110,z8,z5,z6]),(0,[z0,z4,z8,z5,z824,z14]),(0,[z162,z0,z1,z4,z8,z22])],[(0,[z1,z4,z106,z731,z5,z6]),(0,[z59,z1,z4,z8,z5,z288]),(0,[z347,z1,z412,z8,z5,z6]),(0,[z1258,z1,z4,z8,z5,z6])],[(0,[z34,z1,z8,z5,z11,z65]),(0,[z1259,z1,z4,z8,z5,z6]),(0,[z1080,z1,z4,z8,z5,z310])]],
   [[(0,[z1,z4,z8,z5,z11,z111]),(0,[z0,z1,z4,z224,z5,z6]),(0,[z1,z4,z8,z5,z6,z1260]),(0,[z0,z1,z4,z871,z5,z6])],[(0,[z1,z4,z8,z5,z1261,z6]),(0,[z1,z27,z8,z5,z694,z6]),(0,[z1,z4,z54,z101,z6,z11])],[(0,[z20,z0,z1,z5,z92,z6]),(0,[z0,z1,z4,z8,z35,z6]),(0,[z15,z0,z1,z327,z8,z5]),(0,[z1262,z1,z4,z8,z5,z6])],[(0,[z152,z3,z4,z8,z5,z376]),(0,[z0,z1263,z4,z8,z5,z6]),(0,[z33,z305,z4,z8,z5,z6])],[(0,[z15,z1,z4,z8,z5,z11]),(0,[z0,z1,z4,z8,z5,z1264]),(0,[z0,z1,z4,z5,z742,z30])],[(0,[z1,z4,z8,z5,z6,z1156]),(0,[z0,z1,z4,z8,z1265,z6]),(0,[z42,z0,z110,z5,z139,z6]),(0,[z0,z1,z4,z8,z69,z264]),(0,[z0,z1,z1266,z8,z5,z6])],[(0,[z0,z1,z4,z8,z1267,z6]),(1,[z0,z1,z8,z16,z142]),(0,[z1268,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z740])],[(0,[z649,z0,z192,z1,z4,z6]),(0,[z0,z1,z1269,z8,z5,z6])],[(0,[z582,z1,z4,z8,z147,z6]),(0,[z174,z1,z4,z8,z522,z6]),(0,[z0,z1,z4,z1270,z5,z6]),(0,[z1,z4,z8,z5,z204,z11]),(0,[z33,z1,z4,z54,z101,z6]),(0,[z196,z1,z4,z8,z5,z14]),(0,[z208,z0,z1,z5,z92,z6])],[(0,[z146,z1,z4,z5,z300,z6]),(0,[z33,z1,z4,z8,z5,z594]),(0,[z1,z4,z8,z5,z6,z1042]),(0,[z0,z305,z4,z8,z5,z443])],[(0,[z0,z1271,z4,z8,z5,z6]),(0,[z146,z1,z4,z237,z5,z367]),(0,[z1,z4,z8,z5,z11,z154]),(0,[z0,z821,z99,z8,z5,z6]),(0,[z162,z0,z4,z8,z140,z6])],[(0,[z1,z412,z8,z5,z6,z11]),(0,[z1272,z1,z4,z8,z5,z6]),(0,[z0,z1,z435,z8,z226,z6]),(0,[z0,z1,z4,z604,z101,z6])],[(0,[z0,z1,z4,z8,z5,z1273]),(0,[z0,z1,z4,z8,z242,z6]),(0,[z1,z4,z8,z5,z1274,z6])],[(0,[z347,z1,z4,z8,z5,z6])],[(0,[z97,z1,z268,z8,z5,z6]),(0,[z39,z0,z221,z1,z4,z6])],[(0,[z0,z1,z4,z1275,z5,z6])]],
   [[(0,[z33,z1,z4,z8,z5,z734])],[(0,[z59,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z1276,z5,z6]),(0,[z117,z4,z8,z140,z6,z11])],[(0,[z0,z1,z4,z1277,z5,z6]),(0,[z263,z0,z1,z5,z724,z6]),(0,[z0,z525,z63,z8,z5,z6]),(0,[z1278,z1,z4,z8,z5,z6]),(0,[z354,z1,z4,z120,z5,z6])],[(0,[z1279,z1,z4,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1280]),(0,[z603,z511,z4,z8,z5,z6]),(0,[z117,z0,z4,z274,z140,z6]),(0,[z21,z0,z1,z4,z8,z872])],[(0,[z0,z44,z4,z8,z5,z443]),(0,[z1281,z1,z4,z8,z5,z6]),(0,[z15,z930,z1,z4,z8,z5])],[(0,[z0,z525,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z5,z1282]),(0,[z1283,z1,z4,z8,z5,z6]),(0,[z0,z1,z1284,z8,z5,z6])],[(0,[z0,z1,z4,z8,z5,z1285])],[(0,[z44,z4,z8,z5,z12,z253]),(0,[z354,z1,z327,z8,z5,z6])],[(0,[z1286,z1,z4,z8,z5,z6])],[(0,[z269,z1,z4,z8,z5,z849]),(0,[z1287,z1,z4,z8,z5,z6]),(0,[z167,z1,z4,z8,z5,z30])],[(0,[z0,z1,z1288,z8,z5,z6]),(0,[z613,z0,z4,z8,z5,z14]),(0,[z1,z4,z8,z5,z1289,z6])],[(0,[z97,z1,z27,z8,z5,z6]),(0,[z408,z1,z4,z237,z5,z6]),(0,[z1,z4,z8,z259,z5,z11]),(0,[z1212,z1,z8,z5,z6,z11]),(0,[z305,z4,z8,z5,z6,z11]),(0,[z42,z0,z4,z5,z282,z6]),(0,[z270,z1,z4,z8,z5,z12])],[(0,[z0,z1,z4,z8,z5,z1290]),(0,[z33,z1,z4,z8,z5,z487]),(0,[z1065,z1,z4,z8,z5,z11]),(0,[z1,z4,z8,z5,z6,z1291])],[(0,[z0,z1,z4,z8,z1292,z6]),(0,[z97,z1,z867,z8,z5,z6]),(0,[z1293,z1,z4,z8,z5,z6]),(0,[z1294,z1,z4,z8,z5,z6]),(0,[z0,z1,z4,z8,z1295,z6]),(0,[z0,z1,z4,z262,z5,z61])],[(0,[z0,z1,z4,z1296,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 516) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 516).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1029).take 264) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1293)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [516, 513, 264] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 178).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 178).take 160).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 338).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 496).take 16).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [178, 160, 158, 16] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37977

theorem PEqualNP.Outside.L_meta_37977 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4277074088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4277074088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37977.solve