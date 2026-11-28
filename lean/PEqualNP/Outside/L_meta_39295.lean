import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39295

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
  Nat.testBit (4277074664 * 2 ^ 32 + 4272487072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0001821602582a91#64 ++ 0x080003042c04b055#64 ++ 0x01238e3e07f87fff#64 ++ 0xf602471c7c0ff0ff#64 : BitVec 256),
   (0x824c48cb192e6624#64 ++ 0x1104989196325ccc#64 ++ 0x86dc49cf393e666d#64 ++ 0xed0db8939e727ccc#64 : BitVec 256),
   (0x08e0116141828546#64 ++ 0x2011c022c283050a#64 ++ 0x78e071f1c1c787df#64 ++ 0x5ef1c0e3e3838f0f#64 : BitVec 256),
   (0x17006c00ac055008#64 ++ 0x402e00d801580aa0#64 ++ 0x7f007e01fe07f87b#64 ++ 0x3efe00fc03fc0ff0#64 : BitVec 256),
   (0x3df68001f7f0000f#64 ++ 0x807bed0003efe000#64 ++ 0xbfff8001fff80038#64 ++ 0xfd7fff0003fff000#64 : BitVec 256),
   (0x5fbb7fbc00000070#64 ++ 0x00bf76ff78000000#64 ++ 0xdffffffe00000007#64 ++ 0xfdbffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fff 0xf602471c7c0ff0ff

def z1 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c787df 0x5ef1c0e3e3838f0f

def z2 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f87b 0x3efe00fc03fc0ff0

def z3 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff80038 0xfd7fff0003fff000

def z4 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00000007 0xfdbffffffc000000

def z5 : W := mkw 0x804480431b7e6e85 0x190089008636fcdd 0x000000013ffe7ff8 0x02000000027ffcff

def z6 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e666d 0xed0db8939e727ccc

def z7 : W := mkw 0x5fbb7fbca4000078 0x00bf76ff79480000 0xfffffffffe00003f 0xfdfffffffffc0000

def z8 : W := mkw 0x0044000111200004 0x0000880002224000 0x86dc000139380028 0xed0db80002727000

def z9 : W := mkw 0x1db2000000000000 0x003b640000000000 0x9fff800000000000 0xfd3fff0000000000

def z10 : W := mkw 0x4209ffbe02582af1 0x088413ff7c04b055 0x4123fffe07f87fff 0xf68247fffc0ff0ff

def z11 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x87dc4fcf3f3e7e7f 0xff0fb89f9e7e7cfc

def z12 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f80003e380020 0xa10e3f00007c7000

def z13 : W := mkw 0x3df78217f7f82a9f 0x887bef042feff055 0xbfff8e3ffff87fff 0xff7fff1c7ffff0ff

def z14 : W := mkw 0x0000800202582a81 0x080001000404b055 0x0000000007f87ff8 0x02000000000ff0ff

def z15 : W := mkw 0x80440043192e6604 0x1100880086325ccc 0x00000001393e6668 0x0000000002727ccc

def z16 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x7923fe3fc7ffffff 0xfef247fc7f8fffff

def z17 : W := mkw 0x3db29120e6d0814b 0xa07b652241cda102 0x7923b030c6c18192 0x12f24760618d8303

def z18 : W := mkw 0x0200480008044000 0x0004009000100880 0x7e007801f807e07b 0x3efc00f003f00fc0

def z19 : W := mkw 0x00400041ed87d50e 0x6000800083db0faa 0x20000001ffc7fff8 0x0240000003ff8fff

def z20 : W := mkw 0x17006c0000000000 0x002e00d800000000 0x5f007e0000000003 0x3cbe00fc00000000

def z21 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1f1ffff87ff 0xffffffe3e3ffff0f

def z22 : W := mkw 0x15002400a4011008 0x402a004801480220 0x79003600c6019812 0x12f2006c018c0330

def z23 : W := mkw 0x974c6ccbbd2f762c 0x512e98d9977a5eec 0xffdc7fcfff3ffe7f 0xffffb8ff9ffe7ffc

def z24 : W := mkw 0x02006c00ac055008 0x400400d801580aa0 0x60007e01fe07f87b 0x02c000fc03fc0ff0

def z25 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffff8078007 0xfdfffffffff00f00

def z26 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f003e00fe01f832 0x32fe007c01fc03f0

def z27 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x79007e00c607f853 0x12f200fc018c0ff0

def z28 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe01c007df 0xffbffffffc03800f

def z29 : W := mkw 0x5fbb7fbe00082270 0x00bf76ff7c001044 0xdffffffe0138666f 0xfdbffffffc0270cc

def z30 : W := mkw 0x7fffffbdf7f0007f 0x80ffffff7befe000 0xfffffffffff8003f 0xfdfffffffffff000

def z31 : W := mkw 0x08a0112040808142 0x2011402240810102 0x78203030c0c18192 0x12f0406061818303

def z32 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x861c080e38386020 0xa10c38101c7070c0

def z33 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ff81fe00000004 0xc101ff03fc000000

def z34 : W := mkw 0x82444843192e6604 0x1104889086325ccc 0x06004801393e6669 0x2c0c009002727ccc

def z35 : W := mkw 0x88ec11eb51aaa766 0x3111d823d6a3554e 0xf8fc71ffc1ff87df 0xdff1f8e3ff83ff0f

def z36 : W := mkw 0x3db28000e6d0000b 0x807b650001cda000 0x39238000c6c00010 0x10724700018d8000

def z37 : W := mkw 0x820848ca080e6620 0x1104109194101ccc 0x000049ce00066645 0x000000939c000ccc

def z38 : W := mkw 0x15000000a4000008 0x002a000001480000 0x3f000e01fe00787b 0x3e7e001c03fc00f0

def z39 : W := mkw 0x5ffb7ffd41828576 0x20bff6fffa83050a 0xffffffffc1c787df 0xffffffffff838f0f

def z40 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0023803e01f80784 0xc00047007c03f00f

def z41 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7e007001f8078000 0x08fc00e003f00f00

def z42 : W := mkw 0x0000800002500001 0x000001000004a000 0x0123800007f80038 0xf4024700000ff000

def z43 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffffe07f87f 0xfffffffffffc0ff0

def z44 : W := mkw 0x5fbbffbe02582af1 0x08bf77ff7c04b055 0xdffffffe07f87fff 0xffbffffffc0ff0ff

def z45 : W := mkw 0x0001021400000010 0x0000020428000000 0x01238e3e01c007df 0xf602471c7c03800f

def z46 : W := mkw 0x0200480008044000 0x0004009000100880 0x0000480000066041 0x0000009000000cc0

def z47 : W := mkw 0x5fb37f3400000050 0x00bf66fe68000000 0x5f23fe3000000003 0x3cbe47fc60000000

def z48 : W := mkw 0x42097fbc00000070 0x008412ff78000000 0x40007ffe00000007 0x008000fffc000000

def z49 : W := mkw 0x0001821402500891 0x080003042804a011 0x0123863007f819ba 0xf602470c600ff033

def z50 : W := mkw 0x0000800202582a81 0x080001000404b055 0x0000080e07f87ffd 0xe60000101c0ff0ff

def z51 : W := mkw 0x824c6ccb192f7624 0x510498d996325eec 0xc6dc7fcf393ffe6f 0xef8db8ff9e727ffc

def z52 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01038e0e06387820 0xa002071c1c0c70f0

def z53 : W := mkw 0x00000000ac055008 0x4000000001580aa0 0x000000003e007820 0x00000000007c00f0

def z54 : W := mkw 0x08a0112000000040 0x0011402240000000 0x58e071f000000007 0x5cb1c0e3e0000000

def z55 : W := mkw 0x1fb26c00ac055008 0x403f64d801580aa0 0xfffffe01fe07f87b 0xfffffffc03fc0ff0

def z56 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7e007001f807805b 0x1efc00e003f00f00

def z57 : W := mkw 0x02006c0008055000 0x400400d800100aa0 0x41007e000607f87b 0x368200fc000c0ff0

def z58 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fa4 0xe002471c7c0ff0ff

def z59 : W := mkw 0x02006c0008055000 0x400400d800100aa0 0x78007e01c007f85b 0x1ef000fc03800ff0

def z60 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0x87dfcfce00000005 0xed0fbf9f9c000000

def z61 : W := mkw 0x15000000a4000008 0x002a000001480000 0x39000000c6000010 0x10720000018c0000

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020003001c007df 0x560040006003800f

def z63 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x07000e003e007820 0x200e001c007c00f0

def z64 : W := mkw 0x1701ee16ae5d7a99 0x482e03dc2d5cbaf5 0x7f23fe3fffffffff 0xfefe47fc7fffffff

def z65 : W := mkw 0x0208488a00082220 0x0004109114001044 0x86dc49ce0138666d 0xed0db8939c0270cc

def z66 : W := mkw 0x0000000000000000 0x0000000000000000 0x5800700000000003 0x1cb000e000000000

def z67 : W := mkw 0x3df61161f5a2854e 0xa07bec22c3eb450a 0xfedc71c1f8078000 0x09fdb8e383f00f00

def z68 : W := mkw 0x08a0112000000040 0x0011402240000000 0x00e001f000000004 0x4001c003e0000000

def z69 : W := mkw 0x0200480008044000 0x0004009000100880 0x0600480138066069 0x2c0c009002700cc0

def z70 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x80dc01ce01380604 0xc101b8039c02700c

def z71 : W := mkw 0x08e0112141800046 0x0011c02242830000 0x78e071f1c1c0001f 0x5cf1c0e3e3838000

def z72 : W := mkw 0x0001021400000010 0x0000020428000000 0x01238e3e00000007 0xf402471c7c000000

def z73 : W := mkw 0x5fba7da800000060 0x00bf74fb50000000 0xdedc71c000000000 0x09bdb8e380000000

def z74 : W := mkw 0x0000000008055000 0x4000000000100aa0 0x000000000007f840 0x0200000000000ff0

def z75 : W := mkw 0x0208488800000020 0x0004109110000000 0x86dc49ce00000005 0xed0db8939c000000

def z76 : W := mkw 0x0001821402500891 0x080003042804a011 0x0123863006c01992 0x1202470c600d8033

def z77 : W := mkw 0x0004000010200000 0x0000080000204000 0x861c000038380020 0xa10c380000707000

def z78 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0x871f8e0e00000000 0xa10e3f1c1c000000

def z79 : W := mkw 0x17406c41ed87d50e 0x602e80d883db0faa 0x7f007e01ffc7fffb 0x3efe00fc03ff8fff

def z80 : W := mkw 0x0208488808044020 0x0004109110100880 0x86dc49cf3806606d 0xed0db8939e700cc0

def z81 : W := mkw 0x08a0112000000040 0x0011402240000000 0x78e071f1c007805f 0x5ef1c0e3e3800f00

def z82 : W := mkw 0x3df6a401f7f1100f 0xc07bed4803efe220 0xffffb601fff9983a 0xffffff6c03fff330

def z83 : W := mkw 0x3df60001f5a0000e 0x807bec0003eb4000 0xbedc0001f8000000 0x097db80003f00000

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001c007d8 0x020000000003800f

def z85 : W := mkw 0x08a0112000000040 0x0011402240000000 0x58c071c000000000 0x08b180e380000000

def z86 : W := mkw 0x00000000a4011008 0x4000000001480220 0x20000000c6019810 0x02400000018c0330

def z87 : W := mkw 0x3db38216e6d82a9b 0x887b67042dcdb055 0x39238e3ec7f87fff 0xf672471c7d8ff0ff

def z88 : W := mkw 0x5db3373400000050 0x00bb666e68000000 0x5923b63000000002 0x10b2476c60000000

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020003001c00784 0x400040006003800f

def z90 : W := mkw 0x824dcadf1b7e6eb5 0x19049b95be36fcdd 0x87dfcfcf3f3e7e6d 0xed0fbf9f9e7e7cfc

def z91 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x81ff8ffe00000007 0xf503ff1ffc000000

def z92 : W := mkw 0x820848c808064420 0x1104109190100c88 0x000041c000060000 0x0000008380000c00

def z93 : W := mkw 0x08e11377418aafd6 0x2811c226ee83155f 0x78e07fffc1c7ffdf 0x5ef1c0ffff838fff

def z94 : W := mkw 0x0208488800000020 0x0004109110000000 0x86dc41c000000000 0x090db88380000000

def z95 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0xbf1f8001fe380038 0xbd7e3f0003fc7000

def z96 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x00238e3e01f87fc7 0xc200471c7c03f0ff

def z97 : W := mkw 0x3db28000e6d0000b 0x807b650001cda000 0xbfff8000c6c00010 0xfd7fff00018d8000

def z98 : W := mkw 0x0001021600082a90 0x080002042c001055 0x00000e3e00007fc7 0x0200001c7c0000ff

def z99 : W := mkw 0x80440043192e6604 0x1100880086325ccc 0x0000080f393e666d 0xe40000101e727ccc

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x01200e3007c07fff 0x7602401c600f80ff

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000138000028 0x2c0c000002700000

def z102 : W := mkw 0x0000800202582a81 0x080001000404b055 0x01000e0007f87ffb 0x3602001c000ff0ff

def z103 : W := mkw 0x0040004101020404 0x0000800082020408 0x00c041c100060000 0x0801808382000c00

def z104 : W := mkw 0x4ae97ffd41828576 0x2095d2fffa83050a 0x78e07fffc1c787df 0x5ef1c0ffff838f0f

def z105 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78c071c1c0078000 0x08f180e383800f00

def z106 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1c1ffff8038 0xfdffffe383ffff00

def z107 : W := mkw 0x820848ca080e6620 0x1104109194101ccc 0x000049ce013e666d 0xe40000939c027ccc

def z108 : W := mkw 0x824c48c919264424 0x1104989192324c88 0x86dc41c138060000 0x090db88382700c00

def z109 : W := mkw 0x15000000a4000008 0x002a000001480000 0x7f007001fe07807b 0x3efe00e003fc0f00

def z110 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x39238001fff80038 0x1072470003fff000

def z111 : W := mkw 0x1fe07d61ed87d54e 0x603fc0fac3db0faa 0x7ee071f1f9c787df 0x5efdc0e3e3f38f0f

def z112 : W := mkw 0x08a0112040808142 0x2011402240810102 0x78203030c1c187df 0x56f040606183830f

def z113 : W := mkw 0x974c6ccbbd2f762c 0x512e98d9977a5eec 0x87dc4fcf3f3e7e6d 0xed0fb89f9e7e7cfc

def z114 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x80dc49ce013e6645 0xc101b8939c027ccc

def z115 : W := mkw 0x20448001f7f0000f 0x8040890003efe000 0x20000001fff80038 0x0040000003fff000

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x78007001c007805b 0x1ef000e003800f00

def z117 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x87ff8ffe00000004 0xe10fff1ffc000000

def z118 : W := mkw 0x35568001b770000d 0x806aad00036ee000 0x87df80013f380028 0xed0fbf00027e7000

def z119 : W := mkw 0x17006c0008055000 0x402e00d800100aa0 0x5f007e000007f843 0x3ebe00fc00000ff0

def z120 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x873f80003ff80038 0xf50e7f00007ff000

def z121 : W := mkw 0x0040004101020404 0x0000800082020408 0x00c041c10106064d 0x4c01808382020c0c

def z122 : W := mkw 0x35160000b4200008 0x806a2c0001684000 0x861c000038000000 0x010c380000700000

def z123 : W := mkw 0x08e0000141800006 0x0011c00002830000 0x38e00031c1c007df 0x5e71c0006383800f

def z124 : W := mkw 0x8aec59eb59aee766 0x3115d8b3d6b35dce 0x86fc49ff39fe67ed 0xed0df893fe73fccf

def z125 : W := mkw 0x7fffffbdfff5507f 0xc0ffffff7bffeaa0 0xfffffffffffff87f 0xfffffffffffffff0

def z126 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0x80ff800001f80000 0xc101ff000003f000

def z127 : W := mkw 0x0040004141828506 0x200080008283050a 0x20200031c1c787df 0x5640400063838f0f

def z128 : W := mkw 0x5ffa7de941828566 0x20bff4fbd283050a 0xfedc71c1c0078000 0x09fdb8e383800f00

def z129 : W := mkw 0x2044800153f00007 0x8040890002a7e000 0x0000000001f80000 0x000000000003f000

def z130 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x00000e3e07f87fff 0x0200001c7c0ff0ff

def z131 : W := mkw 0xbffec8cbfffe662f 0x917ffd9197fffccc 0xbfffc9cffffe667d 0xfd7fff939ffffccc

def z132 : W := mkw 0x0001021400000890 0x0800020428000011 0x0000063000001982 0x0200000c60000033

def z133 : W := mkw 0x5513261400000010 0x00aa264c28000000 0x0103860000000000 0x0002070c00000000

def z134 : W := mkw 0x1fb26c0000000000 0x003f64d800000000 0xdffffe0000000003 0xfdbffffc00000000

def z135 : W := mkw 0x00000000ac055008 0x4000000001580aa0 0x20000001fe07f878 0x0240000003fc0ff0

def z136 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f820 0x28fe00fc03fc0ff0

def z137 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xfedc79cff93fe67f 0xfffdb8f39ff27fcc

def z138 : W := mkw 0x0040004141828506 0x200080008283050a 0x0000000001c00780 0x000000000003800f

def z139 : W := mkw 0x8044004359aee706 0x3100880086b35dce 0x20000001f9ffe7f8 0x0240000003f3ffcf

def z140 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78203031c1c787da 0x12f0406063838f0f

def z141 : W := mkw 0x08e0000141800006 0x0011c00002830000 0x00e0000001c00000 0x4001c00000038000

def z142 : W := mkw 0x8aec59eb59aee766 0x3115d8b3d6b35dce 0xfefc79fff9ffe7ff 0xfffdf8f3fff3ffcf

def z143 : W := mkw 0x1500000000000000 0x002a000000000000 0x1f00000000000000 0x3c3e000000000000

def z144 : W := mkw 0x1fe07d61ed87d54e 0x603fc0fac3db0faa 0x7fe07ff1ffc7ffff 0x7effc0ffe3ff8fff

def z145 : W := mkw 0x0040004141828506 0x200080008283050a 0x20000001c1c787d8 0x0240000003838f0f

def z146 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x86dc49ce38386025 0xed0db8939c7070c0

def z147 : W := mkw 0x48ba11a800000060 0x0091742350000000 0x80dc01c000000000 0x0101b80380000000

def z148 : W := mkw 0x00008002ae5d7a89 0x48000100055cbaf5 0x20000001fffffff8 0x0240000003ffffff

def z149 : W := mkw 0x08a1933602582ad1 0x081143266c04b055 0x59e3fffe07f87fff 0xfeb3c7fffc0ff0ff

def z150 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8031fff807ff 0xff7fff0063fff00f

def z151 : W := mkw 0x3df79377f7faafdf 0xa87bef26efeff55f 0xffffffffffffffff 0xffffffffffffffff

def z152 : W := mkw 0x00019376025aafd1 0x28000326ec04b55f 0x4123fffe07ffffff 0xf68247fffc0fffff

def z153 : W := mkw 0x1701ee16ae5d7a99 0x482e03dc2d5cbaf5 0x07038e0e3e387820 0xa00e071c1c7c70f0

def z154 : W := mkw 0x28f6916153f28547 0xa051ed22c2a7e50a 0x80ff81f001f80784 0xc101ff03e003f00f

def z155 : W := mkw 0x7dff93bdf7f0007f 0x80fbff277befe000 0xbfff81fffff8003c 0xfd7fff03fffff000

def z156 : W := mkw 0x35568001f7f0000f 0x806aad0003efe000 0xa71f8001fff80038 0xa14e3f0003fff000

def z157 : W := mkw 0x8aeddbff5bfeeff7 0x3915dbb7feb7fddf 0xffffffffffffffff 0xffffffffffffffff

def z158 : W := mkw 0x804c00c911220424 0x1100980192224408 0x80dc01c000000000 0x0101b80380000000

def z159 : W := mkw 0x42097ffc00028570 0x208412fff800050a 0x40007ffe000787c7 0x028000fffc000f0f

def z160 : W := mkw 0x1fba488800000020 0x003f749110000000 0x9fffc9ce00000005 0xfd3fff939c000000

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x78007001c0078000 0x08f000e003800f00

def z162 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0x873f8e3e00000007 0xf50e7f1c7c000000

def z163 : W := mkw 0x82094ade080e6eb0 0x19041295bc101cdd 0x00004ffe00067fc7 0x0200009ffc000cff

def z164 : W := mkw 0x20448041f7f2850f 0xa040890083efe50a 0x20000001ffff87f8 0x0240000003ffff0f

def z165 : W := mkw 0x1512000000000000 0x002a240000000000 0x871f800000000000 0xa10e3f0000000000

def z166 : W := mkw 0x08e1937743daafd7 0x2811c326ee87b55f 0x79e3ffffc7ffffff 0xfef3c7ffff8fffff

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0x79007e01c607f87b 0x3ef200fc038c0ff0

def z168 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0003800e00380000 0x800007001c007000

def z169 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x00e001f001c00784 0x4001c003e003800f

def z170 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x3f000e01fe007838 0x3c7e001c03fc00f0

def z171 : W := mkw 0x3ff66c01fda5500e 0xc07fecd803fb4aa0 0xfedc7001f8078000 0x09fdb8e003f00f00

def z172 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x80dc09ce0138666d 0xe501b8139c0270cc

def z173 : W := mkw 0x1700ec00ae555009 0x402e01d8015caaa0 0x7f23fe01fffff87b 0xfefe47fc03fffff0

def z174 : W := mkw 0x0000000200082200 0x0000000004001044 0x0000080e0138666d 0xe40000101c0270cc

def z175 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01038e0e0638787b 0xb602071c1c0c70f0

def z176 : W := mkw 0x3db68000b6700009 0x807b6d00016ce000 0x9fff80003e380020 0xfd3fff00007c7000

def z177 : W := mkw 0x9fec7debfdaff76e 0x713fd8fbd7fb5fee 0xfffc7fffffffffff 0xfffff8ffffffffff

def z178 : W := mkw 0x5db33734a4011058 0x40bb666e69480220 0x7923b630c6019812 0x12f2476c618c0330

def z179 : W := mkw 0x0000116000028540 0x20000022c000050a 0x400071f0000787c7 0x028000e3e0000f0f

def z180 : W := mkw 0x970c6c8abc2d7228 0x512e18d915785ae4 0xff1c7e0ffe3ff87b 0xbffe38fc1ffc7ff0

def z181 : W := mkw 0x5fff7fbd11200074 0x00bffeff7a224000 0xdfffffff3938002f 0xfdbffffffe727000

def z182 : W := mkw 0x02006c0008055000 0x400400d800100aa0 0x00000e0000007800 0x0000001c000000f0

def z183 : W := mkw 0x0000004000028500 0x200000008000050a 0x00000000000787c0 0x0200000000000f0f

def z184 : W := mkw 0x3df28001e7d0000f 0x807be50003cfa000 0x39e38001c7c00018 0x5c73c700038f8000

def z185 : W := mkw 0x9ffe48cb192e6624 0x113ffc9196325ccc 0x9fffc9cf393e666d 0xfd3fff939e727ccc

def z186 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x5923fffe00000007 0x10b247fffc000000

def z187 : W := mkw 0x804582571b7e6e95 0x19008b04ae36fcdd 0x01238e3f3ffe7fff 0xf602471c7e7ffcff

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000e000600787b 0x3602001c000c00f0

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000700000078043 0x028000e000000f00

def z190 : W := mkw 0x08e0000141800006 0x0011c00002830000 0x38e00001c1c00018 0x5c71c00003838000

def z191 : W := mkw 0x974c48cbbd2e662c 0x112e9891977a5ccc 0xbfdc49cfff3e667d 0xfd7fb8939ffe7ccc

def z192 : W := mkw 0x08e01163418aa746 0x2011c022c683154e 0x78e079ffc1ffe7ff 0xfef1c0f3ff83ffcf

def z193 : W := mkw 0x0000116000028540 0x20000022c000050a 0x000001f000000784 0x00000003e000000f

def z194 : W := mkw 0x15000000a4000008 0x002a000001480000 0x3f000001fe000038 0x3c7e000003fc0000

def z195 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x38e001f1c1c0079c 0x5c71c003e383800f

def z196 : W := mkw 0x401b029c00000030 0x0080360538000000 0x801f800e00000000 0x81003f001c000000

def z197 : W := mkw 0x0000112000000040 0x0000002240000000 0x400071f000000007 0x008000e3e0000000

def z198 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbedc0001fff80038 0x097db80003fff000

def z199 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc09ce39386624 0xe10db8139c7270cc

def z200 : W := mkw 0x1df2116141828546 0x203be422c283050a 0xfffff1f1c1c787df 0xffffffe3e3838f0f

def z201 : W := mkw 0x97446c43bd2f760c 0x512e88d8877a5eec 0x7f007e01ff3ffe7b 0x3efe00fc03fe7ffc

def z202 : W := mkw 0x824c48c919264424 0x1104989192324c88 0x86dc41c1393e0028 0xed0db88382727c00

def z203 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xfffff001ffff807b 0xffffffe003ffff00

def z204 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x861c080f393e6668 0xa10c38101e727ccc

def z205 : W := mkw 0x20458217f7f82a9f 0x88408b042feff055 0x21238e3ffff87fff 0xf642471c7ffff0ff

def z206 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c78784 0x48f1c0e3e3838f0f

def z207 : W := mkw 0x3ff6ec01fff5500f 0xc07fedd803ffeaa0 0xfffffe01fffff87b 0xfffffffc03fffff0

def z208 : W := mkw 0x3df68001fff5500f 0xc07bed0003ffeaa0 0xbfff8001fffff878 0xff7fff0003fffff0

def z209 : W := mkw 0x80000042080e6600 0x1100000084101ccc 0x0000000000066640 0x0000000000000ccc

def z210 : W := mkw 0x0000800202582a81 0x080001000404b055 0x0000000006387820 0x00000000000c70f0

def z211 : W := mkw 0x0001021400000010 0x0000020428000000 0x0123863000000002 0x1002470c60000000

def z212 : W := mkw 0x571bee9e02582ab1 0x08ae37dd3c04b055 0x871f8e0e06387820 0xa10e3f1c1c0c70f0

def z213 : W := mkw 0x7ffefda9f7f0006f 0x80fffdfb53efe000 0xfffff1c1fff80038 0xfdffffe383fff000

def z214 : W := mkw 0x1df6000111200004 0x003bec0002224000 0x9fff800139380028 0xfd3fff0002727000

def z215 : W := mkw 0xdfff7fff192e6674 0x11bffefffe325ccc 0xdfffffff393e666f 0xfdbffffffe727ccc

def z216 : W := mkw 0x0000800002500001 0x000001000004a000 0x0123800006c00010 0x10024700000d8000

def z217 : W := mkw 0x28f7821753f82a97 0x8851ef042ea7f055 0x81ff8e3e07f87fff 0xf703ff1c7c0ff0ff

def z218 : W := mkw 0x0040004141828506 0x200080008283050a 0x78007001c1c787db 0x1ef000e003838f0f

def z219 : W := mkw 0x15002400a4011008 0x402a004801480220 0x79003e00c601f87b 0x36f2007c018c03f0

def z220 : W := mkw 0x820848ca080e6620 0x1104109194101ccc 0x060049cf3806666d 0x2c0c00939e700ccc

def z221 : W := mkw 0x17086c88ac055028 0x402e10d911580aa0 0xffdc7fcffe07f87f 0xffffb8ff9ffc0ff0

def z222 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8e01fff8787b 0xff7fff1c03fff0f0

def z223 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf38066645 0x090db8939e700ccc

def z224 : W := mkw 0x3ff6fd61fff7d54f 0xe07fedfac3ffefaa 0xfffffff1ffffffff 0xffffffffe3ffffff

def z225 : W := mkw 0x0201ee160a5d7a91 0x480403dc2c14baf5 0x4123fe3e07ffffff 0xf68247fc7c0fffff

def z226 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x0600000038000000 0x000c000000700000

def z227 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x00e001f001c007df 0x5601c003e003800f

def z228 : W := mkw 0x824dcadf1b7e6eb5 0x19049b95be36fcdd 0x87ffcfff3ffe7fff 0xff0fff9ffe7ffcff

def z229 : W := mkw 0x400913bc00000070 0x0080122778000000 0x000001fe00000004 0x00000003fc000000

def z230 : W := mkw 0x48b3133400000050 0x0091662668000000 0x0023803000000000 0x0000470060000000

def z231 : W := mkw 0x5fbb7fbca4011078 0x40bf76ff79480220 0xfffffffec6019817 0xfffffffffd8c0330

def z232 : W := mkw 0x02004802080c6200 0x00040090041018c4 0x0600480f393e666d 0xec0c00901e727ccc

def z233 : W := mkw 0x02094a9c00000030 0x0004129538000000 0x87ffcffe00000007 0xfd0fff9ffc000000

def z234 : W := mkw 0x17446c01bd25500c 0x402e88d8037a4aa0 0xffdc7e01ff3ff87b 0xffffb8fc03fe7ff0

def z235 : W := mkw 0x0001021400000010 0x0000020428000000 0x0023803e00000004 0xc00047007c000000

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000080000006069 0x24000010000000c0

def z237 : W := mkw 0x8aec48cb59ae6626 0x1115d89196b35ccc 0xbefc49cff9fe667d 0xfd7df8939ff3fccc

def z238 : W := mkw 0x0000800002500001 0x000001000004a000 0x0103800006380020 0xa0020700000c7000

def z239 : W := mkw 0x824c48cb59aee726 0x3104989196b35dce 0xa6dc49cff9ffe7fd 0xef4db8939ff3ffcf

def z240 : W := mkw 0x17006c0000000000 0x002e00d800000000 0x5f007e000600787b 0x3ebe00fc000c00f0

def z241 : W := mkw 0x4abb5bbc00000070 0x009576b778000000 0x86ffc9fe00000005 0xed0dff93fc000000

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000e0000000003 0x3402001c00000000

def z243 : W := mkw 0xcaff5bff192e6674 0x1195feb7fe325ccc 0x86ffc9ff393e666d 0xed0dff93fe727ccc

def z244 : W := mkw 0x5ffb7ffded87d57e 0x60bff6fffbdb0faa 0xffffffffffc7ffff 0xffffffffffff8fff

def z245 : W := mkw 0x42096e9c00000030 0x008412dd38000000 0x00000e0e00000000 0x0000001c1c000000

def z246 : W := mkw 0x0aa859a800000060 0x001550b350000000 0xdefc79fe00000007 0xfdbdf8f3fc000000

def z247 : W := mkw 0x824c48cb112a2624 0x110498919622544c 0x86dc49ce01380605 0xed0db8939c02700c

def z248 : W := mkw 0x8aec59eb192e6664 0x1115d8b3d6325ccc 0xdefc79ff393e666f 0xfdbdf8f3fe727ccc

def z249 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x40e071f001c787c7 0x4281c0e3e0038f0f

def z250 : W := mkw 0x08e0916343daafc7 0x2811c122c687b55f 0x78e071f1c7ffffff 0x5ef1c0e3e38fffff

def z251 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0xdf1ffe0e00000003 0xbdbe3ffc1c000000

def z252 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x27000e01fe07f878 0x224e001c03fc0ff0

def z253 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0023803e07f87ffc 0xc20047007c0ff0ff

def z254 : W := mkw 0x80440043112a2604 0x110088008622544c 0x0000000001380600 0x000000000002700c

def z255 : W := mkw 0xdfffffff1b7e6ef5 0x19bffffffe36fcdd 0xdfffffff3ffe7fff 0xffbffffffe7ffcff

def z256 : W := mkw 0x28f68001f7f0000f 0x8051ed0003efe000 0xa0ff8001fff80038 0xc141ff0003fff000

def z257 : W := mkw 0x5ffb7ffd41828576 0x20bff6fffa83050a 0xffffffffc0078007 0xfdffffffff800f00

def z258 : W := mkw 0x7fffffbff7f82aff 0x88ffffff7feff055 0xfffffffffff87fff 0xfffffffffffff0ff

def z259 : W := mkw 0x3db28000e6d0000b 0x807b650001cda000 0x39238000c7f80038 0xf4724700018ff000

def z260 : W := mkw 0x3df68041f7f2040f 0x807bed0083efe408 0xbfffc1c1fffe067d 0xfd7fff8383fffc0c

def z261 : W := mkw 0x3ff6c801fff4400f 0x807fed9003ffe880 0xbfffc801fffe6079 0xfd7fff9003fffcc0

def z262 : W := mkw 0x5ffa7de941828566 0x20bff4fbd283050a 0xfefc71f1c1c787df 0x5ffdf8e3e3838f0f

def z263 : W := mkw 0x42097fbc00000070 0x008412ff78000000 0x4123fffe00000007 0xf48247fffc000000

def z264 : W := mkw 0x42097fbe00082af0 0x088412ff7c001055 0x40007ffe00007fc7 0x028000fffc0000ff

def z265 : W := mkw 0x0040000101000004 0x0000800002020000 0x00c0000101000008 0x4c01800002020000

def z266 : W := mkw 0x5db3373440808152 0x20bb666e68810102 0x7923b630c0c18192 0x12f2476c61818303

def z267 : W := mkw 0x7fffffbd53f00077 0x80ffffff7aa7e000 0xdffffffe01f80007 0xfdbffffffc03f000

def z268 : W := mkw 0x3ff7ee17fffd7a9f 0xc87fefdc2ffffaf5 0xfffffe3fffffffff 0xfffffffc7fffffff

def z269 : W := mkw 0x3ff66c01fda5500e 0xc07fecd803fb4aa0 0xffdc7e01fe07f87b 0x3fffb8fc03fc0ff0

def z270 : W := mkw 0x974c6ccb192e6624 0x112e98d996325ccc 0xdfdc7fcf393e666f 0xfdbfb8ff9e727ccc

def z271 : W := mkw 0x0044000111200004 0x0000880002224000 0x0000000139380028 0x0000000002727000

def z272 : W := mkw 0x15002400ac055008 0x402a004801580aa0 0x79003601fe07f87a 0x12f2006c03fc0ff0

def z273 : W := mkw 0x02016e16080d7a90 0x480402dc2c101af5 0x40007e3e0007ffc7 0x028000fc7c000fff

def z274 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0xb8ff8001c1f80018 0xdd71ff000383f000

def z275 : W := mkw 0xbffec88bfffc622f 0x917ffd9117fff8c4 0xbfff880ffff86038 0xfd7fff101ffff0c0

def z276 : W := mkw 0xbfffcadffffe6ebf 0x997fff95bffffcdd 0xbfffcffffffe7fff 0xff7fff9ffffffcff

def z277 : W := mkw 0x0001021600082a90 0x080002042c001055 0x00000e3e01387fef 0xe600001c7c0270ff

def z278 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfdfffce00000000 0xa9bfbfff9c000000

def z279 : W := mkw 0xdfff7fffbd2f767c 0x51bffeffff7a5eec 0xffffffffff3ffe7f 0xfffffffffffe7ffc

def z280 : W := mkw 0x7fffee9df7f0003f 0x80ffffdd3befe000 0xbfff8e0ffff80038 0xfd7fff1c1ffff000

def z281 : W := mkw 0x0000000200082200 0x0000000004001044 0x0000080e00386020 0xa00000101c0070c0

def z282 : W := mkw 0x02007d600807d540 0x600400fac0100faa 0x40007ff00007ffc7 0x028000ffe0000fff

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z284 : W := mkw 0x820859ea080ee760 0x310410b3d4101dce 0x400079fe0007e7c7 0x028000f3fc000fcf

def z285 : W := mkw 0x4abb7fbc00000070 0x009576ff78000000 0xc0fffffe00000007 0xc181fffffc000000

def z286 : W := mkw 0x02006c0008055000 0x400400d800100aa0 0x40007e000007f843 0x028000fc00000ff0

def z287 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xb9ff8000c7f80010 0xd173ff00018ff000

def z288 : W := mkw 0x80440043192e6604 0x1100880086325ccc 0x86dc0001393e6668 0xed0db80002727ccc

def z289 : W := mkw 0x1fe07d6141828546 0x203fc0fac283050a 0x7fe07ff1c1c787df 0x7effc0ffe3838f0f

def z290 : W := mkw 0x35448001f7f0000f 0x806a890003efe000 0x3f000001fff80038 0x3c7e000003fff000

def z291 : W := mkw 0xc2097ffe080e6670 0x118412fffc101ccc 0x40007ffe00066647 0x008000fffc000ccc

def z292 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf383e6020 0xa90db8939e707cc0

def z293 : W := mkw 0x0040804343daaf87 0x280081008687b55f 0x20000001c7fffff8 0x02400000038fffff

def z294 : W := mkw 0x08a0000000000000 0x0011400000000000 0x18e0000000000000 0x5c31c00000000000

def z295 : W := mkw 0x35128000a6500009 0x806a2500014ca000 0x0103800006000000 0x00020700000c0000

def z296 : W := mkw 0x0001821402500891 0x080003042804a011 0x0023803000c00180 0x0000470060018003

def z297 : W := mkw 0x35178216b6782a99 0x886a2f042d6cf055 0x873f8e3e3ff87fff 0xf70e7f1c7c7ff0ff

def z298 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdf3fbe3e00000002 0xb1be7f7c7c000000

def z299 : W := mkw 0x0001021600082a90 0x080002042c001055 0x00200e3e01c07fdf 0x5600401c7c0380ff

def z300 : W := mkw 0x024c488911200024 0x0004989112224000 0x86dc49cf3938002d 0xed0db8939e727000

def z301 : W := mkw 0x08e1937743daafd7 0x2811c326ee87b55f 0x78e3f1ffc1ff87df 0xdef1c7e3ff83ff0f

def z302 : W := mkw 0x1de01161e582854e 0x203bc022c3cb050a 0x7fe071f1ffc787ff 0x7effc0e3e3ff8f0f

def z303 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x86dc01cf3938062c 0xed0db8039e72700c

def z304 : W := mkw 0x17086c8800000020 0x002e10d910000000 0xdfdc7fce00000007 0xfdbfb8ff9c000000

def z305 : W := mkw 0x824dcadf1b7e6eb5 0x19049b95be36fcdd 0x86ffc9ff39fe67ed 0xed0dff93fe73fccf

def z306 : W := mkw 0x17016e16ac0d7a98 0x482e02dc2d581af5 0x7f007e3ffe07ffff 0x3efe00fc7ffc0fff

def z307 : W := mkw 0x8044004119264404 0x1100880082324c88 0x0000000138060000 0x0000000002700c00

def z308 : W := mkw 0x1db2112000000040 0x003b642240000000 0xdffff1f000000007 0xfdbfffe3e0000000

def z309 : W := mkw 0xb75ec8cbbf7e662d 0x916ebd91977efccc 0x87dfc9cf3f3e666d 0xed0fbf939e7e7ccc

def z310 : W := mkw 0x88ec11eb51aaa766 0x3111d823d6a3554e 0x80fc01fe01f80784 0xc101f803fc03f00f

def z311 : W := mkw 0x17006c0008044000 0x002e00d800100880 0x5f007e013806606b 0x3cbe00fc02700cc0

def z312 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbeff8001f9f80000 0xc97dff0003f3f000

def z313 : W := mkw 0x5fbb7fbc40808172 0x20bf76ff78810102 0xfffffffec0c18197 0xfffffffffd818303

def z314 : W := mkw 0x0008008800000020 0x0000100110000000 0x80dc01ce00000004 0xc101b8039c000000

def z315 : W := mkw 0x1fe07d61ed87d54e 0x603fc0fac3db0faa 0x7ec071c1f8078000 0x08fd80e383f00f00

def z316 : W := mkw 0x1df2000141800006 0x003be40002830000 0xbfff8001c1c00018 0xfd7fff0003838000

def z317 : W := mkw 0xc24d7fff192e6674 0x11849afffe325ccc 0xc6dc7fff393e666f 0xed8db8fffe727ccc

def z318 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7e007001fe07f878 0x0afc00e003fc0ff0

def z319 : W := mkw 0x3df60001f5a0000e 0x807bec0003eb4000 0xbfff8001f8000000 0xfd7fff0003f00000

def z320 : W := mkw 0x0208488800000020 0x0004109110000000 0x861c080e00000000 0xa10c38101c000000

def z321 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xffffffffc007805f 0xffffffffff800f00

def z322 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc41cf393e0604 0xc90db8839e727c0c

def z323 : W := mkw 0x0000800202582a81 0x080001000404b055 0x0000000001f80780 0x000000000003f00f

def z324 : W := mkw 0x08e01161ed87d54e 0x6011c022c3db0faa 0x78e071f1ffc7ffff 0x5ef1c0e3e3ff8fff

def z325 : W := mkw 0x5db3373400000050 0x00bb666e68000000 0x5923be3e00000007 0xf4b2477c7c000000

def z326 : W := mkw 0x08e1821743d82a97 0x0811c3042e87b055 0x39e38e3fc7f87fff 0xfe73c71c7f8ff0ff

def z327 : W := mkw 0x0001021600082210 0x000002042c001044 0x01238e3e0138666f 0xf402471c7c0270cc

def z328 : W := mkw 0x3df68041f7f2850f 0xa07bed0083efe50a 0xbfff8001ffff87f8 0xff7fff0003ffff0f

def z329 : W := mkw 0x0000800202582201 0x000001000404b044 0x0123880e07f8667d 0xf40247101c0ff0cc

def z330 : W := mkw 0x974deedfbf7f7ebd 0x592e9bddbf7efefd 0xffffffffffffffff 0xffffffffffffffff

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x0123800000000000 0xf402470000000000

def z332 : W := mkw 0x20448001f7f0000f 0x8040890003efe000 0x21238001fff80038 0xf442470003fff000

def z333 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfdf8001fe380020 0xa97fbf0003fc7000

def z334 : W := mkw 0x3df78217f7f82a9f 0x887bef042feff055 0xbfff803ffff807bc 0xfd7fff007ffff00f

def z335 : W := mkw 0x0000112000008140 0x2000002240000102 0x4000303000018182 0x0280006060000303

def z336 : W := mkw 0x08b2000000000000 0x0011640000000000 0x80ff800000000000 0xc101ff0000000000

def z337 : W := mkw 0x5dbb37bc00000070 0x00bb766f78000000 0xd9ffb7fe00000006 0xd1b3ff6ffc000000

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x38000001c0000018 0x1c70000003800000

def z339 : W := mkw 0x5fba7da800000060 0x00bf74fb50000000 0xdfdc7fc000000003 0x3dbfb8ff80000000

def z340 : W := mkw 0x08a0112000000040 0x0011402240000000 0x58e071f001c007df 0x5eb1c0e3e003800f

def z341 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7e007801f807e069 0x2cfc00f003f00fc0

def z342 : W := mkw 0x00018216ae5d7a99 0x480003042d5cbaf5 0x21238e3fffffffff 0xf642471c7fffffff

def z343 : W := mkw 0x0209ca9e02582ab1 0x080413953c04b055 0x87ffcffe07f87fff 0xff0fff9ffc0ff0ff

def z344 : W := mkw 0x88e4116359aee746 0x3111c822c6b35dce 0x78e071f1f9ffe7ff 0x5ef1c0e3e3f3ffcf

def z345 : W := mkw 0x0001821402500891 0x080003042804a011 0x0103860006001800 0x0002070c000c0030

def z346 : W := mkw 0x824c48c919264424 0x1104989192324c88 0x86dc49c138066069 0x2d0db89382700cc0

def z347 : W := mkw 0x1fa07d20ac055048 0x403f40fa41580aa0 0x7fe07ff1fe07f87f 0x7effc0ffe3fc0ff0

def z348 : W := mkw 0x0040004101020404 0x0000800082020408 0x0000000101060648 0x0000000002020c0c

def z349 : W := mkw 0x571b6e9cac055038 0x40ae36dd39580aa0 0xff1ffe0ffe07f87b 0xbffe3ffc1ffc0ff0

def z350 : W := mkw 0xaafec8cb5bfe6627 0x9155fd9196b7fccc 0x86ffc9cf39fe666d 0xed0dff939e73fccc

def z351 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0x81ff800007f80038 0xf503ff00000ff000

def z352 : W := mkw 0xbffed9ebfffee76f 0xb17ffdb3d7fffdce 0xfffff9ffffffe7ff 0xfffffff3ffffffcf

def z353 : W := mkw 0x00418257035a2e95 0x08008304ae06b45d 0x01e3cfff07fe7fff 0xfe03c79ffe0ffcff

def z354 : W := mkw 0xa24cc8cbfffe662f 0x9144999197fffccc 0xa6dc49cffffe667d 0xed4db8939ffffccc

def z355 : W := mkw 0x0040116101028544 0x20008022c202050a 0x40c071f1010787cf 0x4e8180e3e2020f0f

def z356 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc41c1393e6668 0x090db88382727ccc

def z357 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x5f007e003e007823 0x3cbe00fc007c00f0

def z358 : W := mkw 0x0244480119244004 0x0004889002324880 0x86dc4801393e6069 0xed0db89002727cc0

def z359 : W := mkw 0x48fb13fd41828576 0x2091f627fa83050a 0xf8fff1ffc1c787df 0xdff1ffe3ff838f0f

def z360 : W := mkw 0x08e0800143d00007 0x0011c1000287a000 0x39e38001c7f80038 0xfc73c700038ff000

def z361 : W := mkw 0x0000000200082200 0x0000000004001044 0x0000000001386668 0x00000000000270cc

def z362 : W := mkw 0x0040004101020404 0x0000800082020408 0x00e041f101c607df 0x5e01c083e2038c0f

def z363 : W := mkw 0x3df69121f7f0814f 0xa07bed2243efe102 0xffffb031fff981ba 0xffffff6063fff303

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000005b 0x1600000000000000

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000006000038 0x34020000000c0000

def z366 : W := mkw 0x5ffb7ffd41828576 0x20bff6fffa83050a 0xdffffffe01c00787 0xfdbffffffc03800f

def z367 : W := mkw 0x17406c41ad07540c 0x402e80d8835a0ea8 0x7fc07fc1ff07fe7f 0x7eff80ff83fe0ffc

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020003000000007 0x5400400060000000

def z369 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e06387827 0xf402471c7c0c70f0

def z370 : W := mkw 0x2016800012700001 0x80402d000024e000 0x801f800000380000 0x81003f0000007000

def z371 : W := mkw 0x8208488a080c6220 0x11041091141018c4 0x0000080e00006000 0x000000101c0000c0

def z372 : W := mkw 0x28e48001f7f0000f 0x8051c90003efe000 0x38e00001fff80038 0x5c71c00003fff000

def z373 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x58e071f001c00787 0x5cb1c0e3e003800f

def z374 : W := mkw 0xa0448043fffe660f 0x9140890087fffccc 0x20000001fffe6678 0x0040000003fffccc

def z375 : W := mkw 0x00011376000aafd0 0x28000226ec00155f 0x40007ffe0007ffc7 0x028000fffc000fff

def z376 : W := mkw 0x0000800002500001 0x000001000004a000 0x0123803007f807ff 0xf6024700600ff00f

def z377 : W := mkw 0x7ffe7da9f5a0006e 0x80fffcfb53eb4000 0xfedc71c1f8000000 0x09fdb8e383f00000

def z378 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdefff1fe00000004 0xc9bdffe3fc000000

def z379 : W := mkw 0x024848c901020424 0x0004909192020408 0x86dc49cf0106064d 0xed0db8939e020c0c

def z380 : W := mkw 0x08a0116000028540 0x20114022c000050a 0x58e071f0000787c7 0x5eb1c0e3e0000f0f

def z381 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78c071c1c007805b 0x1ef180e383800f00

def z382 : W := mkw 0x08a0112040808142 0x2011402240810102 0x0020003000c00180 0x0000400060018003

def z383 : W := mkw 0x1db2000000000000 0x003b640000000000 0x1923800000000000 0x1032470000000000

def z384 : W := mkw 0x5db3373400000050 0x00bb666e68000000 0xdfffb63000000002 0xfdbfff6c60000000

def z385 : W := mkw 0x5fb37f34ac055058 0x40bf66fe69580aa0 0x7f23fe31fe07f87b 0x3efe47fc63fc0ff0

def z386 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0x86ff800139f80028 0xed0dff000273f000

def z387 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x000049cf393e666d 0x000000939e727ccc

def z388 : W := mkw 0x0ae859e941828566 0x2015d0b3d283050a 0xfefc79ffc1c787df 0xfffdf8f3ff838f0f

def z389 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xbfff81f1fff807bc 0xfd7fff03e3fff00f

def z390 : W := mkw 0xbffeeccbffff762f 0xd17ffdd997fffeec 0xffffffcffffffe7f 0xffffffff9ffffffc

def z391 : W := mkw 0x0000000200082200 0x0000000004001044 0x0000080e00006645 0x000000101c0000cc

def z392 : W := mkw 0x0200480008044000 0x0004009000100880 0x0600080038006020 0x200c0010007000c0

def z393 : W := mkw 0x8aec59e959a6c566 0x3115d8b3d2b34d8a 0xfedc71c1f8078000 0x09fdb8e383f00f00

def z394 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x87ff80003ff80020 0xe10fff00007ff000

def z395 : W := mkw 0x08e4116151a28546 0x2011c822c2a3450a 0xfefc71f1f9ff87ff 0xfffdf8e3e3f3ff0f

def z396 : W := mkw 0x0000800002500001 0x000001000004a000 0x0023800001f80000 0xc00047000003f000

def z397 : W := mkw 0x1fa07d2000000040 0x003f40fa40000000 0x5fe07ff000000007 0x7cbfc0ffe0000000

def z398 : W := mkw 0x0040004101020404 0x0000800082020408 0x78c071c1c107865f 0x5ef180e383820f0c

def z399 : W := mkw 0x970c6c8abc2d7228 0x512e18d915785ae4 0x871c0e0e3e387820 0xa10e381c1c7c70f0

def z400 : W := mkw 0xc8ff13ff112a2674 0x1191fe27fe22544c 0x80ff81fe01380604 0xc101ff03fc02700c

def z401 : W := mkw 0xbdf68043fffe660f 0x917bed0087fffccc 0xbfff8001fffe6678 0xfd7fff0003fffccc

def z402 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007001fe078038 0x3cfe00e003fc0f00

def z403 : W := mkw 0x20448001f7f0000f 0x8040890003efe000 0xa6dc0001fff80038 0xed4db80003fff000

def z404 : W := mkw 0x820c48ca182e6620 0x1104189194305ccc 0x861c49ce383e6665 0xa10c38939c707ccc

def z405 : W := mkw 0x08a0116040828542 0x20114022c081050a 0x782071f0c0c787d7 0x12f040e3e1818f0f

def z406 : W := mkw 0x0000000008044000 0x0000000000100880 0x0000000138066068 0x0000000002700cc0

def z407 : W := mkw 0x571a6c8800000020 0x00ae34d910000000 0x861c000000000000 0x010c380000000000

def z408 : W := mkw 0x7fbfffbcb6700079 0x80ff7fff796ce000 0xdffffffe3e380027 0xfdbffffffc7c7000

def z409 : W := mkw 0x17006c0000000000 0x002e00d800000000 0x7f007e01c007805b 0x3efe00fc03800f00

def z410 : W := mkw 0x3df6800153f00007 0x807bed0002a7e000 0x9fff800001f80000 0xfd3fff000003f000

def z411 : W := mkw 0x1de00001e580000e 0x003bc00003cb0000 0x3fe00001ffc00038 0x7c7fc00003ff8000

def z412 : W := mkw 0x5fbb7ffc00028570 0x20bf76fff800050a 0xdffffffe000787c7 0xffbffffffc000f0f

def z413 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffff7f000000002 0x19bfffefe0000000

def z414 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0123863007f87ffa 0x1202470c600ff0ff

def z415 : W := mkw 0x08e1937743daafd7 0x2811c326ee87b55f 0x00e381fe01f80784 0xc001c703fc03f00f

def z416 : W := mkw 0x08a0112040808142 0x2011402240810102 0x78003000c0018000 0x00f0006001800300

def z417 : W := mkw 0x0000000200082a80 0x0800000004001055 0x0000000000007fc0 0x02000000000000ff

def z418 : W := mkw 0x5fbb6e9c00000030 0x00bf76dd38000000 0x9fff8e0e00000000 0xfd3fff1c1c000000

def z419 : W := mkw 0x00000000a4000008 0x0000000001480000 0x20000001fe000038 0x0040000003fc0000

def z420 : W := mkw 0x0ae07d614987d546 0x6015c0fac2930faa 0x78e07ff1c1c7ffdf 0x5ef1c0ffe3838fff

def z421 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e01f80787 0xf402471c7c03f00f

def z422 : W := mkw 0x0001021400000010 0x0000020428000000 0x01038e0e00000000 0xa002071c1c000000

def z423 : W := mkw 0x5fba7da8ac055068 0x40bf74fb51580aa0 0xfedc71c1f8078000 0x09fdb8e383f00f00

def z424 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x47007e003e07f863 0x228e00fc007c0ff0

def z425 : W := mkw 0x3fb2ec00eed5500b 0xc07f65d801ddaaa0 0x7f23fe01fec7f87b 0x3efe47fc03fd8ff0

def z426 : W := mkw 0x08e0000141800006 0x0011c00002830000 0x38c00001c0000000 0x0871800003800000

def z427 : W := mkw 0x0200480008044000 0x0004009000100880 0x0600400138060000 0x080c008002700c00

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000001c0078058 0x0240000003800f00

def z429 : W := mkw 0x08a0112040808142 0x2011402240810102 0x78e071f0c0c18197 0x5ef1c0e3e1818303

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000030000007c7 0x020000006000000f

def z431 : W := mkw 0x0040004141828506 0x200080008283050a 0x20000001c0078000 0x0040000003800f00

def z432 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01038e3e06387fe7 0xa202071c7c0c70ff

def z433 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdedc7ffe00000007 0x09bdb8fffc000000

def z434 : W := mkw 0x5df3377541828556 0x20bbe66eea83050a 0x79e3f7f1c1c787df 0x5ef3c7efe3838f0f

def z435 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86fc49ff39fe67ff 0xff0df893fe73fccf

def z436 : W := mkw 0x3df61161f5a2854e 0xa07bec22c3eb450a 0xfefc71f1f9c787df 0x5ffdf8e3e3f38f0f

def z437 : W := mkw 0x15000000a4000008 0x002a000001480000 0x070000003e000020 0x200e0000007c0000

def z438 : W := mkw 0x3df69121f7f0004f 0x807bed2243efe000 0xfffff1f1fff8003f 0xfdffffe3e3fff000

def z439 : W := mkw 0xd75f6edf192e6634 0x11aebeddbe325ccc 0x87dfcfcf393e666d 0xed0fbf9f9e727ccc

def z440 : W := mkw 0x3744ec01fff5500f 0xc06e89d803ffeaa0 0x7f007e01fffff87b 0x3efe00fc03fffff0

def z441 : W := mkw 0x97086ccaac0f7628 0x512e10d995581eec 0x7f007fcffe07fe7f 0x3efe00ff9ffc0ffc

def z442 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f207e31ffc7ffff 0x7efe40fc63ff8fff

def z443 : W := mkw 0x1db2000000000000 0x003b640000000000 0x9edc000000000000 0x093db80000000000

def z444 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7e007e01f807f843 0x0afc00fc03f00ff0

def z445 : W := mkw 0x5fbbffbc025008f1 0x08bf77ff7804a011 0xdffffffe06c01997 0xffbffffffc0d8033

def z446 : W := mkw 0x0240484109064404 0x0004809082120c88 0x06c049c13906666d 0x6c0d809382720ccc

def z447 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e06c07fd7 0x1202471c7c0d80ff

def z448 : W := mkw 0x0040004141828506 0x200080008283050a 0x20c041c1c1c787dd 0x4e41808383838f0f

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000e0006007820 0x2002001c000c00f0

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000e0000007843 0x0200001c000000f0

def z451 : W := mkw 0x5fbbffbeae5d7af9 0x48bf77ff7d5cbaf5 0xffffffffffffffff 0xffffffffffffffff

def z452 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78c071c1c1c787d8 0x0af180e383838f0f

def z453 : W := mkw 0x0044004111220404 0x0000880082224408 0x86dc41c1393e066d 0xed0db88382727c0c

def z454 : W := mkw 0x5db3373400000050 0x00bb666e68000000 0x59e3f7f000000007 0x5cb3c7efe0000000

def z455 : W := mkw 0x17006c00a4011008 0x402e00d801480220 0x7f007e00c6019813 0x3efe00fc018c0330

def z456 : W := mkw 0x1fe07d61ed87d54e 0x603fc0fac3db0faa 0x7fc07fc1fe07f87b 0x3eff80ff83fc0ff0

def z457 : W := mkw 0x824848cb090e6624 0x1104909196121ccc 0x00c049cf0106664d 0x4c0180939e020ccc

def z458 : W := mkw 0x15000000a4000008 0x002a000001480000 0x3e000001f8000000 0x087c000003f00000

def z459 : W := mkw 0x00000000ac055008 0x4000000001580aa0 0x20000001f8078000 0x0040000003f00f00

def z460 : W := mkw 0x80440043192e6604 0x1100880086325ccc 0x00c041c1393e666d 0x4c01808382727ccc

def z461 : W := mkw 0x3df78217f7f82a9f 0x887bef042feff055 0xbfff8e0ffff87838 0xfd7fff1c1ffff0f0

def z462 : W := mkw 0x3df78215f7f0089f 0x887bef042befe011 0xbfff8631fff819ba 0xff7fff0c63fff033

def z463 : W := mkw 0x20048000b6700009 0x80400900016ce000 0x000000003e380020 0x00000000007c7000

def z464 : W := mkw 0x0201ca160a5c6a91 0x080403942c14b8d5 0x0723ce3f3ffe7fff 0xfe0e479c7e7ffcff

def z465 : W := mkw 0x7db3b734e6d0005b 0x80fb676e69cda000 0x7923b630c6c00012 0x10f2476c618d8000

def z466 : W := mkw 0xdfbb7ffe080e6670 0x11bf76fffc101ccc 0xdffffffe00066647 0xfdbffffffc000ccc

def z467 : W := mkw 0x7ffffffdf7f2857f 0xa0fffffffbefe50a 0xffffffffffff87ff 0xffffffffffffff0f

def z468 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01038e0e07387e6d 0xe402071c1c0e70fc

def z469 : W := mkw 0x0001821402500891 0x080003042804a011 0x01238e3006c079fb 0x3602471c600d80f3

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x86dc000000000000 0xed0db80000000000

def z471 : W := mkw 0xdffe7de919264464 0x11bffcfbd2324c88 0xdedc71c138060000 0x09bdb8e382700c00

def z472 : W := mkw 0x48bb93be02582af1 0x089177277c04b055 0x80ff81fe01f80784 0xc101ff03fc03f00f

def z473 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78c071c1c107864d 0x4cf180e383820f0c

def z474 : W := mkw 0x7fff7fbdf5a0007e 0x80fffeff7beb4000 0xfffffffff8000007 0xfdfffffffff00000

def z475 : W := mkw 0x3716ec00be755009 0xc06e2dd8017ceaa0 0xff1ffe01fe3ff87b 0xbffe3ffc03fc7ff0

def z476 : W := mkw 0x5fbb7fbc08055070 0x40bf76ff78100aa0 0xdffffffe0007f847 0xffbffffffc000ff0

def z477 : W := mkw 0x571b6e9cac055038 0x40ae36dd39580aa0 0x871f8e0e3e007820 0xa10e3f1c1c7c00f0

def z478 : W := mkw 0x08a1133400000050 0x0011422668000000 0x59e3fffe00000007 0xfcb3c7fffc000000

def z479 : W := mkw 0xdfff7fff59aee776 0x31bffefffeb35dce 0xfffffffff9ffe7ff 0xfffffffffff3ffcf

def z480 : W := mkw 0x1701ee14ae555899 0x482e03dc295caab1 0x7f23fe31fec7f9fb 0x3efe47fc63fd8ff3

def z481 : W := mkw 0x0044800113700005 0x000089000226e000 0x87ff80013ff80038 0xfd0fff00027ff000

def z482 : W := mkw 0x1de03561e583954e 0x603bc06ac3cb072a 0x79e077f1c7c79fdf 0x5ef3c0efe38f8f3f

def z483 : W := mkw 0x0000116000028540 0x20000022c000050a 0x402071f001c787df 0x568040e3e0038f0f

def z484 : W := mkw 0x974c6cc9bd27542c 0x512e98d9937a4ea8 0xffdc7fc1fe07f87b 0x3fffb8ff83fc0ff0

def z485 : W := mkw 0x1701ee16ae5d7a99 0x482e03dc2d5cbaf5 0x07238e3e3ff87fff 0xf60e471c7c7ff0ff

def z486 : W := mkw 0x4001373400000050 0x0080026e68000000 0x4000363000000002 0x0080006c60000000

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400100060049 0x0c00008002000c00

def z488 : W := mkw 0x571bee9e02582ab1 0x08ae37dd3c04b055 0x873f8e3e07f87fff 0xf70e7f1c7c0ff0ff

def z489 : W := mkw 0x5db3b734025008d1 0x08bb676e6804a011 0x5923b63006c01992 0x12b2476c600d8033

def z490 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007601fe079812 0x1afe00ec03fc0f30

def z491 : W := mkw 0x08e1137541828556 0x2011c226ea83050a 0x79e3ffffc1c787df 0xfef3c7ffff838f0f

def z492 : W := mkw 0x1da03520e481914a 0x603b406a41c90322 0x79203630c6c19992 0x12f2406c618d8333

def z493 : W := mkw 0x1700ec02ae5d7a89 0x482e01d8055cbaf5 0x7f007e01fffffffb 0x3efe00fc03ffffff

def z494 : W := mkw 0x08a0112000000040 0x0011402240000000 0x5820303000000002 0x10b0406060000000

def z495 : W := mkw 0x42097fbc00000070 0x008412ff78000000 0xc6dc7ffe00000007 0xed8db8fffc000000

def z496 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e031f0c1c18796 0x52f1c063e183830f

def z497 : W := mkw 0xa8fe80cb53fa2627 0x9151fd0196a7f44c 0x80ff81ce01f80604 0xc101ff039c03f00c

def z498 : W := mkw 0x00000000ac055008 0x4000000001580aa0 0x78007001fe07f87b 0x1ef000e003fc0ff0

def z499 : W := mkw 0x3db68000f6f0000b 0x807b6d0001ede000 0xbf3f8000fef80030 0xb17e7f0001fdf000

def z500 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x07004e013e067869 0x2c0e009c027c0cf0

def z501 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78c071f1c00787c7 0x0af180e3e3800f0f

def z502 : W := mkw 0x3df60001f5a0000e 0x807bec0003eb4000 0xbedc0001f9380028 0xed7db80003f27000

def z503 : W := mkw 0x1db20000a4000008 0x003b640001480000 0xbfff8001fe000038 0xfd7fff0003fc0000

def z504 : W := mkw 0x5ffb7fbd41800076 0x00bff6ff7a830000 0xffffffffc1c0001f 0xfdffffffff838000

def z505 : W := mkw 0x3ff6ec01f7f0000f 0x807fedd803efe000 0xfffffe01fff8003b 0xfdfffffc03fff000

def z506 : W := mkw 0x5fbb7fbc08044070 0x00bf76ff78100880 0xdfffffff3806606f 0xfdbffffffe700cc0

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020003000c00192 0x1200400060018003

def z508 : W := mkw 0x0044000311282204 0x0000880006225044 0x86dc080f3938666d 0xed0db8101e7270cc

def z509 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e06f879b2 0xb202471c7c0df0f3

def z510 : W := mkw 0x3ff6ec01fff5500f 0xc07fedd803ffeaa0 0xbfff8e01fff87838 0xfd7fff1c03fff0f0

def z511 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x79e07ff1c7c7ffff 0x7ef3c0ffe38f8fff

def z512 : W := mkw 0x820dca9e1a7c6ab1 0x19041b953c34f8d5 0x873f8e3e3ff87fff 0xf70e7f1c7c7ff0ff

def z513 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01f8078003 0x3cfe00fc03f00f00

def z514 : W := mkw 0x0200480008044000 0x0004009000100880 0x07004e013e06787b 0x3e0e009c027c0cf0

def z515 : W := mkw 0x42097fbc08055070 0x408412ff78100aa0 0x40007ffe0007f847 0x028000fffc000ff0

def z516 : W := mkw 0x17006c0000000000 0x002e00d800000000 0x07000e0000000000 0x200e001c00000000

def z517 : W := mkw 0x08e0000141800006 0x0011c00002830000 0x78e07001c1c7805b 0x5ef1c0e003838f00

def z518 : W := mkw 0x3db2a400e6d1100b 0xc07b654801cda220 0x7923b600c6c19812 0x12f2476c018d8330

def z519 : W := mkw 0x0000240000011000 0x4000004800000220 0x4000360000019802 0x0280006c00000330

def z520 : W := mkw 0x80440043bd2f760c 0x51008800877a5eec 0x20000001ff3ffe78 0x0240000003fe7ffc

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x78207031c1c787df 0x5ef040e063838f0f

def z522 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0023803e01f807df 0xd60047007c03f00f

def z523 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0123803e07f807bc 0xf40247007c0ff00f

def z524 : W := mkw 0x8aec59e959a6c566 0x3115d8b3d2b34d8a 0xfefc71f1f9c787df 0x5ffdf8e3e3f38f0f

def z525 : W := mkw 0x0208488800000020 0x0004109110000000 0x000049ce00000005 0x000000939c000000

def z526 : W := mkw 0x7df7b735f7f0005f 0x80fbef6e6befe000 0xffffb631fff8003a 0xfdffff6c63fff000

def z527 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x07000e003e00787b 0x360e001c007c00f0

def z528 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001380028 0xe400000000027000

def z529 : W := mkw 0x0000800202582a81 0x080001000404b055 0x0123800007f87ff8 0xf6024700000ff0ff

def z530 : W := mkw 0x5fbbffbe02582af1 0x08bf77ff7c04b055 0xdffffffe06387827 0xfdbffffffc0c70f0

def z531 : W := mkw 0x804d82df137a2eb5 0x19009b05be26f45d 0x80ff81fe01f80784 0xc101ff03fc03f00f

def z532 : W := mkw 0x1500240000000000 0x002a004800000000 0x5900360000000002 0x10b2006c00000000

def z533 : W := mkw 0x20008000e6d0000b 0x8040010001cda000 0x20000000c6c00010 0x00400000018d8000

def z534 : W := mkw 0x17004800ac044008 0x002e009001580880 0x3f004801fe066079 0x3c7e009003fc0cc0

def z535 : W := mkw 0x8aec59eb59aee766 0x3115d8b3d6b35dce 0xfedc79cff93fe66d 0xedfdb8f39ff27fcc

def z536 : W := mkw 0x08e1937543d28dd7 0x2811c326ea87a51b 0x79e3f7f1c7c79fdf 0x5ef3c7efe38f8f3f

def z537 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x80dc41cf013e064d 0xcd01b8839e027c0c

def z538 : W := mkw 0x15000000ac055008 0x402a000001580aa0 0x3f000001fe07f878 0x3e7e000003fc0ff0

def z539 : W := mkw 0x5fba7da800000060 0x00bf74fb50000000 0xdffff1c000000000 0xfdbfffe380000000

def z540 : W := mkw 0x3df78215f7f0001f 0x807bef042befe000 0xbfff8e3ffff8003f 0xfd7fff1c7ffff000

def z541 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e0e07f87838 0xf402471c1c0ff0f0

def z542 : W := mkw 0x48bb93be02582af1 0x089177277c04b055 0x81ff8ffe07f87fff 0xf703ff1ffc0ff0ff

def z543 : W := mkw 0x3ffec889f7f0002f 0x807ffd9113efe000 0xbfffc9cffff8003d 0xfd7fff939ffff000

def z544 : W := mkw 0x08e0116101020444 0x0011c022c2020408 0x58e071f10106064f 0x5cb1c0e3e2020c0c

def z545 : W := mkw 0x824cc8cb1b7e6625 0x110499919636fccc 0x87ffc9cf3ffe667d 0xfd0fff939e7ffccc

def z546 : W := mkw 0x5db2352000000040 0x00bb646a40000000 0x5800300000000000 0x00b0006000000000

def z547 : W := mkw 0x1fe06c01ed85500e 0x403fc0d803db0aa0 0x7fe07e01ffc7f87b 0x7effc0fc03ff8ff0

def z548 : W := mkw 0xb71ec88abe7c6229 0x916e3d91157cf8c4 0x871f880e3e386020 0xa10e3f101c7c70c0

def z549 : W := mkw 0x5fbbffbe02582af1 0x08bf77ff7c04b055 0xdffffffe01f80787 0xfdbffffffc03f00f

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c041c000000005 0x4c01808380000000

def z551 : W := mkw 0x0000800202582a81 0x080001000404b055 0x0020003007f87fff 0x56004000600ff0ff

def z552 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe0600787f 0xffbffffffc0c00f0

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000006007878 0x02000000000c00f0

def z554 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xdffffffe3e007827 0xfdbffffffc7c00f0

def z555 : W := mkw 0x0001821402500011 0x000003042804a000 0x01238e3e07f8003f 0xf402471c7c0ff000

def z556 : W := mkw 0x0001021600082a90 0x080002042c001055 0x01238e3e00007fc7 0xf602471c7c0000ff

def z557 : W := mkw 0x08e0112141808146 0x2011c02242830102 0x78e03031c1c1819a 0x5ef1c06063838303

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000080e00000005 0xe40000101c000000

def z559 : W := mkw 0x5fba7da800000060 0x00bf74fb50000000 0xdedc79ce00000005 0xedbdb8f39c000000

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100060006001812 0x1202000c000c0030

def z561 : W := mkw 0x0040000141800006 0x0000800002830000 0x20000001c1c00018 0x0040000003838000

def z562 : W := mkw 0x0000800002500001 0x000001000004a000 0x01238e0007f8787b 0xf602471c000ff0f0

def z563 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071c1c1c78018 0x5cf1c0e383838f00

def z564 : W := mkw 0x800c008a10282220 0x1100180114205044 0x801c000e00380000 0x810038001c007000

def z565 : W := mkw 0x17007d60ac07d548 0x602e00fac1580faa 0x7f007ff1fe07ffff 0x3efe00ffe3fc0fff

def z566 : W := mkw 0x15002400a4011008 0x402a004801480220 0x78003000c0018000 0x00f0006001800300

def z567 : W := mkw 0x1db3821602582a91 0x083b67042c04b055 0x9fff8e3e07f87fff 0xff3fff1c7c0ff0ff

def z568 : W := mkw 0x0001021600082a90 0x080002042c001055 0x0000003e00000784 0x000000007c00000f

def z569 : W := mkw 0x5fbb7fbe00082af0 0x08bf76ff7c001055 0xdffffffe00007fc7 0xffbffffffc0000ff

def z570 : W := mkw 0x820dca9e1a7c6ab1 0x19041b953c34f8d5 0x871f8e0e3e387820 0xa10e3f1c1c7c70f0

def z571 : W := mkw 0x5ffb7ffd01020474 0x00bff6fffa020408 0xdfffffff0106064f 0xfdbffffffe020c0c

def z572 : W := mkw 0x57097fbc00000070 0x00ae12ff78000000 0x5f007ffe00000007 0x3cbe00fffc000000

def z573 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0023883e01f867ed 0xe40047107c03f0cf

def z574 : W := mkw 0x0001021600082a90 0x080002042c001055 0x01000e3e06007fff 0x3602001c7c0c00ff

def z575 : W := mkw 0x0000800002500001 0x000001000004a000 0x0000000007f80038 0x00000000000ff000

def z576 : W := mkw 0x20448003f7f82a8f 0x8840890007eff055 0x20000001fff87ff8 0x0240000003fff0ff

def z577 : W := mkw 0x15440001b520000c 0x002a8800036a4000 0xbfdc0001ff380038 0xfd7fb80003fe7000

def z578 : W := mkw 0x02006c0008055000 0x400400d800100aa0 0x46007e013807f86b 0x2e8c00fc02700ff0

def z579 : W := mkw 0x17006c0000000000 0x002e00d800000000 0x5e00700000000000 0x08bc00e000000000

def z580 : W := mkw 0x08a0000040800002 0x0011400000810000 0x38200000c0c00010 0x1070400001818000

def z581 : W := mkw 0x5dbb13bc00000070 0x00bb762778000000 0x9fff81fe00000004 0xfd3fff03fc000000

def z582 : W := mkw 0x0000116000028540 0x20000022c000050a 0x780071f1c00787df 0x1ef000e3e3800f0f

def z583 : W := mkw 0xfffffffffffe667f 0x91fffffffffffccc 0xfffffffffffe667f 0xfdfffffffffffccc

def z584 : W := mkw 0x3df68003f7f8220f 0x807bed0007eff044 0xbfff880ffff8667d 0xfd7fff101ffff0cc

def z585 : W := mkw 0x20448001fff5500f 0xc040890003ffeaa0 0x20000001fffff878 0x0240000003fffff0

def z586 : W := mkw 0xdfff7ffd19264474 0x11bffefffa324c88 0xdfffffff38060007 0xfdbffffffe700c00

def z587 : W := mkw 0x0001021600082a90 0x080002042c001055 0x00000e0e00007800 0x0000001c1c0000f0

def z588 : W := mkw 0x1fa07d20ec85d14a 0x603f40fa41d90ba2 0x7f207e31fec7f9fb 0x3efe40fc63fd8ff3

def z589 : W := mkw 0x0044000111200004 0x0000880002224000 0x80dc000001380000 0xc101b80000027000

def z590 : W := mkw 0x0001021400000010 0x0000020428000000 0x01238e3e0600787f 0xf602471c7c0c00f0

def z591 : W := mkw 0x0ae059614986c546 0x2015c0b2c2930d8a 0x7ee079f1f9c7e7ff 0x7efdc0f3e3f38fcf

def z592 : W := mkw 0x824c48c919264424 0x1104989192324c88 0x86dc41c13906064d 0x4d0db88382720c0c

def z593 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x00e041f101c607cd 0x4c01c083e2038c0f

def z594 : W := mkw 0x00400043010a2604 0x000080008602144c 0x00c049cf013e666d 0xec0180939e027ccc

def z595 : W := mkw 0x0000000040808102 0x2000000000810102 0x20000000c0c18190 0x0240000001818303

def z596 : W := mkw 0xbdfe80cbf7fa262f 0x917bfd0197eff44c 0xbfff81cffff8063c 0xfd7fff039ffff00c

def z597 : W := mkw 0x08e0004141828506 0x2011c0008283050a 0x38e00001c1c787d8 0x5e71c00003838f0f

def z598 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c0c78192 0x1af1c0e3e3818f03

def z599 : W := mkw 0xbffec8c9fff6442f 0x917ffd9193ffec88 0xbfffc1c1fffe0038 0xfd7fff8383fffc00

def z600 : W := mkw 0x08e0916143d28547 0x2011c122c287a50a 0x79e3f1f1c7ff87ff 0xfef3c7e3e38fff0f

def z601 : W := mkw 0xdfff7fff112a2674 0x11bffefffe22544c 0xdffffffe01380607 0xfdbffffffc02700c

def z602 : W := mkw 0x17006c00a4000008 0x002e00d801480000 0x7f007e01fe00003b 0x3cfe00fc03fc0000

def z603 : W := mkw 0x0001021400000010 0x0000020428000000 0x00000e3e00000007 0x0000001c7c000000

def z604 : W := mkw 0x5fba7da8ac055068 0x40bf74fb51580aa0 0xffdc7fc1fe07f87b 0x3fffb8ff83fc0ff0

def z605 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01038e0e07f87ff8 0xa202071c1c0ff0ff

def z606 : W := mkw 0x5fbbffbc02500071 0x00bf77ff7804a000 0xdffffffe07f8003f 0xfdbffffffc0ff000

def z607 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0xd8fff1fe00000007 0xddb1ffe3fc000000

def z608 : W := mkw 0x0200480000000000 0x0004009000000000 0x0600480000000001 0x2c0c009000000000

def z609 : W := mkw 0x15002400a4011008 0x402a004801480220 0x79007601c607985b 0x1ef200ec038c0f30

def z610 : W := mkw 0x15018216a6582a99 0x082a03042d4cb055 0x3f238e3ffff87fff 0xfe7e471c7ffff0ff

def z611 : W := mkw 0x771fee9cb6700039 0x80ee3fdd396ce000 0x871f8e0e3e380020 0xa10e3f1c1c7c7000

def z612 : W := mkw 0x68ff93bd53f00077 0x80d1ff277aa7e000 0x80ff81fe01f80004 0xc101ff03fc03f000

def z613 : W := mkw 0x15002400a4011008 0x402a004801480220 0x7f003601fe01983a 0x3efe006c03fc0330

def z614 : W := mkw 0x0001821402500891 0x080003042804a011 0x01238e3e06c01997 0xf602471c7c0d8033

def z615 : W := mkw 0x1fe1ff77efdfffdf 0x683fc3feefdfbfff 0x7fe3ffffffffffff 0xfeffc7ffffffffff

def z616 : W := mkw 0x820c488818244020 0x1104189110304880 0x861c000038000000 0x010c380000700000

def z617 : W := mkw 0x1501a614a6511899 0x482a034c294ca231 0x7923b630c6c19992 0x12f2476c618d8333

def z618 : W := mkw 0xdffe7deb192e6664 0x11bffcfbd6325ccc 0xdedc79cf393e666d 0xedbdb8f39e727ccc

def z619 : W := mkw 0x08a1933642d8abd3 0x281143266c85b157 0x7923be3ec7f9ffff 0xf6f2477c7d8ff3ff

def z620 : W := mkw 0x0000116000028540 0x20000022c000050a 0x400071c000078000 0x008000e380000f00

def z621 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c0078007 0x5cf1c0e3e3800f00

def z622 : W := mkw 0x00000000ac055008 0x4000000001580aa0 0x21000e01fe07f87b 0x3642001c03fc0ff0

def z623 : W := mkw 0x0000000200082200 0x0000000004001044 0x0020083e01f867ff 0xf60040107c03f0cf

def z624 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x861c080e3938666d 0xe50c38101c7270cc

def z625 : W := mkw 0x35178216b6782a99 0x886a2f042d6cf055 0x871f8e0e3e387820 0xa10e3f1c1c7c70f0

def z626 : W := mkw 0x0041825743daaf97 0x28008304ae87b55f 0x21238e3fc7ffffff 0xf642471c7f8fffff

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000100064d 0x440000000002000c

def z628 : W := mkw 0x1701ee16ae5d7a99 0x482e03dc2d5cbaf5 0x7f03fe0ffe3ff87b 0xbefe07fc1ffc7ff0

def z629 : W := mkw 0x5db3b73602582ad1 0x08bb676e6c04b055 0x5923be3e07f87fff 0xf6b2477c7c0ff0ff

def z630 : W := mkw 0x08a1933442d089d3 0x281143266885a113 0x7923b630c6c19992 0x12f2476c618d8333

def z631 : W := mkw 0x15008000a6500009 0x002a0100014ca000 0x3f238001fff80038 0xfc7e470003fff000

def z632 : W := mkw 0xbffe48cbfdae662e 0x917ffc9197fb5ccc 0xbedc49cff93e666d 0xed7db8939ff27ccc

def z633 : W := mkw 0x17016e14ac055018 0x402e02dc29580aa0 0x7f23fe3ffe07f87f 0xfefe47fc7ffc0ff0

def z634 : W := mkw 0x0000800002500881 0x080001000004a011 0x0000000006c01990 0x02000000000d8033

def z635 : W := mkw 0x02006c0000000000 0x000400d800000000 0x40007e0000000003 0x008000fc00000000

def z636 : W := mkw 0x28f6916153f28547 0xa051ed22c2a7e50a 0xf8fff1f1c1ff87df 0xdff1ffe3e383ff0f

def z637 : W := mkw 0x08e0004141820406 0x0011c00082830408 0x38e041c1c1c6065d 0x5c71c08383838c0c

def z638 : W := mkw 0x3db20000e480000a 0x807b640001c90000 0x38000000c0000000 0x0070000001800000

def z639 : W := mkw 0x4aa97fbc00000070 0x009552ff78000000 0x58e07ffe00000007 0x5cb1c0fffc000000

def z640 : W := mkw 0x820848ca080e6620 0x1104109194101ccc 0x86dc49ce00066645 0xed0db8939c000ccc

def z641 : W := mkw 0x80040002182c6200 0x11000800043058c4 0x0000000038386020 0x00000000007070c0

def z642 : W := mkw 0x3db28000e6d0000b 0x807b650001cda000 0x3f238001fec00038 0x3c7e470003fd8000

def z643 : W := mkw 0x0040116141828546 0x20008022c283050a 0x600071f1c1c787df 0x02c000e3e3838f0f

def z644 : W := mkw 0x824d4adf192e6eb4 0x19049a95be325cdd 0x86dc4fff393e7fef 0xef0db89ffe727cff

def z645 : W := mkw 0xbffe48c9fda6442e 0x917ffc9193fb4c88 0xbedc41c1f8060000 0x097db88383f00c00

def z646 : W := mkw 0x17006c02ac0d7208 0x402e00d805581ae4 0x7f007e0fff3ffe7f 0xfefe00fc1ffe7ffc

def z647 : W := mkw 0x42087da800000060 0x008410fb50000000 0x400071c000000000 0x008000e380000000

def z648 : W := mkw 0x3716ec00be755009 0xc06e2dd8017ceaa0 0x871f8e003e387820 0xa10e3f1c007c70f0

def z649 : W := mkw 0x3ff6ec01fff5500f 0xc07fedd803ffeaa0 0xfffff001ffff8038 0xfdffffe003ffff00

def z650 : W := mkw 0x8ae859eb498ee766 0x3115d0b3d6931dce 0x78e079ffc1c7e7df 0x5ef1c0f3ff838fcf

def z651 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x00c001c000000000 0x0001800380000000

def z652 : W := mkw 0x824cc8cb1b7e6ea5 0x190499919636fcdd 0x86dc49cf3ffe7ffd 0xef0db8939e7ffcff

def z653 : W := mkw 0xdfbf7fbe182c6270 0x11bf7eff7c3058c4 0xdffffffe38386027 0xfdbffffffc7070c0

def z654 : W := mkw 0x02006c0008055000 0x400400d800100aa0 0x4000700000078000 0x008000e000000f00

def z655 : W := mkw 0x3df68003f7f82a8f 0x887bed0007eff055 0xbfff8001fff87ff8 0xff7fff0003fff0ff

def z656 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fec00010 0x197fff0003fd8000

def z657 : W := mkw 0x57097fbcac055078 0x40ae12ff79580aa0 0x7f007ffffe07f87f 0x3efe00fffffc0ff0

def z658 : W := mkw 0x0000000200082200 0x0000000004001044 0x0000000e01380604 0xc00000001c02700c

def z659 : W := mkw 0x804c00cb192e6624 0x1100980196325ccc 0x80dc01cf393e666c 0xc101b8039e727ccc

def z660 : W := mkw 0x8209cade0a5e6eb1 0x19041395bc14bcdd 0x0123cffe07fe7fff 0xf602479ffc0ffcff

def z661 : W := mkw 0x0000000200082200 0x0000000004001044 0x01000e0e07387e7f 0xf602001c1c0e70fc

def z662 : W := mkw 0xd71f6e9e182c6230 0x11ae3edd3c3058c4 0x871f8e0e38386020 0xa10e3f1c1c7070c0

def z663 : W := mkw 0x0040004101020404 0x0000800082020408 0x00c001c001000604 0x400180038002000c

def z664 : W := mkw 0x17016e1400000010 0x002e02dc28000000 0x5f23fe3e00000007 0xfcbe47fc7c000000

def z665 : W := mkw 0x28b2800042d00003 0x805165000085a000 0x0023800000c00000 0x0000470000018000

def z666 : W := mkw 0x82086cca080f7620 0x510410d994101eec 0x40007fce0007fe47 0x028000ff9c000ffc

def z667 : W := mkw 0x0001821402500891 0x080003042804a011 0x0123863007c01fdf 0x5602470c600f803f

def z668 : W := mkw 0x824c48cbbd2f762c 0x51049891977a5eec 0xa6dc49cfff3ffe7d 0xef4db8939ffe7ffc

def z669 : W := mkw 0x3df60001f5a0000e 0x807bec0003eb4000 0xbfdc0001fe000038 0x3d7fb80003fc0000

def z670 : W := mkw 0x5fba7da800000060 0x00bf74fb50000000 0xdefc71f000000007 0x5dbdf8e3e0000000

def z671 : W := mkw 0x0044000111200004 0x0000880002224000 0x86dc000138000000 0x090db80002700000

def z672 : W := mkw 0x571b7fbc00000070 0x00ae36ff78000000 0xc71ffffe00000007 0xa18e3ffffc000000

def z673 : W := mkw 0x5ffbffff43daaff7 0x28bff7fffe87b55f 0xffffffffc7ffffff 0xffffffffff8fffff

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x78003000c0018012 0x12f0006001800300

def z675 : W := mkw 0x974c6ccbbd2f762c 0x512e98d9977a5eec 0xfedc79cff93fe66d 0xedfdb8f39ff27fcc

def z676 : W := mkw 0x1db2800002500001 0x003b65000004a000 0x9fff800007f80038 0xfd3fff00000ff000

def z677 : W := mkw 0x3db38214e6d0089b 0x887b670429cda011 0x39238630c6c01992 0x1272470c618d8033

def z678 : W := mkw 0x48fb13fd41828576 0x2091f627fa83050a 0x80ff81fe01c00784 0xc101ff03fc03800f

def z679 : W := mkw 0x1db3021400000010 0x003b660428000000 0x9fff8e3e00000007 0xfd3fff1c7c000000

def z680 : W := mkw 0x0000004000020400 0x0000000080000408 0x000041c000060645 0x0000008380000c0c

def z681 : W := mkw 0x800800ca000a2620 0x110010019400144c 0x000001ce00000604 0x000000039c00000c

def z682 : W := mkw 0x3df60001f5a0000e 0x807bec0003eb4000 0xbefc0001f9c00018 0x5d7df80003f38000

def z683 : W := mkw 0x824d4adf192e6634 0x11049a95be325ccc 0x87ffcfff393e666f 0xfd0fff9ffe727ccc

def z684 : W := mkw 0x08e1937743daafd7 0x2811c326ee87b55f 0x01e38ffe07f87fff 0xf603c71ffc0ff0ff

def z685 : W := mkw 0x824c488b192c6224 0x11049891163258c4 0x86dc080f39386028 0xed0db8101e7270c0

def z686 : W := mkw 0x974c6cc9bd27542c 0x512e98d9937a4ea8 0xfedc71c1f8078000 0x09fdb8e383f00f00

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020000001c00018 0x5400400000038000

def z688 : W := mkw 0x20440001f5a0000e 0x8040880003eb4000 0x20000001f8000000 0x0040000003f00000

def z689 : W := mkw 0x08e4000151a00006 0x0011c80002a34000 0xbefc0001f9f80038 0xfd7df80003f3f000

def z690 : W := mkw 0x7fbbffbce6d0007b 0x80ff77ff79cda000 0xfffffffec6c00017 0xfdfffffffd8d8000

def z691 : W := mkw 0x02004800ac055008 0x4004009001580aa0 0x26004801fe07f879 0x2e4c009003fc0ff0

def z692 : W := mkw 0x1701ee1602582a91 0x082e03dc2c04b055 0x5f23fe3e07f87fff 0xfebe47fc7c0ff0ff

def z693 : W := mkw 0x804d82df137a2eb5 0x19009b05be26f45d 0x81ff8ffe07f87fff 0xf703ff1ffc0ff0ff

def z694 : W := mkw 0x824c59eb192ee764 0x310498b3d6325dce 0xc6dc79ff393fe7ef 0xef8db8f3fe727fcf

def z695 : W := mkw 0x15002400a4011008 0x402a004801480220 0x0100060006001800 0x0002000c000c0030

def z696 : W := mkw 0x28f6000151a00006 0x8051ec0002a34000 0x80dc000000000000 0x0101b80000000000

def z697 : W := mkw 0x28f7821753f82a97 0x8851ef042ea7f055 0x80ff803e01f80784 0xc101ff007c03f00f

def z698 : W := mkw 0x824c48c919264424 0x1104989192324c88 0x86dc49cf38060005 0xed0db8939e700c00

def z699 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x20e001f1c1c787dc 0x4241c003e3838f0f

def z700 : W := mkw 0x08a0112040808142 0x2011402240810102 0x78207031c0c781db 0x1ef040e063818f03

def z701 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x861c480f383e6069 0xad0c38901e707cc0

def z702 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0123863e07f81f96 0xd202470c7c0ff03f

def z703 : W := mkw 0x1501a616a6593a99 0x482a034c2d4cb275 0x7923be3ec7f9ffff 0xf6f2477c7d8ff3ff

def z704 : W := mkw 0x28e49161f7f2854f 0xa051c922c3efe50a 0x78e071f1ffff87ff 0x5ef1c0e3e3ffff0f

def z705 : W := mkw 0x0045821713782a95 0x08008b042e26f055 0x87ff8e3f3ff87fff 0xff0fff1c7e7ff0ff

def z706 : W := mkw 0x3df29161e7d2854f 0xa07be522c3cfa50a 0x79e3f1f1c7c787df 0x5ef3c7e3e38f8f0f

def z707 : W := mkw 0x08a0112000000040 0x0011402240000000 0x78e071f1c1c787df 0x5ef1c0e3e3838f0f

def z708 : W := mkw 0x48bb13bcac055078 0x4091762779580aa0 0xa0ff81fffe07f87c 0xc341ff03fffc0ff0

def z709 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0x87dfcfce00000000 0xa90fbf9f9c000000

def z710 : W := mkw 0x824c48c919264424 0x1104989192324c88 0x86dc49cf393e002d 0xed0db8939e727c00

def z711 : W := mkw 0x17086c88ac055028 0x402e10d911580aa0 0xff1c7e0ffe07f87b 0xbffe38fc1ffc0ff0

def z712 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0x86ff800039f80020 0xe10dff000073f000

def z713 : W := mkw 0x08f2116141828546 0x2011e422c283050a 0xf8fff1f1c1c787df 0xdff1ffe3e3838f0f

def z714 : W := mkw 0x624dffbdf7f0007f 0x80c49bff7befe000 0x60007ffffff8003f 0x00c000fffffff000

def z715 : W := mkw 0x3df68041f7f2850f 0xa07bed0083efe50a 0xbfff8001ffff8038 0xfd7fff0003ffff00

def z716 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xc6dc79cf393fe66f 0xef8db8f39e727fcc

def z717 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf383e6069 0xad0db8939e707cc0

def z718 : W := mkw 0x3df68041f7f2040f 0x807bed0083efe408 0xbfffc1c1fffe0038 0xfd7fff8383fffc00

def z719 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffffff1ffffffff 0xffffffffe3ffffff

def z720 : W := mkw 0x3df68041f7f2040f 0x807bed0083efe408 0xbfff8001fffe0678 0xfd7fff0003fffc0c

def z721 : W := mkw 0x824dcadd1b764cb5 0x19049b95ba36ec99 0x87ffc7f13ec61992 0x1b0fff8fe27d8c33

def z722 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7fc07fc1fe07f87f 0x7eff80ff83fc0ff0

def z723 : W := mkw 0x954c24cbb52b362c 0x512a9849976a566c 0xf9dc37cec7399e16 0xd3f3b86f9d8e733c

def z724 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xffdfffcffe07f820 0xa9ffbfff9ffc0ff0

def z725 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c787da 0x1af1c0e3e3838f0f

def z726 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xfffff001fff8003b 0xfdffffe003fff000

def z727 : W := mkw 0x0208488a080c6220 0x00041091141018c4 0x86dc49cf393e666d 0xed0db8939e727ccc

def z728 : W := mkw 0xc2096e9e080c6230 0x118412dd3c1018c4 0x00000e0e00006000 0x0000001c1c0000c0

def z729 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf3f3e7e7d 0xef0db8939e7e7cfc

def z730 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfffffff3800002f 0xfdbffffffe700000

def z731 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffffe079817 0xfffffffffffc0f30

def z732 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc41cf393e064d 0xcd0db8839e727c0c

def z733 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfffc001fffe0079 0xfd7fff8003fffc00

def z734 : W := mkw 0x0aba488800000020 0x0015749110000000 0x86ffc9ce00000005 0xed0dff939c000000

def z735 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xbfff81c1fff80038 0xfd7fff0383fff000

def z736 : W := mkw 0x7db3b734e6d008db 0x88fb676e69cda011 0x7923b630c6c01992 0x12f2476c618d8033

def z737 : W := mkw 0x28f6916153f28547 0xa051ed22c2a7e50a 0x86ffc1f139fe07ed 0xed0dff83e273fc0f

def z738 : W := mkw 0x28f68001f7f0000f 0x8051ed0003efe000 0xa6ff8001fff80038 0xed4dff0003fff000

def z739 : W := mkw 0x7db3b734e6d1105b 0xc0fb676e69cda220 0x7923b630c6c19812 0x12f2476c618d8330

def z740 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86fc49ff39fe67ed 0xed0df893fe73fccf

def z741 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x86dc01ce39380624 0xe10db8039c72700c

def z742 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01e3cffe07f87fff 0xfe03c79ffc0ff0ff

def z743 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f8e003e38787b 0xb70e3f1c007c70f0

def z744 : W := mkw 0x00440043112a2604 0x000088008622544c 0x86dc49cf393e666d 0xed0db8939e727ccc

def z745 : W := mkw 0x5fbb7fbca4000078 0x00bf76ff79480000 0xfffffffffe07807f 0xfffffffffffc0f00

def z746 : W := mkw 0x804480431b7e6e85 0x190089008636fcdd 0x0000000139fe67e8 0x000000000273fccf

def z747 : W := mkw 0x824c48cb59ae6626 0x1104989196b35ccc 0xa6dc49cff9fe667d 0xed4db8939ff3fccc

def z748 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c78787 0x5cf1c0e3e3838f0f

def z749 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8601fff8183a 0xff7fff0c03fff030

def z750 : W := mkw 0x48bb13bc40808172 0x2091762778810102 0x80ff81fe00c00184 0xc101ff03fc018003

def z751 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x79e07ff1c1c787df 0x7ef3c0ffe3838f0f

def z752 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7e007e01fe07f87b 0x0afc00fc03fc0ff0

def z753 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ffc1fe00000005 0xcd01ff83fc000000

def z754 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe000007c7 0xffbffffffc00000f

def z755 : W := mkw 0x020c488810200020 0x0004189110204000 0x86dc49ce38380025 0xed0db8939c707000

def z756 : W := mkw 0x3db68000b6700009 0x807b6d00016ce000 0x87ff80003e380020 0xe10fff00007c7000

def z757 : W := mkw 0x35169160b6728549 0xa06a2d22c16ce50a 0xc71ff1f03e3f87e7 0xa38e3fe3e07c7f0f

def z758 : W := mkw 0x4abb5bbc08044070 0x009576b778100880 0x86ffc9ff3806606d 0xed0dff93fe700cc0

def z759 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0x86ff800139f80000 0xc90dff000273f000

def z760 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fd7 0xd202471c7c0ff0ff

def z761 : W := mkw 0x2af6ec015bf55007 0xc055edd802b7eaa0 0xc0fffe0001fff843 0xc381fffc0003fff0

def z762 : W := mkw 0xc2097ffe080f7670 0x518412fffc101eec 0x40007ffe0007fe47 0x028000fffc000ffc

def z763 : W := mkw 0x571bee9eae5d7ab9 0x48ae37dd3d5cbaf5 0x871f8e0e3e387820 0xa10e3f1c1c7c70f0

def z764 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x39238e3fc7f87fff 0xfe72471c7f8ff0ff

def z765 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x0123ce3f07fe7fff 0xfe02479c7e0ffcff

def z766 : W := mkw 0x80448043137a2e85 0x190089008626f45d 0x0000000007f87ff8 0x02000000000ff0ff

def z767 : W := mkw 0xa0448043fffe6e8f 0x9940890087fffcdd 0x20000001fffe7ff8 0x0240000003fffcff

def z768 : W := mkw 0x3db68000f6f0000b 0x807b6d0001ede000 0xbf3f8001fef80038 0xbd7e7f0003fdf000

def z769 : W := mkw 0x3df6b561f7f3954f 0xe07bed6ac3efe72a 0xfffff7f1ffff9fff 0xffffffefe3ffff3f

def z770 : W := mkw 0x4abb7fbc08055070 0x409576ff78100aa0 0xc0fffffe0007f847 0xc381fffffc000ff0

def z771 : W := mkw 0xa0448043ffff760f 0xd140890087fffeec 0x20000001fffffe78 0x0240000003fffffc

def z772 : W := mkw 0x1fbb4a9c00000030 0x003f769538000000 0x9fffcffe00000007 0xfd3fff9ffc000000

def z773 : W := mkw 0x02094a9c00000030 0x0004129538000000 0x87dfcfce00000005 0xed0fbf9f9c000000

def z774 : W := mkw 0x02094a9c00000030 0x0004129538000000 0x86ffc9fe00000005 0xed0dff93fc000000

def z775 : W := mkw 0x20448001f7f0000f 0x8040890003efe000 0xa7ff8001fff80038 0xfd4fff0003fff000

def z776 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49ce393e6665 0xe10db8939c727ccc

def z777 : W := mkw 0x7db3b734e6d0815b 0xa0fb676e69cda102 0x7923b630c6c18192 0x12f2476c618d8303

def z778 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x4123fe3e07ffffff 0xf68247fc7c0fffff

def z779 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87ffa 0xb202471c7c0ff0ff

def z780 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfdffffe00000007 0xa9bfbffffc000000

def z781 : W := mkw 0x35568041f7f2850f 0xa06aad0083efe50a 0xa71f8001ffff87f8 0xa34e3f0003ffff0f

def z782 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x782071f1c1c787df 0x12f040e3e3838f0f

def z783 : W := mkw 0xddf73777192e6654 0x11bbee6eee325ccc 0x5923b631393e666a 0x10b2476c62727ccc

def z784 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xffdff1c1fe3f8020 0xa9ffbfe383fc7f00

def z785 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe07c07fff 0xffbffffffc0f80ff

def z786 : W := mkw 0x824c48cb192e6ea4 0x1904989196325cdd 0x86dc49cf393e7fed 0xef0db8939e727cff

def z787 : W := mkw 0x4abb5bbc00000070 0x009576b778000000 0x86ff89fe00000004 0xe10dff13fc000000

def z788 : W := mkw 0x824c48cb59aee726 0x3104989196b35dce 0xa6dc49cff93fe66d 0xed4db8939ff27fcc

def z789 : W := mkw 0x80448043137a2e85 0x190089008626f45d 0x0000000001f80780 0x000000000003f00f

def z790 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xa7ff8001fff80038 0xe14fff0003fff000

def z791 : W := mkw 0x1fba59a800000060 0x003f74b350000000 0xdffff9fe00000007 0xfdbffff3fc000000

def z792 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8e01fff87838 0xfd7fff1c03fff0f0

def z793 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc41cf383e0000 0x890db8839e707c00

def z794 : W := mkw 0x17086c88ac055028 0x402e10d911580aa0 0xffdc7fc1fe07f87b 0x3fffb8ff83fc0ff0

def z795 : W := mkw 0x3db68000f6f0000b 0x807b6d0001ede000 0xbf1f8000fe380020 0xa17e3f0001fc7000

def z796 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fed 0xe402471c7c0ff0ff

def z797 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x86ff81fe00000004 0xc10dff03fc000000

def z798 : W := mkw 0x024c488b11282224 0x0004989116225044 0x86dc49cf3938666d 0xed0db8939e7270cc

def z799 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x873f80003ff80020 0xe10e7f00007ff000

def z800 : W := mkw 0x3df68041f7f2850f 0xa07bed0083efe50a 0xbfff8031ffff87ff 0xff7fff0063ffff0f

def z801 : W := mkw 0x3df69121f7f0814f 0xa07bed2243efe102 0xbfff8031fff801b8 0xfd7fff0063fff003

def z802 : W := mkw 0xb744c843fffe660f 0x916e899087fffccc 0x3f004801fffe6679 0x3c7e009003fffccc

def z803 : W := mkw 0x08e1937743daafd7 0x2811c326ee87b55f 0x79c3ffcfc63ff820 0xa8f387ff9f8c7ff0

def z804 : W := mkw 0x3df69121f7f0004f 0x807bed2243efe000 0xbfff81f1fff8003c 0xfd7fff03e3fff000

def z805 : W := mkw 0x3df68041f7f2040f 0x807bed0083efe408 0xbfffc1f1fffe07ff 0xff7fff83e3fffc0f

def z806 : W := mkw 0x824c6ccb192e6624 0x110498d996325ccc 0xc6dc7fcf393e666f 0xed8db8ff9e727ccc

def z807 : W := mkw 0xa0448043fffee70f 0xb140890087fffdce 0x20000001ffffe7f8 0x0240000003ffffcf

def z808 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xdedc79cf393e666f 0xfdbdb8f39e727ccc

def z809 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0xd8ffb1fe00000006 0xd1b1ff63fc000000

def z810 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f863 0x2afe00fc03fc0ff0

def z811 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe06007827 0xfdbffffffc0c00f0

def z812 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x87dc49cf3f3e667d 0xfd0fb8939e7e7ccc

def z813 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c7c7ffff 0x5ef1c0e3e38f8fff

def z814 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e079f1c1c7e7ff 0x7ef1c0f3e3838fcf

def z815 : W := mkw 0x17096e9cac055038 0x402e12dd39580aa0 0xfffffffffe07f87f 0xfffffffffffc0ff0

def z816 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c78796 0x5af1c0e3e3838f0f

def z817 : W := mkw 0x5fbb7fbc08055070 0x40bf76ff78100aa0 0xdffffffe00007807 0xfdbffffffc0000f0

def z818 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1ff87ff 0xfef1c0e3e383ff0f

def z819 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x87ffc9cf393e666d 0xfd0fff939e727ccc

def z820 : W := mkw 0x3db68000b6700009 0x807b6d00016ce000 0xbfff8001fe380038 0xfd7fff0003fc7000

def z821 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfdf8001fff80038 0xa97fbf0003fff000

def z822 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc09ce38386020 0xa10db8139c7070c0

def z823 : W := mkw 0x8aac59aa58ace362 0x311558b354b159c6 0xfe3c383ef8f9e1b2 0xb3fc78707df1f3c3

def z824 : W := mkw 0x804480431b7e6e85 0x190089008636fcdd 0x000000013f3e7e68 0x00000000027e7cfc

def z825 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f80003e380038 0xb50e3f00007c7000

def z826 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe01c00787 0xfdbffffffc03800f

def z827 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e666d 0x090db8939e727ccc

def z828 : W := mkw 0x024c48c911220424 0x0004989192224408 0x86dc49cf393e066d 0xed0db8939e727c0c

def z829 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e6624 0xe90db8939e727ccc

def z830 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1c1ffff867d 0xfdffffe383ffff0c

def z831 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xbfff81f1fff807ff 0xff7fff03e3fff00f

def z832 : W := mkw 0x4abb7fbc00000070 0x009576ff78000000 0xc0fff1fe00000004 0xc181ffe3fc000000

def z833 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x86dc49ce3938666d 0xed0db8939c7270cc

def z834 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffff807805f 0xfffffffffff00f00

def z835 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x79e077f1c7c79fdf 0x5ef3c0efe38f8f3f

def z836 : W := mkw 0x35168000f6f0000b 0x806a2d0001ede000 0xa71f8000fef80030 0xa14e3f0001fdf000

def z837 : W := mkw 0x3df68001f7f0088f 0x887bed0003efe011 0xbfff8001fff819b8 0xff7fff0003fff033

def z838 : W := mkw 0x3db68000f6f0000b 0x807b6d0001ede000 0xbfff8000fef80030 0xfd7fff0001fdf000

def z839 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc01ce39380604 0xc10db8039c72700c

def z840 : W := mkw 0x3db39334e6d089db 0xa87b672669cda113 0x7923b630c6c19992 0x12f2476c618d8333

def z841 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f23fe01fe07f87b 0xfefe47fc03fc0ff0

def z842 : W := mkw 0x3df70217f5a82a9e 0x887bee042feb5055 0xbedc0e3ff8007fc7 0x0b7db81c7ff000ff

def z843 : W := mkw 0x5dbb13bc00000070 0x00bb762778000000 0x87ff81fe00000004 0xe10fff03fc000000

def z844 : W := mkw 0x35568001f7f0000f 0x806aad0003efe000 0x871f80003ff80020 0xa10e3f00007ff000

def z845 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfffffce00000000 0xfdbfffff9c000000

def z846 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x9fff80003ff80020 0xfd3fff00007ff000

def z847 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1f1ffff803f 0xfdffffe3e3ffff00

def z848 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fe7 0xe202471c7c0ff0ff

def z849 : W := mkw 0x824c48cb59aee726 0x3104989196b35dce 0x86dc49cf39fe67ed 0xed0db8939e73fccf

def z850 : W := mkw 0xbfbac8caeede662b 0x917f759195ddbccc 0x3923c9cec6c66655 0x107247939d8d8ccc

def z851 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007601fe07f87a 0x1afe00ec03fc0ff0

def z852 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x81ff81fe00000004 0xf503ff03fc000000

def z853 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x86dc01cf39380604 0xc90db8039e72700c

def z854 : W := mkw 0x3df6a401f7f1100f 0xc07bed4803efe220 0xbfff8601fff81838 0xfd7fff0c03fff030

def z855 : W := mkw 0x5fbafdaa02582ae1 0x08bf75fb5404b055 0xdedc71c007f87ff8 0x0bbdb8e3800ff0ff

def z856 : W := mkw 0x3df69161f7f2044f 0x807bed22c3efe408 0xfffff1f1fffe067f 0xfdffffe3e3fffc0c

def z857 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff87878 0xff7fff0003fff0f0

def z858 : W := mkw 0x82494adf090e6eb4 0x19049295be121cdd 0x00e04fff01c67fdf 0x5e01c09ffe038cff

def z859 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80df81ce00000000 0x8101bf039c000000

def z860 : W := mkw 0x02094a9c08044030 0x0004129538100880 0x87ffcfff3e06787f 0xff0fff9ffe7c0cf0

def z861 : W := mkw 0x5dbb37bc00000070 0x00bb766f78000000 0xd8ffb1fe00000004 0xc1b1ff63fc000000

def z862 : W := mkw 0x5dbb13bc00000070 0x00bb762778000000 0x99ff81fe00000004 0xd133ff03fc000000

def z863 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xc7fffffe00000007 0xe18ffffffc000000

def z864 : W := mkw 0x8244c8431b7e6e85 0x190489908636fcdd 0x07004e013ffe7ffb 0x3e0e009c027ffcff

def z865 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x7923be3ec7f9ffff 0xf6f2477c7d8ff3ff

def z866 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x21238e3fc7ffffff 0xf642471c7f8fffff

def z867 : W := mkw 0x82094a9e080c6ab0 0x190412953c1018d5 0x00000e3e00007fc7 0x0200001c7c0000ff

def z868 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0xbf1f8000fe380030 0xb17e3f0001fc7000

def z869 : W := mkw 0x35568041b772040d 0x806aad00836ee408 0x87dfc1c13f3e066d 0xed0fbf83827e7c0c

def z870 : W := mkw 0x804c00cb192e6624 0x1100980196325ccc 0x86dc01cf393e666c 0xed0db8039e727ccc

def z871 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c0c787d7 0x1af1c0e3e3818f0f

def z872 : W := mkw 0x5dbb37bca4011078 0x40bb766f79480220 0xf9ffb7fec6019816 0xd3f3ff6ffd8c0330

def z873 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f207e31fec7f9fb 0x3efe40fc63fd8ff3

def z874 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1f1ffff87bc 0xfdffffe3e3ffff0f

def z875 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbedf8001f8380000 0x897dbf0003f07000

def z876 : W := mkw 0x970dee9ebe7d7ab9 0x592e1bdd3d7cfaf5 0x871f8e0e3e387820 0xa10e3f1c1c7c70f0

def z877 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xffffb001fff9803a 0xffffff6003fff300

def z878 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01ff3ff87b 0xfefe00fc03fe7ff0

def z879 : W := mkw 0x401b029c00000030 0x0080360538000000 0x80df81ce00000004 0xc101bf039c000000

def z880 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffffe07f827 0xfdfffffffffc0ff0

def z881 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdedff1ce00000000 0x89bdbfe39c000000

def z882 : W := mkw 0x824c48cb192f7624 0x5104989196325eec 0x86dc49cf393ffe6d 0xef0db8939e727ffc

def z883 : W := mkw 0x3df6800153f00007 0x807bed0002a7e000 0x9fff800139f80028 0xfd3fff000273f000

def z884 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e079ffc1c787df 0xfef1c0f3ff838f0f

def z885 : W := mkw 0x1701ee16ae5d7a99 0x482e03dc2d5cbaf5 0x7e23f03ff9ff8784 0xc8fc47e07ff3ff0f

def z886 : W := mkw 0xcae97fff090e6674 0x1195d2fffe121ccc 0x58e07fff0106664f 0x5cb1c0fffe020ccc

def z887 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f832 0x3afe00fc03fc0ff0

def z888 : W := mkw 0x7df6b521f7f0004f 0x80fbed6a43efe000 0xffffb001fff80038 0xfdffff6003fff000

def z889 : W := mkw 0x4abb5bbc00000070 0x009576b778000000 0x86ffc1fe00000004 0xc90dff83fc000000

def z890 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49ce39386625 0xed0db8939c7270cc

def z891 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001ffff8078 0xff7fff0003ffff00

def z892 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8e31fff87fff 0xff7fff1c63fff0ff

def z893 : W := mkw 0x824c6ccb192f7624 0x510498d996325eec 0x86dc4fcf393e7e6d 0xed0db89f9e727cfc

def z894 : W := mkw 0x5fbb7fbc40808172 0x20bf76ff78810102 0xdffffffe00c00187 0xfdbffffffc018003

def z895 : W := mkw 0xa0448043f7fa260f 0x9140890087eff44c 0x20000001fff80638 0x0040000003fff00c

def z896 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00c00197 0xffbffffffc018003

def z897 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f8e003e387820 0xa10e3f1c007c70f0

def z898 : W := mkw 0x15448001b770000d 0x002a8900036ee000 0xbfff8001fff80038 0xfd7fff0003fff000

def z899 : W := mkw 0x3df6a401f7f1100f 0xc07bed4803efe220 0xffffbe01fff9f87b 0xffffff7c03fff3f0

def z900 : W := mkw 0x3df68041f7f2850f 0xa07bed0083efe50a 0xbfff8001fff807b8 0xfd7fff0003fff00f

def z901 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f869 0x2cfe00fc03fc0ff0

def z902 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xa6dc49cff93fe67d 0xef4db8939ff27fcc

def z903 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1c1ffff87f8 0xffffffe383ffff0f

def z904 : W := mkw 0x3df68041f7f2040f 0x807bed0083efe408 0xbfff81c1fff8063c 0xfd7fff0383fff00c

def z905 : W := mkw 0x0004800012700001 0x000009000024e000 0x873f80003ff80038 0xf50e7f00007ff000

def z906 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xffdc7fcfff3ffe7f 0xffffb8ff9ffe7ffc

def z907 : W := mkw 0x08e4116151a28546 0x2011c822c2a3450a 0x78e071f1f9ff87ff 0x5ef1c0e3e3f3ff0f

def z908 : W := mkw 0x1db28000a6500009 0x003b6500014ca000 0xbfff8001fff80038 0xfd7fff0003fff000

def z909 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x86ff81fe00000004 0xed0dff03fc000000

def z910 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfefff1f1f9ff87df 0xdffdffe3e3f3ff0f

def z911 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ff8ffe00000007 0xc101ff1ffc000000

def z912 : W := mkw 0x1df6116151a28546 0x203bec22c2a3450a 0xfffff1f1f9ff87ff 0xffffffe3e3f3ff0f

def z913 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbeff8001f9f80018 0xdd7dff0003f3f000

def z914 : W := mkw 0x1df6000151a00006 0x003bec0002a34000 0xbfff8001f9f80038 0xfd7fff0003f3f000

def z915 : W := mkw 0x5dbb13bc00000070 0x00bb762778000000 0x9eff81fe00000004 0xc93dff03fc000000

def z916 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x86dc09ce38386024 0xe10db8139c7070c0

def z917 : W := mkw 0x3db68000f6f0000b 0x807b6d0001ede000 0xbf3f8000fff80038 0xf57e7f0001fff000

def z918 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xbedc49cff93e667d 0xfd7db8939ff27ccc

def z919 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfffc1c1fff8003d 0xfd7fff8383fff000

def z920 : W := mkw 0x1db3133400000050 0x003b662668000000 0xdffffffe00000007 0xfdbffffffc000000

def z921 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff8067d 0xfd7fff0003fff00c

def z922 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe0000606f 0xfdbffffffc0000c0

def z923 : W := mkw 0x824c48cb192ee724 0x3104989196325dce 0x86dc49cf393fe7ed 0xef0db8939e727fcf

def z924 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x87ff8ffe00000007 0xf50fff1ffc000000

def z925 : W := mkw 0x3db68000b6700009 0x807b6d00016ce000 0x9fdf80003e380020 0xa93fbf00007c7000

def z926 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffec607f857 0xfffffffffd8c0ff0

def z927 : W := mkw 0x5fbb7fbc08044070 0x00bf76ff78100880 0xdfffffff3e06787f 0xffbffffffe7c0cf0

def z928 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e31fe07ffff 0x3efe00fc63fc0fff

def z929 : W := mkw 0x5fbb7fbc40800072 0x00bf76ff78810000 0xfffffffec0c00017 0xfdfffffffd818000

def z930 : W := mkw 0x4abb7fbc00000070 0x009576ff78000000 0xc6fffffe00000007 0xed8dfffffc000000

def z931 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xdfffffff3e06786f 0xfdbffffffe7c0cf0

def z932 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdefffffe00000007 0xc9bdfffffc000000

def z933 : W := mkw 0x0044000111200004 0x0000880002224000 0x87ff800139380028 0xfd0fff0002727000

def z934 : W := mkw 0x024c488919244024 0x0004989112324880 0x86dc49cf393e606d 0xed0db8939e727cc0

def z935 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f0c1c787d7 0x52f1c0e3e1838f0f

def z936 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfdf8001ff380028 0xed7fbf0003fe7000

def z937 : W := mkw 0x8ae95bff498eeff6 0x3915d2b7fe931ddf 0x78e07fffc1c7ffdf 0x5ef1c0ffff838fff

def z938 : W := mkw 0x15002400ac055008 0x402a004801580aa0 0x79007601fe07f87b 0x1ef200ec03fc0ff0

def z939 : W := mkw 0xc2097ffe080e6ef0 0x198412fffc101cdd 0x40007ffe00067fc7 0x028000fffc000cff

def z940 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc4fcf393e7e6f 0xef0db89f9e727cfc

def z941 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0xd8fff1fe00000004 0xc9b1ffe3fc000000

def z942 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0xf8fff1ffc007805f 0xdff1ffe3ff800f00

def z943 : W := mkw 0x5fbb7fbca4000078 0x00bf76ff79480000 0xfffffffffe00787f 0xfffffffffffc00f0

def z944 : W := mkw 0x824c48cb59aee726 0x3104989196b35dce 0xfedc79cff9ffe7ff 0xfffdb8f39ff3ffcf

def z945 : W := mkw 0x1df60001b520000c 0x003bec00036a4000 0xbfff8001ff380038 0xfd7fff0003fe7000

def z946 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffff807f847 0xfffffffffff00ff0

def z947 : W := mkw 0x48bb13bc40808172 0x2091762778810102 0xf8ffb1fec0c18196 0xd3f1ff63fd818303

def z948 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fef80030 0xb97fff0003fdf000

def z949 : W := mkw 0x4abb7fbc00000070 0x009576ff78000000 0xc1fffffe00000007 0xf583fffffc000000

def z950 : W := mkw 0x1df6800113700005 0x003bed000226e000 0x9fff80013ff80038 0xfd3fff00027ff000

def z951 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x86dc49cf383e606d 0xed0db8939e707cc0

def z952 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x81ff8ffe0600787f 0xf703ff1ffc0c00f0

def z953 : W := mkw 0x575b6edd41828536 0x20aeb6ddba83050a 0xa71f8e0fc1c787d8 0xa34e3f1c1f838f0f

def z954 : W := mkw 0x3516a400b6711009 0xc06a2d48016ce220 0x871f86003e381820 0xa10e3f0c007c7030

def z955 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf39fe67fd 0xef0db8939e73fccf

def z956 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e0605 0xed0db8939e727c0c

def z957 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffff1fe00000004 0xfdbfffe3fc000000

def z958 : W := mkw 0x3df6a401f7f0000f 0x807bed4803efe000 0xffffb601fff8003a 0xfdffff6c03fff000

def z959 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1c1ffff807b 0xffffffe383ffff00

def z960 : W := mkw 0x0044800113700005 0x000089000226e000 0x86ff800139f80028 0xed0dff000273f000

def z961 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xd9fffffe00000007 0xd1b3fffffc000000

def z962 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f80003ff80038 0xa10e3f00007ff000

def z963 : W := mkw 0x5fbb7fbc08044070 0x00bf76ff78100880 0xdffffffe38006027 0xfdbffffffc7000c0

def z964 : W := mkw 0x3db68000b6700009 0x807b6d00016ce000 0x9fff80003ff80038 0xfd3fff00007ff000

def z965 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbeff8001fff80038 0xc97dff0003fff000

def z966 : W := mkw 0x42097fbc00000070 0x008412ff78000000 0xc7fffffe00000007 0xfd8ffffffc000000

def z967 : W := mkw 0x1fba6c88ac055028 0x403f74d911580aa0 0xffffffcffe07f87f 0xffffffff9ffc0ff0

def z968 : W := mkw 0x571b7fbc00000070 0x00ae36ff78000000 0xc7dffffe00000007 0xed8fbffffc000000

def z969 : W := mkw 0x28f6116151a28546 0xa051ec22c2a3450a 0xf8fc71f1c1c787df 0x5ff1f8e3e3838f0f

def z970 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe0138002f 0xfdbffffffc027000

def z971 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86fc49ff393e666f 0xfd0df893fe727ccc

def z972 : W := mkw 0x08a0116040828542 0x20114022c081050a 0x782071f1c0c787df 0x1ef040e3e3818f0f

def z973 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8031fff807bc 0xfd7fff0063fff00f

def z974 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0xbf1f8001fe380020 0xa97e3f0003fc7000

def z975 : W := mkw 0x1fe07d61ed87d54e 0x603fc0fac3db0faa 0x07e00ff03fc07fa4 0x600fc01fe07f80ff

def z976 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f003e01fe07f87a 0x32fe007c03fc0ff0

def z977 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f838 0x3cfe00fc03fc0ff0

def z978 : W := mkw 0x35568001f7f0000f 0x806aad0003efe000 0xa7df8001fff80038 0xed4fbf0003fff000

def z979 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe06001817 0xffbffffffc0c0030

def z980 : W := mkw 0x0aa95bbc00000070 0x001552b778000000 0xdffffffe00000007 0xfdbffffffc000000

def z981 : W := mkw 0x5fbb7fbca4000078 0x00bf76ff79480000 0xfffffffff8000007 0xfdfffffffff00000

def z982 : W := mkw 0x5dbb37bc00000070 0x00bb766f78000000 0xd9ffbffe00000007 0xf5b3ff7ffc000000

def z983 : W := mkw 0x3df6a401f7f1100f 0xc07bed4803efe220 0xffffb001fff98038 0xfdffff6003fff300

def z984 : W := mkw 0x5fbb7fbcac044078 0x00bf76ff79580880 0xfffffffffe06607f 0xfdfffffffffc0cc0

def z985 : W := mkw 0x820c488a182c6220 0x11041891143058c4 0x86dc49ce38386020 0xa90db8939c7070c0

def z986 : W := mkw 0x82096ede080f7eb0 0x590412ddbc101efd 0x40007ffe0007ffc7 0x028000fffc000fff

def z987 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x79e3f1f1c1c787df 0xfef3c7e3e3838f0f

def z988 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfefff1f1f9ff8784 0xc9fdffe3e3f3ff0f

def z989 : W := mkw 0x5fbb7fbca4011078 0x40bf76ff79480220 0xdffffffe06001807 0xfdbffffffc0c0030

def z990 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffffe07803f 0xfdfffffffffc0f00

def z991 : W := mkw 0xc2097ffe080ee770 0x318412fffc101dce 0x40007ffe0007e7c7 0x028000fffc000fcf

def z992 : W := mkw 0x35568001f7f0000f 0x806aad0003efe000 0xbf1f8001fff80038 0xbd7e3f0003fff000

def z993 : W := mkw 0x17126c00ac055008 0x402e24d801580aa0 0xff1ffe01fe07f87b 0xbffe3ffc03fc0ff0

def z994 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0xff1ff001fe3f807b 0xbffe3fe003fc7f00

def z995 : W := mkw 0x9744ec43bf7f7e8d 0x592e89d8877efefd 0x7f007e01fffffffb 0x3efe00fc03ffffff

def z996 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87ffc 0xe202471c7c0ff0ff

def z997 : W := mkw 0x28f6916153f28547 0xa051ed22c2a7e50a 0xfefff1f1f9ff87ff 0xfffdffe3e3f3ff0f

def z998 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8e01fff8003b 0xfd7fff1c03fff000

def z999 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x87df80003e380020 0xed0fbf00007c7000

def z1000 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0xbeff8001f9f80038 0xfd7dff0003f3f000

def z1001 : W := mkw 0x17096e9c00000030 0x002e12dd38000000 0xdffffffe00000007 0xfdbffffffc000000

def z1002 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfffffff0006004f 0xfdbffffffe000c00

def z1003 : W := mkw 0x571b6e9cac055038 0x40ae36dd39580aa0 0x87dfcfcf3e06786d 0xed0fbf9f9e7c0cf0

def z1004 : W := mkw 0x004c008911200024 0x0000980112224000 0x86dc01cf3938002c 0xed0db8039e727000

def z1005 : W := mkw 0x7db39334e6d0005b 0x80fb672669cda000 0x39238030c6c00010 0x10724700618d8000

def z1006 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfdfffce00000003 0xbdbfbfff9c000000

def z1007 : W := mkw 0x824c48cb112a2624 0x110498919622544c 0x86dc49cf3938062d 0xed0db8939e72700c

def z1008 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1f1ffff81ba 0xffffffe3e3ffff03

def z1009 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0x87ffcffe00000007 0xfd0fff9ffc000000

def z1010 : W := mkw 0x42097fbe080d7af0 0x488412ff7c101af5 0x40007ffe0007ffc7 0x028000fffc000fff

def z1011 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x98ff81fe00000004 0xdd31ff03fc000000

def z1012 : W := mkw 0x08ba008800000020 0x0011740110000000 0x80ff81ce00000004 0xc101ff039c000000

def z1013 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f80013e380028 0xad0e3f00027c7000

def z1014 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf383e6025 0xed0db8939e707cc0

def z1015 : W := mkw 0x00000000ac055008 0x4000000001580aa0 0x79007e01fe07f87b 0x3ef200fc03fc0ff0

def z1016 : W := mkw 0x08e4116151a28546 0x2011c822c2a3450a 0xf8fc71f1c1ff87df 0xdff1f8e3e383ff0f

def z1017 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xffffb031ffff87fa 0xffffff6063ffff0f

def z1018 : W := mkw 0x4abb5bbc00000070 0x009576b778000000 0x87ffcffe00000007 0xfd0fff9ffc000000

def z1019 : W := mkw 0x35568001b770000d 0x806aad00036ee000 0xbfdf8001ff380038 0xfd7fbf0003fe7000

def z1020 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x861f800038380000 0x810c3f0000707000

def z1021 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xdffffffe3e07f867 0xffbffffffc7c0ff0

def z1022 : W := mkw 0x1db6000010200000 0x003b6c0000204000 0x9fff800038380020 0xfd3fff0000707000

def z1023 : W := mkw 0xc2095bfe080e6670 0x118412b7fc101ccc 0x000049fe00066645 0x00000093fc000ccc

def z1024 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ff81fe00000007 0xd501ff03fc000000

def z1025 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xfffffe01fffff87b 0xfffffffc03fffff0

def z1026 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x87df80003e380020 0xa10fbf00007c7000

def z1027 : W := mkw 0x5db3b734a65118d9 0x48bb676e694ca231 0x7923b630c6c19992 0x12f2476c618d8333

def z1028 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0xdfdfffce00000007 0xfdbfbfff9c000000

def z1029 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8031fff8003f 0xfd7fff0063fff000

def z1030 : W := mkw 0x3df69121f7f0814f 0xa07bed2243efe102 0xfffff031ffff81fb 0xffffffe063ffff03

def z1031 : W := mkw 0x4abb7fbc00000070 0x009576ff78000000 0xd8fffffe00000007 0xddb1fffffc000000

def z1032 : W := mkw 0x3df69121f7f0004f 0x807bed2243efe000 0xfffff1f1ffff807f 0xffffffe3e3ffff00

def z1033 : W := mkw 0x1516000010200000 0x002a2c0000204000 0x871f800038380020 0xa10e3f0000707000

def z1034 : W := mkw 0x82094ade080e6630 0x11041295bc101ccc 0x00004ffe00066647 0x0000009ffc000ccc

def z1035 : W := mkw 0x824c6ccb192f7624 0x510498d996325eec 0xc7dc7fcf3f3ffe7f 0xff8fb8ff9e7e7ffc

def z1036 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0xffdc7e01fe07f87b 0xffffb8fc03fc0ff0

def z1037 : W := mkw 0x08a0116040828542 0x20114022c081050a 0x782071f0c1c787df 0x56f040e3e1838f0f

def z1038 : W := mkw 0x5fbb7fbca4000078 0x00bf76ff79480000 0xfffffffec6000017 0xfdfffffffd8c0000

def z1039 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x87dc4fcf393e666f 0xfd0fb89f9e727ccc

def z1040 : W := mkw 0x5fbb7fbca4011078 0x40bf76ff79480220 0xfffffffffe01983f 0xfffffffffffc0330

def z1041 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0x87ff81f03ff807a4 0xe10fff03e07ff00f

def z1042 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbf3f8001fff80038 0xb17e7f0003fff000

def z1043 : W := mkw 0x5fbb7fbc08044070 0x00bf76ff78100880 0xdfffffff38060007 0xfdbffffffe700c00

def z1044 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xfffff1f1fff807bf 0xfdffffe3e3fff00f

def z1045 : W := mkw 0x5dbb13bc00000070 0x00bb762778000000 0x9fff8ffe00000007 0xfd3fff1ffc000000

def z1046 : W := mkw 0x82094a9e080c6ab0 0x190412953c1018d5 0x00000e0e00007800 0x0000001c1c0000f0

def z1047 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c7879c 0x5cf1c0e3e3838f0f

def z1048 : W := mkw 0x804480435bfeef87 0x3900890086b7fddf 0x20000001fffffff8 0x0240000003ffffff

def z1049 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbeff8001f9f80028 0xed7dff0003f3f000

def z1050 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xbfffc1f1fffe07fd 0xfd7fff83e3fffc0f

def z1051 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff80038 0x197fff0003fff000

def z1052 : W := mkw 0x571a6c88ac055028 0x40ae34d911580aa0 0xff1c7e01fe07f87b 0x3ffe38fc03fc0ff0

def z1053 : W := mkw 0x80448043bf7f7e8d 0x59008900877efefd 0x20000001fffffff8 0x0240000003ffffff

def z1054 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x87ffcffe00000005 0xed0fff9ffc000000

def z1055 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xffffffffc607f87f 0xffffffffff8c0ff0

def z1056 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x87ff80003ff80038 0xf50fff00007ff000

def z1057 : W := mkw 0x3df68041f7f2850f 0xa07bed0083efe50a 0xfffff001ffff87fb 0xffffffe003ffff0f

def z1058 : W := mkw 0x08e4916153f28547 0x2011c922c2a7e50a 0xfffff1f1ffff87ff 0xffffffe3e3ffff0f

def z1059 : W := mkw 0x15002400ac055008 0x402a004801580aa0 0x79003e01fe07f87b 0x36f2007c03fc0ff0

def z1060 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x87ff8e3e07f87fff 0xff0fff1c7c0ff0ff

def z1061 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01ff07fe7f 0x7efe00fc03fe0ffc

def z1062 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xfefc79fff9ffe7ff 0xfffdf8f3fff3ffcf

def z1063 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e6028 0xed0db8939e727cc0

def z1064 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0xd9fffffe00000007 0xfdb3fffffc000000

def z1065 : W := mkw 0x0000116000028540 0x20000022c000050a 0x782071f1c1c787df 0x5ef040e3e3838f0f

def z1066 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fe380020 0xfd7fff0003fc7000

def z1067 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e6645 0xc90db8939e727ccc

def z1068 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfdfffce00000005 0xedbfbfff9c000000

def z1069 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x86dc41cf393e066d 0xed0db8839e727c0c

def z1070 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff80010 0xd97fff0003fff000

def z1071 : W := mkw 0x0044804113720405 0x000089008226e408 0x87ffc1f13ffe07ff 0xff0fff83e27ffc0f

def z1072 : W := mkw 0x82094ade080e6eb0 0x19041295bc101cdd 0x00004fce00067e45 0x0000009f9c000cfc

def z1073 : W := mkw 0x5dbb37bc00000070 0x00bb766f78000000 0xd9fff7fe00000007 0xddb3ffeffc000000

def z1074 : W := mkw 0x3df68001f7f0810f 0xa07bed0003efe102 0xbfff8001fff981b8 0xff7fff0003fff303

def z1075 : W := mkw 0x3df6a401f7f1100f 0xc07bed4803efe220 0xfffff601ffff987b 0xffffffec03ffff30

def z1076 : W := mkw 0x82094ade080e6eb0 0x19041295bc101cdd 0x000049fe000667c5 0x00000093fc000ccf

def z1077 : W := mkw 0x28f7937753faafd7 0xa851ef26eea7f55f 0x80ff81fe01f80784 0xc101ff03fc03f00f

def z1078 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff807f8 0xff7fff0003fff00f

def z1079 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xffffffffffc7ffff 0xffffffffffff8fff

def z1080 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e07ff1c1c7ffdf 0x5ef1c0ffe3838fff

def z1081 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00078047 0xffbffffffc000f00

def z1082 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c787c7 0x4af1c0e3e3838f0f

def z1083 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fa7 0xf402471c7c0ff0ff

def z1084 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xffffffffc0078007 0xfdffffffff800f00

def z1085 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x873f80003ef80030 0xb10e7f00007df000

def z1086 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0xbf3f8001fff80038 0xfd7e7f0003fff000

def z1087 : W := mkw 0x1dba008800000020 0x003b740110000000 0x9fff81ce00000004 0xfd3fff039c000000

def z1088 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f207e01ffc7f87b 0x7efe40fc03ff8ff0

def z1089 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe0100064f 0xfdbffffffc02000c

def z1090 : W := mkw 0x0040116141828546 0x20008022c283050a 0x780071f1c1c787df 0x1ef000e3e3838f0f

def z1091 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e667f 0xff0db8939e727ccc

def z1092 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf383e6665 0xa90db8939e707ccc

def z1093 : W := mkw 0x7fbb7fbce480007a 0x80ff76ff79c90000 0xfffffffec0000007 0xfdfffffffd800000

def z1094 : W := mkw 0x2016800012700001 0x80402d000024e000 0x861f800038380020 0xa10c3f0000707000

def z1095 : W := mkw 0xc2096ede080e6630 0x118412ddbc101ccc 0x00004fce00066645 0x0000009f9c000ccc

def z1096 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xdffffffe3e00787f 0xffbffffffc7c00f0

def z1097 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0x87ff8ffe3e007824 0xe10fff1ffc7c00f0

def z1098 : W := mkw 0x17086c88ac055028 0x402e10d911580aa0 0x7f007fcffe07f87f 0x3efe00ff9ffc0ff0

def z1099 : W := mkw 0x20448043f7faaf8f 0xa840890087eff55f 0x20000001fffffff8 0x0240000003ffffff

def z1100 : W := mkw 0x3db68000f6f0000b 0x807b6d0001ede000 0x873f80003ef80020 0xa10e7f00007df000

def z1101 : W := mkw 0xb744ec43ffff760f 0xd16e89d887fffeec 0x7f007e01fffffe7b 0x3efe00fc03fffffc

def z1102 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8000fff80030 0xf17fff0001fff000

def z1103 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x79e071f1c7c787ff 0x7ef3c0e3e38f8f0f

def z1104 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78c071f1c1c787df 0x0af180e3e3838f0f

def z1105 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc41cf393e062c 0xed0db8839e727c0c

def z1106 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f823 0x3cfe00fc03fc0ff0

def z1107 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x87fc4fff3ffe7fff 0xff0ff89ffe7ffcff

def z1108 : W := mkw 0x02006c00ac055008 0x400400d801580aa0 0x78007e01fe07f87b 0x1ef000fc03fc0ff0

def z1109 : W := mkw 0x08e4800153f00007 0x0011c90002a7e000 0xbfff8001fff80038 0xfd7fff0003fff000

def z1110 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdfffbffe00000006 0xf1bfff7ffc000000

def z1111 : W := mkw 0x1df6116111220444 0x003bec22c2224408 0xdffff1f1393e066f 0xfdbfffe3e2727c0c

def z1112 : W := mkw 0x5fbb6e9c00000030 0x00bf76dd38000000 0x9fffcfce00000005 0xfd3fff9f9c000000

def z1113 : W := mkw 0x3df69121f7f0814f 0xa07bed2243efe102 0xffffb001fff98038 0xfdffff6003fff300

def z1114 : W := mkw 0x08a0116040828542 0x20114022c081050a 0x78e071f0c0c787d7 0x5ef1c0e3e1818f0f

def z1115 : W := mkw 0x3df69121f7f0004f 0x807bed2243efe000 0xfffff1c1fff80038 0xfdffffe383fff000

def z1116 : W := mkw 0x5fbb7fbca4000078 0x00bf76ff79480000 0xdffffffe3e000027 0xfdbffffffc7c0000

def z1117 : W := mkw 0x7db3b734a6500059 0x80fb676e694ca000 0x5923b63006000002 0x10b2476c600c0000

def z1118 : W := mkw 0x3df68041f7f2040f 0x807bed0083efe408 0xfffff1c1ffff867f 0xffffffe383ffff0c

def z1119 : W := mkw 0xa04480435bfe6607 0x9140890086b7fccc 0x0000000139fe6668 0x000000000273fccc

def z1120 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff8007b 0xff7fff0003fff000

def z1121 : W := mkw 0x5fba7da800000060 0x00bf74fb50000000 0xdffff9ce00000005 0xfdbffff39c000000

def z1122 : W := mkw 0x3db68000b6700009 0x807b6d00016ce000 0x9f3f80003e380020 0xb13e7f00007c7000

def z1123 : W := mkw 0x5fbb7fbc40808172 0x20bf76ff78810102 0xffffffffc0c781df 0xffffffffff818f03

def z1124 : W := mkw 0x3df6b521f7f1914f 0xe07bed6a43efe322 0xffffb631fff999ba 0xffffff6c63fff333

def z1125 : W := mkw 0x5fbb7fbc08055070 0x40bf76ff78100aa0 0xffffffffc007f85f 0xffffffffff800ff0

def z1126 : W := mkw 0x1fba6c8800000020 0x003f74d910000000 0xdfffffce00000007 0xfdbfffff9c000000

def z1127 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xffffffffc1c787df 0xffffffffff838f0f

def z1128 : W := mkw 0x35568001f7f0000f 0x806aad0003efe000 0xa71f8001fe380020 0xa14e3f0003fc7000

def z1129 : W := mkw 0x0004800012700001 0x000009000024e000 0x871f80003e380020 0xa10e3f00007c7000

def z1130 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fbc 0xf402471c7c0ff0ff

def z1131 : W := mkw 0x5fbb7fbcec85d17a 0x60bf76ff79d90ba2 0xfffffffffec7f9ff 0xfffffffffffd8ff3

def z1132 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49cf393e6668 0xa90db8939e727ccc

def z1133 : W := mkw 0x804480431b7e6605 0x110089008636fccc 0x000000013ffe6678 0x00000000027ffccc

def z1134 : W := mkw 0x3db69120f6f0814b 0xa07b6d2241ede102 0xff3fb030fef981b2 0xb3fe7f6061fdf303

def z1135 : W := mkw 0xa0448043bf7e660d 0x91408900877efccc 0x000000013f3e6668 0x00000000027e7ccc

def z1136 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0xfedc79cff93fe66d 0xedfdb8f39ff27fcc

def z1137 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001f9f80000 0xfd7fff0003f3f000

def z1138 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x871f80003f380028 0xe50e3f00007e7000

def z1139 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x87df8fce00000000 0xa10fbf1f9c000000

def z1140 : W := mkw 0x171a488800000020 0x002e349110000000 0x87dfc9ce00000005 0xed0fbf939c000000

def z1141 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe0000005f 0xffbffffffc000000

def z1142 : W := mkw 0x0040004101020404 0x0000800082020408 0x78e071f1c1c787df 0x5ef1c0e3e3838f0f

def z1143 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xffffffffc000001f 0xfdffffffff800000

def z1144 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfefff1fff8078004 0xc9fdffe3fff00f00

def z1145 : W := mkw 0x0044800113700005 0x000089000226e000 0x87df80013f380028 0xed0fbf00027e7000

def z1146 : W := mkw 0x1556000111200004 0x002aac0002224000 0x87df800139380028 0xed0fbf0002727000

def z1147 : W := mkw 0x4abb5bbc00000070 0x009576b778000000 0x80ffc9fe00000005 0xc101ff93fc000000

def z1148 : W := mkw 0x82095bfe080eeff0 0x390412b7fc101ddf 0x40007ffe0007ffc7 0x028000fffc000fff

def z1149 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0xc0fff1fe00000007 0xc181ffe3fc000000

def z1150 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xfffff001ffff8038 0xfdffffe003ffff00

def z1151 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8801fff86079 0xfd7fff1003fff0c0

def z1152 : W := mkw 0x08f6000111200004 0x0011ec0002224000 0x86ff800139380028 0xed0dff0002727000

def z1153 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8031fff801ba 0xff7fff0063fff003

def z1154 : W := mkw 0x4abb7fbc00000070 0x009576ff78000000 0x80ff8ffe00000004 0xc101ff1ffc000000

def z1155 : W := mkw 0x571b6e9c00000030 0x00ae36dd38000000 0x87df8fce00000004 0xe10fbf1f9c000000

def z1156 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffffe00783f 0xfdfffffffffc00f0

def z1157 : W := mkw 0x35568001f7f0000f 0x806aad0003efe000 0xa73f8001fff80038 0xf54e7f0003fff000

def z1158 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x81ff87fe00000006 0xd103ff0ffc000000

def z1159 : W := mkw 0x48bb37bc00000070 0x0091766f78000000 0xc0ffb7fe00000006 0xc181ff6ffc000000

def z1160 : W := mkw 0x28f6800153f00007 0x8051ed0002a7e000 0x87ff80013ff80038 0xfd0fff00027ff000

def z1161 : W := mkw 0x5fbb7fbc000008f0 0x08bf76ff78000011 0xdffffffe00001987 0xffbffffffc000033

def z1162 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff880ffff8003d 0xfd7fff101ffff000

def z1163 : W := mkw 0x35568001b770000d 0x806aad00036ee000 0x87df80013e380020 0xa90fbf00027c7000

def z1164 : W := mkw 0x0208488800000020 0x0004109110000000 0x87ffc9ce00000005 0xfd0fff939c000000

def z1165 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xffffb1f1fff987be 0xffffff63e3fff30f

def z1166 : W := mkw 0x0200480008044000 0x0004009000100880 0x7f007e01fe07f87b 0x3efe00fc03fc0ff0

def z1167 : W := mkw 0x5fbb7fbc08044070 0x00bf76ff78100880 0xfffffffff807e07f 0xfffffffffff00fc0

def z1168 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x7ee071f1f9c787ff 0x7efdc0e3e3f38f0f

def z1169 : W := mkw 0x5fbb7fbce481917a 0x60bf76ff79c90322 0xfffffffec6c19997 0xfffffffffd8d8333

def z1170 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fff 0x1202471c7c0ff0ff

def z1171 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfff8001fff80020 0xe97fff0003fff000

def z1172 : W := mkw 0x3df69161f7f2854f 0xa07bed22c3efe50a 0xbfff81f1ffff87fc 0xff7fff03e3ffff0f

def z1173 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffff7fe00000006 0xd9bfffeffc000000

def z1174 : W := mkw 0x5fbb7fbc08055070 0x40bf76ff78100aa0 0xdffffffe0607f87f 0xffbffffffc0c0ff0

def z1175 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffff807e06f 0xfdfffffffff00fc0

def z1176 : W := mkw 0x3516a400b6711009 0xc06a2d48016ce220 0xff1fb600fe399832 0xb3fe3f6c01fc7330

def z1177 : W := mkw 0x3df69121f7f0814f 0xa07bed2243efe102 0xfffff1f1fff981bf 0xffffffe3e3fff303

def z1178 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xdffffffe38000007 0xfdbffffffc700000

def z1179 : W := mkw 0x0009029c00000030 0x0000120538000000 0x80ff81fe00000004 0xc101ff03fc000000

def z1180 : W := mkw 0x3df69121f7f0814f 0xa07bed2243efe102 0xffffb031fff987ff 0xffffff6063fff30f

def z1181 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc49ff393e67ef 0xef0db893fe727ccf

def z1182 : W := mkw 0x3df69121f7f0004f 0x807bed2243efe000 0xfffff1f1fff807ff 0xffffffe3e3fff00f

def z1183 : W := mkw 0x824c6ccb192f7624 0x510498d996325eec 0xfedc7fcff93ffe7f 0xfffdb8ff9ff27ffc

def z1184 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ff81fe01c007df 0xd701ff03fc03800f

def z1185 : W := mkw 0x5dbb13bc00000070 0x00bb762778000000 0xdffff1fe00000007 0xfdbfffe3fc000000

def z1186 : W := mkw 0x5fbb7fbc00008170 0x20bf76ff78000102 0xdffffffe00018187 0xffbffffffc000303

def z1187 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x79007e01fe07f87b 0x12f200fc03fc0ff0

def z1188 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc41cf393e666c 0xc90db8839e727ccc

def z1189 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x81ff8ffe00000004 0xe103ff1ffc000000

def z1190 : W := mkw 0x15000000a4000008 0x002a000001480000 0x7f007e01fe07f87b 0x3efe00fc03fc0ff0

def z1191 : W := mkw 0x35568001b770000d 0x806aad00036ee000 0x87ff80013ff80038 0xfd0fff00027ff000

def z1192 : W := mkw 0x824c488b192c6224 0x11049891163258c4 0x86dc49cf3938602d 0xed0db8939e7270c0

def z1193 : W := mkw 0x3df69121f7f0004f 0x807bed2243efe000 0xffffb031fff8003a 0xfdffff6063fff000

def z1194 : W := mkw 0x5fbb7fbc40808172 0x20bf76ff78810102 0xfffffffec1c187df 0xfffffffffd83830f

def z1195 : W := mkw 0x5fbb7fbca4011078 0x40bf76ff79480220 0xfffffffec601f87f 0xfffffffffd8c03f0

def z1196 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc09cf393e666c 0xe10db8139e727ccc

def z1197 : W := mkw 0x5dbb37bc00000070 0x00bb766f78000000 0xdfffb7fe00000006 0xfdbfff6ffc000000

def z1198 : W := mkw 0x820c48ca182e6620 0x1104189194305ccc 0x86dc49ce383e6665 0xed0db8939c707ccc

def z1199 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x9f1f80003e380020 0xbd3e3f00007c7000

def z1200 : W := mkw 0x5dbb37bc00000070 0x00bb766f78000000 0x81ff87fe00000004 0xc103ff0ffc000000

def z1201 : W := mkw 0x5fbb7fbc08044070 0x00bf76ff78100880 0xdffffffe00066047 0xfdbffffffc000cc0

def z1202 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe01c0001f 0xfdbffffffc038000

def z1203 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x873f80303ff807ff 0xf70e7f00607ff00f

def z1204 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00000007 0x19bffffffc000000

def z1205 : W := mkw 0x2056800113700005 0x8040ad000226e000 0x86df800139380028 0xed0dbf0002727000

def z1206 : W := mkw 0x5fbb7fbc08055070 0x40bf76ff78100aa0 0xdfffffff3807f86f 0xffbffffffe700ff0

def z1207 : W := mkw 0xa044804353fa2607 0x9140890086a7f44c 0x0000000001f80600 0x000000000003f00c

def z1208 : W := mkw 0x5fbb7fbc08055070 0x40bf76ff78100aa0 0xdffffffe00078007 0xfdbffffffc000f00

def z1209 : W := mkw 0x3df60001f5a0000e 0x807bec0003eb4000 0xbfff8001f9380028 0xfd7fff0003f27000

def z1210 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x87ff80013ff80028 0xed0fff00027ff000

def z1211 : W := mkw 0x1fba4888ac044028 0x003f749111580880 0xbfffc9cffe06607d 0xfd7fff939ffc0cc0

def z1212 : W := mkw 0x824c48cb59aee726 0x3104989196b35dce 0xa6fc49fff9ffe7ff 0xff4df893fff3ffcf

def z1213 : W := mkw 0x3db69120b6700049 0x807b6d22416ce000 0xdffff1f03e380027 0xfdbfffe3e07c7000

def z1214 : W := mkw 0xcae97fff498ee776 0x3195d2fffe931dce 0x78e07fffc1c7e7df 0x5ef1c0ffff838fcf

def z1215 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00000004 0xe9bffffffc000000

def z1216 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0x86ff800039f80000 0xc10dff000073f000

def z1217 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e0ffe07f87f 0xfefe00fc1ffc0ff0

def z1218 : W := mkw 0x5fbb7fbc40808172 0x20bf76ff78810102 0xfffffffec0018007 0xfdfffffffd800300

def z1219 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f207e31fe07f87f 0x7efe40fc63fc0ff0

def z1220 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xfffffffec0018017 0xfffffffffd800300

def z1221 : W := mkw 0x4abb5bbc00000070 0x009576b778000000 0xdefff9fe00000007 0xfdbdfff3fc000000

def z1222 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xffdfffcffe07f87b 0xbfffbfff9ffc0ff0

def z1223 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00000002 0xb9bffffffc000000

def z1224 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc09cf3938662c 0xed0db8139e7270cc

def z1225 : W := mkw 0x88ed93ff53faaff7 0x3911db27fea7f55f 0x80ff81fe01f80784 0xc101ff03fc03f00f

def z1226 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdefff1fe00000007 0xddbdffe3fc000000

def z1227 : W := mkw 0x5fbb7fbca4011078 0x40bf76ff79480220 0xfffffffec0018007 0xfdfffffffd800300

def z1228 : W := mkw 0x35568001b770000d 0x806aad00036ee000 0x87df80003f380020 0xe10fbf00007e7000

def z1229 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0xa71f8001fe380038 0xa14e3f0003fc7000

def z1230 : W := mkw 0x5fbb7fbcac055078 0x40bf76ff79580aa0 0xfffffffefe01f837 0xfffffffffdfc03f0

def z1231 : W := mkw 0x5dbb13bca4000078 0x00bb762779480000 0xbfff81fffe00003c 0xfd7fff03fffc0000

def z1232 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xfffff031ffff87ff 0xffffffe063ffff0f

def z1233 : W := mkw 0x35568001b770000d 0x806aad00036ee000 0x871f80013f380028 0xa10e3f00027e7000

def z1234 : W := mkw 0x3df68001b770000d 0x807bed00036ee000 0x9fff80013f380028 0xfd3fff00027e7000

def z1235 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x01238e3e07f87fb6 0xf202471c7c0ff0ff

def z1236 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ff89fe00000005 0xe501ff13fc000000

def z1237 : W := mkw 0x571b6e9cac055038 0x40ae36dd39580aa0 0xffdfffcffe07f87f 0xffffbfff9ffc0ff0

def z1238 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe00007847 0xffbffffffc0000f0

def z1239 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x87dc4fcf3f3e7e6d 0xed0fb89f9e7e7cfc

def z1240 : W := mkw 0x824c6ccb192f7624 0x510498d996325eec 0xc6dc79cf393fe66d 0xed8db8f39e727fcc

def z1241 : W := mkw 0x35168000b6700009 0x806a2d00016ce000 0x873f80003e380020 0xf50e7f00007c7000

def z1242 : W := mkw 0x5fbb7fbc00011070 0x40bf76ff78000220 0xdffffffe00019807 0xffbffffffc000330

def z1243 : W := mkw 0x0009029c00000030 0x0000120538000000 0x81ff8ffe00000007 0xf503ff1ffc000000

def z1244 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86dc09ce3938666d 0xe50db8139c7270cc

def z1245 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c787dc 0x4af1c0e3e3838f0f

def z1246 : W := mkw 0xc2097fbe080c6270 0x118412ff7c1018c4 0x40007ffe00006007 0x008000fffc0000c0

def z1247 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f878 0x2afe00fc03fc0ff0

def z1248 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdefff9fe00000005 0xedbdfff3fc000000

def z1249 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x5923fe3e07f87fff 0xfeb247fc7c0ff0ff

def z1250 : W := mkw 0x5fbb5bbc00000070 0x00bf76b778000000 0x9fffc9fe00000005 0xfd3fff93fc000000

def z1251 : W := mkw 0x48bb13bc00000070 0x0091762778000000 0x80ff81fe01c00784 0xc101ff03fc03800f

def z1252 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0xfefc71f1c1c787df 0xfffdf8e3e3838f0f

def z1253 : W := mkw 0x08e0116141828546 0x2011c022c283050a 0x78e071f1c1c787cd 0x4cf1c0e3e3838f0f

def z1254 : W := mkw 0x3df68001f7f0000f 0x807bed0003efe000 0xbfdf8001fe380038 0xbd7fbf0003fc7000

def z1255 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01ffc7fffb 0x3efe00fc03ff8fff

def z1256 : W := mkw 0x804c00cb112a2624 0x110098019622544c 0x86dc09cf3938666d 0xed0db8139e7270cc

def z1257 : W := mkw 0x5fbb7fbca4011078 0x40bf76ff79480220 0xffffffffc607985f 0xffffffffff8c0f30

def z1258 : W := mkw 0x08e4116151a28546 0x2011c822c2a3450a 0xfefc71f1f9c787df 0x5ffdf8e3e3f38f0f

def z1259 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0x9fff8ffe00000004 0xfd3fff1ffc000000

def z1260 : W := mkw 0x15002400ac055008 0x402a004801580aa0 0x7f003601fe07f87a 0x3efe006c03fc0ff0

def z1261 : W := mkw 0x0001821602582a91 0x080003042c04b055 0x07238e3f3ff87fff 0xfe0e471c7e7ff0ff

def z1262 : W := mkw 0x3df68001f7f1100f 0xc07bed0003efe220 0xbfff8001fff99838 0xff7fff0003fff330

def z1263 : W := mkw 0x5fbb7fbc00000070 0x00bf76ff78000000 0xdffffffe0600003f 0xfdbffffffc0c0000

def z1264 : W := mkw 0x3df68041f7f2850f 0xa07bed0083efe50a 0xbfffc1c1ffff87fd 0xff7fff8383ffff0f

def z1265 : W := mkw 0x17006c00ac055008 0x402e00d801580aa0 0x7f007e01fe07f853 0x1afe00fc03fc0ff0

def z1266 : W := mkw 0x824c48cb192e6624 0x1104989196325ccc 0x86fc49cf39fe667d 0xfd0df8939e73fccc

def z1267 : W := mkw 0x421b4a9c00000030 0x0084369538000000 0x86dfc9ce00000005 0xed0dbf939c000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z2,z3,z7,z6]),(0,[z0,z8,z1,z2,z9,z4,z6]),(0,[z0,z1,z2,z3,z10,z4,z6])],[(1,[z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z12,z13,z4,z6]),(0,[z14,z0,z1,z2,z3,z15,z6]),(0,[z0,z16,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z17,z3,z4,z6]),(0,[z0,z18,z1,z2,z3,z4,z6])],[(0,[z0,z19,z1,z2,z3,z4,z6]),(0,[z0,z1,z20,z2,z21,z4,z6]),(0,[z0,z1,z22,z2,z3,z4,z23]),(0,[z0,z24,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z25,z6]),(0,[z0,z1,z26,z2,z3,z4,z6]),(0,[z0,z1,z27,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z28,z6]),(0,[z0,z1,z2,z3,z4,z29,z6]),(0,[z0,z1,z2,z21,z4,z30,z6]),(0,[z0,z31,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z33,z34,z6]),(0,[z0,z1,z2,z3,z4,z6,z35]),(0,[z0,z1,z2,z36,z3,z4,z37])],[(0,[z0,z1,z38,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z39,z6])],[(0,[z40,z0,z1,z41,z3,z4,z6]),(0,[z42,z0,z8,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z43,z44,z6]),(0,[z0,z1,z2,z3,z21,z43,z6]),(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z0,z46,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z4,z6]),(0,[z0,z1,z2,z48,z4,z30,z6]),(0,[z49,z0,z1,z2,z3,z4,z6]),(0,[z50,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z21,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z51])]],
   [[(0,[z52,z0,z1,z2,z12,z4,z6]),(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z0,z54,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z55,z3,z4,z6])],[(0,[z0,z1,z56,z2,z3,z4,z6]),(0,[z0,z57,z1,z2,z3,z4,z6]),(1,[z58,z1,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z12,z4,z6]),(1,[z0,z1,z2,z3,z60,z6]),(0,[z0,z1,z61,z2,z3,z4,z6])],[(0,[z62,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z63,z64,z3,z4,z6]),(0,[z0,z65,z1,z2,z3,z4,z6]),(0,[z0,z1,z63,z2,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z67,z3,z4,z6]),(0,[z0,z68,z1,z2,z3,z33,z6]),(0,[z0,z69,z1,z2,z3,z4,z70]),(0,[z0,z71,z1,z2,z3,z4,z6])],[(0,[z72,z0,z1,z2,z3,z73,z6]),(0,[z74,z0,z1,z2,z3,z4,z6])],[(0,[z0,z75,z1,z2,z3,z43,z6])],[(0,[z76,z0,z1,z2,z21,z4,z6]),(0,[z0,z77,z1,z2,z12,z4,z6]),(0,[z0,z2,z3,z78,z4,z39,z6]),(0,[z0,z1,z2,z79,z3,z4,z6]),(0,[z0,z80,z1,z2,z3,z43,z6]),(0,[z0,z81,z1,z2,z3,z4,z6]),(0,[z0,z1,z22,z2,z82,z4,z6]),(0,[z0,z8,z1,z2,z3,z4,z70])],[(0,[z0,z1,z2,z83,z3,z4,z6])],[(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z0,z85,z1,z2,z3,z4,z6]),(0,[z76,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z78,z4,z6]),(0,[z86,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z87,z3,z4,z6])]],
   [[(0,[z40,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z12,z88,z4,z6]),(0,[z0,z69,z1,z3,z4,z6,z23])],[(0,[z89,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z90]),(0,[z0,z1,z41,z2,z3,z91,z6]),(0,[z0,z1,z2,z3,z4,z92,z6]),(0,[z0,z1,z93,z2,z3,z4,z6]),(0,[z0,z94,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z58,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z95,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z43,z6,z23]),(0,[z0,z1,z2,z97,z3,z4,z6])],[(0,[z98,z0,z1,z2,z4,z37,z6]),(0,[z0,z1,z2,z3,z4,z99,z6]),(0,[z100,z0,z1,z2,z3,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z70,z6]),(0,[z0,z8,z75,z1,z2,z3,z4])],[(0,[z0,z103,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z104,z4,z6])],[(0,[z0,z105,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z107,z6]),(0,[z76,z0,z1,z2,z3,z4,z108]),(0,[z0,z1,z109,z2,z21,z4,z6]),(0,[z0,z1,z2,z110,z3,z4,z6])],[(0,[z0,z1,z2,z111,z3,z4,z6]),(0,[z0,z112,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z113]),(0,[z0,z1,z2,z3,z4,z114,z6]),(0,[z0,z1,z2,z115,z3,z4,z6])],[(0,[z116,z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z118,z3,z4,z6]),(0,[z0,z1,z119,z2,z3,z4,z6])],[(0,[z0,z105,z1,z2,z120,z4,z6]),(0,[z0,z121,z1,z2,z3,z43,z6])]],
   [[(0,[z0,z1,z2,z122,z3,z4,z6]),(0,[z0,z123,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z124]),(0,[z0,z1,z2,z3,z4,z125,z6]),(0,[z0,z1,z2,z126,z3,z43,z6])],[(0,[z0,z127,z1,z2,z3,z4,z6]),(0,[z0,z1,z63,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z128,z6]),(0,[z0,z1,z2,z129,z3,z4,z6]),(0,[z130,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z36,z3,z4,z131])],[(0,[z132,z0,z1,z2,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z12,z4,z37,z6]),(0,[z0,z1,z2,z3,z133,z4,z6]),(0,[z0,z1,z2,z134,z3,z4,z6]),(0,[z135,z0,z1,z2,z3,z33,z6])],[(1,[z0,z1,z136,z3,z4,z6]),(0,[z0,z1,z2,z3,z73,z43,z6]),(0,[z0,z1,z2,z3,z4,z6,z137]),(0,[z0,z138,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z139,z6]),(0,[z0,z140,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z88,z4,z15])],[(0,[z0,z1,z2,z21,z73,z4,z6]),(0,[z0,z1,z2,z3,z4,z108,z23]),(0,[z116,z0,z1,z2,z3,z33,z6]),(0,[z0,z141,z1,z2,z3,z4,z6]),(1,[z0,z121,z2,z3,z4,z142]),(0,[z0,z1,z143,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z70,z6,z23])],[(0,[z0,z1,z41,z144,z3,z4,z6]),(0,[z0,z31,z2,z3,z21,z4,z6]),(0,[z0,z145,z1,z2,z3,z4,z146]),(0,[z0,z1,z22,z3,z4,z43,z6]),(0,[z0,z1,z2,z3,z147,z33,z6])],[(0,[z148,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z144,z3,z33,z6]),(0,[z0,z149,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z60,z4,z6])],[(1,[z0,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z32,z108]),(0,[z0,z1,z2,z21,z151,z4,z6]),(0,[z0,z152,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z23])]],
   [[(0,[z0,z1,z2,z153,z3,z4,z6]),(0,[z0,z1,z2,z154,z21,z4,z6]),(0,[z0,z69,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z155,z6])],[(0,[z0,z1,z41,z2,z21,z4,z6]),(1,[z76,z1,z2,z3,z4,z108]),(0,[z0,z1,z2,z156,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z157]),(0,[z0,z1,z2,z3,z4,z158,z6]),(0,[z40,z1,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z154,z3,z4,z6]),(0,[z0,z1,z2,z3,z159,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z142]),(0,[z0,z1,z2,z160,z3,z4,z6])],[(0,[z161,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z162,z4,z6]),(0,[z0,z1,z2,z3,z4,z163,z6]),(0,[z0,z1,z2,z164,z3,z4,z6]),(0,[z0,z1,z165,z2,z3,z4,z6]),(0,[z0,z8,z1,z2,z12,z4,z6])],[(0,[z52,z0,z166,z2,z3,z4,z6]),(0,[z40,z1,z166,z2,z3,z4,z6]),(0,[z167,z0,z1,z2,z3,z4,z6]),(0,[z168,z0,z1,z2,z3,z4,z6]),(0,[z0,z169,z1,z144,z3,z4,z6]),(1,[z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z170,z2,z3,z4,z6]),(0,[z0,z1,z2,z9,z12,z4,z6]),(0,[z0,z1,z2,z3,z171,z4,z6]),(0,[z0,z1,z2,z2,z3,z33,z6])],[(0,[z62,z1,z166,z2,z3,z4,z6]),(0,[z0,z1,z166,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z172,z6]),(0,[z0,z1,z2,z173,z3,z4,z6]),(0,[z98,z0,z1,z2,z3,z43,z6]),(0,[z174,z0,z1,z2,z21,z4,z6]),(0,[z175,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z176,z4,z6]),(0,[z135,z0,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z37,z6]),(0,[z0,z1,z2,z9,z3,z48,z6])],[(0,[z1,z2,z83,z3,z13,z4,z6]),(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z6,z177]),(0,[z0,z1,z2,z12,z3,z33,z6]),(0,[z0,z1,z2,z3,z178,z43,z6])],[(0,[z174,z0,z1,z2,z3,z4,z6]),(0,[z179,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z6,z180]),(0,[z0,z1,z2,z3,z4,z181,z6]),(0,[z0,z8,z1,z2,z3,z4,z37])]],
   [[(0,[z0,z169,z1,z2,z21,z4,z6]),(1,[z0,z31,z2,z21,z4,z6]),(0,[z0,z182,z1,z2,z21,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z32,z23]),(0,[z0,z1,z2,z184,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z185]),(0,[z0,z1,z2,z3,z186,z4,z6]),(0,[z0,z1,z2,z3,z4,z187,z6])],[(0,[z188,z0,z1,z2,z3,z4,z11]),(0,[z42,z0,z1,z2,z83,z4,z6]),(0,[z72,z0,z75,z1,z2,z3,z6]),(0,[z189,z0,z1,z2,z3,z4,z6]),(1,[z0,z190,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z191])],[(0,[z0,z1,z192,z2,z3,z4,z6]),(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z0,z182,z1,z2,z3,z4,z6]),(0,[z0,z1,z194,z2,z3,z33,z6]),(0,[z0,z195,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z78,z44,z6]),(0,[z0,z1,z2,z3,z196,z4,z6]),(0,[z0,z190,z1,z2,z12,z4,z6]),(0,[z197,z0,z1,z2,z3,z4,z6])],[(0,[z62,z52,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z198,z3,z4,z6]),(0,[z174,z0,z1,z2,z3,z4,z108]),(1,[z0,z1,z2,z3,z4,z199]),(0,[z116,z0,z2,z144,z3,z4,z6]),(0,[z0,z31,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z43,z43,z6]),(0,[z0,z1,z2,z200,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z201])],[(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z0,z1,z2,z3,z203,z4,z6]),(0,[z0,z1,z2,z3,z4,z204,z6]),(0,[z0,z145,z2,z3,z78,z4,z6]),(0,[z0,z1,z20,z3,z4,z43,z6]),(0,[z0,z1,z2,z205,z3,z4,z6])],[(0,[z0,z1,z2,z3,z117,z4,z6])],[(1,[z0,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z64,z12,z4,z6]),(0,[z0,z1,z2,z3,z33,z78,z6]),(0,[z0,z1,z2,z3,z207,z43,z6]),(0,[z0,z1,z2,z207,z4,z37,z6]),(0,[z0,z1,z2,z3,z208,z4,z6]),(0,[z0,z1,z2,z3,z4,z209,z6])]],
   [[(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z212,z4,z6]),(0,[z0,z1,z2,z3,z4,z213,z6]),(0,[z0,z1,z2,z21,z207,z4,z6]),(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z0,z1,z22,z2,z3,z4,z70]),(0,[z0,z1,z2,z214,z4,z6,z215])],[(0,[z216,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z32])],[(0,[z0,z1,z2,z3,z21,z4,z6]),(0,[z0,z1,z2,z217,z3,z4,z6]),(0,[z0,z218,z1,z2,z3,z33,z6]),(0,[z0,z8,z1,z2,z48,z4,z6])],[(1,[z40,z1,z41,z3,z4,z6]),(0,[z0,z145,z54,z2,z3,z4,z6])],[(0,[z0,z1,z219,z2,z3,z4,z6]),(0,[z0,z145,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z220,z6]),(1,[z0,z1,z221,z3,z4,z6])],[(0,[z0,z1,z2,z3,z222,z4,z6]),(0,[z0,z1,z2,z3,z4,z223,z6]),(0,[z0,z63,z2,z144,z3,z4,z6]),(0,[z0,z1,z2,z21,z224,z4,z6]),(0,[z0,z225,z1,z2,z3,z4,z6])],[(0,[z0,z1,z226,z2,z3,z4,z6]),(0,[z0,z227,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z163,z6,z228]),(0,[z0,z1,z2,z3,z229,z33,z6]),(0,[z0,z1,z2,z3,z230,z4,z6]),(0,[z0,z1,z22,z2,z3,z231,z6])],[(0,[z0,z105,z1,z2,z3,z43,z6]),(0,[z0,z232,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z2,z12,z4,z6]),(0,[z14,z0,z1,z2,z3,z44,z6]),(1,[z0,z233,z1,z2,z3,z6]),(0,[z0,z1,z2,z12,z4,z70,z6]),(0,[z0,z1,z2,z234,z3,z4,z6])]],
   [[(0,[z235,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z36,z3,z33,z6]),(0,[z0,z75,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z214,z3,z4,z6])],[(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z42,z98,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z237]),(0,[z0,z54,z1,z2,z21,z4,z6]),(0,[z238,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z239]),(0,[z0,z80,z1,z2,z3,z4,z6])],[(0,[z40,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z240,z2,z3,z4,z6]),(0,[z0,z169,z63,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z241,z4,z6])],[(0,[z62,z0,z1,z2,z21,z4,z6]),(0,[z242,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z91,z4,z6]),(1,[z72,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z3,z4,z6,z243])],[(0,[z40,z0,z1,z2,z3,z4,z6]),(0,[z40,z0,z1,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z244,z6]),(0,[z0,z1,z2,z21,z245,z4,z6]),(0,[z0,z1,z2,z21,z4,z15,z6]),(0,[z0,z1,z246,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z247,z6])],[(0,[z0,z1,z2,z3,z4,z6,z248]),(0,[z0,z249,z1,z2,z3,z4,z6])],[(0,[z0,z1,z250,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z251,z4,z6]),(0,[z0,z1,z252,z2,z3,z4,z6]),(0,[z253,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z254,z6]),(1,[z0,z1,z2,z36,z4,z37])],[(0,[z179,z0,z2,z12,z3,z4,z6])]],
   [[(0,[z52,z0,z1,z2,z3,z33,z6]),(0,[z0,z105,z2,z144,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z11]),(0,[z0,z1,z2,z3,z4,z6,z255]),(0,[z0,z1,z2,z256,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z257,z6]),(0,[z0,z169,z1,z2,z3,z43,z6]),(0,[z0,z121,z1,z2,z21,z4,z6])],[(1,[z62,z166,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z258,z6]),(0,[z72,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z259,z3,z4,z6]),(0,[z0,z1,z2,z126,z21,z4,z6]),(0,[z0,z1,z2,z3,z260,z4,z6]),(0,[z0,z1,z2,z3,z33,z70,z6]),(0,[z0,z1,z2,z3,z261,z4,z6])],[(0,[z0,z1,z2,z3,z4,z262,z6]),(0,[z0,z121,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z263,z4,z6]),(0,[z0,z1,z2,z3,z264,z4,z6]),(0,[z14,z0,z1,z2,z21,z4,z6]),(0,[z0,z265,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z215]),(0,[z0,z1,z2,z12,z33,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z23]),(0,[z0,z1,z2,z3,z266,z4,z6]),(0,[z0,z1,z2,z126,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z267,z6])],[(0,[z0,z1,z2,z3,z268,z4,z6]),(0,[z0,z1,z2,z3,z269,z4,z6]),(1,[z0,z1,z2,z3,z4,z146]),(0,[z0,z1,z2,z3,z4,z6,z270]),(0,[z0,z271,z1,z2,z3,z4,z6]),(0,[z0,z1,z272,z2,z3,z4,z6])],[(0,[z0,z273,z1,z2,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z274,z3,z4,z6]),(0,[z0,z1,z22,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z73,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z142]),(0,[z0,z1,z2,z3,z4,z6,z275]),(0,[z0,z1,z20,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z276]),(0,[z116,z0,z1,z2,z203,z4,z6]),(0,[z0,z75,z1,z2,z3,z78,z6]),(0,[z0,z31,z2,z3,z4,z32,z6]),(1,[z135,z0,z1,z3,z33,z6]),(0,[z277,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z278,z4,z6]),(0,[z116,z0,z1,z144,z3,z4,z6]),(0,[z0,z75,z1,z2,z3,z4,z142]),(0,[z0,z1,z2,z3,z4,z6,z279]),(0,[z0,z1,z2,z3,z88,z4,z215])],[(0,[z42,z0,z1,z2,z13,z4,z6]),(0,[z0,z1,z2,z3,z4,z280,z6])],[(0,[z281,z0,z1,z2,z3,z4,z6]),(0,[z0,z282,z1,z2,z3,z4,z6]),(0,[z135,z0,z1,z2,z21,z4,z6]),(0,[z283,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z284,z6]),(0,[z0,z1,z2,z3,z285,z4,z6]),(1,[z0,z286,z1,z126,z4,z6]),(0,[z0,z1,z2,z287,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z288,z6])],[(0,[z188,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z1,z2,z12,z4,z6]),(0,[z0,z286,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z289,z3,z4,z6]),(0,[z0,z1,z2,z290,z3,z4,z6]),(1,[z0,z1,z2,z4,z6,z291])],[(1,[z0,z1,z2,z3,z4,z292]),(0,[z0,z293,z1,z2,z3,z4,z6]),(0,[z116,z0,z1,z2,z21,z4,z6]),(0,[z0,z294,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z295,z3,z4,z6]),(0,[z0,z1,z2,z3,z88,z4,z32])],[(0,[z296,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z297,z3,z4,z6]),(0,[z0,z1,z2,z3,z298,z4,z6])],[(0,[z0,z166,z2,z144,z3,z4,z6]),(0,[z98,z0,z1,z2,z21,z4,z6]),(0,[z299,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z23]),(0,[z0,z300,z1,z2,z3,z4,z6])]],
   [[(0,[z72,z1,z2,z3,z4,z44,z6]),(0,[z14,z1,z2,z3,z73,z4,z6]),(0,[z0,z1,z2,z3,z33,z155,z6]),(0,[z0,z1,z2,z9,z4,z37,z6])],[(0,[z0,z1,z301,z2,z3,z4,z6]),(0,[z98,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z108,z6]),(0,[z0,z1,z63,z2,z3,z33,z6]),(0,[z0,z1,z2,z21,z4,z6,z131]),(0,[z0,z1,z2,z3,z78,z43,z6]),(0,[z0,z121,z1,z2,z260,z4,z6]),(0,[z0,z1,z2,z302,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z303,z6]),(0,[z0,z1,z2,z304,z3,z4,z6]),(0,[z0,z75,z1,z2,z115,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6,z305]),(0,[z0,z1,z2,z306,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z307,z6]),(0,[z0,z54,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z33,z6,z142]),(0,[z0,z1,z2,z3,z178,z4,z6])],[],[(0,[z62,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z41,z2,z3,z25,z6]),(0,[z0,z190,z2,z3,z21,z4,z6]),(0,[z0,z1,z2,z308,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z309]),(0,[z0,z121,z1,z2,z3,z4,z142]),(0,[z0,z1,z2,z3,z4,z6,z310])],[(0,[z0,z1,z2,z3,z78,z73,z6]),(0,[z0,z1,z2,z21,z4,z43,z6]),(0,[z0,z1,z2,z12,z4,z39,z6]),(0,[z0,z1,z2,z9,z3,z30,z6]),(0,[z0,z1,z311,z2,z3,z4,z6])],[(0,[z52,z1,z2,z64,z3,z4,z6]),(0,[z0,z1,z2,z312,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z228]),(0,[z116,z16,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z308,z3,z4,z6]),(0,[z0,z1,z20,z2,z12,z4,z6]),(0,[z0,z31,z1,z2,z3,z313,z6]),(0,[z0,z314,z1,z2,z3,z4,z6])],[(0,[z188,z0,z206,z2,z3,z4,z6]),(0,[z188,z1,z2,z64,z3,z4,z6]),(0,[z0,z1,z2,z315,z3,z4,z6]),(0,[z0,z1,z2,z12,z21,z4,z6]),(0,[z0,z1,z2,z316,z3,z4,z6])]],
   [[(0,[z0,z169,z105,z2,z3,z4,z6]),(0,[z179,z0,z1,z2,z21,z4,z6]),(0,[z0,z69,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z6,z317])],[(0,[z0,z1,z318,z2,z3,z4,z6]),(0,[z0,z1,z2,z319,z3,z4,z6]),(0,[z0,z1,z109,z2,z3,z4,z6]),(0,[z0,z320,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z142,z23])],[(0,[z116,z0,z1,z2,z3,z321,z6]),(1,[z0,z1,z2,z21,z33,z6]),(1,[z0,z69,z1,z3,z4,z23])],[(1,[z0,z1,z2,z3,z4,z322]),(0,[z0,z1,z2,z3,z207,z4,z6]),(0,[z323,z0,z1,z2,z3,z43,z6]),(0,[z0,z8,z1,z2,z3,z33,z6])],[(1,[z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z324,z2,z3,z4,z6]),(0,[z0,z1,z2,z9,z3,z33,z6])],[(0,[z0,z1,z64,z144,z3,z4,z6]),(0,[z0,z1,z2,z3,z325,z4,z6]),(0,[z0,z1,z2,z3,z4,z32,z6])],[(0,[z0,z1,z326,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z37,z6]),(1,[z0,z8,z1,z2,z4,z131]),(0,[z327,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z328,z4,z6]),(0,[z0,z1,z2,z3,z33,z30,z6]),(0,[z329,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z330]),(0,[z331,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z332,z3,z4,z6]),(0,[z0,z1,z2,z3,z224,z4,z6]),(0,[z0,z1,z2,z3,z33,z39,z6]),(0,[z0,z1,z2,z3,z4,z313,z6])],[(0,[z62,z0,z1,z2,z333,z4,z6]),(0,[z0,z105,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z334,z4,z6]),(0,[z14,z0,z1,z2,z3,z73,z6]),(0,[z76,z0,z1,z2,z12,z4,z6]),(0,[z335,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z194,z3,z207,z4,z6]),(0,[z0,z336,z1,z2,z3,z33,z6]),(0,[z0,z69,z1,z2,z3,z337,z6])],[(0,[z1,z2,z3,z4,z108,z6,z228]),(0,[z0,z1,z2,z3,z4,z108,z142]),(0,[z338,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z303]),(0,[z0,z1,z2,z3,z43,z244,z6]),(0,[z0,z1,z2,z3,z48,z33,z6])],[(0,[z0,z105,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z339,z4,z6]),(0,[z42,z0,z1,z2,z4,z37,z6]),(0,[z0,z340,z1,z2,z3,z4,z6]),(0,[z0,z1,z341,z2,z3,z4,z6]),(0,[z0,z190,z1,z2,z3,z33,z6]),(0,[z0,z342,z1,z2,z3,z4,z6]),(0,[z0,z69,z1,z22,z3,z4,z6]),(0,[z0,z343,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z344])],[(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z346,z6]),(0,[z0,z1,z2,z347,z3,z4,z6]),(0,[z0,z348,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z349,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z350]),(0,[z135,z0,z1,z2,z3,z43,z6])],[(0,[z0,z1,z2,z351,z3,z4,z6]),(0,[z0,z145,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z352]),(0,[z0,z353,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z354]),(0,[z0,z355,z1,z2,z3,z4,z6])],[(0,[z0,z1,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z33,z6]),(0,[z0,z1,z2,z3,z4,z356,z6]),(1,[z14,z1,z2,z3,z73,z6]),(0,[z116,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z357,z2,z3,z4,z6]),(0,[z0,z358,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z359,z6])],[(0,[z0,z1,z360,z2,z3,z4,z6]),(0,[z0,z1,z2,z64,z3,z33,z6]),(0,[z361,z0,z1,z2,z3,z4,z6]),(0,[z0,z362,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z245,z4,z6]),(0,[z0,z1,z2,z115,z12,z4,z6]),(0,[z0,z1,z2,z3,z363,z4,z6])]],
   [[(0,[z364,z0,z1,z2,z3,z4,z6]),(0,[z365,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z144,z3,z43,z6]),(0,[z0,z1,z2,z3,z4,z366,z6]),(0,[z0,z1,z2,z367,z3,z4,z6]),(0,[z0,z31,z1,z2,z118,z4,z6]),(0,[z0,z1,z2,z115,z3,z48,z6]),(0,[z0,z75,z1,z2,z3,z4,z15])],[(1,[z52,z105,z2,z3,z4,z6]),(1,[z0,z75,z1,z2,z3,z215])],[(0,[z368,z0,z1,z2,z3,z4,z6]),(0,[z1,z166,z2,z64,z3,z4,z6]),(1,[z98,z1,z2,z83,z4,z6]),(0,[z0,z1,z2,z122,z12,z4,z6]),(0,[z369,z0,z1,z2,z3,z4,z6])],[(0,[z62,z0,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z13,z207,z4,z6]),(0,[z174,z1,z2,z3,z4,z6,z228]),(0,[z0,z1,z2,z370,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z371,z6]),(0,[z0,z1,z2,z372,z3,z4,z6]),(0,[z0,z373,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z6,z243]),(0,[z0,z1,z2,z3,z6,z374,z131])],[(0,[z375,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z73,z4,z6]),(0,[z376,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z22,z3,z4,z70,z6]),(0,[z0,z1,z2,z3,z4,z377,z6])],[(0,[z0,z233,z1,z2,z3,z6,z228]),(0,[z0,z169,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z378,z6]),(0,[z376,z0,z1,z2,z3,z4,z6]),(0,[z0,z379,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z43,z6]),(0,[z0,z380,z1,z2,z3,z4,z6])],[(0,[z62,z0,z1,z2,z3,z28,z6]),(1,[z0,z1,z2,z312,z4,z6]),(0,[z0,z381,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z2,z3,z33,z6]),(0,[z0,z382,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z36,z4,z6]),(0,[z0,z1,z2,z383,z3,z4,z6]),(0,[z0,z1,z2,z36,z4,z37,z6]),(0,[z0,z1,z2,z3,z384,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z215]),(0,[z0,z1,z2,z3,z385,z4,z6])]],
   [[(0,[z105,z1,z166,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z3,z43,z6]),(0,[z0,z1,z2,z386,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z387,z6]),(0,[z0,z1,z388,z2,z3,z4,z6])],[(0,[z174,z76,z1,z2,z3,z4,z6]),(0,[z179,z0,z1,z2,z3,z43,z6])],[(0,[z0,z1,z2,z21,z4,z44,z6]),(0,[z0,z169,z1,z2,z389,z4,z6]),(1,[z0,z2,z12,z21,z4,z6]),(0,[z0,z1,z2,z12,z297,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z390]),(0,[z0,z1,z2,z3,z4,z30,z6]),(0,[z0,z8,z1,z2,z3,z88,z4])],[(0,[z391,z0,z1,z2,z3,z4,z6])],[(0,[z1,z41,z2,z64,z3,z4,z6]),(0,[z0,z392,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z393]),(0,[z0,z1,z194,z2,z3,z43,z6])],[(0,[z0,z1,z41,z2,z12,z4,z6]),(0,[z0,z1,z2,z394,z3,z4,z6]),(0,[z0,z2,z3,z21,z4,z6,z142]),(0,[z0,z1,z165,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z33,z88,z6]),(0,[z0,z8,z395,z2,z3,z4,z6])],[(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z108,z6]),(0,[z0,z1,z2,z397,z3,z4,z6]),(0,[z0,z31,z1,z2,z3,z43,z6]),(0,[z0,z398,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z115,z48,z4,z6]),(1,[z0,z395,z2,z3,z4,z6])],[(0,[z0,z1,z166,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z399]),(0,[z0,z1,z2,z3,z4,z6,z400]),(0,[z0,z1,z2,z3,z4,z6,z401])]],
   [[(0,[z0,z1,z402,z2,z3,z4,z6]),(0,[z0,z1,z2,z403,z3,z4,z6])],[(0,[z174,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z404,z6]),(0,[z0,z1,z2,z12,z4,z6,z309]),(0,[z0,z75,z1,z2,z3,z39,z6]),(0,[z0,z8,z405,z2,z3,z4,z6])],[(0,[z72,z0,z1,z2,z3,z33,z6]),(0,[z406,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z407,z4,z6]),(0,[z0,z1,z2,z3,z4,z408,z6]),(0,[z0,z1,z409,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z70,z6]),(0,[z0,z1,z2,z410,z3,z4,z6])],[(0,[z0,z1,z2,z411,z3,z4,z6]),(0,[z0,z1,z2,z3,z389,z4,z6]),(0,[z0,z1,z2,z3,z4,z412,z6]),(0,[z0,z1,z194,z2,z3,z285,z6]),(0,[z0,z8,z1,z2,z126,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z131])],[(0,[z0,z1,z2,z3,z413,z4,z6]),(0,[z0,z54,z1,z2,z156,z4,z6]),(0,[z0,z1,z2,z3,z78,z4,z6]),(0,[z414,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z415,z2,z3,z4,z6]),(0,[z0,z416,z1,z2,z3,z4,z6]),(0,[z417,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z418,z4,z6]),(0,[z0,z54,z1,z2,z3,z4,z6]),(0,[z0,z145,z1,z2,z3,z43,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z420,z2,z3,z4,z6]),(1,[z0,z1,z22,z3,z43,z6]),(0,[z421,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z22,z2,z3,z33,z6])],[(0,[z422,z0,z1,z2,z3,z4,z6]),(0,[z14,z0,z75,z1,z2,z3,z6]),(0,[z76,z0,z1,z2,z3,z4,z228]),(0,[z0,z1,z2,z3,z423,z43,z6])]],
   [[(0,[z62,z0,z1,z2,z3,z4,z6]),(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z68,z1,z2,z3,z4,z6]),(0,[z0,z1,z424,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z207,z4,z6]),(0,[z0,z1,z2,z3,z425,z4,z6])],[(0,[z0,z426,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z120,z3,z4,z6]),(0,[z0,z427,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z228]),(0,[z0,z1,z2,z3,z33,z108,z6]),(0,[z428,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z125,z6]),(1,[z0,z1,z272,z3,z4,z6]),(0,[z0,z429,z1,z2,z3,z4,z6])],[(0,[z430,z0,z1,z2,z3,z4,z6]),(0,[z0,z431,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z228]),(0,[z432,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z32,z6]),(0,[z0,z1,z2,z36,z3,z43,z6])],[(1,[z0,z1,z2,z106,z4,z6]),(0,[z188,z0,z1,z2,z3,z4,z322]),(0,[z0,z1,z2,z3,z433,z4,z6]),(0,[z283,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z434,z4,z6])],[(0,[z188,z0,z1,z2,z3,z33,z6]),(0,[z42,z1,z2,z3,z13,z4,z6]),(0,[z0,z1,z2,z3,z4,z146,z6]),(0,[z0,z286,z1,z2,z3,z33,z6])],[(1,[z0,z1,z2,z3,z4,z435]),(0,[z0,z1,z2,z436,z3,z4,z6])],[(1,[z0,z1,z2,z120,z4,z6]),(0,[z0,z1,z437,z2,z3,z4,z6]),(1,[z0,z1,z2,z438,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z439]),(1,[z0,z1,z2,z3,z313,z6]),(0,[z0,z1,z2,z440,z3,z4,z6]),(0,[z0,z75,z1,z2,z36,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z441])],[(0,[z62,z0,z1,z442,z3,z4,z6]),(0,[z323,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z443,z3,z4,z6])]],
   [[(0,[z62,z0,z1,z2,z3,z278,z6]),(0,[z0,z1,z444,z2,z3,z4,z6]),(0,[z0,z1,z2,z126,z83,z4,z6]),(0,[z0,z1,z2,z3,z4,z445,z6]),(0,[z0,z1,z2,z3,z43,z6,z23]),(0,[z102,z0,z1,z2,z3,z4,z6])],[(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z447,z0,z1,z2,z3,z4,z6]),(0,[z0,z448,z1,z2,z3,z4,z6])],[(0,[z52,z0,z1,z2,z3,z43,z6]),(0,[z0,z75,z1,z2,z12,z4,z6]),(0,[z0,z286,z1,z2,z3,z4,z303])],[(0,[z449,z0,z1,z2,z3,z4,z6]),(0,[z450,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z451,z6]),(0,[z0,z452,z1,z2,z3,z4,z6]),(0,[z0,z453,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z43,z6,z142])],[(0,[z0,z8,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z12,z4,z15,z6]),(1,[z0,z31,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z454,z4,z6]),(0,[z0,z1,z455,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z151,z4,z6]),(0,[z0,z1,z2,z456,z3,z4,z6]),(0,[z0,z1,z2,z9,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z457,z6]),(0,[z0,z1,z2,z3,z33,z32,z6]),(0,[z0,z1,z2,z9,z3,z15,z6])],[(0,[z40,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z458,z2,z3,z4,z6]),(0,[z459,z0,z1,z2,z3,z4,z6]),(0,[z0,z54,z1,z2,z3,z78,z6]),(0,[z0,z1,z2,z3,z4,z460,z6]),(0,[z0,z1,z194,z2,z126,z4,z6]),(0,[z0,z1,z20,z2,z3,z33,z6]),(0,[z0,z75,z1,z2,z3,z88,z6])],[(0,[z0,z1,z2,z3,z461,z4,z6]),(0,[z0,z1,z2,z3,z462,z4,z6]),(0,[z0,z145,z1,z2,z3,z4,z239])]],
   [[(1,[z0,z1,z2,z222,z4,z6]),(0,[z0,z1,z2,z463,z3,z4,z6]),(0,[z135,z0,z1,z2,z3,z4,z6]),(0,[z0,z464,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z82,z4,z6]),(0,[z0,z1,z2,z3,z4,z465,z6]),(0,[z0,z1,z2,z3,z4,z6,z466])],[(0,[z0,z1,z63,z41,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z467,z6])],[(0,[z0,z1,z2,z333,z3,z4,z6]),(0,[z116,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z144,z21,z4,z6]),(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z0,z31,z1,z2,z363,z4,z6]),(0,[z469,z0,z1,z2,z3,z4,z6]),(0,[z470,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z36,z3,z88,z4]),(0,[z0,z1,z2,z3,z4,z6,z471])],[(0,[z0,z1,z2,z3,z147,z4,z6]),(0,[z0,z1,z2,z3,z472,z4,z6]),(0,[z0,z473,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z474,z6]),(0,[z0,z1,z2,z144,z3,z4,z6]),(0,[z0,z190,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z215])],[(0,[z0,z121,z1,z2,z12,z4,z6]),(0,[z0,z1,z437,z2,z12,z4,z6]),(0,[z0,z1,z2,z475,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z476,z6]),(0,[z0,z1,z2,z3,z477,z43,z6]),(0,[z0,z1,z2,z3,z4,z6,z374])],[(0,[z0,z478,z1,z2,z3,z4,z6]),(0,[z188,z0,z1,z2,z3,z378,z6]),(1,[z16,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z126,z12,z4,z6]),(0,[z0,z1,z126,z3,z207,z4,z6]),(0,[z0,z75,z1,z2,z3,z4,z215])],[(0,[z188,z0,z1,z2,z312,z4,z6]),(0,[z174,z0,z1,z2,z3,z4,z228]),(0,[z0,z1,z2,z12,z4,z30,z6]),(0,[z0,z1,z2,z3,z4,z6,z479]),(0,[z0,z1,z2,z3,z33,z15,z6]),(0,[z0,z75,z1,z2,z9,z3,z6])]],
   [[(0,[z0,z169,z166,z2,z3,z4,z6]),(0,[z0,z1,z2,z64,z21,z4,z6]),(0,[z0,z1,z2,z83,z3,z33,z6]),(0,[z14,z0,z1,z2,z12,z4,z6]),(1,[z0,z1,z2,z118,z4,z6]),(0,[z0,z1,z2,z115,z3,z30,z6])],[(0,[z0,z1,z2,z480,z3,z4,z6]),(0,[z76,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z43,z39,z6])],[(0,[z0,z481,z1,z2,z3,z4,z6]),(0,[z0,z75,z1,z2,z3,z4,z32]),(0,[z0,z1,z2,z482,z3,z4,z6]),(0,[z0,z75,z1,z221,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z292,z6]),(0,[z483,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z484]),(0,[z0,z1,z2,z485,z3,z4,z6]),(0,[z0,z1,z63,z2,z3,z43,z6]),(0,[z0,z121,z31,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z486,z4,z6]),(1,[z0,z1,z2,z3,z88,z15])],[(0,[z487,z0,z1,z2,z3,z4,z6]),(0,[z116,z0,z1,z2,z3,z4,z137]),(0,[z0,z1,z2,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z488,z4,z6]),(0,[z0,z8,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z44,z6]),(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z0,z1,z490,z2,z3,z4,z6]),(0,[z179,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z491,z2,z3,z4,z6]),(0,[z0,z1,z2,z492,z3,z4,z6]),(0,[z0,z1,z2,z95,z3,z4,z6]),(0,[z0,z1,z194,z2,z21,z4,z6]),(0,[z0,z1,z395,z2,z3,z4,z6])],[(0,[z0,z1,z2,z493,z3,z4,z6]),(0,[z0,z1,z2,z463,z12,z4,z6]),(0,[z0,z1,z2,z295,z12,z4,z6]),(0,[z0,z494,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z115,z3,z33,z6]),(0,[z0,z1,z2,z3,z33,z6,z215]),(0,[z0,z1,z2,z3,z495,z4,z6])]],
   [[(0,[z0,z31,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z12,z4,z408,z6]),(0,[z0,z1,z194,z2,z3,z4,z6]),(0,[z0,z286,z1,z2,z3,z476,z6]),(0,[z0,z496,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z497])],[(0,[z0,z1,z2,z442,z3,z4,z6]),(0,[z52,z0,z105,z2,z3,z4,z6]),(0,[z299,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z131]),(0,[z0,z1,z2,z3,z39,z15,z6]),(0,[z498,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z499,z4,z6]),(0,[z0,z1,z500,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z465])],[(0,[z0,z501,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z502,z3,z4,z6]),(0,[z0,z1,z2,z12,z78,z4,z6]),(0,[z0,z31,z1,z2,z3,z4,z6]),(0,[z135,z0,z1,z20,z3,z4,z6]),(0,[z0,z69,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z503,z3,z43,z6])],[(0,[z98,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z504,z6]),(0,[z0,z1,z2,z3,z505,z4,z6]),(0,[z0,z69,z1,z2,z3,z506,z6]),(1,[z0,z1,z22,z3,z4,z70])],[(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z0,z508,z1,z2,z3,z4,z6]),(0,[z0,z481,z1,z2,z4,z6,z228]),(1,[z0,z1,z2,z21,z43,z6]),(0,[z0,z1,z2,z21,z4,z70,z6]),(0,[z509,z0,z1,z2,z3,z4,z6]),(0,[z0,z286,z1,z126,z3,z4,z6]),(1,[z0,z300,z1,z2,z3,z4]),(0,[z0,z8,z1,z2,z36,z4,z6])],[(0,[z116,z0,z1,z2,z394,z4,z6]),(0,[z0,z1,z2,z3,z510,z4,z6]),(0,[z0,z121,z1,z2,z3,z4,z32]),(0,[z0,z286,z1,z2,z126,z4,z6]),(0,[z0,z8,z1,z2,z3,z43,z6])],[(1,[z0,z511,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z228]),(0,[z0,z1,z2,z3,z4,z512,z6]),(1,[z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z9,z3,z43,z6]),(0,[z0,z1,z2,z3,z88,z15,z6])],[(0,[z0,z1,z513,z2,z3,z4,z6]),(0,[z0,z514,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z515,z43,z6]),(1,[z0,z1,z2,z3,z506,z6])]],
   [[(0,[z0,z1,z516,z2,z3,z4,z6]),(0,[z0,z218,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z337,z6])],[(0,[z0,z1,z2,z126,z13,z4,z6]),(0,[z0,z1,z2,z3,z44,z39,z6]),(0,[z0,z517,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z518,z3,z4,z6]),(0,[z519,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z33,z6]),(0,[z0,z1,z2,z3,z4,z520,z6])],[(0,[z521,z0,z1,z2,z3,z4,z6]),(0,[z0,z145,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z15,z6]),(1,[z0,z1,z2,z214,z4,z6]),(0,[z0,z1,z2,z4,z6,z291,z215])],[(0,[z62,z0,z166,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z15,z6]),(1,[z0,z481,z1,z2,z4,z6]),(0,[z522,z0,z1,z2,z3,z4,z6]),(0,[z523,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z423,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z524]),(0,[z0,z169,z1,z2,z95,z4,z6]),(0,[z0,z1,z2,z36,z21,z4,z6]),(0,[z0,z1,z2,z3,z229,z4,z6]),(0,[z0,z1,z2,z3,z48,z43,z6]),(0,[z0,z1,z2,z3,z33,z6,z131]),(0,[z0,z525,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z526,z6])],[(0,[z0,z1,z527,z2,z3,z4,z6]),(0,[z0,z1,z41,z2,z3,z33,z6]),(0,[z528,z0,z1,z2,z3,z4,z6]),(0,[z0,z190,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z21,z48,z4,z6]),(0,[z529,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z530,z6]),(0,[z0,z1,z2,z3,z4,z531,z6]),(1,[z0,z1,z2,z12,z33,z6]),(0,[z0,z121,z2,z3,z4,z6,z142]),(1,[z0,z1,z2,z3,z285,z6]),(0,[z0,z1,z2,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z291])],[(0,[z0,z1,z166,z2,z3,z33,z6]),(0,[z0,z1,z532,z2,z3,z4,z6]),(0,[z0,z1,z2,z533,z3,z4,z6]),(0,[z0,z1,z534,z2,z3,z4,z6]),(0,[z0,z1,z2,z160,z3,z6,z131])]],
   [[(0,[z0,z1,z2,z3,z13,z43,z6])],[(0,[z0,z1,z2,z64,z3,z43,z6]),(0,[z0,z1,z2,z21,z13,z4,z6]),(0,[z174,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z33,z6,z228]),(0,[z0,z1,z2,z21,z33,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z23]),(1,[z0,z1,z2,z160,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6,z535]),(0,[z0,z1,z536,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z537,z6]),(0,[z0,z1,z2,z12,z4,z457,z6]),(0,[z0,z1,z2,z3,z43,z6,z279]),(0,[z0,z1,z538,z2,z3,z4,z6])],[(1,[z0,z1,z2,z333,z4,z6]),(0,[z0,z1,z2,z3,z539,z4,z6]),(0,[z0,z1,z2,z3,z540,z4,z6]),(0,[z0,z31,z1,z2,z3,z4,z142])],[(0,[z52,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z199,z6]),(0,[z283,z0,z1,z2,z21,z4,z6]),(0,[z541,z0,z1,z2,z3,z4,z6]),(0,[z0,z54,z2,z3,z4,z39,z6]),(0,[z0,z1,z2,z3,z542,z4,z6]),(0,[z0,z1,z2,z3,z543,z4,z6]),(0,[z0,z544,z1,z2,z3,z4,z6])],[(0,[z0,z105,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z545]),(0,[z98,z0,z8,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z546,z4,z6]),(0,[z0,z1,z1,z2,z21,z4,z6]),(0,[z0,z8,z1,z2,z207,z4,z6]),(0,[z0,z1,z2,z3,z196,z33,z6])],[(0,[z52,z0,z1,z2,z3,z4,z6]),(0,[z98,z0,z1,z2,z13,z4,z6]),(0,[z0,z1,z2,z547,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z548])],[(0,[z0,z1,z2,z3,z4,z549,z6]),(0,[z0,z1,z2,z3,z4,z321,z6]),(0,[z0,z169,z1,z63,z3,z4,z6]),(0,[z0,z59,z1,z2,z3,z4,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z551,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z188,z0,z1,z2,z222,z4,z6]),(1,[z0,z1,z2,z3,z552,z6]),(0,[z553,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z554,z6]),(0,[z555,z0,z1,z2,z3,z4,z6]),(0,[z556,z0,z1,z2,z3,z4,z6]),(0,[z0,z557,z1,z2,z3,z4,z6]),(0,[z0,z75,z1,z2,z3,z6,z215])],[(0,[z42,z0,z1,z2,z3,z43,z6]),(0,[z558,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z559,z4,z6]),(0,[z0,z1,z2,z3,z15,z6,z215])],[(0,[z560,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z108,z6]),(0,[z0,z561,z1,z2,z3,z4,z6]),(0,[z0,z145,z1,z2,z3,z78,z6]),(0,[z562,z0,z1,z2,z3,z4,z6])],[(0,[z0,z563,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z564,z6]),(0,[z0,z1,z2,z565,z3,z4,z6]),(0,[z0,z77,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z476,z6]),(0,[z0,z1,z2,z3,z33,z542,z6]),(0,[z0,z1,z2,z9,z115,z4,z6]),(1,[z0,z1,z2,z3,z6,z374])],[(0,[z0,z1,z2,z17,z21,z4,z6]),(0,[z0,z1,z2,z3,z21,z33,z6]),(0,[z0,z1,z2,z36,z3,z4,z23])],[(0,[z0,z1,z566,z2,z3,z4,z6]),(0,[z0,z1,z2,z370,z12,z4,z6]),(0,[z0,z1,z2,z567,z3,z4,z6]),(1,[z0,z405,z2,z3,z4,z6])],[(0,[z14,z72,z1,z2,z3,z4,z6])],[(0,[z568,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z569,z6]),(0,[z0,z1,z2,z3,z4,z570,z6]),(0,[z116,z0,z169,z2,z3,z4,z6]),(0,[z0,z169,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z12,z475,z4,z6]),(0,[z0,z54,z1,z2,z3,z39,z6]),(0,[z0,z1,z2,z3,z4,z571,z6]),(1,[z0,z1,z194,z207,z4,z6]),(0,[z0,z1,z2,z3,z572,z4,z6]),(0,[z0,z1,z2,z3,z88,z43,z6]),(0,[z573,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z3,z91,z6]),(0,[z0,z1,z2,z3,z5,z6,z228]),(0,[z0,z1,z2,z21,z88,z4,z6]),(0,[z0,z286,z1,z194,z3,z4,z6]),(0,[z574,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z43,z6,z23]),(0,[z0,z1,z2,z3,z230,z33,z6])],[(0,[z575,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z163,z6]),(0,[z0,z1,z2,z3,z328,z4,z6]),(0,[z0,z1,z2,z3,z477,z4,z6])],[(0,[z0,z1,z2,z576,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z44,z6]),(1,[z0,z1,z2,z363,z4,z6]),(0,[z0,z1,z2,z126,z4,z37,z6]),(0,[z0,z75,z1,z2,z3,z33,z6]),(0,[z0,z1,z577,z2,z3,z4,z6]),(0,[z0,z578,z1,z2,z3,z4,z6])],[(0,[z0,z1,z579,z2,z3,z4,z6]),(0,[z0,z580,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z581,z6]),(0,[z0,z1,z2,z3,z581,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z43,z6]),(0,[z0,z1,z2,z3,z4,z6,z583])],[(0,[z0,z1,z2,z3,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z435]),(0,[z188,z0,z1,z41,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z584,z4,z6]),(1,[z179,z0,z2,z12,z4,z6]),(0,[z0,z1,z2,z585,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z506,z6])],[(0,[z0,z1,z2,z3,z4,z6,z586]),(0,[z0,z1,z63,z2,z21,z4,z6]),(0,[z0,z1,z2,z67,z21,z4,z6]),(0,[z179,z0,z2,z3,z4,z6,z142])],[(0,[z40,z0,z1,z2,z3,z33,z6]),(0,[z587,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z588,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z32,z6]),(0,[z0,z589,z1,z2,z3,z4,z6]),(0,[z590,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z591,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z592,z6]),(0,[z0,z1,z194,z2,z207,z4,z6]),(0,[z0,z593,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z9,z30,z6])]],
   [[(0,[z587,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z51]),(0,[z0,z1,z22,z2,z3,z43,z6])],[(0,[z62,z0,z1,z136,z3,z4,z6]),(0,[z0,z594,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z83,z21,z4,z6]),(0,[z116,z58,z1,z2,z3,z4,z6]),(0,[z595,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z241,z6]),(0,[z0,z1,z2,z3,z4,z6,z596]),(0,[z0,z597,z1,z2,z3,z4,z6])],[(0,[z0,z598,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z599]),(0,[z0,z1,z2,z21,z4,z37,z6])],[(0,[z0,z1,z600,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z73,z39,z6]),(1,[z0,z1,z2,z203,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z601]),(0,[z0,z1,z602,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z465,z30])],[(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z604,z4,z6]),(0,[z0,z69,z1,z2,z21,z4,z6]),(0,[z605,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z48,z4,z37,z6])],[(0,[z62,z0,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z606,z6]),(0,[z0,z1,z2,z3,z33,z44,z6]),(0,[z0,z1,z2,z3,z4,z32,z228]),(0,[z0,z1,z63,z2,z3,z607,z6]),(0,[z0,z121,z1,z2,z3,z33,z6]),(0,[z0,z608,z1,z2,z3,z4,z6]),(0,[z283,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z3,z33,z4,z43,z6]),(0,[z0,z1,z2,z9,z4,z30,z6]),(0,[z0,z300,z1,z2,z3,z4,z30])],[(0,[z188,z0,z511,z2,z3,z4,z6]),(0,[z0,z1,z511,z2,z3,z4,z6]),(0,[z188,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z609,z2,z3,z4,z6]),(0,[z0,z1,z610,z2,z3,z4,z6]),(0,[z0,z1,z194,z2,z3,z7,z6]),(0,[z0,z286,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z126,z3,z33,z6]),(0,[z0,z1,z2,z503,z3,z4,z6]),(0,[z0,z69,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z611,z6]),(0,[z0,z1,z2,z3,z4,z612,z6]),(0,[z0,z1,z613,z2,z3,z4,z6])],[(1,[z0,z2,z21,z4,z6,z142]),(0,[z0,z121,z1,z2,z499,z4,z6]),(1,[z0,z1,z2,z386,z4,z6]),(0,[z614,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z615,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z616,z6]),(0,[z0,z1,z617,z2,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z4,z6,z618]),(1,[z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z115,z21,z4,z6]),(0,[z0,z453,z1,z2,z3,z4,z6]),(0,[z0,z54,z1,z2,z12,z4,z6]),(0,[z0,z619,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z15,z6]),(0,[z0,z1,z2,z115,z3,z15,z6])],[(0,[z620,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z156,z4,z6]),(1,[z0,z1,z2,z3,z231,z6]),(0,[z0,z8,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z12,z4,z6]),(0,[z0,z621,z1,z2,z3,z4,z6]),(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z623,z0,z1,z2,z3,z4,z6]),(0,[z135,z0,z1,z3,z33,z4,z6]),(0,[z135,z0,z1,z3,z4,z6,z23]),(0,[z0,z1,z2,z9,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z624,z6]),(0,[z0,z1,z2,z3,z378,z4,z6]),(0,[z0,z1,z2,z625,z3,z4,z6]),(0,[z0,z1,z63,z2,z3,z554,z6]),(0,[z0,z1,z2,z3,z515,z4,z6])],[(0,[z188,z40,z1,z2,z3,z4,z6]),(1,[z42,z1,z2,z13,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z108]),(0,[z0,z626,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z34,z6]),(0,[z0,z1,z2,z3,z337,z4,z6])],[(0,[z627,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z552,z6]),(0,[z0,z1,z2,z3,z4,z254,z6])],[(0,[z0,z1,z2,z628,z3,z4,z6]),(0,[z0,z1,z2,z290,z3,z33,z6]),(0,[z0,z8,z1,z2,z4,z6,z131]),(0,[z0,z1,z2,z4,z37,z6,z131]),(0,[z0,z1,z2,z3,z629,z4,z6])],[(0,[z0,z630,z1,z2,z3,z4,z6]),(0,[z0,z1,z631,z2,z3,z4,z6]),(1,[z0,z1,z2,z389,z4,z6]),(0,[z0,z336,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z359,z4,z6])]],
   [[(0,[z98,z0,z1,z2,z83,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z632]),(0,[z0,z1,z2,z633,z3,z4,z6]),(0,[z634,z0,z1,z2,z3,z4,z6]),(1,[z116,z0,z144,z3,z4,z6]),(1,[z0,z1,z2,z3,z607,z6]),(0,[z0,z635,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z636,z3,z4,z6]),(0,[z0,z1,z20,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z43,z6,z215]),(0,[z0,z1,z2,z3,z48,z4,z6]),(0,[z0,z637,z1,z2,z3,z4,z6])],[(1,[z0,z1,z442,z3,z4,z6]),(0,[z0,z1,z2,z638,z3,z4,z6]),(0,[z0,z190,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z371,z6]),(0,[z0,z1,z2,z3,z639,z4,z6]),(0,[z0,z31,z1,z2,z3,z60,z6]),(0,[z0,z1,z2,z3,z4,z640,z6])],[(1,[z0,z1,z2,z3,z278,z6]),(0,[z0,z1,z2,z3,z4,z641,z6]),(0,[z0,z1,z2,z3,z4,z7,z6]),(0,[z0,z1,z2,z642,z3,z4,z6])],[(0,[z98,z0,z1,z2,z3,z33,z6]),(0,[z0,z233,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z30,z6]),(0,[z0,z643,z1,z2,z3,z4,z6])],[(0,[z52,z105,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z6]),(0,[z116,z0,z1,z63,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z137]),(0,[z0,z69,z1,z2,z3,z4,z23])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z6]),(0,[z0,z1,z2,z3,z4,z6,z644]),(1,[z0,z1,z2,z3,z321,z6]),(0,[z0,z1,z2,z3,z4,z6,z645])],[(0,[z0,z1,z2,z3,z4,z28,z6]),(0,[z0,z1,z2,z646,z3,z4,z6]),(1,[z0,z1,z2,z3,z554,z6]),(0,[z0,z1,z2,z164,z21,z4,z6]),(0,[z0,z286,z1,z2,z207,z4,z6])],[(0,[z0,z1,z2,z3,z647,z4,z6]),(0,[z98,z1,z2,z83,z3,z4,z6]),(1,[z0,z54,z2,z3,z39,z6]),(0,[z0,z1,z2,z648,z3,z4,z6])]],
   [[(0,[z0,z1,z166,z2,z21,z4,z6]),(0,[z188,z0,z1,z2,z3,z552,z6]),(0,[z0,z1,z2,z3,z649,z4,z6]),(0,[z0,z1,z2,z12,z83,z4,z6]),(0,[z76,z1,z2,z3,z4,z108,z6]),(0,[z0,z1,z2,z3,z607,z4,z6]),(1,[z0,z1,z2,z260,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z142]),(0,[z0,z314,z1,z2,z3,z33,z6])],[(0,[z72,z0,z1,z2,z3,z44,z6]),(0,[z0,z81,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z4,z6,z650])],[(0,[z0,z651,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z83,z3,z43,z6]),(0,[z0,z1,z2,z3,z4,z6,z652]),(0,[z135,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z653])],[(0,[z0,z654,z1,z2,z3,z4,z6]),(0,[z42,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z655,z4,z6]),(0,[z0,z1,z2,z656,z3,z4,z6]),(0,[z76,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z21,z4,z108,z6])],[(0,[z116,z0,z1,z2,z12,z4,z6]),(0,[z0,z405,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z106,z4,z6]),(0,[z42,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z394,z4,z6]),(0,[z0,z1,z2,z3,z207,z33,z6]),(0,[z0,z1,z2,z3,z43,z6,z131]),(0,[z0,z1,z2,z3,z657,z4,z6])],[(0,[z0,z1,z2,z144,z12,z4,z6])],[(0,[z238,z0,z1,z2,z3,z4,z6]),(0,[z658,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z659,z6]),(0,[z0,z1,z2,z3,z4,z660,z6]),(0,[z0,z75,z1,z272,z3,z4,z6])]],
   [[(0,[z40,z52,z1,z2,z3,z4,z6]),(0,[z0,z2,z12,z3,z21,z4,z6]),(0,[z0,z1,z2,z12,z4,z43,z6]),(0,[z0,z1,z2,z3,z438,z4,z6]),(0,[z0,z2,z3,z4,z32,z6,z142]),(1,[z0,z1,z3,z33,z43,z6]),(0,[z661,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z662])],[(1,[z188,z1,z64,z3,z4,z6]),(1,[z174,z1,z2,z3,z4,z228]),(0,[z0,z663,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z115,z3,z43,z6])],[(0,[z0,z1,z2,z664,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z6,z228]),(1,[z0,z145,z2,z3,z78,z6]),(0,[z0,z1,z2,z665,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z666,z6]),(0,[z0,z1,z2,z36,z3,z4,z70])],[(0,[z0,z145,z1,z2,z3,z39,z6]),(0,[z667,z0,z1,z2,z3,z4,z6]),(0,[z0,z286,z1,z2,z3,z581,z6]),(0,[z0,z1,z2,z3,z4,z6,z668]),(1,[z0,z1,z2,z82,z4,z6]),(0,[z0,z1,z22,z2,z3,z241,z6]),(0,[z0,z1,z2,z3,z88,z4,z6])],[(0,[z0,z1,z2,z669,z3,z4,z6]),(0,[z116,z0,z1,z2,z3,z4,z199])],[(0,[z0,z1,z2,z3,z670,z4,z6]),(0,[z0,z105,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z129,z3,z43,z6])],[(0,[z0,z206,z1,z2,z3,z4,z6]),(0,[z0,z671,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z672,z4,z6]),(0,[z0,z1,z2,z12,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z231,z6])],[(0,[z0,z1,z2,z3,z4,z673,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z674,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z32,z6]),(0,[z179,z0,z1,z2,z12,z4,z6]),(0,[z0,z54,z1,z2,z438,z4,z6]),(0,[z0,z138,z1,z2,z3,z43,z6])]],
   [[(0,[z62,z0,z1,z2,z3,z4,z435]),(0,[z0,z1,z2,z3,z4,z6,z675]),(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z0,z286,z1,z2,z3,z4,z51])],[(0,[z235,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z677,z3,z4,z6]),(0,[z0,z1,z2,z3,z678,z4,z6]),(0,[z0,z1,z22,z2,z386,z4,z6])],[(0,[z0,z1,z2,z679,z3,z4,z6]),(0,[z0,z1,z2,z83,z207,z4,z6]),(0,[z0,z1,z2,z3,z4,z228,z23]),(0,[z0,z1,z22,z2,z21,z4,z6]),(0,[z680,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z194,z2,z12,z4,z6]),(0,[z0,z1,z2,z176,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z681,z6]),(0,[z590,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z682,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z683]),(0,[z0,z75,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z33,z43,z6])],[(0,[z0,z31,z1,z2,z12,z4,z6]),(0,[z0,z145,z1,z2,z328,z4,z6]),(0,[z0,z1,z2,z3,z43,z451,z6]),(0,[z0,z1,z22,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z228,z142]),(0,[z0,z1,z684,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z685,z6]),(0,[z179,z0,z31,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z78,z15,z6]),(0,[z0,z1,z2,z3,z4,z6,z686]),(0,[z0,z1,z2,z3,z4,z37,z6])],[(0,[z179,z0,z190,z2,z3,z4,z6])],[(0,[z0,z1,z136,z2,z3,z4,z6]),(0,[z687,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z41,z2,z3,z43,z6]),(0,[z0,z1,z2,z688,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z73,z6]),(0,[z0,z169,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z21,z4,z6,z142]),(0,[z0,z1,z2,z21,z4,z6,z352]),(0,[z0,z1,z689,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z690,z6]),(0,[z0,z691,z1,z2,z3,z4,z6])]],
   [[(0,[z188,z0,z1,z2,z21,z4,z6]),(0,[z0,z286,z1,z2,z21,z4,z6]),(1,[z0,z1,z2,z12,z43,z6]),(0,[z0,z1,z2,z692,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z693,z6])],[(0,[z283,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z166,z2,z3,z43,z6]),(0,[z0,z8,z1,z2,z3,z4,z131])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z188,z0,z1,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z694]),(1,[z0,z1,z2,z3,z4,z239]),(0,[z0,z286,z1,z2,z3,z4,z6])],[(0,[z62,z0,z1,z2,z3,z4,z292]),(0,[z174,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z695,z2,z3,z4,z6]),(1,[z0,z1,z20,z3,z43,z6])],[(0,[z0,z1,z2,z696,z3,z4,z6]),(0,[z0,z1,z2,z697,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z698,z6]),(0,[z0,z145,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z88,z4,z142]),(0,[z0,z699,z1,z2,z3,z4,z6]),(0,[z0,z700,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z221,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z701,z6]),(0,[z0,z1,z2,z12,z48,z4,z6]),(0,[z0,z145,z1,z2,z176,z4,z6]),(0,[z0,z1,z2,z499,z3,z4,z6]),(0,[z702,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z703,z2,z3,z4,z6]),(0,[z0,z1,z2,z704,z3,z4,z6]),(0,[z0,z705,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z706,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z322,z6]),(0,[z1,z2,z3,z73,z4,z44,z6]),(0,[z0,z1,z2,z12,z639,z4,z6])],[(0,[z0,z1,z2,z3,z4,z467,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z483,z0,z2,z12,z4,z6]),(0,[z58,z1,z2,z394,z4,z6]),(0,[z0,z429,z2,z3,z39,z6]),(0,[z0,z121,z2,z3,z4,z142]),(0,[z0,z707,z2,z3,z43,z6]),(0,[z135,z0,z1,z3,z708,z6])],[(0,[z0,z1,z2,z3,z278,z6]),(0,[z52,z105,z2,z120,z4,z6]),(0,[z98,z0,z395,z2,z4,z6])],[(0,[z0,z1,z2,z3,z709,z6]),(0,[z0,z1,z2,z503,z125,z6])],[(0,[z0,z1,z2,z3,z4,z710]),(0,[z76,z1,z2,z21,z4,z108]),(0,[z0,z1,z2,z3,z4,z137]),(0,[z587,z1,z2,z67,z4,z6]),(0,[z0,z75,z1,z2,z3,z653])],[(0,[z45,z1,z2,z3,z44,z6]),(0,[z58,z1,z2,z3,z43,z6]),(0,[z0,z1,z711,z3,z4,z6]),(0,[z0,z1,z2,z712,z4,z6]),(0,[z0,z713,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z714,z6])],[(0,[z0,z1,z2,z715,z4,z6]),(0,[z76,z1,z2,z3,z4,z108]),(0,[z0,z31,z2,z12,z4,z32]),(0,[z0,z54,z2,z156,z39,z6])],[(0,[z0,z54,z2,z3,z39,z6])],[(0,[z16,z1,z63,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z716])],[(0,[z0,z1,z2,z3,z4,z717]),(0,[z0,z1,z2,z21,z5,z6])],[(0,[z0,z1,z2,z718,z4,z6]),(0,[z0,z1,z2,z719,z4,z6]),(0,[z0,z112,z2,z21,z4,z6]),(0,[z0,z1,z2,z203,z4,z199]),(0,[z116,z0,z144,z3,z4,z137]),(0,[z0,z1,z27,z3,z4,z70])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z347,z3,z33,z6])],[(0,[z0,z1,z2,z720,z4,z6])],[(0,[z0,z1,z2,z394,z4,z6]),(0,[z0,z300,z1,z2,z12,z4])],[(0,[z72,z1,z2,z3,z542,z6]),(0,[z0,z340,z2,z3,z39,z6]),(0,[z1,z2,z3,z4,z721,z228]),(0,[z0,z2,z21,z4,z6,z237]),(0,[z0,z1,z722,z3,z4,z6]),(0,[z0,z1,z3,z43,z6,z270]),(1,[z0,z1,z3,z4,z723])],[(0,[z0,z1,z2,z3,z724,z6]),(0,[z0,z1,z2,z3,z552,z11]),(0,[z0,z725,z2,z3,z4,z6]),(0,[z0,z1,z2,z726,z4,z6])],[(0,[z16,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z499,z33,z6]),(0,[z0,z1,z3,z33,z43,z6])]],
   [[(0,[z0,z1,z2,z12,z278,z6]),(0,[z0,z1,z2,z222,z378,z6]),(0,[z0,z727,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z6,z728])],[(0,[z0,z1,z2,z3,z4,z729]),(0,[z0,z1,z2,z3,z730,z6])],[(0,[z0,z1,z2,z3,z731,z6]),(0,[z116,z0,z144,z394,z4,z6]),(0,[z0,z1,z2,z17,z4,z37]),(0,[z0,z1,z2,z82,z4,z6])],[(0,[z0,z511,z2,z3,z4,z322]),(0,[z0,z1,z2,z3,z43,z322]),(0,[z0,z1,z318,z3,z33,z6]),(0,[z0,z1,z2,z12,z321,z6]),(0,[z0,z69,z1,z3,z506,z23])],[],[(0,[z40,z1,z41,z21,z4,z6])],[(0,[z0,z1,z2,z3,z4,z732])],[(0,[z16,z1,z2,z3,z4,z199])],[(0,[z0,z1,z2,z733,z4,z6]),(0,[z0,z286,z1,z126,z476,z6]),(0,[z0,z1,z2,z36,z4,z666])],[(0,[z0,z481,z1,z2,z33,z6]),(0,[z0,z1,z2,z160,z12,z6]),(0,[z0,z1,z734,z2,z3,z6])],[(0,[z0,z1,z2,z150,z43,z6]),(0,[z0,z1,z2,z735,z4,z6]),(0,[z0,z1,z2,z3,z4,z736]),(0,[z0,z1,z2,z737,z4,z6]),(0,[z0,z1,z2,z738,z4,z6])],[(0,[z0,z1,z2,z3,z321,z199])],[(0,[z0,z31,z2,z3,z4,z685]),(0,[z0,z1,z22,z12,z4,z70]),(0,[z0,z31,z2,z260,z4,z6])],[(0,[z72,z1,z2,z21,z44,z6])],[(0,[z0,z1,z2,z3,z4,z739]),(0,[z0,z1,z2,z9,z543,z6])],[(0,[z0,z511,z2,z12,z4,z6]),(0,[z72,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z12,z43,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z740]),(0,[z0,z145,z2,z12,z78,z6]),(0,[z0,z1,z2,z12,z4,z741]),(0,[z742,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z176,z43,z6]),(0,[z0,z1,z2,z363,z60,z6])],[(0,[z0,z1,z2,z333,z33,z6]),(0,[z52,z105,z2,z3,z43,z6]),(0,[z0,z1,z2,z743,z4,z6]),(0,[z174,z1,z2,z3,z5,z228]),(0,[z0,z744,z1,z2,z21,z4]),(0,[z0,z1,z2,z21,z745,z6]),(0,[z0,z145,z2,z176,z78,z6]),(1,[z0,z1,z3,z708,z6])],[(0,[z0,z1,z2,z3,z746,z6])],[(0,[z0,z1,z136,z333,z4,z6]),(0,[z522,z1,z41,z3,z4,z6]),(0,[z42,z705,z1,z2,z4,z6]),(0,[z590,z1,z2,z3,z44,z6]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z0,z2,z12,z21,z33,z6])],[(0,[z0,z190,z2,z21,z43,z6]),(0,[z0,z31,z2,z3,z313,z32])],[(0,[z0,z748,z2,z3,z4,z6])],[],[(0,[z0,z511,z2,z312,z4,z6]),(0,[z0,z1,z2,z312,z43,z6]),(0,[z0,z1,z2,z749,z4,z6]),(0,[z0,z192,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z43,z199]),(0,[z0,z1,z2,z21,z4,z146]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z234,z3,z43,z6])],[(0,[z0,z1,z2,z3,z4,z11]),(0,[z0,z751,z2,z3,z4,z6]),(0,[z0,z1,z752,z3,z4,z6]),(0,[z0,z1,z2,z3,z753,z6])],[],[(0,[z0,z1,z2,z3,z754,z6]),(0,[z0,z206,z2,z3,z43,z6]),(0,[z0,z755,z1,z2,z3,z4]),(0,[z0,z1,z3,z241,z43,z6]),(0,[z0,z1,z2,z756,z33,z6])],[(0,[z0,z166,z442,z3,z4,z6]),(0,[z0,z2,z757,z21,z4,z6]),(0,[z0,z405,z2,z3,z33,z6])],[(0,[z0,z1,z3,z758,z43,z6])],[(0,[z0,z1,z2,z759,z4,z6]),(0,[z0,z2,z21,z4,z142,z23])],[(0,[z62,z166,z2,z3,z278,z6])],[(0,[z760,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z476,z303]),(0,[z0,z1,z221,z3,z43,z6])]],
   [[(0,[z0,z1,z2,z12,z4,z239]),(0,[z0,z1,z2,z118,z313,z6])],[(0,[z0,z1,z136,z3,z28,z6]),(0,[z0,z1,z2,z176,z4,z239]),(0,[z0,z8,z1,z2,z4,z185]),(0,[z0,z1,z221,z115,z3,z6])],[(0,[z0,z1,z126,z761,z4,z6]),(0,[z0,z1,z2,z43,z6,z762]),(0,[z0,z1,z272,z3,z33,z6]),(0,[z0,z75,z1,z272,z3,z215]),(0,[z0,z75,z1,z2,z214,z4])],[(0,[z0,z2,z3,z763,z4,z6]),(0,[z764,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z203,z117,z6]),(0,[z765,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z266,z15]),(0,[z0,z1,z2,z3,z766,z6])],[(0,[z0,z1,z2,z3,z6,z767]),(0,[z0,z1,z2,z768,z4,z6]),(0,[z0,z1,z2,z126,z4,z303])],[(0,[z667,z1,z2,z3,z4,z108])],[(0,[z0,z1,z2,z769,z4,z6]),(0,[z0,z1,z2,z12,z7,z6]),(0,[z0,z31,z2,z118,z4,z32]),(0,[z0,z395,z2,z295,z4,z6])],[(0,[z0,z2,z21,z4,z6,z344]),(0,[z0,z18,z1,z3,z4,z23]),(0,[z0,z1,z2,z3,z581,z303])],[(0,[z0,z1,z2,z95,z4,z6]),(0,[z0,z1,z2,z3,z770,z6]),(0,[z0,z1,z2,z3,z6,z771])],[(0,[z0,z1,z2,z3,z278,z292]),(0,[z0,z1,z2,z12,z25,z6]),(0,[z0,z1,z2,z772,z3,z6])],[(0,[z0,z2,z21,z33,z359,z6])],[(0,[z0,z773,z1,z2,z3,z6]),(0,[z0,z774,z1,z2,z3,z6]),(0,[z0,z1,z2,z775,z4,z6]),(0,[z0,z1,z609,z3,z4,z70]),(0,[z0,z1,z2,z518,z4,z37])],[(0,[z0,z69,z1,z21,z4,z23]),(0,[z0,z398,z2,z3,z4,z142]),(0,[z0,z75,z1,z2,z533,z3])],[(0,[z62,z166,z2,z3,z43,z6]),(0,[z0,z300,z1,z2,z21,z4])],[(0,[z0,z1,z2,z120,z43,z6]),(0,[z0,z1,z2,z3,z4,z776]),(0,[z0,z1,z2,z21,z33,z6]),(0,[z0,z1,z2,z21,z4,z777]),(0,[z0,z195,z2,z21,z4,z6]),(0,[z0,z1,z2,z438,z43,z6]),(0,[z0,z69,z1,z3,z4,z23]),(0,[z0,z395,z2,z3,z88,z4])],[(0,[z188,z1,z64,z3,z4,z11]),(0,[z1,z2,z3,z4,z108,z721])]],
   [[(0,[z778,z1,z2,z3,z4,z6])],[(0,[z16,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z12,z4,z51]),(0,[z779,z1,z2,z3,z4,z6])],[(0,[z0,z1,z136,z3,z4,z6]),(0,[z0,z1,z2,z3,z780,z6]),(0,[z0,z1,z2,z3,z15,z652]),(0,[z0,z1,z2,z781,z4,z6]),(0,[z0,z782,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z15,z783])],[(0,[z0,z1,z2,z4,z37,z644]),(0,[z0,z1,z2,z328,z4,z6])],[(0,[z0,z1,z2,z21,z4,z303]),(0,[z0,z1,z3,z4,z723,z23])],[(0,[z0,z1,z2,z36,z4,z526]),(0,[z0,z75,z1,z2,z214,z215])],[(0,[z0,z1,z2,z3,z4,z303])],[(0,[z0,z1,z442,z3,z33,z6])],[(0,[z0,z1,z2,z3,z43,z292]),(0,[z0,z1,z2,z784,z4,z6]),(0,[z40,z1,z41,z3,z91,z6]),(0,[z0,z8,z1,z2,z374,z131])],[(0,[z0,z300,z1,z2,z3,z43]),(0,[z0,z1,z2,z214,z15,z6])],[(0,[z0,z1,z2,z333,z4,z435]),(0,[z42,z0,z395,z2,z4,z6]),(0,[z14,z1,z2,z3,z73,z6]),(0,[z0,z1,z2,z3,z785,z6]),(0,[z0,z1,z2,z160,z21,z6]),(0,[z0,z1,z2,z12,z231,z6])],[(0,[z0,z1,z2,z3,z4,z786]),(0,[z0,z1,z2,z3,z787,z6])],[(0,[z0,z1,z2,z3,z4,z788])],[(0,[z0,z1,z2,z3,z789,z6]),(0,[z0,z1,z2,z790,z4,z6]),(0,[z0,z1,z2,z791,z3,z6]),(0,[z0,z75,z1,z2,z3,z215])],[(0,[z0,z1,z2,z150,z278,z6]),(0,[z0,z1,z2,z792,z4,z6]),(0,[z0,z1,z2,z3,z4,z793]),(0,[z0,z1,z3,z43,z6,z441])],[]],
   [[(0,[z0,z1,z2,z21,z378,z6]),(0,[z0,z1,z794,z3,z4,z6]),(0,[z0,z1,z2,z795,z4,z6]),(0,[z796,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z797,z6]),(0,[z0,z798,z1,z2,z3,z4]),(0,[z0,z1,z2,z12,z607,z6]),(0,[z0,z1,z2,z295,z4,z457])],[(0,[z0,z1,z2,z799,z4,z6]),(0,[z0,z1,z2,z800,z4,z6]),(0,[z0,z1,z2,z801,z4,z6]),(0,[z0,z121,z2,z12,z4,z142]),(0,[z0,z1,z2,z3,z33,z465])],[(0,[z0,z1,z415,z3,z43,z6]),(0,[z0,z1,z3,z43,z612,z6]),(0,[z0,z1,z2,z3,z6,z802]),(0,[z0,z1,z2,z3,z230,z34])],[(0,[z62,z803,z2,z3,z4,z6])],[(0,[z0,z1,z2,z12,z4,z137]),(0,[z0,z1,z2,z804,z4,z6])],[(0,[z0,z1,z2,z805,z4,z6]),(0,[z0,z1,z2,z3,z4,z806]),(0,[z0,z286,z1,z761,z4,z6])],[(0,[z76,z1,z2,z12,z4,z108])],[(0,[z0,z1,z2,z3,z28,z435]),(0,[z0,z1,z173,z3,z43,z6]),(0,[z0,z1,z2,z21,z6,z807]),(0,[z0,z54,z2,z12,z39,z6]),(0,[z0,z1,z367,z3,z43,z6])],[(0,[z0,z1,z2,z3,z4,z808]),(0,[z0,z8,z1,z2,z43,z131])],[(0,[z40,z1,z41,z3,z4,z6]),(0,[z0,z1,z2,z222,z552,z6]),(0,[z0,z1,z2,z3,z6,z807]),(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z1,z2,z363,z313,z6]),(0,[z0,z1,z22,z3,z758,z6]),(0,[z102,z1,z2,z3,z147,z6])],[(0,[z0,z1,z810,z3,z4,z6]),(0,[z0,z1,z2,z3,z811,z6]),(0,[z0,z1,z2,z3,z4,z812]),(0,[z0,z813,z2,z3,z4,z6]),(0,[z0,z814,z2,z3,z4,z6]),(0,[z0,z362,z2,z3,z4,z142])],[(0,[z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z815,z3,z6]),(0,[z0,z1,z2,z503,z30,z6])],[],[(0,[z0,z816,z2,z3,z4,z6]),(0,[z0,z233,z1,z2,z3,z6]),(0,[z0,z1,z2,z21,z817,z6])],[(0,[z0,z600,z2,z12,z4,z6]),(0,[z0,z818,z2,z3,z4,z6]),(0,[z0,z2,z21,z4,z611,z6])]],
   [[(0,[z0,z1,z2,z3,z817,z6]),(0,[z0,z1,z22,z21,z43,z6]),(0,[z0,z1,z2,z33,z6,z291])],[(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z1,z2,z820,z43,z6])],[(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z3,z4,z822]),(0,[z0,z121,z2,z3,z4,z823]),(0,[z0,z1,z22,z3,z43,z6]),(0,[z0,z1,z2,z214,z43,z6])],[(0,[z0,z1,z2,z3,z824,z6]),(0,[z0,z1,z2,z825,z4,z6]),(0,[z0,z1,z272,z21,z4,z6]),(0,[z0,z286,z1,z126,z581,z6])],[(0,[z0,z1,z2,z3,z826,z6]),(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z828,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z829]),(0,[z98,z1,z2,z83,z43,z6]),(0,[z0,z1,z2,z830,z4,z6])],[(0,[z0,z1,z2,z394,z4,z199]),(0,[z0,z1,z2,z3,z745,z6])],[(0,[z0,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z21,z4,z435]),(0,[z0,z1,z2,z831,z4,z6])],[(0,[z0,z1,z2,z3,z832,z6])],[(0,[z0,z1,z2,z3,z4,z435]),(0,[z52,z1,z442,z3,z4,z6]),(0,[z0,z1,z20,z3,z708,z6])],[(0,[z0,z1,z2,z3,z4,z833])],[(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z835,z2,z3,z4,z6]),(0,[z0,z755,z1,z2,z12,z4]),(0,[z0,z1,z221,z3,z78,z6])],[(0,[z42,z1,z2,z297,z4,z6]),(0,[z102,z1,z2,z3,z73,z6]),(0,[z0,z1,z2,z3,z4,z146]),(0,[z0,z1,z2,z836,z4,z6])],[(0,[z0,z1,z2,z837,z4,z6]),(0,[z0,z112,z2,z3,z4,z32]),(0,[z0,z388,z2,z21,z4,z6]),(0,[z0,z1,z2,z838,z4,z6]),(0,[z498,z0,z1,z3,z33,z6]),(0,[z0,z218,z2,z3,z78,z6]),(0,[z0,z1,z2,z207,z4,z303]),(0,[z0,z8,z1,z2,z4,z350]),(0,[z0,z68,z2,z3,z359,z6])],[],[(0,[z0,z233,z1,z2,z3,z142])]],
   [[(0,[z0,z1,z442,z3,z4,z435]),(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z2,z757,z3,z4,z6]),(0,[z0,z1,z22,z3,z43,z23])],[(0,[z72,z1,z2,z12,z44,z6]),(0,[z0,z395,z2,z3,z43,z6])],[(0,[z0,z1,z2,z840,z21,z4]),(0,[z0,z286,z1,z126,z4,z6]),(0,[z0,z1,z2,z214,z88,z4])],[(0,[z0,z1,z841,z3,z4,z6]),(0,[z1,z2,z83,z842,z4,z6]),(0,[z16,z1,z2,z203,z4,z6]),(0,[z0,z1,z2,z3,z843,z6])],[(0,[z0,z1,z2,z222,z4,z6]),(0,[z16,z1,z144,z3,z4,z6]),(0,[z0,z1,z2,z844,z4,z6])],[(0,[z0,z1,z2,z3,z845,z6]),(0,[z174,z233,z1,z2,z3,z228]),(0,[z0,z1,z2,z846,z4,z6]),(0,[z179,z0,z2,z12,z33,z6])],[(0,[z0,z1,z2,z847,z4,z6]),(0,[z848,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z54,z2,z438,z39,z6]),(0,[z0,z1,z194,z207,z43,z6]),(0,[z0,z300,z1,z2,z3,z33]),(0,[z0,z1,z2,z3,z4,z850])],[(0,[z0,z1,z3,z4,z70,z723])],[(0,[z167,z0,z1,z3,z43,z6]),(0,[z0,z1,z851,z3,z4,z6]),(0,[z0,z1,z21,z43,z6,z23])],[(0,[z0,z1,z2,z12,z4,z11]),(0,[z0,z1,z2,z3,z852,z6]),(0,[z0,z429,z2,z21,z4,z6]),(0,[z0,z69,z1,z3,z4,z723])],[(0,[z0,z1,z2,z3,z4,z853]),(0,[z0,z1,z2,z854,z4,z6]),(0,[z0,z8,z1,z2,z4,z390])],[(0,[z1,z2,z3,z855,z4,z6]),(1,[z0,z300,z1,z2,z9]),(0,[z0,z1,z2,z856,z4,z6])],[(0,[z0,z1,z2,z857,z4,z6]),(0,[z0,z1,z2,z4,z858,z6])],[(0,[z0,z1,z2,z3,z178,z15])],[]],
   [[(0,[z0,z1,z2,z3,z859,z6]),(0,[z0,z860,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z2,z21,z4,z6,z524]),(0,[z0,z1,z2,z3,z862,z6])],[],[(0,[z0,z1,z2,z3,z863,z6]),(0,[z0,z1,z2,z12,z843,z6]),(0,[z0,z1,z2,z156,z33,z6])],[(0,[z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z864,z6]),(0,[z0,z1,z2,z203,z43,z6]),(0,[z865,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z465]),(0,[z0,z1,z2,z3,z4,z777]),(0,[z0,z2,z3,z4,z6,z823])],[(0,[z0,z57,z1,z126,z4,z6])],[(0,[z0,z206,z2,z3,z4,z11]),(0,[z16,z1,z2,z3,z321,z6]),(0,[z0,z1,z2,z499,z4,z6])],[(0,[z866,z1,z2,z3,z4,z6]),(0,[z0,z380,z2,z12,z4,z6])],[(0,[z0,z1,z442,z3,z859,z6]),(0,[z0,z1,z2,z3,z117,z137]),(0,[z0,z31,z2,z3,z43,z32]),(0,[z0,z1,z2,z4,z867,z6]),(0,[z0,z1,z2,z386,z43,z6])],[(0,[z0,z1,z2,z761,z4,z6])],[(0,[z116,z0,z144,z3,z33,z6]),(0,[z0,z1,z2,z21,z506,z6]),(0,[z0,z1,z2,z868,z4,z6])],[(0,[z0,z1,z2,z869,z4,z6]),(0,[z0,z1,z2,z3,z4,z870]),(0,[z0,z80,z1,z3,z4,z23])],[(0,[z188,z1,z64,z222,z4,z6]),(0,[z0,z871,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z872,z6])],[(0,[z0,z1,z873,z3,z4,z6]),(0,[z0,z1,z2,z3,z714,z6])],[(0,[z0,z1,z2,z36,z4,z850])],[(0,[z0,z1,z2,z874,z4,z6]),(0,[z521,z0,z2,z21,z4,z6]),(0,[z0,z1,z532,z3,z43,z6]),(0,[z0,z727,z1,z2,z3,z43])],[(0,[z0,z1,z136,z150,z4,z6]),(0,[z0,z1,z2,z875,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z6,z876]),(0,[z0,z1,z2,z394,z117,z6]),(0,[z0,z1,z2,z877,z4,z6]),(0,[z0,z1,z2,z21,z285,z6]),(0,[z0,z69,z1,z12,z4,z23])],[(0,[z0,z1,z878,z3,z4,z6]),(0,[z16,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z879,z6]),(0,[z0,z8,z395,z2,z4,z131])],[(0,[z0,z1,z136,z3,z880,z6]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z0,z1,z2,z3,z285,z6]),(0,[z0,z1,z2,z3,z4,z882]),(0,[z0,z1,z2,z883,z4,z6])],[(0,[z0,z1,z2,z118,z43,z6])],[(0,[z0,z1,z136,z12,z4,z6]),(0,[z0,z884,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z378,z6])],[(0,[z0,z31,z2,z21,z33,z6]),(0,[z0,z8,z75,z1,z2,z9])],[(0,[z188,z1,z885,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z886])],[(0,[z0,z1,z887,z3,z4,z6]),(0,[z0,z1,z2,z4,z888,z6]),(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z2,z12,z4,z303]),(0,[z0,z355,z2,z12,z4,z6]),(0,[z0,z1,z2,z260,z43,z6])],[(0,[z0,z1,z2,z3,z4,z890]),(0,[z0,z2,z12,z21,z4,z6]),(0,[z0,z1,z2,z43,z6,z291]),(0,[z135,z0,z1,z3,z241,z6])],[(0,[z0,z1,z2,z21,z552,z6]),(0,[z188,z1,z64,z3,z33,z6]),(0,[z174,z1,z2,z3,z33,z228]),(0,[z0,z1,z2,z891,z4,z6])],[(0,[z0,z1,z2,z892,z4,z6]),(0,[z0,z1,z3,z33,z349,z6])],[(0,[z0,z1,z2,z21,z4,z893]),(0,[z0,z1,z221,z3,z39,z6]),(0,[z0,z1,z2,z9,z155,z6])],[(0,[z0,z481,z1,z2,z4,z23]),(0,[z0,z1,z2,z3,z894,z6]),(0,[z0,z1,z2,z21,z476,z6]),(0,[z0,z1,z2,z21,z6,z374])],[(0,[z0,z1,z442,z333,z4,z6]),(0,[z0,z1,z2,z3,z4,z893]),(0,[z0,z1,z613,z207,z4,z6]),(0,[z0,z1,z22,z3,z43,z70]),(0,[z0,z80,z1,z2,z3,z215]),(0,[z0,z1,z2,z3,z6,z895])],[(0,[z0,z233,z1,z2,z12,z6]),(0,[z0,z1,z109,z224,z4,z6]),(0,[z0,z405,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z476,z6]),(0,[z0,z1,z2,z3,z6,z374])]],
   [[(0,[z0,z1,z2,z3,z896,z6]),(0,[z0,z1,z2,z897,z4,z6]),(0,[z0,z1,z898,z2,z4,z6]),(0,[z574,z1,z2,z83,z4,z6]),(0,[z0,z637,z2,z21,z4,z6]),(0,[z0,z1,z2,z756,z4,z6])],[(0,[z0,z511,z2,z3,z43,z6]),(0,[z0,z405,z2,z3,z4,z6]),(0,[z0,z1,z27,z3,z43,z6])],[(0,[z0,z1,z2,z21,z91,z6]),(0,[z0,z1,z2,z899,z4,z6]),(0,[z0,z1,z2,z900,z4,z6]),(0,[z0,z453,z2,z21,z4,z142])],[(0,[z0,z1,z901,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z902]),(0,[z0,z31,z2,z363,z4,z32]),(0,[z0,z1,z2,z9,z181,z6])],[(0,[z0,z453,z2,z3,z4,z142]),(0,[z0,z1,z3,z708,z4,z6]),(0,[z0,z1,z3,z43,z6,z23])],[(0,[z1,z166,z442,z3,z4,z6]),(0,[z0,z1,z2,z903,z4,z6]),(0,[z0,z233,z1,z2,z163,z6]),(0,[z0,z1,z2,z904,z4,z6]),(0,[z0,z1,z2,z21,z581,z6]),(0,[z0,z905,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z906]),(0,[z299,z1,z2,z83,z4,z6]),(0,[z174,z481,z1,z2,z4,z228]),(0,[z179,z0,z2,z757,z4,z6]),(0,[z0,z138,z2,z3,z477,z6]),(0,[z0,z907,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z823,z142]),(0,[z0,z1,z2,z3,z88,z139])],[(0,[z1,z885,z64,z3,z4,z6]),(0,[z0,z1,z2,z908,z4,z6]),(0,[z376,z1,z2,z151,z4,z6]),(0,[z582,z0,z2,z12,z4,z6]),(0,[z0,z1,z272,z3,z4,z6])],[(0,[z1,z41,z885,z3,z4,z6]),(0,[z0,z1,z2,z308,z467,z6]),(0,[z0,z8,z1,z2,z4,z497]),(0,[z0,z1,z2,z3,z6,z783])],[(0,[z0,z1,z2,z386,z241,z6]),(0,[z0,z1,z2,z3,z909,z6])],[(0,[z0,z2,z21,z359,z4,z6]),(0,[z0,z1,z2,z9,z30,z6]),(0,[z0,z1,z2,z9,z209,z6]),(0,[z0,z1,z2,z3,z783,z215])],[(0,[z0,z1,z2,z910,z4,z6]),(0,[z188,z1,z64,z3,z378,z6]),(0,[z40,z1,z41,z12,z4,z6]),(0,[z0,z1,z3,z43,z6,z180]),(0,[z0,z1,z2,z36,z33,z37])],[(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z912,z4,z6])],[(0,[z0,z1,z2,z913,z4,z6])],[(0,[z0,z1,z2,z914,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z1,z490,z3,z43,z6]),(0,[z0,z1,z2,z3,z33,z916])],[(0,[z0,z1,z221,z3,z88,z6])],[(0,[z62,z166,z136,z3,z4,z6]),(0,[z0,z1,z2,z917,z4,z6]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z0,z1,z2,z919,z4,z6]),(0,[z0,z1,z2,z3,z43,z239])],[(0,[z0,z1,z2,z920,z3,z6]),(0,[z0,z1,z455,z3,z43,z6])],[(0,[z0,z1,z2,z21,z4,z6]),(0,[z0,z1,z2,z921,z4,z6]),(0,[z0,z1,z2,z3,z922,z6]),(0,[z0,z2,z21,z4,z70,z142]),(0,[z0,z1,z2,z3,z4,z923]),(0,[z0,z1,z22,z12,z43,z6])],[(0,[z0,z1,z2,z3,z924,z6]),(0,[z0,z1,z2,z925,z4,z6]),(0,[z0,z2,z21,z4,z6,z650]),(0,[z0,z1,z2,z3,z926,z6]),(0,[z0,z8,z1,z2,z160,z131])],[(0,[z0,z1,z2,z150,z4,z435]),(0,[z0,z1,z2,z3,z927,z6])],[],[(0,[z0,z514,z1,z3,z4,z23])],[(0,[z0,z1,z928,z3,z4,z6]),(0,[z551,z1,z2,z3,z73,z6]),(0,[z0,z1,z2,z203,z4,z137]),(0,[z0,z1,z2,z3,z929,z6]),(0,[z0,z1,z2,z3,z930,z6])],[(0,[z58,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z203,z321,z6]),(0,[z116,z0,z144,z21,z4,z6])],[(0,[z0,z1,z442,z21,z4,z6]),(0,[z0,z1,z2,z12,z4,z435]),(0,[z52,z803,z2,z3,z4,z6]),(1,[z1,z2,z3,z855,z6])],[],[(0,[z0,z1,z442,z3,z4,z6]),(0,[z0,z1,z136,z3,z4,z292]),(0,[z98,z1,z2,z4,z660,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z1,z2,z363,z43,z6])],[(0,[z0,z8,z1,z2,z4,z545]),(0,[z0,z453,z1,z2,z4,z352]),(0,[z0,z1,z2,z12,z4,z146]),(0,[z0,z1,z2,z4,z37,z317])],[(0,[z0,z1,z2,z3,z932,z6]),(0,[z0,z933,z1,z2,z4,z6]),(0,[z0,z597,z2,z21,z4,z6]),(0,[z0,z1,z2,z176,z4,z146])]],
   [[(0,[z0,z206,z2,z825,z4,z6]),(0,[z0,z233,z1,z2,z3,z32]),(0,[z0,z1,z2,z21,z554,z6]),(0,[z0,z934,z1,z2,z3,z4])],[(0,[z0,z935,z2,z3,z4,z6]),(0,[z0,z1,z22,z3,z241,z70])],[(0,[z0,z1,z2,z3,z855,z6]),(0,[z0,z1,z2,z3,z554,z6])],[(0,[z0,z1,z2,z3,z43,z51])],[(0,[z0,z1,z2,z936,z4,z6]),(0,[z0,z1,z2,z4,z6,z937]),(0,[z0,z1,z938,z3,z4,z6]),(0,[z0,z314,z1,z2,z3,z243])],[(0,[z0,z1,z2,z312,z4,z11]),(0,[z0,z1,z2,z4,z6,z939]),(0,[z0,z1,z2,z3,z15,z354])],[(1,[z511,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z0,z1,z2,z82,z241,z6])],[(0,[z0,z1,z2,z3,z941,z6]),(0,[z16,z1,z2,z3,z4,z137]),(0,[z0,z1,z2,z3,z942,z6]),(0,[z0,z1,z22,z386,z4,z70])],[(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z1,z2,z3,z33,z944]),(0,[z0,z1,z2,z3,z4,z465])],[(0,[z0,z1,z2,z333,z28,z6]),(0,[z0,z1,z2,z3,z33,z322]),(0,[z0,z2,z21,z4,z228,z142]),(0,[z0,z1,z2,z945,z43,z6]),(0,[z0,z1,z2,z4,z6,z762]),(0,[z0,z1,z22,z3,z231,z70])],[],[(0,[z188,z1,z64,z21,z4,z6]),(0,[z0,z1,z2,z3,z946,z6]),(0,[z174,z1,z2,z21,z4,z228]),(0,[z0,z481,z1,z2,z4,z70]),(0,[z0,z1,z2,z3,z321,z137]),(0,[z0,z1,z2,z3,z947,z6])],[(0,[z0,z1,z2,z948,z4,z6]),(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z1,z2,z950,z4,z6]),(0,[z0,z1,z2,z3,z4,z951]),(0,[z0,z2,z17,z21,z4,z142]),(0,[z0,z395,z2,z9,z4,z6])],[(0,[z0,z511,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z952,z6]),(0,[z0,z2,z3,z78,z953,z6]),(0,[z0,z1,z2,z954,z4,z6])],[(0,[z0,z1,z2,z3,z4,z955]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z1,z2,z3,z506,z6])],[(0,[z0,z1,z2,z3,z957,z6]),(0,[z42,z1,z2,z13,z43,z6]),(0,[z0,z2,z3,z4,z32,z823]),(0,[z0,z1,z2,z958,z4,z6])]],
   [[(0,[z0,z1,z2,z150,z33,z6]),(0,[z0,z1,z2,z959,z4,z6]),(0,[z0,z233,z1,z2,z21,z6]),(0,[z16,z1,z2,z394,z4,z6]),(1,[z0,z2,z757,z4,z6])],[(0,[z0,z206,z2,z222,z4,z6]),(0,[z0,z960,z1,z2,z4,z6]),(0,[z0,z75,z1,z2,z12,z215]),(0,[z0,z1,z194,z207,z7,z6]),(0,[z0,z69,z1,z3,z337,z23])],[(0,[z0,z481,z1,z2,z4,z6]),(0,[z0,z1,z2,z389,z43,z6]),(0,[z0,z1,z2,z3,z961,z6]),(0,[z0,z1,z3,z33,z385,z6]),(0,[z0,z8,z1,z2,z4,z596])],[(0,[z0,z1,z2,z962,z4,z6]),(0,[z0,z1,z2,z3,z963,z6]),(0,[z0,z1,z609,z3,z43,z6])],[(0,[z0,z1,z2,z964,z4,z6]),(0,[z0,z1,z2,z965,z4,z6]),(0,[z0,z1,z2,z3,z966,z6]),(0,[z0,z1,z2,z394,z321,z6]),(0,[z0,z121,z2,z3,z43,z142]),(0,[z0,z1,z2,z967,z3,z6])],[(0,[z0,z1,z2,z33,z163,z6]),(0,[z0,z1,z2,z12,z33,z6]),(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z453,z1,z2,z4,z131])],[(0,[z0,z2,z969,z3,z4,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z1,z2,z176,z33,z6])],[(0,[z0,z1,z2,z3,z4,z971]),(0,[z52,z105,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z43,z137])],[(0,[z0,z8,z1,z2,z160,z4])],[(0,[z62,z166,z2,z3,z4,z435]),(0,[z76,z1,z2,z3,z43,z108]),(0,[z0,z972,z2,z3,z4,z6])],[(0,[z0,z1,z2,z333,z4,z6]),(0,[z0,z190,z2,z21,z33,z6]),(0,[z0,z1,z2,z3,z178,z254])],[(0,[z0,z1,z2,z3,z378,z322])],[(0,[z1,z2,z3,z842,z4,z6]),(0,[z0,z127,z2,z3,z78,z6])],[(0,[z0,z1,z2,z973,z4,z6]),(0,[z0,z511,z2,z719,z4,z6]),(0,[z0,z1,z2,z312,z33,z6]),(0,[z1,z2,z885,z3,z4,z6]),(0,[z0,z1,z2,z974,z4,z6]),(0,[z0,z1,z2,z3,z33,z199]),(0,[z0,z2,z975,z3,z4,z6]),(0,[z0,z1,z20,z21,z43,z6]),(0,[z0,z1,z2,z17,z4,z371]),(0,[z0,z1,z976,z3,z4,z6]),(0,[z0,z1,z2,z3,z88,z783])],[(0,[z0,z140,z2,z3,z78,z6])],[(0,[z0,z1,z2,z3,z552,z6]),(0,[z0,z1,z20,z3,z43,z6])]],
   [[(0,[z0,z1,z977,z3,z4,z6]),(0,[z0,z206,z2,z3,z33,z6]),(0,[z0,z1,z2,z394,z43,z6]),(0,[z0,z2,z12,z706,z4,z6]),(0,[z0,z1,z2,z978,z4,z6])],[(0,[z0,z1,z2,z3,z979,z6])],[(0,[z0,z1,z980,z2,z3,z6]),(0,[z0,z1,z2,z3,z981,z6]),(0,[z0,z31,z2,z869,z4,z6]),(0,[z0,z1,z194,z475,z4,z6])],[(0,[z0,z1,z22,z82,z4,z70])],[(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z1,z2,z983,z4,z6]),(0,[z0,z1,z2,z5,z163,z6]),(0,[z0,z1,z2,z12,z285,z6]),(0,[z0,z1,z2,z3,z984,z6])],[(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z218,z2,z21,z33,z6]),(0,[z0,z1,z221,z3,z33,z6])],[(0,[z0,z1,z2,z21,z28,z6]),(0,[z0,z1,z2,z4,z986,z6]),(0,[z0,z987,z2,z3,z4,z6]),(0,[z0,z700,z2,z21,z4,z6]),(0,[z0,z2,z260,z4,z6,z142]),(0,[z0,z1,z2,z82,z43,z6])],[(0,[z0,z1,z2,z3,z91,z6]),(0,[z0,z1,z2,z12,z378,z6]),(0,[z0,z1,z219,z3,z4,z70]),(0,[z0,z75,z1,z2,z214,z6])],[(0,[z0,z1,z2,z3,z28,z6]),(0,[z0,z1,z2,z988,z4,z6]),(0,[z0,z1,z240,z3,z43,z6]),(0,[z0,z1,z2,z3,z989,z6])],[(0,[z0,z1,z2,z3,z990,z6])],[(0,[z0,z1,z2,z3,z581,z6])],[(0,[z0,z206,z2,z874,z4,z6]),(0,[z58,z1,z2,z21,z4,z6]),(0,[z179,z0,z2,z12,z4,z6]),(0,[z0,z1,z2,z21,z60,z6]),(0,[z0,z2,z12,z757,z4,z6]),(0,[z0,z1,z2,z4,z6,z991]),(0,[z0,z1,z2,z992,z33,z6])],[(0,[z0,z481,z233,z1,z2,z6]),(0,[z0,z1,z993,z3,z4,z6])],[(0,[z0,z123,z2,z21,z4,z6])],[(0,[z0,z1,z2,z994,z4,z6]),(1,[z0,z8,z1,z2,z160]),(0,[z0,z1,z2,z3,z88,z690])],[(0,[z0,z1,z442,z3,z28,z6]),(0,[z0,z1,z2,z3,z6,z995]),(0,[z996,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z997,z4,z6])]],
   [[(0,[z0,z1,z2,z998,z4,z6]),(0,[z0,z1,z3,z43,z32,z23]),(0,[z0,z1,z2,z999,z4,z6])],[(0,[z0,z1,z2,z1000,z4,z6]),(0,[z0,z1,z2,z12,z476,z6]),(0,[z0,z1,z2,z12,z6,z374])],[(0,[z0,z206,z2,z3,z378,z6]),(0,[z0,z1,z2,z3,z43,z739])],[(0,[z62,z166,z2,z3,z33,z6]),(0,[z0,z1,z2,z1001,z3,z6]),(0,[z0,z2,z21,z4,z108,z142]),(0,[z0,z405,z2,z12,z4,z6]),(1,[z0,z2,z3,z4,z823])],[(0,[z0,z1,z2,z120,z33,z6]),(0,[z0,z1,z2,z3,z1002,z6]),(0,[z0,z1,z2,z438,z33,z6]),(0,[z0,z1,z2,z3,z1003,z6]),(0,[z0,z1004,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z33,z1005]),(0,[z0,z1,z2,z386,z231,z6]),(1,[z0,z75,z1,z2,z214])],[(0,[z0,z1,z2,z3,z1006,z6]),(0,[z188,z1,z64,z3,z552,z6]),(0,[z98,z1,z2,z842,z4,z6]),(0,[z0,z145,z2,z3,z78,z239])],[(0,[z0,z1,z2,z9,z408,z6]),(0,[z0,z2,z3,z953,z39,z6])],[(0,[z0,z1,z2,z156,z4,z6]),(0,[z0,z580,z2,z21,z4,z6]),(0,[z0,z59,z1,z3,z43,z6]),(0,[z0,z1,z2,z3,z4,z1007])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1008,z4,z6])],[(0,[z0,z1,z2,z3,z1009,z6]),(0,[z0,z1,z2,z1010,z4,z6]),(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z1,z272,z12,z4,z6]),(0,[z0,z1012,z1,z2,z3,z6]),(0,[z0,z1,z2,z1013,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1014]),(0,[z1015,z0,z1,z3,z4,z6]),(0,[z0,z1016,z2,z3,z4,z6]),(0,[z0,z1,z2,z1017,z4,z6])],[(0,[z0,z511,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z43,z11]),(0,[z0,z1,z2,z3,z1018,z6]),(0,[z0,z1,z3,z43,z6,z400])],[(0,[z0,z1,z2,z222,z4,z322]),(0,[z0,z1,z2,z1019,z4,z6]),(0,[z0,z1,z79,z3,z43,z6])],[(0,[z0,z1,z2,z3,z33,z292]),(0,[z52,z105,z2,z106,z4,z6]),(0,[z0,z395,z2,z48,z4,z6])],[(0,[z98,z1,z2,z67,z4,z6]),(0,[z1,z2,z3,z4,z6,z721]),(0,[z116,z0,z144,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z1020,z4,z6]),(0,[z0,z1,z2,z3,z4,z723])],[(0,[z0,z1,z2,z3,z1021,z6]),(0,[z0,z182,z1,z154,z4,z6])],[(0,[z0,z1,z2,z791,z21,z6]),(0,[z0,z75,z1,z2,z21,z215]),(0,[z0,z1,z2,z1022,z4,z6])],[(0,[z0,z81,z2,z3,z244,z6]),(0,[z0,z1,z3,z43,z6,z243]),(0,[z0,z1,z2,z33,z6,z1023])],[(0,[z0,z1,z136,z3,z1024,z6]),(0,[z0,z1,z2,z1025,z4,z6])],[(0,[z803,z166,z2,z3,z4,z6]),(0,[z0,z1,z2,z1026,z4,z6]),(0,[z0,z77,z1,z2,z4,z309]),(0,[z0,z643,z2,z12,z4,z6])],[(0,[z0,z1,z2,z757,z4,z6])],[(0,[z62,z166,z2,z333,z4,z6]),(0,[z0,z1,z2,z3,z1027,z4]),(0,[z0,z1,z2,z3,z1028,z6]),(0,[z0,z59,z1,z12,z43,z6]),(0,[z0,z2,z3,z763,z43,z6])],[(0,[z0,z1,z2,z1029,z4,z6]),(1,[z803,z2,z3,z4,z6]),(0,[z0,z1,z2,z1030,z4,z6])],[(0,[z0,z1,z2,z3,z1031,z6])],[],[(0,[z0,z1,z2,z1032,z4,z6]),(0,[z0,z8,z405,z2,z4,z131])],[(0,[z0,z1,z2,z95,z43,z6]),(0,[z0,z31,z2,z21,z4,z6]),(0,[z0,z1,z1033,z2,z4,z6]),(0,[z0,z54,z2,z3,z359,z6])],[(0,[z0,z1,z2,z4,z1034,z6])],[(0,[z0,z93,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z1035]),(0,[z0,z1,z2,z43,z163,z6]),(0,[z0,z1,z2,z21,z4,z199]),(0,[z0,z59,z1,z370,z4,z6]),(0,[z0,z121,z2,z260,z4,z142]),(0,[z0,z1,z1036,z3,z4,z6])],[(0,[z0,z1,z442,z12,z4,z6]),(0,[z0,z803,z2,z3,z4,z6]),(0,[z0,z1037,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1038,z6]),(0,[z0,z8,z1,z2,z33,z131])]],
   [[(0,[z188,z1,z64,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1039]),(0,[z174,z1,z2,z3,z4,z228]),(0,[z0,z1,z2,z3,z1040,z6])],[(0,[z40,z1,z56,z3,z4,z6]),(0,[z0,z206,z2,z21,z4,z6]),(0,[z0,z1,z646,z3,z43,z6]),(0,[z0,z1,z2,z1041,z4,z6]),(0,[z0,z1,z2,z1042,z4,z6]),(0,[z590,z1,z2,z3,z451,z6]),(0,[z0,z1,z2,z82,z231,z6])],[(0,[z0,z1,z2,z333,z4,z292]),(0,[z562,z1,z2,z13,z4,z6]),(0,[z0,z69,z1,z3,z43,z23])],[(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z2,z118,z21,z4,z6]),(0,[z0,z1,z2,z1044,z4,z6])],[(0,[z0,z1,z2,z3,z1045,z6]),(0,[z0,z1,z2,z12,z554,z6]),(1,[z0,z2,z3,z953,z6])],[(0,[z0,z1,z2,z4,z1046,z6]),(1,[z0,z1,z2,z3,z783])],[(0,[z0,z1,z136,z3,z43,z6]),(0,[z0,z1047,z2,z3,z4,z6]),(0,[z0,z1,z2,z394,z4,z137]),(0,[z0,z1,z221,z21,z4,z6]),(0,[z0,z54,z2,z3,z953,z6])],[(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z563,z2,z21,z4,z6]),(0,[z0,z1,z2,z328,z43,z6])],[(0,[z166,z2,z442,z3,z4,z6]),(0,[z0,z1,z2,z214,z33,z6]),(1,[z0,z1,z2,z4,z850])],[(0,[z0,z828,z1,z2,z21,z4]),(0,[z0,z75,z1,z2,z214,z3])],[(0,[z0,z1,z2,z12,z4,z465]),(0,[z0,z1,z2,z3,z43,z303])],[(0,[z98,z1,z2,z83,z33,z6])],[(0,[z0,z1,z2,z1049,z4,z6]),(0,[z0,z1,z2,z308,z30,z6])],[(0,[z0,z2,z153,z21,z4,z6]),(0,[z0,z31,z2,z21,z4,z142]),(0,[z0,z496,z2,z21,z4,z6]),(0,[z0,z1,z2,z1050,z4,z6])],[(0,[z0,z1,z602,z3,z43,z6])],[(0,[z0,z1,z2,z1051,z4,z6])]],
   [[(0,[z0,z1,z3,z43,z6,z484]),(0,[z0,z1,z2,z12,z506,z6])],[(0,[z0,z1,z3,z1052,z4,z6]),(0,[z0,z1,z2,z3,z1053,z6]),(0,[z72,z343,z1,z2,z3,z6]),(0,[z0,z1,z3,z43,z142,z23])],[(0,[z0,z1,z2,z3,z1054,z6]),(0,[z0,z1,z2,z36,z4,z37])],[(0,[z0,z1,z2,z3,z1055,z6]),(0,[z0,z1,z437,z475,z4,z6])],[(0,[z62,z166,z2,z21,z4,z6]),(0,[z0,z1,z2,z1056,z4,z6]),(1,[z1,z2,z3,z4,z721]),(0,[z0,z1,z3,z678,z43,z6])],[(0,[z0,z1,z2,z3,z552,z322]),(0,[z0,z1,z2,z1057,z33,z6])],[(0,[z0,z2,z21,z33,z6,z142]),(0,[z0,z1,z3,z230,z43,z6]),(0,[z0,z1,z2,z3,z4,z916])],[(0,[z0,z1,z1058,z2,z4,z6]),(0,[z0,z395,z2,z3,z33,z6])],[(0,[z0,z1,z1059,z3,z4,z6]),(0,[z0,z2,z21,z4,z6,z309])],[(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z221,z3,z4,z142]),(0,[z1060,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1061,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1062]),(0,[z1,z2,z3,z855,z44,z6]),(0,[z135,z0,z1,z21,z33,z6])],[(0,[z0,z1,z2,z3,z4,z1063]),(0,[z0,z1,z2,z3,z1064,z6]),(0,[z1065,z0,z2,z3,z4,z6])],[(0,[z0,z707,z2,z3,z4,z6]),(0,[z135,z0,z1,z3,z33,z6])],[(0,[z62,z166,z442,z3,z4,z6]),(0,[z0,z1,z194,z207,z33,z6])],[(0,[z0,z1,z2,z1066,z4,z6]),(0,[z0,z1,z2,z3,z4,z1067]),(0,[z40,z1,z41,z3,z43,z6])],[(0,[z0,z1,z2,z3,z1068,z6]),(0,[z0,z1,z2,z21,z4,z292]),(0,[z116,z16,z144,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z1069])]],
   [[(0,[z58,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1070,z4,z6]),(0,[z0,z1071,z1,z2,z4,z6]),(0,[z0,z1,z252,z3,z33,z6]),(0,[z0,z1,z2,z3,z60,z6]),(0,[z0,z1,z2,z4,z6,z291])],[(0,[z0,z1,z2,z4,z1072,z6]),(0,[z0,z1,z2,z12,z552,z6]),(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z1,z20,z12,z43,z6]),(0,[z0,z1,z2,z1074,z4,z6]),(0,[z0,z1,z2,z1075,z4,z6])],[(0,[z0,z1,z2,z312,z378,z6])],[(0,[z52,z381,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z1076,z6]),(0,[z623,z1,z2,z3,z4,z228]),(0,[z0,z1,z1077,z21,z4,z6]),(0,[z0,z1,z12,z33,z43,z6]),(0,[z323,z1,z2,z3,z423,z6])],[(0,[z0,z1,z2,z150,z28,z6]),(0,[z105,z803,z2,z3,z4,z6]),(0,[z0,z80,z1,z2,z3,z279])],[(0,[z0,z1,z1077,z3,z4,z6]),(0,[z161,z0,z144,z3,z4,z6]),(0,[z0,z75,z1,z221,z3,z215]),(0,[z0,z75,z1,z2,z291,z215])],[(0,[z0,z1,z2,z1078,z4,z6])],[(0,[z0,z1,z442,z3,z4,z292]),(0,[z0,z1,z2,z3,z1079,z6]),(0,[z0,z1080,z2,z3,z4,z6]),(0,[z14,z1,z2,z3,z423,z6]),(0,[z0,z1,z2,z3,z1081,z6]),(0,[z0,z1,z2,z21,z117,z6]),(0,[z0,z420,z2,z21,z4,z6]),(0,[z0,z300,z1,z2,z9,z30]),(0,[z0,z1,z2,z4,z37,z850])],[(0,[z0,z1082,z2,z3,z4,z6]),(0,[z0,z1,z2,z312,z552,z6]),(0,[z0,z1,z2,z12,z91,z6]),(0,[z0,z1,z2,z203,z33,z6])],[(0,[z0,z1,z2,z12,z28,z6]),(0,[z376,z1,z2,z13,z4,z6]),(0,[z72,z1,z2,z3,z855,z6]),(0,[z1083,z1,z2,z3,z4,z6]),(0,[z0,z75,z2,z21,z4,z142]),(0,[z0,z81,z2,z3,z39,z6])],[(0,[z0,z1,z2,z106,z43,z6]),(0,[z14,z1,z2,z3,z855,z6]),(0,[z0,z8,z1,z221,z3,z4])],[(0,[z0,z206,z2,z3,z552,z6]),(0,[z0,z1,z2,z12,z581,z6])],[(0,[z0,z1,z2,z3,z43,z435]),(0,[z0,z1,z2,z3,z1084,z6]),(0,[z0,z1,z2,z21,z4,z322]),(0,[z0,z1,z2,z1085,z4,z6]),(0,[z0,z31,z2,z3,z33,z32]),(0,[z0,z1,z2,z386,z33,z6]),(0,[z0,z1,z3,z506,z6,z23])],[(0,[z0,z1,z993,z12,z4,z6]),(0,[z0,z934,z1,z2,z3,z43]),(0,[z0,z1,z2,z3,z4,z944])],[(0,[z0,z1,z442,z3,z1079,z6]),(0,[z0,z1,z2,z1086,z4,z6]),(0,[z0,z1,z2,z3,z4,z322]),(0,[z42,z1,z2,z842,z4,z6]),(0,[z0,z1,z2,z1087,z3,z6])]],
   [[(0,[z0,z1,z1088,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z146])],[(0,[z0,z1,z2,z3,z1089,z6]),(0,[z0,z145,z2,z3,z78,z146]),(0,[z0,z1,z2,z3,z60,z142]),(0,[z0,z1,z304,z3,z43,z6]),(0,[z0,z1090,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z4,z1091]),(0,[z0,z1,z2,z3,z4,z1092]),(0,[z0,z1,z409,z3,z43,z6]),(0,[z0,z691,z1,z3,z33,z6])],[(0,[z0,z1,z2,z3,z1093,z6]),(0,[z0,z31,z2,z21,z60,z6]),(0,[z0,z1,z2,z1094,z4,z6])],[],[(0,[z0,z71,z2,z21,z4,z6]),(0,[z0,z1,z2,z4,z6,z1095])],[(0,[z0,z1,z2,z150,z4,z6]),(0,[z0,z1,z2,z3,z1096,z6]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z0,z286,z1,z126,z43,z6]),(0,[z0,z1,z1098,z3,z4,z6])],[(0,[z0,z1,z2,z1099,z3,z6]),(0,[z449,z1,z64,z3,z4,z6]),(0,[z1,z511,z64,z3,z4,z6]),(0,[z16,z1,z2,z3,z33,z6]),(0,[z0,z2,z21,z4,z6,z548]),(0,[z0,z1,z2,z1100,z4,z6]),(0,[z0,z1,z2,z9,z465,z30])],[(0,[z0,z511,z2,z222,z4,z6]),(0,[z0,z1,z2,z222,z43,z6]),(0,[z40,z1,z41,z3,z25,z6]),(0,[z0,z395,z2,z126,z4,z6]),(0,[z0,z1,z2,z844,z43,z6]),(0,[z0,z300,z1,z2,z9,z4])],[(0,[z0,z1,z2,z3,z880,z6]),(0,[z116,z0,z975,z3,z4,z6]),(0,[z0,z1,z2,z118,z33,z6]),(0,[z0,z75,z1,z2,z3,z185]),(0,[z0,z1,z2,z3,z6,z1101])],[(0,[z0,z1,z136,z3,z278,z6]),(0,[z0,z1,z2,z1102,z4,z6]),(0,[z0,z2,z295,z21,z4,z6]),(0,[z0,z1,z2,z3,z953,z6])],[(0,[z0,z1,z2,z12,z4,z6]),(0,[z52,z105,z2,z21,z4,z6]),(0,[z0,z1103,z2,z3,z4,z6]),(0,[z0,z1104,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z849])],[(0,[z0,z1,z2,z176,z4,z6])],[(0,[z52,z105,z2,z3,z4,z6]),(0,[z0,z1,z442,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z1105])],[(0,[z0,z1,z1106,z3,z4,z6]),(0,[z0,z2,z704,z12,z4,z6]),(0,[z0,z1,z2,z260,z33,z6])],[(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1108,z1,z3,z4,z6])]],
   [[(0,[z0,z190,z2,z21,z4,z6]),(0,[z0,z1,z3,z178,z43,z23])],[(0,[z116,z0,z144,z12,z4,z6])],[(0,[z0,z1,z1109,z2,z4,z6]),(0,[z0,z145,z2,z3,z953,z6])],[(0,[z0,z1,z2,z3,z4,z199])],[(0,[z0,z511,z41,z3,z4,z6]),(0,[z0,z1,z2,z3,z1110,z6]),(0,[z0,z1,z2,z1111,z4,z6]),(0,[z0,z1,z2,z3,z1112,z6]),(0,[z0,z1,z22,z3,z33,z70]),(0,[z0,z1,z2,z4,z6,z850])],[],[(0,[z0,z206,z2,z3,z4,z6]),(0,[z188,z1,z64,z3,z4,z322])],[(0,[z0,z1,z2,z1113,z4,z6]),(0,[z0,z511,z2,z3,z33,z6]),(0,[z16,z2,z144,z3,z4,z6]),(0,[z238,z1,z2,z297,z4,z6]),(0,[z0,z1,z2,z3,z708,z6])],[(0,[z62,z166,z2,z3,z28,z6]),(0,[z0,z395,z2,z21,z4,z6]),(0,[z0,z1114,z2,z3,z4,z6])],[(0,[z175,z105,z2,z3,z4,z6]),(0,[z116,z0,z144,z3,z4,z199]),(0,[z0,z1,z2,z499,z43,z6])],[(0,[z40,z1,z885,z3,z4,z6]),(0,[z299,z1,z2,z122,z4,z6])],[(0,[z0,z1,z2,z1115,z4,z6]),(0,[z0,z1,z2,z3,z1116,z6]),(0,[z0,z218,z2,z21,z4,z6]),(0,[z0,z1,z2,z12,z1031,z6]),(0,[z0,z1,z2,z3,z4,z1117]),(0,[z0,z145,z2,z328,z78,z6]),(0,[z0,z1,z221,z3,z4,z6]),(0,[z0,z1,z2,z1118,z4,z6]),(0,[z0,z8,z1,z2,z543,z4])],[(0,[z167,z0,z144,z3,z4,z6]),(0,[z116,z58,z144,z3,z4,z6]),(0,[z0,z1,z26,z3,z43,z6]),(0,[z0,z75,z1,z2,z3,z243]),(0,[z0,z1,z272,z3,z241,z6]),(0,[z0,z75,z1,z2,z3,z181])],[(0,[z89,z166,z2,z3,z4,z6]),(0,[z0,z8,z1,z2,z4,z309])],[(0,[z0,z1,z2,z3,z6,z1119]),(0,[z0,z80,z1,z3,z43,z23])],[(0,[z0,z2,z21,z43,z6,z142]),(0,[z179,z0,z2,z118,z4,z6]),(0,[z0,z1,z22,z386,z43,z6])]],
   [[],[(0,[z0,z1,z2,z992,z4,z6])],[(0,[z0,z1,z2,z1120,z4,z6]),(0,[z188,z1,z64,z12,z4,z6]),(0,[z174,z1,z2,z12,z4,z228])],[(0,[z0,z1,z2,z3,z28,z292]),(0,[z0,z1,z2,z3,z1121,z6]),(0,[z0,z481,z1,z2,z43,z6]),(0,[z0,z1,z22,z3,z506,z6])],[(0,[z40,z511,z2,z3,z4,z6]),(0,[z0,z557,z2,z21,z4,z6]),(0,[z0,z75,z1,z2,z3,z439]),(0,[z0,z1,z2,z1122,z4,z6])],[(0,[z0,z1,z2,z3,z1123,z6])],[(0,[z0,z1,z221,z36,z3,z4])],[(0,[z0,z405,z2,z118,z4,z6])],[(0,[z0,z1,z2,z920,z21,z6]),(0,[z0,z1,z2,z21,z313,z6]),(0,[z0,z1,z2,z3,z33,z239]),(0,[z0,z286,z1,z126,z4,z51]),(0,[z0,z8,z1,z3,z43,z23]),(0,[z0,z395,z2,z3,z4,z23])],[(0,[z62,z166,z2,z3,z4,z6]),(0,[z0,z511,z2,z3,z378,z6])],[(0,[z0,z1,z2,z120,z4,z6]),(0,[z188,z1,z64,z312,z4,z6]),(0,[z0,z1,z2,z438,z4,z6]),(0,[z0,z1,z2,z3,z313,z6]),(0,[z0,z1,z357,z3,z43,z6])],[(0,[z0,z1,z2,z333,z43,z6]),(0,[z0,z1,z2,z1124,z4,z6]),(0,[z0,z1,z2,z3,z1125,z6]),(0,[z0,z1,z2,z328,z4,z239]),(0,[z0,z1,z2,z1126,z3,z6]),(0,[z0,z1,z2,z3,z4,z1005])],[(0,[z0,z2,z636,z12,z4,z6]),(0,[z0,z578,z1,z3,z4,z23])],[(0,[z188,z206,z64,z3,z4,z6]),(0,[z0,z2,z12,z21,z43,z6])],[(0,[z0,z1,z2,z3,z4,z721]),(0,[z0,z31,z2,z21,z4,z32])],[(0,[z0,z1,z2,z3,z1127,z6])]],
   [[(0,[z0,z1,z2,z1128,z4,z6]),(0,[z0,z1129,z1,z2,z4,z6]),(0,[z1130,z1,z2,z3,z4,z6]),(0,[z0,z395,z2,z36,z4,z6])],[(0,[z0,z1,z2,z3,z278,z435]),(0,[z0,z1,z2,z3,z1131,z6])],[(0,[z0,z1,z2,z3,z4,z1132]),(0,[z0,z1,z2,z3,z1133,z6])],[(0,[z0,z2,z3,z953,z4,z6]),(0,[z0,z1,z2,z363,z33,z6]),(0,[z0,z218,z2,z3,z196,z6])],[(0,[z0,z1,z2,z3,z4,z292]),(0,[z0,z1,z2,z3,z4,z1069])],[(0,[z76,z1,z2,z3,z4,z721]),(0,[z0,z1,z2,z1134,z4,z6]),(0,[z0,z1,z2,z3,z6,z1135]),(0,[z0,z75,z1,z2,z3,z479]),(0,[z0,z405,z2,z3,z43,z6])],[(0,[z0,z1,z2,z900,z43,z6]),(0,[z0,z1,z440,z3,z43,z6])],[(0,[z0,z1,z2,z3,z4,z1136]),(0,[z0,z1,z3,z43,z228,z23]),(0,[z0,z286,z1,z154,z4,z6]),(0,[z0,z1,z3,z4,z6,z723]),(0,[z0,z1,z221,z9,z3,z6])],[(0,[z0,z1,z2,z1137,z4,z6]),(0,[z0,z1,z2,z1138,z4,z6]),(0,[z16,z1,z2,z21,z4,z6]),(0,[z0,z1,z27,z126,z4,z6]),(0,[z0,z1,z3,z708,z43,z6])],[(1,[z1,z885,z3,z4,z6]),(0,[z0,z1,z2,z3,z33,z51])],[(0,[z0,z1,z2,z3,z1139,z6]),(0,[z0,z1,z221,z3,z4,z32])],[(0,[z0,z1,z22,z82,z43,z6])],[(0,[z0,z1,z2,z1140,z3,z6]),(0,[z0,z1,z2,z3,z78,z146]),(0,[z0,z1,z2,z908,z43,z6]),(0,[z0,z1,z272,z3,z43,z6])],[(0,[z0,z1,z2,z3,z1141,z6]),(0,[z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z21,z88,z15]),(0,[z0,z2,z200,z12,z4,z6])],[(0,[z0,z1142,z2,z3,z4,z6]),(0,[z0,z1,z633,z3,z33,z6]),(0,[z135,z0,z1,z12,z33,z6])],[(0,[z0,z1,z219,z3,z43,z6]),(0,[z0,z1,z194,z207,z285,z6]),(0,[z0,z1,z2,z3,z88,z15])]],
   [[],[(0,[z0,z31,z2,z3,z4,z823]),(0,[z0,z395,z2,z207,z4,z6])],[(0,[z58,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1143,z6]),(0,[z0,z1,z2,z12,z60,z6]),(0,[z0,z1,z2,z3,z758,z6])],[(0,[z0,z1,z2,z12,z4,z292]),(0,[z0,z1,z2,z3,z1144,z6]),(0,[z116,z0,z144,z3,z117,z6])],[],[(0,[z0,z1145,z1,z2,z4,z6]),(0,[z42,z1,z2,z13,z33,z6]),(0,[z0,z1,z22,z21,z4,z70]),(0,[z0,z8,z1,z2,z4,z131])],[(0,[z0,z1,z1146,z2,z4,z6]),(0,[z0,z1,z3,z33,z657,z6]),(0,[z0,z1,z2,z3,z1147,z6])],[(0,[z0,z1,z2,z4,z1148,z6]),(0,[z0,z1,z2,z3,z4,z783])],[(0,[z0,z511,z2,z21,z4,z6]),(0,[z0,z1,z2,z389,z33,z6]),(0,[z0,z1,z2,z21,z43,z6]),(0,[z0,z1,z2,z3,z1149,z6]),(0,[z0,z300,z1,z2,z3,z4])],[(0,[z1,z803,z2,z3,z4,z6]),(0,[z0,z1,z2,z1150,z4,z6]),(0,[z0,z1,z2,z1151,z4,z6]),(0,[z0,z140,z2,z21,z4,z6]),(0,[z0,z1,z1152,z2,z33,z6]),(0,[z0,z75,z395,z2,z3,z4])],[(0,[z521,z0,z144,z3,z4,z6]),(0,[z58,z1,z2,z3,z4,z199]),(0,[z0,z1,z2,z21,z337,z6]),(0,[z0,z121,z2,z3,z33,z142])],[(0,[z0,z1,z2,z1153,z4,z6]),(0,[z0,z1,z2,z21,z1154,z6]),(0,[z0,z1,z2,z3,z1155,z6])],[(0,[z0,z1,z2,z3,z337,z6])],[(0,[z0,z2,z625,z21,z4,z6]),(0,[z0,z1,z2,z3,z33,z137]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z0,z1,z2,z3,z1154,z6]),(0,[z0,z700,z2,z3,z4,z32]),(0,[z0,z8,z1,z2,z160,z6])],[(0,[z0,z1,z3,z33,z604,z6]),(0,[z0,z1,z2,z3,z1156,z6]),(0,[z0,z1,z613,z3,z43,z6]),(0,[z0,z713,z2,z3,z33,z6]),(0,[z0,z1,z2,z214,z4,z6])],[(0,[z0,z1,z2,z1157,z4,z6]),(0,[z0,z1,z2,z3,z1158,z6]),(0,[z76,z1,z2,z3,z33,z108]),(0,[z0,z1,z2,z3,z1159,z6])]],
   [[(0,[z0,z1,z2,z1160,z4,z6])],[(0,[z0,z1,z442,z3,z43,z6]),(0,[z0,z1,z2,z12,z4,z322]),(0,[z98,z1,z2,z83,z4,z6]),(0,[z0,z1,z2,z3,z1161,z6]),(0,[z0,z1,z2,z1162,z4,z6]),(0,[z622,z0,z1,z3,z33,z6]),(0,[z0,z1,z194,z761,z4,z6])],[(0,[z0,z1,z2,z1163,z4,z6]),(0,[z0,z1,z2,z3,z60,z32])],[],[(0,[z0,z1164,z1,z2,z3,z6])],[(0,[z469,z1,z2,z3,z4,z108]),(0,[z0,z2,z869,z21,z4,z6]),(1,[z0,z1,z761,z4,z6]),(0,[z0,z1,z2,z3,z476,z51]),(0,[z0,z1,z2,z1165,z4,z6]),(0,[z0,z1,z2,z160,z3,z6])],[(0,[z0,z1,z2,z312,z4,z6]),(0,[z0,z1,z2,z394,z33,z6])],[],[],[(0,[z0,z1,z3,z33,z708,z6])],[(0,[z0,z1,z109,z207,z4,z6]),(0,[z0,z1,z761,z3,z4,z6])],[(0,[z0,z1166,z1,z3,z4,z6]),(0,[z100,z1,z64,z3,z4,z6]),(1,[z1,z2,z842,z4,z6]),(0,[z0,z491,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z1167,z6]),(0,[z0,z1168,z2,z3,z4,z6]),(0,[z0,z1,z2,z1057,z4,z6])],[(0,[z0,z206,z2,z3,z4,z322]),(0,[z0,z1,z2,z3,z1169,z6]),(0,[z0,z1,z2,z3,z43,z465]),(0,[z0,z1,z2,z82,z33,z6])],[(0,[z0,z395,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z581,z51]),(0,[z1170,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1171,z4,z6])],[(0,[z0,z1,z2,z333,z278,z6]),(0,[z52,z105,z2,z12,z4,z6]),(0,[z0,z975,z144,z3,z4,z6]),(0,[z0,z1,z2,z1172,z4,z6]),(0,[z0,z1,z2,z3,z88,z34])]],
   [[(0,[z0,z1,z2,z3,z43,z951]),(0,[z0,z1004,z1,z2,z3,z33])],[(0,[z62,z166,z2,z3,z4,z292]),(0,[z0,z1,z2,z3,z1173,z6]),(0,[z0,z1,z2,z3,z1174,z6]),(0,[z0,z1108,z1,z12,z4,z6])],[(0,[z0,z1,z2,z842,z4,z6]),(0,[z0,z1,z2,z3,z1175,z6]),(0,[z0,z190,z2,z757,z4,z6]),(0,[z0,z2,z302,z12,z4,z6]),(0,[z0,z1,z2,z1176,z4,z6]),(0,[z0,z395,z2,z4,z6,z131]),(0,[z0,z1,z2,z1177,z4,z6])],[(0,[z0,z1,z2,z3,z1178,z6]),(0,[z0,z1,z2,z222,z4,z11]),(0,[z0,z1179,z1,z2,z3,z6]),(0,[z0,z1,z194,z207,z4,z6])],[(0,[z0,z1,z2,z1180,z4,z6]),(0,[z0,z2,z21,z104,z4,z6])],[(0,[z0,z1,z2,z4,z163,z6]),(0,[z0,z1,z2,z12,z4,z199])],[(0,[z0,z452,z2,z21,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1181]),(0,[z0,z1,z22,z3,z4,z247])],[(0,[z0,z105,z442,z3,z4,z6]),(0,[z0,z206,z2,z12,z4,z6]),(0,[z0,z1,z2,z1182,z4,z6]),(0,[z0,z1,z2,z3,z4,z1183]),(0,[z0,z1,z221,z3,z230,z6])],[],[(0,[z0,z1,z2,z3,z1184,z6]),(1,[z16,z144,z3,z4,z6]),(0,[z0,z1,z2,z21,z1185,z6]),(0,[z0,z1,z2,z21,z4,z51]),(0,[z0,z1,z2,z3,z1186,z6])],[(0,[z14,z1,z2,z3,z187,z6]),(0,[z0,z1,z2,z21,z241,z6]),(0,[z0,z1,z1187,z3,z4,z6]),(0,[z0,z1,z2,z160,z36,z3])],[(0,[z0,z1,z444,z3,z43,z6]),(0,[z72,z0,z1,z221,z3,z6]),(0,[z0,z1,z36,z3,z43,z23])],[(0,[z0,z1,z2,z3,z4,z1188]),(0,[z14,z0,z1,z221,z3,z6]),(0,[z0,z1,z2,z12,z1116,z6]),(0,[z0,z1,z2,z12,z4,z1117]),(0,[z0,z1,z221,z12,z4,z6]),(0,[z0,z1,z2,z3,z39,z146])],[(0,[z0,z1,z55,z3,z33,z6]),(0,[z0,z1,z2,z714,z30,z6]),(0,[z0,z1,z2,z160,z37,z6])],[(0,[z0,z744,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1189,z6]),(0,[z0,z1,z2,z203,z4,z6])]],
   [[(0,[z0,z206,z2,z312,z4,z6]),(0,[z0,z1,z1190,z21,z4,z6])],[(0,[z0,z1,z2,z1191,z4,z6]),(0,[z0,z16,z144,z3,z4,z6]),(0,[z0,z689,z2,z21,z4,z6]),(0,[z0,z1,z2,z3,z4,z1192]),(0,[z0,z1,z2,z1193,z4,z6])],[(0,[z0,z1,z136,z3,z4,z435]),(0,[z0,z1,z2,z3,z33,z11]),(0,[z0,z1,z2,z3,z1194,z6])],[(0,[z511,z2,z64,z3,z4,z6]),(0,[z0,z511,z2,z3,z552,z6]),(0,[z0,z1,z2,z3,z1195,z6]),(0,[z0,z1,z2,z3,z4,z1196]),(0,[z0,z1,z2,z21,z231,z6]),(0,[z0,z31,z2,z3,z4,z32]),(0,[z0,z1,z2,z386,z4,z6]),(0,[z0,z1,z2,z3,z1197,z6])],[(0,[z58,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z4,z1198]),(0,[z0,z1,z2,z1199,z4,z6])],[(0,[z116,z0,z144,z203,z4,z6]),(0,[z0,z1,z2,z3,z1200,z6])],[(0,[z62,z166,z2,z150,z4,z6]),(0,[z0,z1,z2,z328,z4,z146]),(0,[z0,z1,z2,z3,z1201,z6])],[(0,[z0,z1,z2,z3,z1202,z6]),(0,[z0,z1,z2,z1203,z4,z6]),(0,[z0,z1,z2,z3,z1204,z6]),(0,[z0,z1,z2,z1205,z4,z6]),(0,[z0,z1090,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1206,z6])],[],[],[(0,[z0,z1,z2,z21,z607,z6]),(0,[z0,z1,z2,z3,z6,z1207]),(0,[z0,z300,z1,z2,z9,z6])],[(0,[z0,z1,z2,z3,z1024,z6]),(0,[z62,z166,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1208,z6]),(0,[z0,z1,z2,z1209,z4,z6]),(0,[z0,z1,z2,z1210,z4,z6]),(0,[z0,z1,z2,z1211,z3,z6])],[(0,[z0,z1,z2,z21,z278,z6]),(0,[z0,z1,z2,z3,z4,z1212]),(0,[z174,z1,z2,z4,z163,z228]),(0,[z0,z1,z2,z12,z313,z6])],[(0,[z16,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z840,z3,z4]),(0,[z0,z1,z2,z1213,z4,z6]),(0,[z0,z1,z2,z12,z1125,z6]),(0,[z0,z1,z2,z1140,z12,z6])],[(0,[z0,z1,z2,z21,z4,z137])],[(0,[z0,z1,z2,z21,z321,z6]),(0,[z0,z1,z2,z118,z4,z6]),(0,[z179,z0,z2,z12,z43,z6]),(0,[z0,z286,z1,z126,z4,z303]),(0,[z0,z8,z1,z2,z160,z3]),(0,[z0,z1,z2,z4,z6,z1214])]],
   [[(0,[z0,z31,z2,z21,z313,z6]),(0,[z0,z75,z1,z2,z3,z783])],[(0,[z0,z1,z2,z3,z1215,z6]),(0,[z0,z1,z2,z150,z4,z292]),(0,[z0,z1,z2,z1216,z4,z6]),(0,[z0,z1,z1217,z3,z4,z6]),(0,[z0,z1,z2,z3,z321,z6]),(0,[z0,z54,z2,z21,z39,z6]),(0,[z0,z1,z761,z207,z4,z6]),(0,[z0,z1,z2,z386,z4,z23])],[(0,[z0,z1,z2,z95,z33,z6]),(0,[z0,z300,z1,z2,z115,z3])],[(0,[z0,z1,z2,z3,z1218,z6]),(0,[z0,z1,z885,z3,z4,z6]),(0,[z0,z591,z2,z21,z4,z6])],[(0,[z0,z1,z1219,z3,z4,z6]),(0,[z0,z1,z2,z3,z378,z11]),(0,[z0,z1,z513,z3,z43,z6]),(0,[z0,z1,z2,z260,z4,z6])],[(0,[z0,z1,z442,z3,z278,z6])],[(0,[z100,z166,z2,z3,z4,z6]),(0,[z0,z1,z3,z472,z43,z6]),(0,[z0,z1,z2,z3,z1220,z6]),(0,[z0,z517,z2,z21,z4,z6]),(0,[z0,z75,z1,z2,z3,z662])],[(0,[z116,z0,z144,z3,z321,z6]),(0,[z0,z1,z2,z3,z1221,z6]),(0,[z0,z1,z2,z12,z6,z1135])],[(0,[z0,z1,z475,z3,z43,z6]),(0,[z0,z1,z2,z3,z1027,z43]),(0,[z0,z69,z1,z3,z33,z23])],[(0,[z0,z1,z12,z43,z6,z23])],[(0,[z0,z1,z2,z3,z1222,z6]),(0,[z0,z1,z22,z3,z4,z70])],[(0,[z0,z1,z2,z3,z1223,z6]),(0,[z0,z1,z2,z3,z4,z1224])],[(0,[z0,z1,z136,z3,z33,z6]),(0,[z1,z2,z3,z73,z855,z6]),(0,[z0,z145,z2,z21,z78,z6]),(0,[z0,z1,z2,z156,z43,z6])],[(0,[z0,z1,z2,z3,z43,z6]),(0,[z0,z511,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1225]),(0,[z0,z1,z2,z3,z1226,z6]),(0,[z0,z1,z2,z3,z1227,z6]),(0,[z0,z1,z2,z328,z33,z6]),(0,[z0,z1,z2,z1228,z4,z6])],[(0,[z0,z1,z2,z3,z4,z741]),(0,[z0,z1,z2,z36,z4,z457]),(0,[z0,z145,z2,z3,z78,z6]),(0,[z0,z1,z2,z1010,z43,z6])],[(0,[z0,z1,z2,z12,z117,z6]),(0,[z0,z59,z1,z126,z4,z6]),(0,[z0,z121,z2,z499,z4,z142]),(0,[z0,z1,z2,z1229,z4,z6])]],
   [[(0,[z0,z2,z21,z88,z4,z142]),(0,[z0,z1,z2,z3,z33,z303])],[(0,[z0,z75,z1,z2,z3,z683]),(0,[z0,z1,z2,z12,z88,z15]),(0,[z0,z1,z119,z3,z43,z6])],[(0,[z0,z1,z493,z3,z43,z6]),(0,[z174,z1,z2,z3,z4,z721]),(0,[z0,z1,z2,z3,z1230,z6])],[(0,[z0,z501,z2,z12,z4,z6]),(0,[z116,z0,z144,z3,z43,z6]),(0,[z0,z1,z2,z4,z6,z1023])],[(0,[z166,z64,z144,z3,z4,z6]),(0,[z167,z1,z64,z3,z4,z6]),(0,[z0,z511,z2,z1020,z4,z6])],[(0,[z0,z1,z2,z3,z1231,z6]),(0,[z0,z24,z1,z3,z33,z6])],[(0,[z0,z1,z2,z1232,z4,z6])],[(0,[z0,z1,z2,z3,z117,z199]),(0,[z0,z1,z2,z1233,z4,z6])],[(0,[z0,z2,z21,z4,z6,z35]),(0,[z0,z1,z2,z1234,z4,z6]),(0,[z0,z1,z22,z3,z4,z723])],[(0,[z1235,z1,z2,z3,z4,z6]),(0,[z0,z395,z2,z3,z4,z70])],[(0,[z0,z145,z2,z3,z477,z6])],[(0,[z0,z1,z2,z3,z1236,z6]),(0,[z0,z1,z2,z3,z1237,z6]),(0,[z0,z8,z1,z2,z4,z850]),(0,[z0,z1,z221,z3,z6,z215])],[(0,[z0,z1,z2,z312,z4,z322]),(0,[z0,z1,z2,z21,z4,z239]),(0,[z0,z2,z648,z21,z4,z6])],[(0,[z0,z1,z2,z3,z1238,z6])],[(0,[z0,z1,z2,z12,z337,z6]),(0,[z0,z1,z2,z3,z4,z239])],[(0,[z0,z1,z2,z3,z4,z1239]),(0,[z0,z1,z2,z3,z4,z1240]),(0,[z0,z1,z2,z1032,z43,z6]),(0,[z0,z1,z2,z804,z33,z6]),(0,[z0,z336,z1,z2,z155,z6])]],
   [[(0,[z0,z31,z2,z21,z43,z6])],[(1,[z166,z442,z3,z4,z6])],[(0,[z0,z1,z2,z1241,z4,z6]),(0,[z0,z1,z2,z21,z7,z6]),(0,[z0,z1,z2,z3,z1242,z6])],[(0,[z0,z1,z2,z21,z4,z11]),(0,[z0,z481,z1,z2,z5,z6])],[(0,[z188,z511,z64,z3,z4,z6]),(0,[z188,z1,z64,z3,z43,z6]),(0,[z40,z1,z41,z3,z33,z6]),(0,[z174,z1,z2,z3,z43,z228]),(0,[z0,z1,z3,z43,z108,z23]),(0,[z0,z1,z21,z33,z43,z6]),(0,[z0,z1243,z1,z2,z3,z6])],[(0,[z0,z1,z2,z21,z25,z6])],[(0,[z58,z1,z2,z203,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1244]),(0,[z0,z1,z2,z3,z25,z6]),(0,[z0,z1245,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z6,z1246])],[(0,[z661,z1,z2,z3,z4,z228]),(0,[z0,z1,z2,z363,z4,z6])],[(0,[z521,z166,z2,z3,z4,z6]),(0,[z16,z169,z2,z3,z4,z6]),(0,[z0,z31,z2,z3,z60,z32])],[(0,[z235,z1,z2,z3,z542,z6])],[(0,[z0,z300,z1,z2,z9,z3])],[(0,[z0,z1,z1247,z3,z4,z6]),(0,[z0,z1,z2,z3,z1248,z6]),(0,[z1249,z1,z2,z3,z4,z6]),(0,[z0,z140,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z1250,z6])],[(0,[z0,z1,z2,z3,z1251,z6]),(0,[z0,z249,z2,z12,z4,z6]),(0,[z0,z300,z1,z2,z48,z4])],[(0,[z0,z1,z2,z3,z1185,z6]),(0,[z0,z395,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z51]),(0,[z0,z1,z2,z386,z4,z70])]],
   [[(0,[z0,z1,z2,z3,z241,z6]),(0,[z0,z1252,z2,z3,z4,z6])],[(0,[z0,z1,z2,z106,z33,z6]),(0,[z0,z1253,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1254,z4,z6]),(0,[z0,z1,z1255,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1256]),(0,[z0,z1,z12,z475,z43,z6]),(0,[z0,z8,z1,z2,z486,z4])],[(0,[z0,z1,z2,z3,z33,z435]),(0,[z0,z1,z2,z3,z1257,z6])],[(0,[z0,z1258,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1259,z6]),(0,[z0,z1,z3,z43,z6,z201])],[(0,[z0,z1,z1190,z3,z4,z6]),(0,[z0,z1,z2,z945,z4,z6])],[(0,[z0,z2,z21,z4,z6,z142]),(0,[z0,z1,z2,z3,z33,z146]),(0,[z0,z1,z2,z118,z60,z6]),(0,[z0,z1,z2,z36,z43,z37]),(0,[z0,z1,z1260,z3,z4,z6]),(0,[z0,z1,z2,z4,z850,z131])],[(0,[z58,z1,z2,z3,z4,z137]),(0,[z1261,z1,z2,z3,z4,z6])],[(0,[z58,z1,z2,z3,z321,z6]),(0,[z0,z1,z2,z3,z231,z6]),(0,[z0,z1,z538,z3,z33,z6])],[(0,[z0,z1,z311,z3,z43,z6]),(0,[z0,z1,z2,z1262,z4,z6])],[(0,[z0,z598,z2,z21,z4,z6]),(0,[z0,z1,z975,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z1183]),(0,[z0,z448,z2,z3,z4,z142])],[(0,[z0,z1,z2,z3,z1263,z6]),(0,[z42,z1,z2,z13,z4,z6]),(0,[z0,z1,z38,z207,z4,z6]),(0,[z0,z1,z165,z2,z408,z6])],[(0,[z1,z2,z842,z13,z4,z6]),(0,[z0,z2,z12,z436,z4,z6]),(0,[z0,z1,z2,z1099,z21,z6]),(0,[z0,z286,z1,z126,z33,z6]),(0,[z0,z1,z2,z1264,z4,z6])],[(0,[z0,z1,z136,z21,z4,z6]),(0,[z0,z1,z1265,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1266]),(0,[z0,z1,z2,z222,z33,z6]),(0,[z0,z1,z2,z389,z4,z6]),(0,[z0,z1,z2,z3,z1267,z6]),(0,[z0,z121,z2,z21,z4,z142]),(0,[z0,z1,z2,z9,z714,z6])],[(0,[z0,z1,z2,z3,z607,z6]),(0,[z0,z1,z2,z12,z241,z6]),(0,[z0,z1,z1152,z2,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 512).take 508) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1020).take 368) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1388)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [512, 508, 368] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 163).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 163).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 305).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 447).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [163, 142, 142, 65] = true :=
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

end PEqualNP.Outside.L_meta_39295

theorem PEqualNP.Outside.L_meta_39295 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4272487072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4272487072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39295.solve