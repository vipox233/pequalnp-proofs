import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41096

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4272596992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00828e30c01555ba#64 ++ 0x000828e30c01555b#64 ++ 0xc18f9e31c03ffffd#64 ++ 0xec18f9e31c03ffff#64 : BitVec 256),
   (0x423622f630cccc5c#64 ++ 0x0423622f630cccc5#64 ++ 0x467667fe31cccc7b#64 ++ 0xe467667fe31cccc7#64 : BitVec 256),
   (0x9858701b760f0e80#64 ++ 0x09858701b760f0e8#64 ++ 0xb878783ffe0f0f87#64 ++ 0xfb878783ffe0f0f8#64 : BitVec 256),
   (0x2d807d401b700b60#64 ++ 0x12d807d401b700b6#64 ++ 0xff807fc03ff00fff#64 ++ 0x7ff807fc03ff00ff#64 : BitVec 256),
   (0x377d00002daaa000#64 ++ 0x2377d00002daaa00#64 ++ 0xffff80003ffff00f#64 ++ 0xbffff80003ffff00#64 : BitVec 256),
   (0x3fefdfad80000000#64 ++ 0x43fefdfad8000000#64 ++ 0x3fffffffc000000f#64 ++ 0xd3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [7, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc18f9e31c03ffffd 0xec18f9e31c03ffff

def z1 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff807fc03ff00fff 0x7ff807fc03ff00ff

def z2 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xffff80003ffff00f 0xbffff80003ffff00

def z3 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3fffffffc000000f 0xd3fffffffc000000

def z4 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467667fe31cccc7b 0xe467667fe31cccc7

def z5 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb878783ffe0f0f87 0xfb878783ffe0f0f8

def z6 : W := mkw 0x985af23bf60f5e9a 0x0985af23bf60f5e9 0xb87ff83ffe0fff87 0xfb87ff83ffe0fff8

def z7 : W := mkw 0x000282ad80000000 0x4000282ad8000000 0x0000003fc0000000 0x00000003fc000000

def z8 : W := mkw 0x0882dfad80000000 0x40882dfad8000000 0x00007fffc0000000 0x400007fffc000000

def z9 : W := mkw 0x3fefffed9b700b60 0x53fefffed9b700b6 0xfffffffffff00fff 0xffffffffffff00ff

def z10 : W := mkw 0x354900000d222000 0x2354900000d22200 0xb98980000e333004 0x1b98980000e33300

def z11 : W := mkw 0x400222f610444c5c 0x0400222f610444c5 0x000067fe00000c70 0x4000067fe00000c7

def z12 : W := mkw 0x422602e400c0c05c 0x0422602e400c0c05 0x460607c001c0c078 0x0460607c001c0c07

def z13 : W := mkw 0x423420c630c88844 0x0423420c630c8884 0x067061ce31c00002 0x0067061ce31c0000

def z14 : W := mkw 0x4010205230cccc5c 0x04010205230cccc5 0x460067c031cccc7b 0x6460067c031cccc7

def z15 : W := mkw 0x423602b6208cc41c 0x0423602b6208cc41 0x0076003e000cc000 0x80076003e000cc00

def z16 : W := mkw 0x00102012300c0c00 0x000102012300c0c0 0x0070603e300c0c03 0xe0070603e300c0c0

def z17 : W := mkw 0x9848500946030280 0x0984850094603028 0xb8081801ce030384 0x1b8081801ce03038

def z18 : W := mkw 0x1848500900000000 0x0184850090000000 0x3878783fc0000007 0xd3878783fc000000

def z19 : W := mkw 0x2d805d0000000000 0x02d805d000000000 0x3f807fc00000000f 0x53f807fc00000000

def z20 : W := mkw 0xfffe7fff7fffcffc 0x1fffe7fff7fffcff 0xfffe7fffffffcfff 0xffffe7fffffffcff

def z21 : W := mkw 0x7f7d71cf30c88844 0x47f7d71cf30c8884 0x3e7061ce31c00002 0x13e7061ce31c0000

def z22 : W := mkw 0x4010205230cccc5c 0x04010205230cccc5 0x4000000031cccc70 0x24000000031cccc7

def z23 : W := mkw 0xb77d20127fafae80 0x2b77d20127fafae8 0xffff80003fffff8f 0xbffff80003fffff8

def z24 : W := mkw 0x3f6d518d00000000 0x43f6d518d0000000 0x3fffe1ce0000000f 0x93fffe1ce0000000

def z25 : W := mkw 0x3dc85d0900000000 0x03dc85d090000000 0x3ff87fffc000000f 0xd3ff87fffc000000

def z26 : W := mkw 0xbdd87d5b7f7f0fe0 0x1bdd87d5b7f7f0fe 0xfff87fffffff0fff 0xffff87fffffff0ff

def z27 : W := mkw 0x6d907d523bfccf7c 0x16d907d523bfccf7 0xff807fc03ffccfff 0x7ff807fc03ffccff

def z28 : W := mkw 0x00800c0000100120 0x000800c000010012 0xc1801e0000300ffd 0x6c1801e0000300ff

def z29 : W := mkw 0x3f6fd3ad80000000 0x43f6fd3ad8000000 0x3e7fe1ffc0000002 0x93e7fe1ffc000000

def z30 : W := mkw 0x2d82ff609b700b60 0x12d82ff609b700b6 0xff8ffff1fff00fff 0xfff8ffff1fff00ff

def z31 : W := mkw 0x0000001040050480 0x0000000104005048 0x80081831c00f0f85 0xe80081831c00f0f8

def z32 : W := mkw 0x423622f670cdccdc 0x0423622f670cdccd 0xc67e7ffff1cfcfff 0xec67e7ffff1cfcff

def z33 : W := mkw 0x022602a400000000 0x0022602a40000000 0x067667fe0000000b 0xc067667fe0000000

def z34 : W := mkw 0xbf7d701b760f0e80 0x0bf7d701b760f0e8 0xbffff83ffe0f0f8f 0xfbffff83ffe0f0f8

def z35 : W := mkw 0x3f6d500900000000 0x03f6d50090000000 0x3ffff83fc000000f 0xd3ffff83fc000000

def z36 : W := mkw 0xc80272ff52454edc 0x0c80272ff52454ed 0x00007fffc0000ff0 0x400007fffc0000ff

def z37 : W := mkw 0x12ef8ead80000000 0x412ef8ead8000000 0x01ff9e3fc000000d 0xc01ff9e3fc000000

def z38 : W := mkw 0x37fd8c00edbbb1a2 0x237fd8c00edbbb1a 0xffff9801fffff38f 0xbffff9801fffff38

def z39 : W := mkw 0x08807d4012500b60 0x108807d4012500b6 0x00007fc000000ff0 0x400007fc000000ff

def z40 : W := mkw 0x127d0000248aa000 0x2127d0000248aa00 0x007f8000000ff000 0x8007f8000000ff00

def z41 : W := mkw 0x0000204010400840 0x0000020401040084 0x4000000031c00c70 0x24000000031c00c7

def z42 : W := mkw 0x3fffdfadadaaa000 0x63fffdfadadaaa00 0xfffffffffffff00f 0xffffffffffffff00

def z43 : W := mkw 0xbfffffbff60f0e80 0x4bfffffbff60f0e8 0xbffffffffe0f0f8f 0xfbffffffffe0f0f8

def z44 : W := mkw 0x127d0000248aa000 0x2127d0000248aa00 0xc1ff8000003ff00d 0xac1ff8000003ff00

def z45 : W := mkw 0x2fa65fa400000000 0x02fa65fa40000000 0x3ff67ffe0000000f 0xd3ff67ffe0000000

def z46 : W := mkw 0x777d20c63deaa844 0x2777d20c63deaa84 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z47 : W := mkw 0x4882ffff90444c5c 0x44882ffff90444c5 0x00007fffc0000c70 0x400007fffc0000c7

def z48 : W := mkw 0x001000106dbff5ba 0x2001000106dbff5b 0xc00000003ffffff0 0x2c00000003ffffff

def z49 : W := mkw 0x25800d0009300120 0x125800d000930012 0x0180000000300000 0x0018000000030000

def z50 : W := mkw 0x3dc9dd098d222000 0x63dc9dd098d22200 0xb9899801ce333004 0x1b9899801ce33300

def z51 : W := mkw 0x00808c00c01111a2 0x000808c00c01111a 0x81899801c0333384 0x081899801c033338

def z52 : W := mkw 0x42b6aef6f0ddddfe 0x042b6aef6f0ddddf 0xc7fffffff1ffffff 0xec7fffffff1fffff

def z53 : W := mkw 0x42a68ee480d0d17e 0x042a68ee480d0d17 0x478787c001f0f078 0x0478787c001f0f07

def z54 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x7e7600003fccc00b 0xb7e7600003fccc00

def z55 : W := mkw 0x126f82ad80000000 0x4126f82ad8000000 0x007f803fc0000000 0x8007f803fc000000

def z56 : W := mkw 0xd27e22ff74cfccdc 0x0d27e22ff74cfccd 0x467e67fff1cfcc7b 0xe467e67fff1cfcc7

def z57 : W := mkw 0xc010205276cfcedc 0x0c010205276cfced 0xc00000003fcfcff0 0x2c00000003fcfcff

def z58 : W := mkw 0xda7e72ff76cfcedc 0x0da7e72ff76cfced 0xfe7e7fffffcfcfff 0xffe7e7fffffcfcff

def z59 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0x7f8067c03ff0007a 0x17f8067c03ff0007

def z60 : W := mkw 0xbdd87d1b7f3f0fa0 0x1bdd87d1b7f3f0fa 0xb9f8783ffe3f0f87 0xfb9f8783ffe3f0f8

def z61 : W := mkw 0x25800d4009700160 0x125800d400970016 0x478007c001f00078 0x0478007c001f0007

def z62 : W := mkw 0x0aa6dfad80000000 0x40aa6dfad8000000 0x06767fffc000000b 0xc06767fffc000000

def z63 : W := mkw 0x02a68eb4c01555ba 0x002a68eb4c01555b 0xc7ffffffc03fffff 0xec7ffffffc03ffff

def z64 : W := mkw 0x00028230c005549a 0x000028230c005549 0x000f8031c00ff000 0x8000f8031c00ff00

def z65 : W := mkw 0x9058001b640f0480 0x09058001b640f048 0xb878003ffe0f0007 0xbb878003ffe0f000

def z66 : W := mkw 0x9848700956030a80 0x09848700956030a8 0xb8087801fe030f87 0x7b8087801fe030f8

def z67 : W := mkw 0x9058001b640f0480 0x09058001b640f048 0x0078003fc00f0000 0x80078003fc00f000

def z68 : W := mkw 0x422622e410c0c85c 0x0422622e410c0c85 0x460667c031c0cc7b 0x6460667c031c0cc7

def z69 : W := mkw 0x001020403ffaab60 0x3001020403ffaab6 0xc00000003ffffff0 0x2c00000003ffffff

def z70 : W := mkw 0x400222f610444c5c 0x0400222f610444c5 0x460067fe31c00c7b 0x6460067fe31c00c7

def z71 : W := mkw 0x6f3673f63becce5c 0x16f3673f63becce5 0x7e7667fe3fcccc7b 0xf7e7667fe3fcccc7

def z72 : W := mkw 0x126f82bdc005549a 0x4126f82bdc005549 0x007f803fc00ff000 0x8007f803fc00ff00

def z73 : W := mkw 0x3fefffad92000a00 0x43fefffad92000a0 0xbffffffffe000f8f 0xfbffffffffe000f8

def z74 : W := mkw 0x376d000000000000 0x0376d00000000000 0x3fff80000000000f 0x93fff80000000000

def z75 : W := mkw 0x422602e400c0c05c 0x0422602e400c0c05 0x467667fe01c0c07b 0xc467667fe01c0c07

def z76 : W := mkw 0x00000010401555ba 0x000000010401555b 0xc0000000003ffff0 0x2c0000000003ffff

def z77 : W := mkw 0x00828e2080000000 0x000828e208000000 0x018f9e31c000000d 0xc018f9e31c000000

def z78 : W := mkw 0x4000205210444c5c 0x04000205210444c5 0x0000000000000c70 0x00000000000000c7

def z79 : W := mkw 0x2500000000000000 0x0250000000000000 0x3f8000000000000f 0x13f8000000000000

def z80 : W := mkw 0x3dd87d403f7a0b60 0x13dd87d403f7a0b6 0xfff87fc03fff0fff 0xffff87fc03fff0ff

def z81 : W := mkw 0x9848500946030280 0x0984850094603028 0xb878783fce030387 0xdb878783fce03038

def z82 : W := mkw 0x777d20c63deaa844 0x2777d20c63deaa84 0xffffe1ce3ffff00f 0xbffffe1ce3ffff00

def z83 : W := mkw 0x2d82ffed9b700b60 0x52d82ffed9b700b6 0xff807ffffff00fff 0x7ff807ffffff00ff

def z84 : W := mkw 0x3dc87d491b700b60 0x13dc87d491b700b6 0xfff87ffffff00fff 0xffff87ffffff00ff

def z85 : W := mkw 0x2735000029a8a000 0x22735000029a8a00 0x47f7800031fcf00b 0xa47f7800031fcf00

def z86 : W := mkw 0x3f6d518d00000000 0x43f6d518d0000000 0x3e7061ce00000002 0x13e7061ce0000000

def z87 : W := mkw 0x80102012760f0e80 0x080102012760f0e8 0x800000003e0f0f80 0x2800000003e0f0f8

def z88 : W := mkw 0x4010205270ddddfe 0x04010205270ddddf 0xc000000031fffff0 0x2c000000031fffff

def z89 : W := mkw 0x3fefdfad89200000 0x43fefdfad8920000 0xfffffffffff0000f 0xffffffffffff0000

def z90 : W := mkw 0xbf7d701b7fafae80 0x2bf7d701b7fafae8 0xfffff83fffffff8f 0xffffff83fffffff8

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000060000000c79 0x64000060000000c7

def z92 : W := mkw 0x3f6f53ad00000000 0x43f6f53ad0000000 0x3e7667fe0000000b 0xd3e7667fe0000000

def z93 : W := mkw 0x2500000009200000 0x0250000000920000 0xff8000003ff0000f 0x3ff8000003ff0000

def z94 : W := mkw 0x673622f639eccc5c 0x0673622f639eccc5 0xfff667fe3ffccc7f 0xffff667fe3ffccc7

def z95 : W := mkw 0x98d87d5b765f0fe0 0x198d87d5b765f0fe 0xb8787ffffe0f0ff7 0xfb8787ffffe0f0ff

def z96 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x40061e31c00ccff9 0xe40061e31c00ccff

def z97 : W := mkw 0x2fa7dfad80000000 0x42fa7dfad8000000 0x0787ffffc0000008 0x40787ffffc000000

def z98 : W := mkw 0x1a6e52ad00000000 0x01a6e52ad0000000 0x3e7e7fffc000000f 0xd3e7e7fffc000000

def z99 : W := mkw 0x2d80dd00cb3113a2 0x12d80dd00cb3113a 0xb9899801ce333384 0x1b9899801ce33338

def z100 : W := mkw 0x0882dfad80000000 0x40882dfad8000000 0x018fffffc000000d 0xc018fffffc000000

def z101 : W := mkw 0x022622e410400840 0x0022622e41040084 0x467667fe31c00c7b 0xe467667fe31c00c7

def z102 : W := mkw 0x0000204010400840 0x0000020401040084 0x460067c031c00c7b 0x6460067c031c00c7

def z103 : W := mkw 0x377d20123daeac00 0x2377d20123daeac0 0xffffe03e3ffffc0f 0xfffffe03e3ffffc0

def z104 : W := mkw 0x423602b6208cc41c 0x0423602b6208cc41 0x4676003e31ccc00b 0xa4676003e31ccc00

def z105 : W := mkw 0x00100000248aa000 0x200100000248aa00 0x00000000000ff000 0x000000000000ff00

def z106 : W := mkw 0x022782a480000000 0x4022782a48000000 0x0007800000000000 0x0000780000000000

def z107 : W := mkw 0x5a7e72ff30cccc5c 0x05a7e72ff30cccc5 0x7e7e7ffff1cccc7f 0xf7e7e7ffff1cccc7

def z108 : W := mkw 0x0002023000044418 0x0000202300004441 0x0000063000000c70 0x40000063000000c7

def z109 : W := mkw 0x377d0000248aa000 0x2377d0000248aa00 0x3fff8000000ff00f 0x93fff8000000ff00

def z110 : W := mkw 0x35cb8e30cd3775ba 0x235cb8e30cd3775b 0xf98f9e31ce3ffffd 0xff98f9e31ce3ffff

def z111 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0x3870783ffe000f82 0x53870783ffe000f8

def z112 : W := mkw 0x10580000240a0000 0x010580000240a000 0x387000003e000002 0x1387000003e00000

def z113 : W := mkw 0x377f02302daee418 0x2377f02302daee41 0xffff86303ffffc7f 0xfffff86303ffffc7

def z114 : W := mkw 0x376f02a400000000 0x0376f02a40000000 0x3fffe7fe0000000f 0xd3fffe7fe0000000

def z115 : W := mkw 0x3dc9fd499b700b60 0x53dc9fd499b700b6 0xff89ffc1fff00fff 0x7ff89ffc1fff00ff

def z116 : W := mkw 0xc23622f676cfcedc 0x0c23622f676cfced 0xc67667fe3fcfcffb 0xec67667fe3fcfcff

def z117 : W := mkw 0x001000002daaa000 0x2001000002daaa00 0x000000003fc00000 0x0000000003fc0000

def z118 : W := mkw 0x423622e630c88844 0x0423622e630c8884 0x067667fe31c0000b 0xc067667fe31c0000

def z119 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x007667fe000ccc70 0xc007667fe000ccc7

def z120 : W := mkw 0x0800700012000a00 0x00800700012000a0 0xb80078003e000f87 0x7b80078003e000f8

def z121 : W := mkw 0x4a3672f632ccce5c 0x04a3672f632ccce5 0xfe767ffe3fcccfff 0xffe767ffe3fcccff

def z122 : W := mkw 0x927f82bfe40f0480 0x4927f82bfe40f048 0x007f803fc00f0000 0x8007f803fc00f000

def z123 : W := mkw 0xad907d527f7f0fe0 0x1ad907d527f7f0fe 0xff807fc03fff0fff 0x7ff807fc03fff0ff

def z124 : W := mkw 0x98d87c1b761f0fa0 0x098d87c1b761f0fa 0xf9f87e3ffe3f0fff 0xff9f87e3ffe3f0ff

def z125 : W := mkw 0x9058000b240a0000 0x09058000b240a000 0x0070000e00000000 0x00070000e0000000

def z126 : W := mkw 0x00800c0000100120 0x000800c000010012 0xc18f9e00003ffffd 0xec18f9e00003ffff

def z127 : W := mkw 0x40100012208cc41c 0x040100012208cc41 0x00000000000cc000 0x000000000000cc00

def z128 : W := mkw 0x08107012320c0e00 0x008107012320c0e0 0xb870783e3e0c0f87 0xfb870783e3e0c0f8

def z129 : W := mkw 0x0000001040050480 0x0000000104005048 0x00080031c00f0000 0x800080031c00f000

def z130 : W := mkw 0x3f7d518d2daaa000 0x63f7d518d2daaa00 0xffffe1ce3ffff00f 0xbffffe1ce3ffff00

def z131 : W := mkw 0x98dafe3bf61f5fba 0x098dafe3bf61f5fb 0xf9fffe3ffe3fffff 0xff9fffe3ffe3ffff

def z132 : W := mkw 0x251000002daaa000 0x2251000002daaa00 0xff8000003ffff00f 0x3ff8000003ffff00

def z133 : W := mkw 0xbd58714b3f6a0a40 0x1bd58714b3f6a0a4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z134 : W := mkw 0x00102052304c0c40 0x000102052304c0c4 0x467067fe31cc0c7b 0xe467067fe31cc0c7

def z135 : W := mkw 0x001000002daaa000 0x2001000002daaa00 0xc00000003ffff000 0x2c00000003ffff00

def z136 : W := mkw 0x527f02b6248ee41c 0x2527f02b6248ee41 0x007f803e000ff000 0x8007f803e000ff00

def z137 : W := mkw 0x02342012308c8c00 0x002342012308c8c0 0x4676603e31cccc0b 0xe4676603e31cccc0

def z138 : W := mkw 0x00802c4010500960 0x000802c401050096 0xc7807fc031f00fff 0x6c7807fc031f00ff

def z139 : W := mkw 0x98c8dc09c61313a2 0x098c8dc09c61313a 0xb9899801ce333384 0x1b9899801ce33338

def z140 : W := mkw 0x801020527f7f0fe0 0x1801020527f7f0fe 0xc00000003fff0ff0 0x2c00000003fff0ff

def z141 : W := mkw 0x023622b6300c0c00 0x0023622b6300c0c0 0x067667fe300c0c0b 0xe067667fe300c0c0

def z142 : W := mkw 0x9848500906020200 0x0984850090602020 0x380000000e000000 0x1380000000e00000

def z143 : W := mkw 0x126d000000000000 0x0126d00000000000 0x007f800000000000 0x8007f80000000000

def z144 : W := mkw 0x4000004000c0c05c 0x04000004000c0c05 0x4000000001c0c070 0x04000000001c0c07

def z145 : W := mkw 0x0800704012400a40 0x00800704012400a4 0xfe007fc03fc00fff 0x7fe007fc03fc00ff

def z146 : W := mkw 0x2d82ff70db755ffa 0x12d82ff70db755ff 0xff807ff1fff00fff 0x7ff807ff1fff00ff

def z147 : W := mkw 0x0000200010000800 0x0000020001000080 0x0000600030000c03 0x60000600030000c0

def z148 : W := mkw 0x777f22f630cccc5c 0x0777f22f630cccc5 0x7fffe7fe31cccc7f 0xf7fffe7fe31cccc7

def z149 : W := mkw 0x3f7d518d2daaa000 0x63f7d518d2daaa00 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z150 : W := mkw 0x0002023000044418 0x0000202300004441 0x00060030000cc000 0x800060030000cc00

def z151 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb870600e3e0f0f82 0x3b870600e3e0f0f8

def z152 : W := mkw 0x3fffffedbffaab60 0x73fffffedbffaab6 0xffffffffffffffff 0xffffffffffffffff

def z153 : W := mkw 0x2d805d000b300320 0x12d805d000b30032 0xbf807fc00e30038f 0x5bf807fc00e30038

def z154 : W := mkw 0x2d805d000b300320 0x12d805d000b30032 0xf9801e000e300ffd 0x7f9801e000e300ff

def z155 : W := mkw 0x2725000009a0a000 0x22725000009a0a00 0xc78f800001fff00d 0xac78f800001fff00

def z156 : W := mkw 0x0234000020888000 0x0023400002088800 0x4676000031ccc00b 0xa4676000031ccc00

def z157 : W := mkw 0x777f22f63deeec5c 0x2777f22f63deeec5 0xffffe7fe3ffffc7f 0xfffffe7fe3ffffc7

def z158 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc0001e31c03ffff0 0x6c0001e31c03ffff

def z159 : W := mkw 0x023400002daaa000 0x2023400002daaa00 0xc67600003ffff00b 0xac67600003ffff00

def z160 : W := mkw 0x000000000b300320 0x1000000000b30032 0x800000000e300380 0x0800000000e30038

def z161 : W := mkw 0x88807d5b52550fe0 0x188807d5b52550fe 0x00007fffc0000ff0 0x400007fffc0000ff

def z162 : W := mkw 0xd858705b76cfcedc 0x0d858705b76cfced 0xf878783fffcfcff7 0xff878783fffcfcff

def z163 : W := mkw 0x42b68eb6e09dd5be 0x042b68eb6e09dd5b 0xc1ff9e3fc03ffffd 0xec1ff9e3fc03ffff

def z164 : W := mkw 0x2d0071401b600a40 0x12d0071401b600a4 0x3e0061c03fc00002 0x13e0061c03fc0000

def z165 : W := mkw 0x9858701b761f5fba 0x09858701b761f5fb 0xf878783ffe3ffff7 0xff878783ffe3ffff

def z166 : W := mkw 0x8800701b52050e80 0x08800701b52050e8 0xb800783ffe000f87 0x7b800783ffe000f8

def z167 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x39ff983fc0000004 0x939ff983fc000000

def z168 : W := mkw 0xff7f72ff7fefeedc 0x2ff7f72ff7fefeed 0xffffffffffffffff 0xffffffffffffffff

def z169 : W := mkw 0x3fefdfad80100120 0x43fefdfad8010012 0xffffffffc0300fff 0xfffffffffc0300ff

def z170 : W := mkw 0x354900000d222000 0x2354900000d22200 0x380000000e000000 0x1380000000e00000

def z171 : W := mkw 0x08805d0000000000 0x008805d000000000 0x00007fc000000000 0x400007fc00000000

def z172 : W := mkw 0x1048000004020000 0x0104800000402000 0xb80800000e030004 0x1b80800000e03000

def z173 : W := mkw 0x2d82ff70db755ffa 0x12d82ff70db755ff 0xff8ffff1ffffffff 0xfff8ffff1fffffff

def z174 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff8fffc03fffffff 0xfff8fffc03ffffff

def z175 : W := mkw 0x0224008400000000 0x0022400840000000 0x067061ce00000002 0x0067061ce0000000

def z176 : W := mkw 0x127d00002daaa000 0x2127d00002daaa00 0xc07f80003ffff000 0xac07f80003ffff00

def z177 : W := mkw 0x2500000009200000 0x0250000000920000 0xff8f80003ffff00f 0xbff8f80003ffff00

def z178 : W := mkw 0x1aefdfad80000000 0x41aefdfad8000000 0x007fffffc0000000 0xc007fffffc000000

def z179 : W := mkw 0x777f02b62daee41c 0x2777f02b62daee41 0xffff803e3ffff00f 0xbffff803e3ffff00

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000000003ff000 0x2c0000000003ff00

def z181 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x067067fe31c00c72 0x4067067fe31c00c7

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x418780000030f008 0x0418780000030f00

def z183 : W := mkw 0x90582012760f0e80 0x090582012760f0e8 0xb87800003e0f0f87 0xbb87800003e0f0f8

def z184 : W := mkw 0x9058001b640f0480 0x09058001b640f048 0x8078183fc00f0f85 0xe8078183fc00f0f8

def z185 : W := mkw 0xbf7d701b7fafae80 0x2bf7d701b7fafae8 0xbe78783fffcf0f87 0xfbe78783fffcf0f8

def z186 : W := mkw 0xda7e72bf768fce9c 0x0da7e72bf768fce9 0xb87e783ffe0fcf87 0xfb87e783ffe0fcf8

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0xc18f8000003ff00d 0xac18f8000003ff00

def z188 : W := mkw 0x354900000d222000 0x2354900000d22200 0xf98f80000e3ff00d 0xbf98f80000e3ff00

def z189 : W := mkw 0x0800700012000a00 0x00800700012000a0 0x0000780000000f80 0x40000780000000f8

def z190 : W := mkw 0x8000201252050e80 0x08000201252050e8 0x0000000000000f80 0x00000000000000f8

def z191 : W := mkw 0x0000201210040c00 0x00000201210040c0 0x0000603e00000c00 0x40000603e00000c0

def z192 : W := mkw 0x9848501946070680 0x0984850194607068 0xb8081831ce0f0f85 0xfb8081831ce0f0f8

def z193 : W := mkw 0x0882fe30d2155fba 0x00882fe30d2155fb 0xf98ffe31fe3fffff 0xff98ffe31fe3ffff

def z194 : W := mkw 0x6fb6fff6fbfddffe 0x16fb6fff6fbfddff 0xffffffffffffffff 0xffffffffffffffff

def z195 : W := mkw 0x3fefdfbdc01555ba 0x43fefdfbdc01555b 0xffffffffc03fffff 0xfffffffffc03ffff

def z196 : W := mkw 0x3fefffed92500b60 0x53fefffed92500b6 0x3fffffffc0000fff 0xd3fffffffc0000ff

def z197 : W := mkw 0x7fefdfed80c0c05c 0x47fefdfed80c0c05 0x7fffffffc1c0c07f 0xd7fffffffc1c0c07

def z198 : W := mkw 0x3fffdfada48aa000 0x63fffdfada48aa00 0x3fffffffc00ff00f 0xd3fffffffc00ff00

def z199 : W := mkw 0x9a7d701b768fae80 0x29a7d701b768fae8 0xb87ff83ffe0fff87 0xfb87ff83ffe0fff8

def z200 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xfff000003ff0000f 0x3fff000003ff0000

def z201 : W := mkw 0x2500000009200000 0x0250000000920000 0x3e0000003fc00002 0x13e0000003fc0000

def z202 : W := mkw 0x0000001040050480 0x0000000104005048 0x00001831c0000f80 0x400001831c0000f8

def z203 : W := mkw 0x00828e208010513a 0x000828e208010513 0x418786000030f078 0x0418786000030f07

def z204 : W := mkw 0x3f6d518d00000000 0x43f6d518d0000000 0x3e7879ffc0000007 0xd3e7879ffc000000

def z205 : W := mkw 0x00028230c005549a 0x000028230c005549 0x800f9831c00fff85 0xe800f9831c00fff8

def z206 : W := mkw 0x376d000009200000 0x0376d00000920000 0xffff80003ff0000f 0xbffff80003ff0000

def z207 : W := mkw 0x2d00510000000000 0x02d0051000000000 0x3e0061c000000002 0x13e0061c00000000

def z208 : W := mkw 0x0234000020888000 0x0023400002088800 0x00760000000cc000 0x800760000000cc00

def z209 : W := mkw 0x3dc9dd098b300320 0x53dc9dd098b30032 0xb9899801ce300384 0x1b9899801ce30038

def z210 : W := mkw 0x2d805d000b300320 0x12d805d000b30032 0xb98018000e300384 0x1b98018000e30038

def z211 : W := mkw 0x0000004000400040 0x0000000400040004 0x460007c001c00078 0x0460007c001c0007

def z212 : W := mkw 0x3fefdfad8b300320 0x53fefdfad8b30032 0xbfffffffce30038f 0xdbfffffffce30038

def z213 : W := mkw 0x0224000000808000 0x0022400000080800 0x4606000001c0c008 0x04606000001c0c00

def z214 : W := mkw 0x2d0071401b600a40 0x12d0071401b600a4 0xff8061c03ff0000f 0x3ff8061c03ff0000

def z215 : W := mkw 0x0000001040050480 0x0000000104005048 0x80000000000f0f80 0x280000000000f0f8

def z216 : W := mkw 0x08807d4012500b60 0x108807d4012500b6 0x46007fc031c00ffb 0x646007fc031c00ff

def z217 : W := mkw 0x022602a400000000 0x0022602a40000000 0x060607c000000008 0x0060607c00000000

def z218 : W := mkw 0x3dc9dd0980000000 0x43dc9dd098000000 0x39899801c0000004 0x139899801c000000

def z219 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x067661fe31ccc002 0x8067661fe31ccc00

def z220 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x3e7000003fc00002 0x13e7000003fc0000

def z221 : W := mkw 0x00102012700d0c80 0x000102012700d0c8 0x8078783ff00f0f87 0xe8078783ff00f0f8

def z222 : W := mkw 0x9858501b660f0680 0x09858501b660f068 0xb878183fce0f0384 0x9b878183fce0f038

def z223 : W := mkw 0xbfffffbfffafae80 0x6bfffffbfffafae8 0xffffffffffffff8f 0xfffffffffffffff8

def z224 : W := mkw 0x2d805d400b700360 0x12d805d400b70036 0xff801fc00ff003fc 0x1ff801fc00ff003f

def z225 : W := mkw 0x00828e308014553a 0x000828e308014553 0x41878630003cfc79 0xe41878630003cfc7

def z226 : W := mkw 0x00800c0000100120 0x000800c000010012 0x00001e0000000ff0 0x400001e0000000ff

def z227 : W := mkw 0x423622e630c8c85c 0x0423622e630c8c85 0x467667ce31c0c07a 0x0467667ce31c0c07

def z228 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xb9ff80000e3ff004 0x9b9ff80000e3ff00

def z229 : W := mkw 0x1848501940050480 0x0184850194005048 0xb878783fc00f0f87 0xfb878783fc00f0f8

def z230 : W := mkw 0x0000000000100120 0x0000000000010012 0xc000000000300ff0 0x2c000000000300ff

def z231 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0x3e007fc03fc00ff2 0x53e007fc03fc00ff

def z232 : W := mkw 0x27a78e2089b0f13a 0x227a78e2089b0f13 0x4787860001f0f078 0x04787860001f0f07

def z233 : W := mkw 0x3ffd7d403ffaab60 0x33ffd7d403ffaab6 0xffffffc03fffffff 0xfffffffc03ffffff

def z234 : W := mkw 0x7fff7ff63ffeef7c 0x37fff7ff63ffeef7 0xfffffffe3fffffff 0xffffffffe3ffffff

def z235 : W := mkw 0x000020401b700b60 0x1000020401b700b6 0xc00000003ff00ff0 0x2c00000003ff00ff

def z236 : W := mkw 0x2d0071401b600a40 0x12d0071401b600a4 0xbe0079c03fc00f87 0x7be0079c03fc00f8

def z237 : W := mkw 0x1048000900000000 0x0104800090000000 0x0078003fc0000000 0x80078003fc000000

def z238 : W := mkw 0x00800c10401505a0 0x000800c10401505a 0xc1881e31c03f0ffd 0xec1881e31c03f0ff

def z239 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x3e7f80003fcff002 0x93e7f80003fcff00

def z240 : W := mkw 0x9858705b7f7f0fe0 0x19858705b7f7f0fe 0xf878783fffff0ff7 0xff878783fffff0ff

def z241 : W := mkw 0x8882fe3bd2155fba 0x08882fe3bd2155fb 0xc18ffe3fc03ffffd 0xec18ffe3fc03ffff

def z242 : W := mkw 0x3feffffddb755ffa 0x53feffffddb755ff 0xffffffffffffffff 0xffffffffffffffff

def z243 : W := mkw 0x0002022000000000 0x0000202200000000 0x0006063000000009 0xc000606300000000

def z244 : W := mkw 0x0002023000044418 0x0000202300004441 0x40060630000ccc79 0xe40060630000ccc7

def z245 : W := mkw 0x7fffffefb0c88844 0x47fffffefb0c8884 0x3ffffffff1c0000f 0xd3ffffffff1c0000

def z246 : W := mkw 0x2d805d4009700160 0x12d805d400970016 0x7f807fc001f0007f 0x57f807fc001f0007

def z247 : W := mkw 0x67a60fe409f0c17c 0x167a60fe409f0c17 0x478607c001f0c078 0x0478607c001f0c07

def z248 : W := mkw 0x00820e3000144538 0x000820e300014453 0xc1861e30003ccffd 0xec1861e30003ccff

def z249 : W := mkw 0x00008000c0011082 0x000008000c001108 0x00098001c0033000 0x000098001c003300

def z250 : W := mkw 0x0800500900000000 0x0080050090000000 0x0000783fc0000000 0x40000783fc000000

def z251 : W := mkw 0x2725000009a0a000 0x22725000009a0a00 0x4787800001f0f008 0x04787800001f0f00

def z252 : W := mkw 0x37ef8fa480000000 0x437ef8fa48000000 0x3fff87c00000000f 0x93fff87c00000000

def z253 : W := mkw 0x000020401b700b60 0x1000020401b700b6 0xc60067c03ff00ffb 0x6c60067c03ff00ff

def z254 : W := mkw 0x355900002d2a2000 0x2355900002d2a200 0xb9f980003e3f3007 0xbb9f980003e3f300

def z255 : W := mkw 0xbfefdfadc6030280 0x4bfefdfadc603028 0xbfffffffce03038f 0xdbfffffffce03038

def z256 : W := mkw 0x37ef8e2080000000 0x037ef8e208000000 0x3fff9e31c000000f 0xd3fff9e31c000000

def z257 : W := mkw 0x2d805d0000000000 0x02d805d000000000 0x3980180000000004 0x1398018000000000

def z258 : W := mkw 0x00808c10c01555ba 0x000808c10c01555b 0xc1899801c03ffff4 0x2c1899801c03ffff

def z259 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb8081801fe0f0f84 0x3b8081801fe0f0f8

def z260 : W := mkw 0x777f22f63deeec5c 0x2777f22f63deeec5 0x7e7667fe3fcccc7b 0xf7e7667fe3fcccc7

def z261 : W := mkw 0x9858700b360a0a00 0x09858700b360a0a0 0x3870600e3e000002 0x13870600e3e00000

def z262 : W := mkw 0x376f82ad80000000 0x4376f82ad8000000 0x3fff803fc000000f 0x93fff803fc000000

def z263 : W := mkw 0x527e22f634cecc5c 0x0527e22f634cecc5 0xfe7e67fe3fcfcc7f 0xffe7e67fe3fcfcc7

def z264 : W := mkw 0x127d0000248aa000 0x2127d0000248aa00 0x467f800031cff00b 0xa467f800031cff00

def z265 : W := mkw 0x8810701b720d0e80 0x08810701b720d0e8 0x0070783ff00c0f83 0xe0070783ff00c0f8

def z266 : W := mkw 0x355900002daaa000 0x2355900002daaa00 0xf98980003ffff004 0x3f98980003ffff00

def z267 : W := mkw 0x423420c630c88844 0x0423420c630c8884 0x467067ce31c00c7b 0x6467067ce31c00c7

def z268 : W := mkw 0x0800700012000a00 0x00800700012000a0 0x380060003e000002 0x1380060003e00000

def z269 : W := mkw 0x08805d0002100320 0x108805d000210032 0x0000180000000380 0x0000018000000038

def z270 : W := mkw 0x27a78fe489700160 0x527a78fe48970016 0x478787c001f00078 0x0478787c001f0007

def z271 : W := mkw 0x00828e30c005549a 0x000828e30c005549 0x018f9e31c00ff00d 0xc018f9e31c00ff00

def z272 : W := mkw 0x423622f63bfccf7c 0x1423622f63bfccf7 0xc67667fe3ffccffb 0xec67667fe3ffccff

def z273 : W := mkw 0x527f82bfa08cc41c 0x4527f82bfa08cc41 0x007f803fc00cc000 0x8007f803fc00cc00

def z274 : W := mkw 0x376d00000d222000 0x2376d00000d22200 0xbfff80000e33300f 0x9bfff80000e33300

def z275 : W := mkw 0xbdc85d094f3303a0 0x1bdc85d094f3303a 0xb9881801ce330384 0x1b9881801ce33038

def z276 : W := mkw 0x673722f639ecec5c 0x2673722f639ecec5 0x47f7e7fe31fcfc7b 0xe47f7e7fe31fcfc7

def z277 : W := mkw 0x98dafe3bf61f5fba 0x098dafe3bf61f5fb 0xb8787e3ffe0f0ff7 0xfb8787e3ffe0f0ff

def z278 : W := mkw 0x423420d630cc8c44 0x0423420d630cc8c4 0x067061fe31cc0c03 0xe067061fe31cc0c0

def z279 : W := mkw 0x0000000000000000 0x0000000000000000 0x060067c00000000b 0x4060067c00000000

def z280 : W := mkw 0xca3672ff72cdcedc 0x0ca3672ff72cdced 0x46767ffff1cccffb 0xe46767ffff1cccff

def z281 : W := mkw 0x00028230c005549a 0x000028230c005549 0xc18f8031c03ff00d 0xac18f8031c03ff00

def z282 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x00001e31c0000ff0 0x400001e31c0000ff

def z283 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0xffffffffc03ff00f 0xfffffffffc03ff00

def z284 : W := mkw 0x0000000040010080 0x0000000004001008 0x80081801c0030384 0x080081801c003038

def z285 : W := mkw 0x7fffdfbfa08cc41c 0x47fffdfbfa08cc41 0x3fffffffc00cc00f 0xd3fffffffc00cc00

def z286 : W := mkw 0x2725018400000000 0x4272501840000000 0x060001c000000000 0x0060001c00000000

def z287 : W := mkw 0xbfefffbfd2050e80 0x4bfefffbfd2050e8 0x3fffffffc0000f8f 0xd3fffffffc0000f8

def z288 : W := mkw 0x7fffffffb0cccc5c 0x47fffffffb0cccc5 0x7ffffffff1cccc7f 0xf7ffffffff1cccc7

def z289 : W := mkw 0x376d00000da2a000 0x2376d00000da2a00 0xff8f80000ff3f00c 0x1ff8f80000ff3f00

def z290 : W := mkw 0x1848700912000a00 0x01848700912000a0 0xb878783ffe000f87 0xfb878783ffe000f8

def z291 : W := mkw 0x3fefdfbdc005549a 0x43fefdfbdc005549 0x3fffffffc00ff00f 0xd3fffffffc00ff00

def z292 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3e707fffc0000002 0x53e707fffc000000

def z293 : W := mkw 0x8810701b760f0e80 0x08810701b760f0e8 0x8000783ffe0f0f80 0x68000783ffe0f0f8

def z294 : W := mkw 0x377d20403deaa840 0x2377d20403deaa84 0xffffe7c03ffffc7f 0xfffffe7c03ffffc7

def z295 : W := mkw 0x00800c0000100120 0x000800c000010012 0x4180060000300078 0x0418006000030007

def z296 : W := mkw 0x25828f70c97555fa 0x125828f70c97555f 0xc78f9ff1c1fffffd 0xec78f9ff1c1fffff

def z297 : W := mkw 0x2d0070001b200a00 0x02d0070001b200a0 0xff8078003ff00f8f 0x7ff8078003ff00f8

def z298 : W := mkw 0x00828e208010513a 0x000828e208010513 0xc18f8600003ff07d 0xac18f8600003ff07

def z299 : W := mkw 0x2d82df2080000000 0x02d82df208000000 0x3f8ffff1c000000f 0xd3f8ffff1c000000

def z300 : W := mkw 0x2d80fd40db711be2 0x12d80fd40db711be 0xff89ffc1fff33fff 0x7ff89ffc1fff33ff

def z301 : W := mkw 0x00808c0080000000 0x000808c008000000 0x01899801c0000004 0x001899801c000000

def z302 : W := mkw 0x0880dd0980000000 0x40880dd098000000 0x00001801c0000000 0x000001801c000000

def z303 : W := mkw 0x022500000080a000 0x2022500000080a00 0x000780000000f000 0x0000780000000f00

def z304 : W := mkw 0x2d807d505b750fe0 0x12d807d505b750fe 0xff887ff1ffff0fff 0xfff887ff1ffff0ff

def z305 : W := mkw 0x10580000240a0000 0x010580000240a000 0xb87800003e0f0007 0xbb87800003e0f000

def z306 : W := mkw 0x354900000d222000 0x2354900000d22200 0xff8980003ff3300f 0x3ff8980003ff3300

def z307 : W := mkw 0xda7c70cf36ca8a44 0x0da7c70cf36ca8a4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z308 : W := mkw 0x9858700b760b0a80 0x09858700b760b0a8 0xb878780ffe030386 0x1b878780ffe03038

def z309 : W := mkw 0x0224000000000000 0x0022400000000000 0x067600000000000b 0x8067600000000000

def z310 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xb9807fc00e300ff4 0x5b9807fc00e300ff

def z311 : W := mkw 0x37ff8fa4adaaa000 0x637ff8fa4adaaa00 0xffff87c03ffff00f 0xbffff87c03ffff00

def z312 : W := mkw 0x37ff8e20adaaa000 0x237ff8e20adaaa00 0xffff9e31fffff00f 0xfffff9e31fffff00

def z313 : W := mkw 0x80102012760f0e80 0x080102012760f0e8 0x80081831fe0f0f85 0xe80081831fe0f0f8

def z314 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x018f9e31c0000ffd 0xc018f9e31c0000ff

def z315 : W := mkw 0xd27e02bf648fc49c 0x0d27e02bf648fc49 0x007e003fc00fc000 0x8007e003fc00fc00

def z316 : W := mkw 0x25800c0009300120 0x025800c000930012 0xff801e003ff00fff 0x7ff801e003ff00ff

def z317 : W := mkw 0xbdd87d4b3f7a0b60 0x1bdd87d4b3f7a0b6 0xfff07fce3ff00fff 0x7fff07fce3ff00ff

def z318 : W := mkw 0x0882ffed92500b60 0x50882ffed92500b6 0x00007fffc0000ff0 0x400007fffc0000ff

def z319 : W := mkw 0x00828fa480000000 0x400828fa48000000 0x000007c000000000 0x0000007c00000000

def z320 : W := mkw 0x0882ff70d2555ffa 0x10882ff70d2555ff 0x00007ff1c0000ff0 0x400007ff1c0000ff

def z321 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x4076003e31cccc70 0xa4076003e31cccc7

def z322 : W := mkw 0xbdd87d1b760f0e80 0x0bdd87d1b760f0e8 0xbff87ffffe0f0f8f 0xfbff87ffffe0f0f8

def z323 : W := mkw 0x4ab6ffffb0cccc5c 0x44ab6ffffb0cccc5 0x46767ffff1cccc7b 0xe46767ffff1cccc7

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x0070603e00000003 0xc0070603e0000000

def z325 : W := mkw 0x3fed7d401b700b60 0x13fed7d401b700b6 0xffffffc03ff00fff 0xfffffffc03ff00ff

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x40060000000cc009 0xa40060000000cc00

def z327 : W := mkw 0x422400c400c08044 0x0422400c400c0804 0x060001c001c00000 0x0060001c001c0000

def z328 : W := mkw 0x401222f630cccc5c 0x0401222f630cccc5 0x400067fe31cccc70 0x6400067fe31cccc7

def z329 : W := mkw 0x3fefdfad8010513a 0x43fefdfad8010513 0x7fffffffc030f07f 0xd7fffffffc030f07

def z330 : W := mkw 0x27a78fa489a0a000 0x627a78fa489a0a00 0x478787c001f0f008 0x0478787c001f0f00

def z331 : W := mkw 0x3fefdfad89a0a000 0x63fefdfad89a0a00 0x7fffffffc1f0f00f 0xd7fffffffc1f0f00

def z332 : W := mkw 0x4010204230c88844 0x04010204230c8884 0x0000000031c00000 0x00000000031c0000

def z333 : W := mkw 0x423602f620ccc45c 0x0423602f620ccc45 0x467607fe01ccc078 0x8467607fe01ccc07

def z334 : W := mkw 0x000202a400000000 0x0000202a40000000 0x000067fe00000000 0x4000067fe0000000

def z335 : W := mkw 0x7ffffffff0ddddfe 0x47ffffffff0ddddf 0xfffffffff1ffffff 0xffffffffff1fffff

def z336 : W := mkw 0x2d82dfad80000000 0x42d82dfad8000000 0x3f807fffc000000f 0x53f807fffc000000

def z337 : W := mkw 0x18cade39c01555ba 0x018cade39c01555b 0xf9fffe3fc03fffff 0xff9fffe3fc03ffff

def z338 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xf9fff83ffe3fff8f 0xff9fff83ffe3fff8

def z339 : W := mkw 0x905a823be40f549a 0x0905a823be40f549 0x007f803fc00ff000 0x8007f803fc00ff00

def z340 : W := mkw 0x00100000240a0000 0x000100000240a000 0x800000003e0f0000 0x2800000003e0f000

def z341 : W := mkw 0x8800701b52050e80 0x08800701b52050e8 0x0000783fc0000f80 0x40000783fc0000f8

def z342 : W := mkw 0x0000200012000a00 0x00000200012000a0 0x800000003e000f80 0x2800000003e000f8

def z343 : W := mkw 0x00808c00c01111a2 0x000808c00c01111a 0xc1899e01c0333ffd 0x6c1899e01c0333ff

def z344 : W := mkw 0x2501000009202000 0x2250100000920200 0x0181800000303000 0x0018180000030300

def z345 : W := mkw 0x25802d401b700b60 0x125802d401b700b6 0xc78007c03ff00ff8 0x2c78007c03ff00ff

def z346 : W := mkw 0x67b7aff6b0cccc5c 0x467b7aff6b0cccc5 0x47f7e7fe31cccc7b 0xe47f7e7fe31cccc7

def z347 : W := mkw 0x77ffaef6fdfffdfe 0x277ffaef6fdfffdf 0xffffffffffffffff 0xffffffffffffffff

def z348 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xbff980003ff33006 0x1bff980003ff3300

def z349 : W := mkw 0x401222f6304c4c5c 0x0401222f6304c4c5 0x007067fe300c0c73 0xe007067fe300c0c7

def z350 : W := mkw 0xbfffffbff61f5fba 0x4bfffffbff61f5fb 0xfffffffffe3fffff 0xffffffffffe3ffff

def z351 : W := mkw 0x377f82adadaaa000 0x6377f82adadaaa00 0xffff803ffffff00f 0xbffff803ffffff00

def z352 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x81899e31c0333ff4 0x481899e31c0333ff

def z353 : W := mkw 0x7fefffff90444c5c 0x47fefffff90444c5 0x3fffffffc0000c7f 0xd3fffffffc0000c7

def z354 : W := mkw 0x27a78fa480000000 0x427a78fa48000000 0x07f7e7fe0000000b 0xc07f7e7fe0000000

def z355 : W := mkw 0x10580000240a0000 0x010580000240a000 0xf9ff80003e3ff00f 0xbf9ff80003e3ff00

def z356 : W := mkw 0x0082ae70db755ffa 0x10082ae70db755ff 0xc18f9e31fffffffd 0xec18f9e31fffffff

def z357 : W := mkw 0x377d20403ffaab60 0x3377d20403ffaab6 0xffff80003fffffff 0xbffff80003ffffff

def z358 : W := mkw 0x00828e208010513a 0x000828e208010513 0xc1879e000030fffd 0x6c1879e000030fff

def z359 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3f8f9fc1c000000c 0x13f8f9fc1c000000

def z360 : W := mkw 0x02360230208cc418 0x002360230208cc41 0x4676063031cccc7b 0xe4676063031cccc7

def z361 : W := mkw 0x2d807d401b600a40 0x12d807d401b600a4 0x3f807fc03fc0000f 0x53f807fc03fc0000

def z362 : W := mkw 0x423602e420c8c05c 0x0423602e420c8c05 0x467607c031ccc07b 0xa467607c031ccc07

def z363 : W := mkw 0x0882ff70d2555ffa 0x10882ff70d2555ff 0xc18ffff1c03ffffd 0xec18ffff1c03ffff

def z364 : W := mkw 0x080070401b700b60 0x1080070401b700b6 0xf80078003ff00ff7 0x7f80078003ff00ff

def z365 : W := mkw 0xbd4950094f232280 0x2bd4950094f23228 0xb9899801ce333384 0x1b9899801ce33338

def z366 : W := mkw 0x022602a400000000 0x0022602a40000000 0x0076003e00000000 0x80076003e0000000

def z367 : W := mkw 0x48827ff612544f7c 0x148827ff612544f7 0x00007ffe00000ff0 0x400007ffe00000ff

def z368 : W := mkw 0x3fefdfad8d222000 0x63fefdfad8d22200 0xbfffffffce33300f 0xdbfffffffce33300

def z369 : W := mkw 0x00808c00c01111a2 0x000808c00c01111a 0xc18f9801c03ff38d 0xac18f9801c03ff38

def z370 : W := mkw 0x2500014009600040 0x1250001400960004 0x060001c001c00000 0x0060001c001c0000

def z371 : W := mkw 0x3fffdfbdedbff5ba 0x63fffdfbdedbff5b 0xffffffffffffffff 0xffffffffffffffff

def z372 : W := mkw 0x80102012761f5fba 0x080102012761f5fb 0xc00000003e3ffff0 0x2c00000003e3ffff

def z373 : W := mkw 0x02b68e30e09dd5ba 0x002b68e30e09dd5b 0xc7ff9e31f1ffffff 0xec7ff9e31f1fffff

def z374 : W := mkw 0x3dc9dd0980000000 0x43dc9dd098000000 0x39f9f83fc0000007 0xd39f9f83fc000000

def z375 : W := mkw 0x0000000009200000 0x0000000000920000 0xc00000003ff00000 0x2c00000003ff0000

def z376 : W := mkw 0x127f82ada48aa000 0x6127f82ada48aa00 0x007f803fc00ff000 0x8007f803fc00ff00

def z377 : W := mkw 0x3dcbdfad80000000 0x43dcbdfad8000000 0x3989ffffc0000004 0x53989ffffc000000

def z378 : W := mkw 0xbf7d50096faba280 0x2bf7d50096faba28 0xffff9801fffff38f 0xbffff9801fffff38

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x8189800000333004 0x0818980000033300

def z380 : W := mkw 0x127f8230e48ff49a 0x2127f8230e48ff49 0x007f8031c00ff000 0x8007f8031c00ff00

def z381 : W := mkw 0x0000204010400840 0x0000020401040084 0x000067c000000c70 0x4000067c000000c7

def z382 : W := mkw 0x80100012640f0480 0x080100012640f048 0x00000000000f0000 0x000000000000f000

def z383 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x818f9831c03ff384 0x8818f9831c03ff38

def z384 : W := mkw 0x00020230401555ba 0x000020230401555b 0xc0060630003ffff9 0xec0060630003ffff

def z385 : W := mkw 0x423622f63deeec5c 0x2423622f63deeec5 0xc67667fe3ffffc7b 0xec67667fe3ffffc7

def z386 : W := mkw 0x9858700b360a0a00 0x09858700b360a0a0 0xb870780e3e000f87 0x7b870780e3e000f8

def z387 : W := mkw 0x37ff8e30edbff5ba 0x237ff8e30edbff5b 0xffff9e31ffffffff 0xfffff9e31fffffff

def z388 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3ff7e7ce0000000a 0x13ff7e7ce0000000

def z389 : W := mkw 0x126f82ad80000000 0x4126f82ad8000000 0x067fe7ffc000000b 0xc067fe7ffc000000

def z390 : W := mkw 0x9848701b52050e80 0x09848701b52050e8 0x3878783fc0000f87 0xd3878783fc0000f8

def z391 : W := mkw 0xd85a72ff764f4edc 0x0d85a72ff764f4ed 0xb8787ffffe0f0ff7 0xfb8787ffffe0f0ff

def z392 : W := mkw 0x2725000000000000 0x0272500000000000 0x0787800000000008 0x0078780000000000

def z393 : W := mkw 0x2fa57d401bf0ab60 0x32fa57d401bf0ab6 0xff87ffc03ff0ffff 0x7ff87ffc03ff0fff

def z394 : W := mkw 0x0800500002000200 0x0080050000200020 0xb80018000e000384 0x1b80018000e00038

def z395 : W := mkw 0x9058201b740f0c80 0x09058201b740f0c8 0x0078603ff00f0c03 0xe0078603ff00f0c0

def z396 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x3fff80003fc0000f 0x93fff80003fc0000

def z397 : W := mkw 0x1858701b300c0c00 0x01858701b300c0c0 0x3878783ff00c0c07 0xf3878783ff00c0c0

def z398 : W := mkw 0x27a78fa48010513a 0x427a78fa48010513 0x478787c00030f078 0x0478787c00030f07

def z399 : W := mkw 0x37ef8fad80000000 0x437ef8fad8000000 0x07ff87ffc0000008 0x807ff87ffc000000

def z400 : W := mkw 0x8882ffbfd2050e80 0x48882ffbfd2050e8 0x00007fffc0000f80 0x400007fffc0000f8

def z401 : W := mkw 0x3fed5d8d00000000 0x43fed5d8d0000000 0x3ff07fce0000000f 0x53ff07fce0000000

def z402 : W := mkw 0x80102012760f0e80 0x080102012760f0e8 0x8070603e3e0f0f83 0xe8070603e3e0f0f8

def z403 : W := mkw 0x3fefdfbdc0050480 0x43fefdfbdc005048 0xbfffffffc00f0f8f 0xfbfffffffc00f0f8

def z404 : W := mkw 0x27a78fa480000000 0x427a78fa48000000 0x078f9ff1c000000d 0xc078f9ff1c000000

def z405 : W := mkw 0x6fb67ff63bfccf7c 0x16fb67ff63bfccf7 0xfff67ffe3ffccfff 0xffff67ffe3ffccff

def z406 : W := mkw 0x90da8e3be41f55ba 0x090da8e3be41f55b 0xc1ff9e3fc03ffffd 0xec1ff9e3fc03ffff

def z407 : W := mkw 0x2d807d4012500b60 0x12d807d4012500b6 0x3f807fc000000fff 0x53f807fc000000ff

def z408 : W := mkw 0x6d827ff61b744f7c 0x16d827ff61b744f7 0xff807ffe3ff00fff 0x7ff807ffe3ff00ff

def z409 : W := mkw 0x400202e40040405c 0x0400202e40040405 0x000007c000000070 0x0000007c00000007

def z410 : W := mkw 0x42b6aef6b0cccc5c 0x042b6aef6b0cccc5 0x47fffffff1cccc7f 0xe47fffffff1cccc7

def z411 : W := mkw 0x4234008620888004 0x0423400862088800 0x0070000e00000000 0x00070000e0000000

def z412 : W := mkw 0x12ef8ebdc01555ba 0x412ef8ebdc01555b 0xc1ff9e3fc03ffffd 0xec1ff9e3fc03ffff

def z413 : W := mkw 0x3fffffbfb00c0c00 0x43fffffbfb00c0c0 0x3ffffffff00c0c0f 0xf3ffffffff00c0c0

def z414 : W := mkw 0x3fefdfbdc01555ba 0x43fefdfbdc01555b 0x3fffffffc0000fff 0xd3fffffffc0000ff

def z415 : W := mkw 0x0882dfbdc01555ba 0x40882dfbdc01555b 0x00007fffc0000ff0 0x400007fffc0000ff

def z416 : W := mkw 0x377d00106dafa480 0x2377d00106dafa48 0xffff9831ffffff8f 0xfffff9831ffffff8

def z417 : W := mkw 0x273500002daaa000 0x2273500002daaa00 0xc78780003ffff008 0x2c78780003ffff00

def z418 : W := mkw 0x27a78fa480000000 0x427a78fa48000000 0x078787c000000008 0x0078787c00000000

def z419 : W := mkw 0x1a6fd2ad80000000 0x41a6fd2ad8000000 0x387ff83fc0000007 0xd387ff83fc000000

def z420 : W := mkw 0x2725000009a0a000 0x22725000009a0a00 0xff8780003ff0f00f 0x3ff8780003ff0f00

def z421 : W := mkw 0x3fefdfadc01111a2 0x43fefdfadc01111a 0xbfffffffc033338f 0xdbfffffffc033338

def z422 : W := mkw 0x3fefffed90400840 0x43fefffed9040084 0x7ffffffff1c00c7f 0xf7ffffffff1c00c7

def z423 : W := mkw 0xbd58715b7f6f0ec0 0x1bd58715b7f6f0ec 0xbe7879ffffcf0f87 0xfbe7879ffffcf0f8

def z424 : W := mkw 0x400020c610400844 0x0400020c61040084 0x000061ce00000000 0x0000061ce0000000

def z425 : W := mkw 0xbf7d700b3faaaa00 0x2bf7d700b3faaaa0 0x3e70600e3fc00002 0x13e70600e3fc0000

def z426 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0x3878603ffe0f0002 0x93878603ffe0f000

def z427 : W := mkw 0x0002227010444c58 0x00002227010444c5 0x460667f031cccc7b 0xe460667f031cccc7

def z428 : W := mkw 0x377d0000240a0000 0x0377d0000240a000 0xbfff80003e0f000f 0xbbfff80003e0f000

def z429 : W := mkw 0x2500000009200000 0x0250000000920000 0x4780000001f00008 0x04780000001f0000

def z430 : W := mkw 0x98daffbff60f0e80 0x498daffbff60f0e8 0xb8787ffffe0f0f87 0xfb8787ffffe0f0f8

def z431 : W := mkw 0x88107012760f0e80 0x088107012760f0e8 0xb80078003e0f0f87 0x7b80078003e0f0f8

def z432 : W := mkw 0x37fd0c002dbaa120 0x237fd0c002dbaa12 0xffff9e003fffffff 0xfffff9e003ffffff

def z433 : W := mkw 0x42b6aef6b0dcdd7e 0x042b6aef6b0dcdd7 0x47f7e7fe31fcfc7b 0xe47f7e7fe31fcfc7

def z434 : W := mkw 0xbd58701b7f2f0e80 0x0bd58701b7f2f0e8 0xfff8783fffff0f8f 0xffff8783fffff0f8

def z435 : W := mkw 0x8800500942010280 0x0880050094201028 0x00001801c0000380 0x000001801c000038

def z436 : W := mkw 0x18587000360a0a00 0x018587000360a0a0 0xb87878003e0f0f87 0xfb87878003e0f0f8

def z437 : W := mkw 0x2d82df30cb3557ba 0x12d82df30cb3557b 0xf98f9e31ce3ffffd 0xff98f9e31ce3ffff

def z438 : W := mkw 0x00028230c005549a 0x000028230c005549 0x400f8631c00ffc79 0xe400f8631c00ffc7

def z439 : W := mkw 0x000282208000501a 0x0000282208000501 0x000780000000f000 0x0000780000000f00

def z440 : W := mkw 0x0000001000040400 0x0000000100004040 0x00000030000c0c01 0xe00000030000c0c0

def z441 : W := mkw 0x3fffdfada0888000 0x43fffdfada088800 0x7ffffffff1ccc00f 0xf7ffffffff1ccc00

def z442 : W := mkw 0x9a7c701b768f8e80 0x09a7c701b768f8e8 0xfe7e783fffcfcf8f 0xffe7e783fffcfcf8

def z443 : W := mkw 0x777d20523deeec5c 0x2777d20523deeec5 0xffff80003ffffc7f 0xbffff80003ffffc7

def z444 : W := mkw 0xbf7d700b3faaaa00 0x2bf7d700b3faaaa0 0xffffe00e3ffff00f 0xbffffe00e3ffff00

def z445 : W := mkw 0x3dcbdf39c01555ba 0x43dcbdf39c01555b 0xf98f9e31c03ffffd 0xff98f9e31c03ffff

def z446 : W := mkw 0x2d907d523b7c0f60 0x12d907d523b7c0f6 0xfff07ffe3ffc0fff 0xffff07ffe3ffc0ff

def z447 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc1801e31c0300ffd 0x6c1801e31c0300ff

def z448 : W := mkw 0x0882dfbdc01555ba 0x40882dfbdc01555b 0xc18fffffc03ffffd 0xec18fffffc03ffff

def z449 : W := mkw 0x3fefffed9b600a40 0x53fefffed9b600a4 0x3fffffffffc0000f 0xd3fffffffffc0000

def z450 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0xc7ffe7fe31fffc7f 0xec7ffe7fe31fffc7

def z451 : W := mkw 0x80102002360a0a00 0x080102002360a0a0 0x000000003e000000 0x0000000003e00000

def z452 : W := mkw 0x0010200230080800 0x0001020023008080 0x0070600e30000002 0x00070600e3000000

def z453 : W := mkw 0x6fb67ff630cccc5c 0x06fb67ff630cccc5 0x7ff67ffe31cccc7f 0xf7ff67ffe31cccc7

def z454 : W := mkw 0x423602b6208cc41c 0x0423602b6208cc41 0x067667fe000cc00b 0xc067667fe000cc00

def z455 : W := mkw 0x9858705b764f0ec0 0x09858705b764f0ec 0xfe787fffffcf0fff 0xffe787fffffcf0ff

def z456 : W := mkw 0x00828e20c01111a2 0x000828e20c01111a 0x818f9e31c033338d 0xc818f9e31c033338

def z457 : W := mkw 0x2fa7ffe49b700b60 0x52fa7ffe49b700b6 0xff87ffc03ff00fff 0x7ff87ffc03ff00ff

def z458 : W := mkw 0x10580010640f0480 0x010580010640f048 0xb8781831fe0f0f87 0xfb8781831fe0f0f8

def z459 : W := mkw 0x2d805d0009200000 0x02d805d000920000 0xff807fc03ff0000f 0x7ff807fc03ff0000

def z460 : W := mkw 0x4236a2f6f0cddcde 0x04236a2f6f0cddcd 0x467fe7fff1cffc7b 0xe467fe7fff1cffc7

def z461 : W := mkw 0x00828e208010513a 0x000828e208010513 0x418f9e31c030f07d 0xc418f9e31c030f07

def z462 : W := mkw 0x0002023040054498 0x0000202304005449 0xc00e1e31c00fcffd 0xec00e1e31c00fcff

def z463 : W := mkw 0xbf7d719f760f0e80 0x4bf7d719f760f0e8 0xbe7879fffe0f0f87 0xfbe7879fffe0f0f8

def z464 : W := mkw 0x18cadfad80000000 0x418cadfad8000000 0x38787fffc0000007 0xd38787fffc000000

def z465 : W := mkw 0xfffffffff6cfcedc 0x4fffffffff6cfced 0xffffffffffcfcfff 0xfffffffffffcfcff

def z466 : W := mkw 0x4082aef6d0555dfe 0x04082aef6d0555df 0x00007fffc0000ff0 0x400007fffc0000ff

def z467 : W := mkw 0x02a68ea480000000 0x002a68ea48000000 0x07ffffffc000000f 0xc07ffffffc000000

def z468 : W := mkw 0x00000010401555ba 0x000000010401555b 0xc18f8000003ffffd 0xac18f8000003ffff

def z469 : W := mkw 0xbddaff7bff7f5ffa 0x1bddaff7bff7f5ff 0xffffffffffffffff 0xffffffffffffffff

def z470 : W := mkw 0x377f8230edaff49a 0x2377f8230edaff49 0xffff8031fffff00f 0xbffff8031fffff00

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z472 : W := mkw 0x126d008d00000000 0x4126d008d0000000 0x0070000e00000000 0x00070000e0000000

def z473 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xbe7800003fcf0007 0xbbe7800003fcf000

def z474 : W := mkw 0x25800d4009700160 0x125800d400970016 0xc7801fc001f00ffd 0x6c7801fc001f00ff

def z475 : W := mkw 0xbfffdfbfe40f0480 0x4bfffdfbfe40f048 0x3fffffffc00f000f 0xd3fffffffc00f000

def z476 : W := mkw 0x2500204019600840 0x0250020401960084 0xff8067c03ff00c7f 0x7ff8067c03ff00c7

def z477 : W := mkw 0x801020127fafae80 0x2801020127fafae8 0xc00000003fffff80 0x2c00000003fffff8

def z478 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x460607c031cccc78 0x2460607c031cccc7

def z479 : W := mkw 0x00828e30c0050480 0x000828e30c005048 0x818f9e31c00f0f8d 0xe818f9e31c00f0f8

def z480 : W := mkw 0x6fa67fe41bf0cb7c 0x16fa67fe41bf0cb7 0xff867fc03ff0cfff 0x7ff867fc03ff0cff

def z481 : W := mkw 0x1049000004022000 0x2104900000402200 0x0009800000033000 0x0000980000003300

def z482 : W := mkw 0xad807d5b5b750fe0 0x1ad807d5b5b750fe 0xff807ffffff00fff 0x7ff807ffffff00ff

def z483 : W := mkw 0x3fed7dcd1b700b60 0x53fed7dcd1b700b6 0xfff07fce3ff00fff 0x7fff07fce3ff00ff

def z484 : W := mkw 0x4012227230cccc5c 0x04012227230cccc5 0x4006063031cccc79 0xe4006063031cccc7

def z485 : W := mkw 0x9858701b360e0e00 0x09858701b360e0e0 0x3870603e3e0c0c03 0xf3870603e3e0c0c0

def z486 : W := mkw 0x12ff8e30e49ff5ba 0x212ff8e30e49ff5b 0xc1ff9e31c03ffffd 0xec1ff9e31c03ffff

def z487 : W := mkw 0x00828e3080044418 0x000828e308004441 0x418f9e31c00ccc7d 0xe418f9e31c00ccc7

def z488 : W := mkw 0xbdd9fd1bf60f0e80 0x4bdd9fd1bf60f0e8 0xb9f9f83ffe0f0f87 0xfb9f9f83ffe0f0f8

def z489 : W := mkw 0x25818d0080000000 0x425818d008000000 0x0181800000000000 0x0018180000000000

def z490 : W := mkw 0x2d0071401b600a40 0x12d0071401b600a4 0x7e0067c03fc00c7b 0x77e0067c03fc00c7

def z491 : W := mkw 0x2734000029a88000 0x02734000029a8800 0xfff600003ffcc00f 0xbfff600003ffcc00

def z492 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x80081e31c00f0ff5 0xe80081e31c00f0ff

def z493 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0x0078783fc00f0f80 0xc0078783fc00f0f8

def z494 : W := mkw 0x3ffd7d403ffaab60 0x33ffd7d403ffaab6 0xfff07fc03ff00fff 0x7fff07fc03ff00ff

def z495 : W := mkw 0x37ff8e20adbaf13a 0x237ff8e20adbaf13 0xffff86003ffff07f 0xbffff86003ffff07

def z496 : W := mkw 0x3f7d70003faaaa00 0x23f7d70003faaaa0 0xfffff8003fffff8f 0xffffff8003fffff8

def z497 : W := mkw 0x18585009240a0000 0x018585009240a000 0xb878783ffe0f0007 0xfb878783ffe0f000

def z498 : W := mkw 0x2d805d0000100120 0x02d805d000010012 0xff807fc000300fff 0x7ff807fc000300ff

def z499 : W := mkw 0x355800002d2a0000 0x0355800002d2a000 0xfff800003fff000f 0xbfff800003fff000

def z500 : W := mkw 0x08807d4012500b60 0x108807d4012500b6 0xb8007fc03e000ff7 0x7b8007fc03e000ff

def z501 : W := mkw 0x0000000000000000 0x0000000000000000 0x00081831c0000005 0xc00081831c000000

def z502 : W := mkw 0x3fefdfed89700160 0x53fefdfed8970016 0x7fffffffc1f0007f 0xd7fffffffc1f0007

def z503 : W := mkw 0x67a78fe480c0c05c 0x467a78fe480c0c05 0x478787c001c0c078 0x0478787c001c0c07

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x018f80000000000d 0x8018f80000000000

def z505 : W := mkw 0x0000000000000000 0x0000000000000000 0x80080000000f0005 0xa80080000000f000

def z506 : W := mkw 0x0082ae70d0555dfa 0x00082ae70d0555df 0xc78ffff1f1ffffff 0xec78ffff1f1fffff

def z507 : W := mkw 0x00928e30edbff5ba 0x200928e30edbff5b 0xc18f9e31fffffffd 0xec18f9e31fffffff

def z508 : W := mkw 0x0002022000004018 0x0000202200000401 0x400606000000c078 0x0400606000000c07

def z509 : W := mkw 0x3ffd5d002fbaa320 0x33ffd5d002fbaa32 0xffff98003ffff38f 0xbffff98003ffff38

def z510 : W := mkw 0x000020401b600a40 0x1000020401b600a4 0x000000003fc00000 0x0000000003fc0000

def z511 : W := mkw 0x2d82ff609b705b7a 0x12d82ff609b705b7 0xff87ffc03ff0ffff 0x7ff87ffc03ff0fff

def z512 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0x47807fc001f00ff8 0x447807fc001f00ff

def z513 : W := mkw 0x3feddd0980000000 0x43feddd098000000 0x3fff9801c000000f 0x93fff9801c000000

def z514 : W := mkw 0x9a7e72bf760f0e80 0x09a7e72bf760f0e8 0xbe7e7ffffe0f0f8f 0xfbe7e7ffffe0f0f8

def z515 : W := mkw 0x4092ae72f0ddddfe 0x04092ae72f0ddddf 0xc18f9e31f1fffffd 0xec18f9e31f1fffff

def z516 : W := mkw 0x8800701b52050e80 0x08800701b52050e8 0x8008783fc00f0f85 0xe8008783fc00f0f8

def z517 : W := mkw 0x00028230c005549a 0x000028230c005549 0x00000031c0000000 0x000000031c000000

def z518 : W := mkw 0x2d827f701b744f78 0x12d827f701b744f7 0xff867ff03ffccfff 0xfff867ff03ffccff

def z519 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x000f9e31c00ffff0 0xc000f9e31c00ffff

def z520 : W := mkw 0x7fffffffbbfccf7c 0x57fffffffbbfccf7 0xfffffffffffccfff 0xffffffffffffccff

def z521 : W := mkw 0x00828e2080000000 0x000828e208000000 0x0187860000000008 0x0018786000000000

def z522 : W := mkw 0x3dc95d000f322320 0x33dc95d000f32232 0xb98998000e333384 0x1b98998000e33338

def z523 : W := mkw 0xda7e72ff36cece5c 0x0da7e72ff36cece5 0x7e7667fe3fcccc7b 0xf7e7667fe3fcccc7

def z524 : W := mkw 0x00028230c01555ba 0x000028230c01555b 0xc00f8031c03ffff0 0xac00f8031c03ffff

def z525 : W := mkw 0x3f6d71cd1b600a40 0x53f6d71cd1b600a4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z526 : W := mkw 0x25802d4019700960 0x125802d401970096 0x478067c031f00c7b 0x6478067c031f00c7

def z527 : W := mkw 0x3dc9dd0980000000 0x43dc9dd098000000 0x3f89ffc1c000000f 0x53f89ffc1c000000

def z528 : W := mkw 0x9858701b7fafae80 0x29858701b7fafae8 0xf878783fffffff87 0xff878783fffffff8

def z529 : W := mkw 0x98dafe3bf60f0e80 0x098dafe3bf60f0e8 0xb9fffe3ffe0f0f8f 0xfb9fffe3ffe0f0f8

def z530 : W := mkw 0x023602a420888000 0x0023602a42088800 0x467667fe31ccc00b 0xe467667fe31ccc00

def z531 : W := mkw 0x000000000d222000 0x2000000000d22200 0x800000000e333000 0x0800000000e33300

def z532 : W := mkw 0x423420c630c88844 0x0423420c630c8884 0x467661ce31ccc00b 0xa467661ce31ccc00

def z533 : W := mkw 0x00828e208010513a 0x000828e208010513 0x0000060000000070 0x0000006000000007

def z534 : W := mkw 0x127d0000248aa000 0x2127d0000248aa00 0xb87f80003e0ff007 0xbb87f80003e0ff00

def z535 : W := mkw 0x2d805d000b300320 0x12d805d000b30032 0xff8018003ff0038f 0x3ff8018003ff0038

def z536 : W := mkw 0x27a78e30c9b5f5ba 0x227a78e30c9b5f5b 0xc78f9e31c1fffffd 0xec78f9e31c1fffff

def z537 : W := mkw 0x377f02a42daaa000 0x2377f02a42daaa00 0xffffe7fe3ffff00f 0xfffffe7fe3ffff00

def z538 : W := mkw 0x3ffd5d002daaa000 0x23ffd5d002daaa00 0xffffffc03ffff00f 0xfffffffc03ffff00

def z539 : W := mkw 0x0002023000044418 0x0000202300004441 0xc18f8630003ffc7d 0xec18f8630003ffc7

def z540 : W := mkw 0x98cade39c61757ba 0x098cade39c61757b 0xf98f9e31ce3ffffd 0xff98f9e31ce3ffff

def z541 : W := mkw 0x423602b6208cc41c 0x0423602b6208cc41 0x4076063e000ccc79 0xe4076063e000ccc7

def z542 : W := mkw 0x08807c0012100b20 0x008807c0012100b2 0xf9807e003e300fff 0x7f9807e003e300ff

def z543 : W := mkw 0x8000000046030280 0x0800000004603028 0x800000000e030380 0x0800000000e03038

def z544 : W := mkw 0x001000002daaa000 0x2001000002daaa00 0xc18f80003ffff00d 0xac18f80003ffff00

def z545 : W := mkw 0x9858501b640f0480 0x09858501b640f048 0x3878783fc00f0007 0xd3878783fc00f000

def z546 : W := mkw 0x0000204012500b60 0x10000204012500b6 0x0000000000000ff0 0x00000000000000ff

def z547 : W := mkw 0x10580000240a0000 0x010580000240a000 0x00780000000f0000 0x800780000000f000

def z548 : W := mkw 0x25800d0000000000 0x025800d000000000 0x078007c000000008 0x0078007c00000000

def z549 : W := mkw 0x1048000000000000 0x0104800000000000 0x3878000000000007 0x9387800000000000

def z550 : W := mkw 0x400222f610444c5c 0x0400222f610444c5 0x400667fe000ccc79 0xe400667fe000ccc7

def z551 : W := mkw 0x00102012300c0c00 0x000102012300c0c0 0x00000000300c0c00 0x200000000300c0c0

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000180000000f85 0x68000180000000f8

def z553 : W := mkw 0x3fffdfadadaaa000 0x63fffdfadadaaa00 0x3fffffffffc0000f 0xd3fffffffffc0000

def z554 : W := mkw 0x3dc9dd09c01111a2 0x43dc9dd09c01111a 0xb9899801c0333384 0x1b9899801c033338

def z555 : W := mkw 0x401020523deeec5c 0x2401020523deeec5 0xc00000003ffffc70 0x2c00000003ffffc7

def z556 : W := mkw 0x67b62ff639fccd7c 0x167b62ff639fccd7 0x47f667fe31fccc7b 0xe47f667fe31fccc7

def z557 : W := mkw 0xda7c70df76cf8ec4 0x0da7c70df76cf8ec 0xbe7879ffffcf0f87 0xfbe7879ffffcf0f8

def z558 : W := mkw 0x527f22f634ceec5c 0x2527f22f634ceec5 0x467fe7fe31cffc7b 0xe467fe7fe31cffc7

def z559 : W := mkw 0x9848701b56070e80 0x09848701b56070e8 0xb808783fce030f84 0x5b808783fce030f8

def z560 : W := mkw 0x1848500900000000 0x0184850090000000 0x3870600e00000002 0x13870600e0000000

def z561 : W := mkw 0x0800500000000000 0x0080050000000000 0x3800780000000007 0x5380078000000000

def z562 : W := mkw 0x3fffdfada40a0000 0x43fffdfada40a000 0xbffffffffe0f000f 0xfbffffffffe0f000

def z563 : W := mkw 0x0002822080000000 0x0000282208000000 0x000f8031c0000000 0x8000f8031c000000

def z564 : W := mkw 0x422622f610c4cc5c 0x0422622f610c4cc5 0x460667fe01c0cc78 0x4460667fe01c0cc7

def z565 : W := mkw 0x0800701052050e80 0x00800701052050e8 0xb8087831fe0f0f87 0xfb8087831fe0f0f8

def z566 : W := mkw 0x377d00106dbff5ba 0x2377d00106dbff5b 0xffff80003fffffff 0xbffff80003ffffff

def z567 : W := mkw 0x4ab67ff632dccf7c 0x14ab67ff632dccf7 0x46767ffe31cccffb 0xe46767ffe31cccff

def z568 : W := mkw 0xbfffffffff7f0fe0 0x5bfffffffff7f0fe 0xffffffffffff0fff 0xfffffffffffff0ff

def z569 : W := mkw 0x00800c10401555ba 0x000800c10401555b 0xc1801e00003ffffd 0x6c1801e00003ffff

def z570 : W := mkw 0x423420d630cccc5c 0x0423420d630cccc5 0x467061ce31cccc72 0x2467061ce31cccc7

def z571 : W := mkw 0x0000004009700160 0x1000000400970016 0x4000000001f00070 0x04000000001f0007

def z572 : W := mkw 0x105800002daaa000 0x2105800002daaa00 0xf87800003ffff007 0xbf87800003ffff00

def z573 : W := mkw 0x022602b400044418 0x0022602b40004441 0x467667fe000ccc7b 0xe467667fe000ccc7

def z574 : W := mkw 0xbffd7d5b7fffafe0 0x3bffd7d5b7fffafe 0xffffffffffffffff 0xffffffffffffffff

def z575 : W := mkw 0x401020523bfccf7c 0x1401020523bfccf7 0xc00000003ffccff0 0x2c00000003ffccff

def z576 : W := mkw 0x4010205230cccc5c 0x04010205230cccc5 0x4070603e31cccc73 0xe4070603e31cccc7

def z577 : W := mkw 0x376d000009a0a000 0x2376d000009a0a00 0x7fff800001f0f00f 0x97fff800001f0f00

def z578 : W := mkw 0x42b62ef630dccd7c 0x042b62ef630dccd7 0xc7f67ffe31fccfff 0xec7f67ffe31fccff

def z579 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x418f8631c03ff078 0x8418f8631c03ff07

def z580 : W := mkw 0x422622f610444c5c 0x0422622f610444c5 0x067667fe00000c7b 0xc067667fe00000c7

def z581 : W := mkw 0x98585009660b0280 0x098585009660b028 0xb8781801fe0f0387 0xbb8781801fe0f038

def z582 : W := mkw 0x0800714012400a40 0x10800714012400a4 0x000061c000000000 0x0000061c00000000

def z583 : W := mkw 0x777f02e42deae05c 0x2777f02e42deae05 0xffff87c03ffff07f 0xbffff87c03ffff07

def z584 : W := mkw 0x423682b6e08dd49e 0x0423682b6e08dd49 0x007f803fc00ff000 0x8007f803fc00ff00

def z585 : W := mkw 0x10582012340e0c00 0x010582012340e0c0 0xb878603e3e0f0c07 0xfb878603e3e0f0c0

def z586 : W := mkw 0x4082aef6d0555dfe 0x04082aef6d0555df 0xc18fffffc03ffffd 0xec18fffffc03ffff

def z587 : W := mkw 0x0234000020888000 0x0023400002088800 0x0670000031c00002 0x00670000031c0000

def z588 : W := mkw 0x00802c401b700b60 0x100802c401b700b6 0xc1801e003ff00ffd 0x6c1801e003ff00ff

def z589 : W := mkw 0x8000001b40050480 0x08000001b4005048 0x0000003fc0000000 0x00000003fc000000

def z590 : W := mkw 0x672702e409e0e05c 0x2672702e409e0e05 0x478787c001f0f078 0x0478787c001f0f07

def z591 : W := mkw 0x3dc97d401f722b60 0x33dc97d401f722b6 0xff89ffc03ff33fff 0x7ff89ffc03ff33ff

def z592 : W := mkw 0x2d807d0012000a00 0x02d807d0012000a0 0xbf807fc03e000f8f 0x7bf807fc03e000f8

def z593 : W := mkw 0x00808c00c01111a2 0x000808c00c01111a 0x00001801c0000380 0x000001801c000038

def z594 : W := mkw 0x376d000000000000 0x0376d00000000000 0x3e70000000000002 0x13e7000000000000

def z595 : W := mkw 0x423622b6308ccc1c 0x0423622b6308ccc1 0x0076603e300ccc03 0xe0076603e300ccc0

def z596 : W := mkw 0x2725000009a0a000 0x22725000009a0a00 0x0600000001c00000 0x00600000001c0000

def z597 : W := mkw 0xb77d001b6dafa480 0x2b77d001b6dafa48 0xffff803ffffff00f 0xbffff803ffffff00

def z598 : W := mkw 0x6f3471c63be88a44 0x16f3471c63be88a4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z599 : W := mkw 0x0000001040050480 0x0000000104005048 0xc18f9831c03fff8d 0xec18f9831c03fff8

def z600 : W := mkw 0x08807d401b700b60 0x108807d401b700b6 0xc0007fc03ff00ff0 0x6c0007fc03ff00ff

def z601 : W := mkw 0x00828e2080000000 0x000828e208000000 0xc18f9e31c03ff00d 0xec18f9e31c03ff00

def z602 : W := mkw 0x927d001b648fa480 0x2927d001b648fa48 0x007f803fc00ff000 0x8007f803fc00ff00

def z603 : W := mkw 0x1848500900000000 0x0184850090000000 0x38081801c0000004 0x138081801c000000

def z604 : W := mkw 0xbfffffafb60a0a00 0x4bfffffafb60a0a0 0x3ffffffffe00000f 0xd3ffffffffe00000

def z605 : W := mkw 0x0010000020888000 0x0001000002088800 0x4000000031ccc000 0x24000000031ccc00

def z606 : W := mkw 0x376d000000000000 0x0376d00000000000 0xffff8000003ff00f 0xbffff8000003ff00

def z607 : W := mkw 0x25828e30c93555ba 0x025828e30c93555b 0xff8f9e31ffffffff 0xfff8f9e31fffffff

def z608 : W := mkw 0x127c0000248a8000 0x0127c0000248a800 0xfe7e00003fcfc00f 0xbfe7e00003fcfc00

def z609 : W := mkw 0x00800c0000000000 0x000800c000000000 0x01801e000000000d 0x401801e000000000

def z610 : W := mkw 0x00122232300c4c18 0x000122232300c4c1 0x4076663e300ccc7b 0xe4076663e300ccc7

def z611 : W := mkw 0xdafefefff6dfdffe 0x0dafefefff6dfdff 0xffffffffffffffff 0xffffffffffffffff

def z612 : W := mkw 0x00000010401555ba 0x000000010401555b 0xc0081831c03ffff5 0xec0081831c03ffff

def z613 : W := mkw 0x9858700b360a0a00 0x09858700b360a0a0 0x3878783ffe000007 0xd3878783ffe00000

def z614 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x7ff780003ff0f00a 0x17ff780003ff0f00

def z615 : W := mkw 0x27a50d4009f0a160 0x327a50d4009f0a16 0x478787c001f0f078 0x0478787c001f0f07

def z616 : W := mkw 0x7fffffffbdeeec5c 0x67fffffffbdeeec5 0xfffffffffffffc7f 0xffffffffffffffc7

def z617 : W := mkw 0x42a68ef4c0d5d5fe 0x042a68ef4c0d5d5f 0xc78f9ff1c1fffffd 0xec78f9ff1c1fffff

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0xc18000000030000d 0x2c18000000030000

def z619 : W := mkw 0x0092ae32f01d5dba 0x00092ae32f01d5db 0xc1fffe3ff03fffff 0xec1fffe3ff03ffff

def z620 : W := mkw 0x2d807d001b300b20 0x12d807d001b300b2 0xb98078003e300f87 0x7b98078003e300f8

def z621 : W := mkw 0x37fd0d402dfaa160 0x337fd0d402dfaa16 0xffff87c03ffff07f 0xbffff87c03ffff07

def z622 : W := mkw 0x3f7d50092daaa000 0x23f7d50092daaa00 0xfffff83ffffff00f 0xffffff83ffffff00

def z623 : W := mkw 0x25828f608970517a 0x125828f608970517 0x478787c001f0f078 0x0478787c001f0f07

def z624 : W := mkw 0x0234000020888000 0x0023400002088800 0xc7ff800031fff00f 0xac7ff800031fff00

def z625 : W := mkw 0x3549000000000000 0x0354900000000000 0x3989800000000004 0x1398980000000000

def z626 : W := mkw 0x0234204030c88840 0x00234204030c8884 0x467667c031cccc7b 0xe467667c031cccc7

def z627 : W := mkw 0xbdc9dd09c6030280 0x4bdc9dd09c603028 0xb9899801ce030384 0x1b9899801ce03038

def z628 : W := mkw 0x00808c10c01515a2 0x000808c10c01515a 0x81899831c03f3f85 0xe81899831c03f3f8

def z629 : W := mkw 0x000020505b755ffa 0x1000020505b755ff 0xc00000003ffffff0 0x2c00000003ffffff

def z630 : W := mkw 0x422602f400c4c45c 0x0422602f400c4c45 0x460607f001cccc79 0xe460607f001cccc7

def z631 : W := mkw 0x9858700b360a0a00 0x09858700b360a0a0 0xb878600e3e0f0007 0xbb878600e3e0f000

def z632 : W := mkw 0x98d8fc1bf61f1fa2 0x098d8fc1bf61f1fa 0xb9f9f83ffe3f3f87 0xfb9f9f83ffe3f3f8

def z633 : W := mkw 0x2d0071401b700b60 0x12d0071401b700b6 0xfe0061c03ff00ff2 0x3fe0061c03ff00ff

def z634 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x41879e31c030fff8 0x441879e31c030fff

def z635 : W := mkw 0x8800700b12000a00 0x08800700b12000a0 0x0000600e00000000 0x00000600e0000000

def z636 : W := mkw 0x0000000009a0a000 0x20000000009a0a00 0x4000000001f0f000 0x04000000001f0f00

def z637 : W := mkw 0x2fa7dfa480000000 0x42fa7dfa48000000 0x3f87ffc00000000f 0x53f87ffc00000000

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x4600000031c0000b 0x24600000031c0000

def z639 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc1878600003ffff8 0x2c1878600003ffff

def z640 : W := mkw 0x422602a40080c01c 0x0422602a40080c01 0x000600000000c000 0x0000600000000c00

def z641 : W := mkw 0x400202b60004441c 0x0400202b60004441 0x0000003e00000000 0x00000003e0000000

def z642 : W := mkw 0x00828e2080100120 0x000828e208010012 0xc18f9e31c0300ffd 0xec18f9e31c0300ff

def z643 : W := mkw 0x2d907d403ffaab60 0x32d907d403ffaab6 0xff807fc03fffffff 0x7ff807fc03ffffff

def z644 : W := mkw 0x000000104005549a 0x0000000104005549 0x00000000000ff000 0x000000000000ff00

def z645 : W := mkw 0x3d49510900000000 0x43d4951090000000 0x3800000000000000 0x1380000000000000

def z646 : W := mkw 0x37ef8e30c01555ba 0x037ef8e30c01555b 0xffff9e31c03fffff 0xfffff9e31c03ffff

def z647 : W := mkw 0x6fb47dc63bf88b64 0x16fb47dc63bf88b6 0xfff07fce3ff00fff 0x7fff07fce3ff00ff

def z648 : W := mkw 0x1049800980000000 0x4104980098000000 0x00098001c0000000 0x000098001c000000

def z649 : W := mkw 0x35c98c00cd3331a2 0x235c98c00cd3331a 0xb9899801ce333384 0x1b9899801ce33338

def z650 : W := mkw 0x2d82df30c01555ba 0x02d82df30c01555b 0xff8ffff1c03fffff 0xfff8ffff1c03ffff

def z651 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x47ff800001fff008 0x847ff800001fff00

def z652 : W := mkw 0x00000000401111a2 0x000000000401111a 0x8000000000333380 0x0800000000033338

def z653 : W := mkw 0x3ffddd09adaaa000 0x63ffddd09adaaa00 0xffff9801fffff00f 0xbffff9801fffff00

def z654 : W := mkw 0x0800518d00000000 0x40800518d0000000 0x000061ce00000000 0x0000061ce0000000

def z655 : W := mkw 0x3dcbdf2980000000 0x43dcbdf298000000 0x398f9e31c000000d 0xd398f9e31c000000

def z656 : W := mkw 0x9a7ff2bff60f0e80 0x49a7ff2bff60f0e8 0xb87ff83ffe0f0f87 0xfb87ff83ffe0f0f8

def z657 : W := mkw 0xbd59701b7f2f2e80 0x2bd59701b7f2f2e8 0xb9f9f83ffe3f3f87 0xfb9f9f83ffe3f3f8

def z658 : W := mkw 0x000000000010513a 0x0000000000010513 0x400000000030f070 0x0400000000030f07

def z659 : W := mkw 0x18cade2980000000 0x018cade298000000 0x39fffe3fc000000f 0xd39fffe3fc000000

def z660 : W := mkw 0xbf7d718f360a0a00 0x4bf7d718f360a0a0 0x3e7061ce3e000002 0x13e7061ce3e00000

def z661 : W := mkw 0x00800d4000500160 0x100800d400050016 0x000007c000000070 0x0000007c00000007

def z662 : W := mkw 0x2d807d4010400840 0x02d807d401040084 0x7f807fc031c00c7f 0x77f807fc031c00c7

def z663 : W := mkw 0x42b6aef6f0ddddfe 0x042b6aef6f0ddddf 0x46767ffff1cccffb 0xe46767ffff1cccff

def z664 : W := mkw 0x3feddd8d80000000 0x43feddd8d8000000 0x3ff9f9cfc0000006 0x13ff9f9cfc000000

def z665 : W := mkw 0x527fa2ffb0cccc5c 0x4527fa2ffb0cccc5 0x467fe7fff1cccc7b 0xe467fe7fff1cccc7

def z666 : W := mkw 0x0010000020080000 0x0001000002008000 0x00700000300c0003 0xa00700000300c000

def z667 : W := mkw 0x8092ae32f61f5fba 0x08092ae32f61f5fb 0xc18f9e31fe3ffffd 0xec18f9e31fe3ffff

def z668 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xbf8079c03ff00386 0x1bf8079c03ff0038

def z669 : W := mkw 0x00828e2080000000 0x000828e208000000 0x00001e31c0000000 0x400001e31c000000

def z670 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xf98018003ff00ff4 0x3f98018003ff00ff

def z671 : W := mkw 0x8882fe3bd2155fba 0x08882fe3bd2155fb 0x00007e3fc0000ff0 0x400007e3fc0000ff

def z672 : W := mkw 0x27a78fb4c01555ba 0x427a78fb4c01555b 0xc78f9ff1c03ffffd 0xec78f9ff1c03ffff

def z673 : W := mkw 0x3fffff70fffffffa 0x33fffff70fffffff 0xfffffff1ffffffff 0xffffffff1fffffff

def z674 : W := mkw 0x3f7d71403feaaa40 0x33f7d71403feaaa4 0xffffe1c03ffff00f 0xbffffe1c03ffff00

def z675 : W := mkw 0x00808c0080101122 0x000808c008010112 0x0181800000303000 0x0018180000030300

def z676 : W := mkw 0x2500000009200000 0x0250000000920000 0xb98000000e300004 0x1b98000000e30000

def z677 : W := mkw 0x08807d4012500b60 0x108807d4012500b6 0xc1807fc000300ffd 0x6c1807fc000300ff

def z678 : W := mkw 0x0000001000044418 0x0000000100004441 0x40000000000ccc70 0x240000000000ccc7

def z679 : W := mkw 0x3f7d71403feaaa40 0x33f7d71403feaaa4 0x3e7061c03fc00002 0x13e7061c03fc0000

def z680 : W := mkw 0x9058201b760f0e80 0x09058201b760f0e8 0x8078003ffe0f0f80 0xa8078003ffe0f0f8

def z681 : W := mkw 0x2d0051000b200200 0x12d0051000b20020 0x380000000e000000 0x1380000000e00000

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0xb80000003e000007 0x3b80000003e00000

def z683 : W := mkw 0x00000010401555ba 0x000000010401555b 0x0000000000000ff0 0x00000000000000ff

def z684 : W := mkw 0x3fefdfbd80044418 0x43fefdfbd8004441 0x7fffffffc00ccc7f 0xf7fffffffc00ccc7

def z685 : W := mkw 0x9048000944030080 0x0904800094403008 0x00080001c0030000 0x000080001c003000

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f8000000ff000 0x8000f8000000ff00

def z687 : W := mkw 0x3fed5d0000000000 0x03fed5d000000000 0x3fffffc00000000f 0xd3fffffc00000000

def z688 : W := mkw 0xbdc87d495f730be0 0x1bdc87d495f730be 0xff887fc1fff30fff 0x7ff887fc1fff30ff

def z689 : W := mkw 0x127d0000248aa000 0x2127d0000248aa00 0x0070000000000000 0x0007000000000000

def z690 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xfe7000003ffff002 0x3fe7000003ffff00

def z691 : W := mkw 0x0000204010400840 0x0000020401040084 0x060061c031c00002 0x0060061c031c0000

def z692 : W := mkw 0x00100012200c0400 0x000100012200c040 0x0070003e000c0000 0x80070003e000c000

def z693 : W := mkw 0x25800d4009700160 0x125800d400970016 0xff8007c03ff0007f 0x3ff8007c03ff0007

def z694 : W := mkw 0x2fa67fe41b700b60 0x12fa67fe41b700b6 0xfff67ffe3ff00fff 0xffff67ffe3ff00ff

def z695 : W := mkw 0x00828e20c01151ba 0x000828e20c01151b 0xc18f9e01c033f3fc 0x0c18f9e01c033f3f

def z696 : W := mkw 0x00800c0000100120 0x000800c000010012 0x8180180000300384 0x0818018000030038

def z697 : W := mkw 0x985a723b760f4e98 0x0985a723b760f4e9 0xf87e7e3ffe0fcfff 0xff87e7e3ffe0fcff

def z698 : W := mkw 0xbffffe3bffbfffba 0x2bffffe3bffbfffb 0xfffffe3fffffffff 0xffffffe3ffffffff

def z699 : W := mkw 0x2d807d505b755ffa 0x12d807d505b755ff 0xff807fc03fffffff 0x7ff807fc03ffffff

def z700 : W := mkw 0x10da8e30e41f55ba 0x010da8e30e41f55b 0xf9ff9e31fe3fffff 0xff9ff9e31fe3ffff

def z701 : W := mkw 0x423622f670ddddfe 0x0423622f670ddddf 0xc67667fe31fffffb 0xec67667fe31fffff

def z702 : W := mkw 0x7f7f73ff30cccc5c 0x47f7f73ff30cccc5 0x7e7667fe31cccc7b 0xf7e7667fe31cccc7

def z703 : W := mkw 0x250020401b700b60 0x1250020401b700b6 0xff8000003ff00fff 0x3ff8000003ff00ff

def z704 : W := mkw 0x2fb47d403bf88b60 0x12fb47d403bf88b6 0xfff67fc03ffccfff 0xffff67fc03ffccff

def z705 : W := mkw 0x4234205230cccc5c 0x04234205230cccc5 0x4676000031cccc7b 0xa4676000031cccc7

def z706 : W := mkw 0x377d000020888000 0x0377d00002088800 0x7fff800031ccc00f 0xb7fff800031ccc00

def z707 : W := mkw 0x3f6d519d401555ba 0x43f6d519d401555b 0xfe7061ce003ffff2 0x3fe7061ce003ffff

def z708 : W := mkw 0x80102052765f0fe0 0x180102052765f0fe 0x800000003e0f0ff0 0x2800000003e0f0ff

def z709 : W := mkw 0x3fefdfad8da2a000 0x63fefdfad8da2a00 0xffffffffcff3f00f 0xdffffffffcff3f00

def z710 : W := mkw 0x9848701b56070e80 0x09848701b56070e8 0xb878783fce030f87 0xdb878783fce030f8

def z711 : W := mkw 0x7dd9fd5bb0cccc5c 0x47dd9fd5bb0cccc5 0x79899801f1cccc74 0x379899801f1cccc7

def z712 : W := mkw 0x3d48510900000000 0x03d4851090000000 0x3e7879ffc0000007 0xd3e7879ffc000000

def z713 : W := mkw 0x105800002daaa000 0x2105800002daaa00 0xf9ff80003ffff00f 0xbf9ff80003ffff00

def z714 : W := mkw 0x98dafe2bb61a5b3a 0x098dafe2bb61a5b3 0x79f7e60e3e30f07a 0x179f7e60e3e30f07

def z715 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0xc6767ffe31cccfff 0xec6767ffe31cccff

def z716 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xfe007fc03ff00ff2 0x7fe007fc03ff00ff

def z717 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc78f9e31f1ffffff 0xec78f9e31f1fffff

def z718 : W := mkw 0x1aefdfad80000000 0x41aefdfad8000000 0x387fffffc0000007 0xd387fffffc000000

def z719 : W := mkw 0x126fa2ed9b700b60 0x5126fa2ed9b700b6 0xc07f803ffff00ff0 0xac07f803ffff00ff

def z720 : W := mkw 0x127f82bde48ff49a 0x6127f82bde48ff49 0x007f803fc00ff000 0x8007f803fc00ff00

def z721 : W := mkw 0x023622e430c88840 0x0023622e430c8884 0x467667fe31cccc7b 0xe467667fe31cccc7

def z722 : W := mkw 0x9858700b760b0a80 0x09858700b760b0a8 0xb878783ffe030387 0xdb878783ffe03038

def z723 : W := mkw 0x422622f610c4cc5c 0x0422622f610c4cc5 0x467667fe01c0cc7b 0xc467667fe01c0cc7

def z724 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xffffe03e3ffff00f 0xfffffe03e3ffff00

def z725 : W := mkw 0x377d008d2daaa000 0x6377d008d2daaa00 0xffff800e3ffff00f 0xbffff800e3ffff00

def z726 : W := mkw 0x3f6fd3ad80000000 0x43f6fd3ad8000000 0x3e7ff9ffc0000007 0xd3e7ff9ffc000000

def z727 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3ff9ffffc0000006 0x53ff9ffffc000000

def z728 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x39ffffffc0000004 0xd39ffffffc000000

def z729 : W := mkw 0x355800002d2a0000 0x0355800002d2a000 0xffff80003ffff00f 0xbffff80003ffff00

def z730 : W := mkw 0x2d805d0009300120 0x02d805d000930012 0xff807fc03ff00fff 0x7ff807fc03ff00ff

def z731 : W := mkw 0x9858701b768fae80 0x29858701b768fae8 0xb878783ffe0fff87 0xfb878783ffe0fff8

def z732 : W := mkw 0x18cadfad80000000 0x418cadfad8000000 0x00787fffc0000000 0xc00787fffc000000

def z733 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff867fc03ffccfff 0xfff867fc03ffccff

def z734 : W := mkw 0x4010205270cddcde 0x04010205270cddcd 0x4000000031cffc70 0x24000000031cffc7

def z735 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb878783fce0f0f84 0xdb878783fce0f0f8

def z736 : W := mkw 0x3dc9dd0989300120 0x53dc9dd098930012 0x39899801c0300004 0x139899801c030000

def z737 : W := mkw 0x00828fb4c01555ba 0x400828fb4c01555b 0xc18f9ff1c03ffffd 0xec18f9ff1c03ffff

def z738 : W := mkw 0x3f7d71cd3feaaa40 0x73f7d71cd3feaaa4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z739 : W := mkw 0x0892dfadadaaa000 0x60892dfadadaaa00 0xc0007ffffffff000 0x6c0007ffffffff00

def z740 : W := mkw 0x00800c10401505a0 0x000800c10401505a 0xc18f9e31c03ffffd 0xec18f9e31c03ffff

def z741 : W := mkw 0x25802d401b700b60 0x125802d401b700b6 0xff8007c03ff00fff 0x3ff8007c03ff00ff

def z742 : W := mkw 0x354900000d222000 0x2354900000d22200 0xff8f80003ffff00f 0xbff8f80003ffff00

def z743 : W := mkw 0x422602e400c0c05c 0x0422602e400c0c05 0x467667ce01c0c07a 0x0467667ce01c0c07

def z744 : W := mkw 0x3dcadf2980000000 0x03dcadf298000000 0x3fffffffc000000f 0xd3fffffffc000000

def z745 : W := mkw 0x4236a2f6f0cddcde 0x04236a2f6f0cddcd 0xc7ffe7fff1fffc7f 0xec7ffe7fff1fffc7

def z746 : W := mkw 0xbdc9dd09cf3303a0 0x5bdc9dd09cf3303a 0xb9899801ce330384 0x1b9899801ce33038

def z747 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467667fe31c0cc7a 0x4467667fe31c0cc7

def z748 : W := mkw 0x126f82ad80000000 0x4126f82ad8000000 0x067fe1ffc0000002 0x8067fe1ffc000000

def z749 : W := mkw 0x3fefdfad8f322320 0x73fefdfad8f32232 0xbfffffffce33338f 0xdbfffffffce33338

def z750 : W := mkw 0xbdc85d090f320320 0x1bdc85d090f32032 0xb98018000e300384 0x1b98018000e30038

def z751 : W := mkw 0xb5d80d5b6d7f05e0 0x1b5d80d5b6d7f05e 0x47f807ffc1ff0078 0x847f807ffc1ff007

def z752 : W := mkw 0xd858705b76cf8ec4 0x0d858705b76cf8ec 0xb878783fffcf0f87 0xfb878783fffcf0f8

def z753 : W := mkw 0x9859701b760f2e80 0x29859701b760f2e8 0xb879f83ffe0f3f87 0xfb879f83ffe0f3f8

def z754 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467067fe31cccc72 0x6467067fe31cccc7

def z755 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb878783ffe0f0386 0x9b878783ffe0f038

def z756 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0xc67667fe31fffc7b 0xec67667fe31fffc7

def z757 : W := mkw 0x4010205270cdccdc 0x04010205270cdccd 0xc000000031cfcff0 0x2c000000031cfcff

def z758 : W := mkw 0xaf25701b5ba5ae80 0x2af25701b5ba5ae8 0x4787f83fc1f0ff88 0x44787f83fc1f0ff8

def z759 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0x7fff80003ffff00a 0x97fff80003ffff00

def z760 : W := mkw 0x0aa6dfad80000000 0x40aa6dfad8000000 0x06707fffc0000002 0x406707fffc000000

def z761 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x7ffffffff1c0000f 0xf7ffffffff1c0000

def z762 : W := mkw 0x25800d4009700160 0x125800d400970016 0xff801fc03ff00fff 0x7ff801fc03ff00ff

def z763 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x067667fe31c00c7b 0xc067667fe31c00c7

def z764 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb87ff83ffe0fff87 0xfb87ff83ffe0fff8

def z765 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff887fc03fff0fff 0xfff887fc03fff0ff

def z766 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467667fe31ccc07a 0x8467667fe31ccc07

def z767 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff89ffc03ff33fff 0x7ff89ffc03ff33ff

def z768 : W := mkw 0x2725000009a0a000 0x22725000009a0a00 0xff8f80003ffff00f 0xbff8f80003ffff00

def z769 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x067067fe31cc0c73 0xe067067fe31cc0c7

def z770 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3fffe7ffc000000a 0x93fffe7ffc000000

def z771 : W := mkw 0xa7b7afb6f60f0e80 0x4a7b7afb6f60f0e8 0x878787c03e0f0f88 0x2878787c03e0f0f8

def z772 : W := mkw 0xff7d70cf3feaaa44 0x2ff7d70cf3feaaa4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z773 : W := mkw 0x40828eb6c01555be 0x040828eb6c01555b 0xc18f9e3fc03ffffd 0xec18f9e3fc03ffff

def z774 : W := mkw 0xbfefdfad86020200 0x4bfefdfad8602020 0x3fffffffce00000f 0xd3fffffffce00000

def z775 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467667fe01cccc78 0xc467667fe01cccc7

def z776 : W := mkw 0x4010205230cccc5c 0x04010205230cccc5 0x467067fe31cccc7b 0xe467067fe31cccc7

def z777 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0x3878783ffe0f0f82 0xd3878783ffe0f0f8

def z778 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0xbffffffffe00000f 0xfbffffffffe00000

def z779 : W := mkw 0x1afd7d4036daab60 0x31afd7d4036daab6 0x007fffc0000ffff0 0xc007fffc0000ffff

def z780 : W := mkw 0x1858701b320c0e00 0x01858701b320c0e0 0xb878783ffe0c0f87 0xfb878783ffe0c0f8

def z781 : W := mkw 0x3fefdfad8b300320 0x53fefdfad8b30032 0xfffffffffff0038f 0xffffffffffff0038

def z782 : W := mkw 0x022622f410444c58 0x0022622f410444c5 0x467667fe31cccc7b 0xe467667fe31cccc7

def z783 : W := mkw 0x2fa6dfa480000000 0x02fa6dfa48000000 0x3fffffffc000000f 0xd3fffffffc000000

def z784 : W := mkw 0x9858715b764f0ec0 0x19858715b764f0ec 0xb87879fffe0f0f87 0xfb87879fffe0f0f8

def z785 : W := mkw 0xad807d4b1b700b60 0x1ad807d4b1b700b6 0xff807fce3ff00fff 0x7ff807fce3ff00ff

def z786 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xf9ff80003ffff004 0xbf9ff80003ffff00

def z787 : W := mkw 0x9848500946030280 0x0984850094603028 0xb878183fce030384 0x9b878183fce03038

def z788 : W := mkw 0x401020527dfffdfe 0x2401020527dfffdf 0xc00000003ffffff0 0x2c00000003ffffff

def z789 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x7fffffffc030f00f 0xd7fffffffc030f00

def z790 : W := mkw 0xc0102052764f4edc 0x0c0102052764f4ed 0x800000003e0f0ff0 0x2800000003e0f0ff

def z791 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467067fe31c00c7b 0x6467067fe31c00c7

def z792 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0xbfffffffc033300f 0xdbfffffffc033300

def z793 : W := mkw 0x37ff8e30edbff5ba 0x237ff8e30edbff5b 0x3e701e31ffc00ff2 0x53e701e31ffc00ff

def z794 : W := mkw 0x0002023040054498 0x0000202304005449 0xc18f9e31c03ffffd 0xec18f9e31c03ffff

def z795 : W := mkw 0x10582012740f0c80 0x010582012740f0c8 0xb878783ffe0f0f87 0xfb878783ffe0f0f8

def z796 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xf9f8783ffe3f0f8f 0xff9f8783ffe3f0f8

def z797 : W := mkw 0xc010205276dfdffe 0x0c010205276dfdff 0xc00000003ffffff0 0x2c00000003ffffff

def z798 : W := mkw 0x423420c630c88844 0x0423420c630c8884 0x467667ce31cccc7b 0xe467667ce31cccc7

def z799 : W := mkw 0x3dc9dd098f322320 0x73dc9dd098f32232 0xb9899801ce333384 0x1b9899801ce33338

def z800 : W := mkw 0x18585019640f0480 0x018585019640f048 0xb878783ffe0f0f87 0xfb878783ffe0f0f8

def z801 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xfff780003ffff00a 0x3fff780003ffff00

def z802 : W := mkw 0x423622f670cdccdc 0x0423622f670cdccd 0xc67667fe31cfcffb 0xec67667fe31cfcff

def z803 : W := mkw 0xd858701b768fce9c 0x0d858701b768fce9 0xb878783ffe0fcf87 0xfb878783ffe0fcf8

def z804 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc18f9831c03ffff4 0xac18f9831c03ffff

def z805 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff801fc03ff00ffc 0x3ff801fc03ff00ff

def z806 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xbf807fc03ff00ff6 0x5bf807fc03ff00ff

def z807 : W := mkw 0x2d0070401b600a40 0x02d0070401b600a4 0xff807fc03ff00fff 0x7ff807fc03ff00ff

def z808 : W := mkw 0x0a2652ad00000000 0x00a2652ad0000000 0x06767fffc000000b 0xc06767fffc000000

def z809 : W := mkw 0x9858700b360a0a00 0x09858700b360a0a0 0xb878783ffe000f87 0xfb878783ffe000f8

def z810 : W := mkw 0x3fefdfad89a0a000 0x63fefdfad89a0a00 0xfffffffffff0f00f 0xffffffffffff0f00

def z811 : W := mkw 0x80102052764f0ec0 0x080102052764f0ec 0xc00000003fcf0ff0 0x2c00000003fcf0ff

def z812 : W := mkw 0x3fefdfad8d222000 0x63fefdfad8d22200 0x3fffffffce00000f 0xd3fffffffce00000

def z813 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x818f9e31c03ffff4 0xc818f9e31c03ffff

def z814 : W := mkw 0x9858701b768f8e80 0x09858701b768f8e8 0xf878783fffcfcf87 0xff878783fffcfcf8

def z815 : W := mkw 0x754b22f61d666c5c 0x2754b22f61d666c5 0xb989e7fe0e333c74 0x5b989e7fe0e333c7

def z816 : W := mkw 0x00000010401555ba 0x000000010401555b 0xc18f9831c03ffffd 0xec18f9831c03ffff

def z817 : W := mkw 0x6fb65fb62bbcc73c 0x16fb65fb62bbcc73 0xb9f6183e0e3cc384 0x9b9f6183e0e3cc38

def z818 : W := mkw 0xda6e52ed46c3c2dc 0x0da6e52ed46c3c2d 0xfe0e1fc1cfc3c3fc 0x1fe0e1fc1cfc3c3f

def z819 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0x418f9e31c03ffff8 0xc418f9e31c03ffff

def z820 : W := mkw 0x98585009660b0280 0x098585009660b028 0xb878783ffe0f0387 0xfb878783ffe0f038

def z821 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff8fffc03ff00fff 0xfff8fffc03ff00ff

def z822 : W := mkw 0x08807c4012500b60 0x008807c4012500b6 0xff807fc03ff00fff 0x7ff807fc03ff00ff

def z823 : W := mkw 0x3fefdfad82000200 0x43fefdfad8200020 0xbfffffffce00038f 0xdbfffffffce00038

def z824 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3fffffffc00ff00f 0xd3fffffffc00ff00

def z825 : W := mkw 0x3fefdfad80004018 0x43fefdfad8000401 0x7fffffffc000c07f 0xd7fffffffc000c07

def z826 : W := mkw 0xc010205274cfccdc 0x0c010205274cfccd 0x4000000031cfcc70 0x24000000031cfcc7

def z827 : W := mkw 0x12ef8ead80000000 0x412ef8ead8000000 0x07ffffffc000000f 0xc07ffffffc000000

def z828 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff8067c03ff00ffa 0x3ff8067c03ff00ff

def z829 : W := mkw 0x1aeedead80000000 0x01aeedead8000000 0x3fffffffc000000f 0xd3fffffffc000000

def z830 : W := mkw 0x3f6f52ad00000000 0x03f6f52ad0000000 0x3fffffffc000000f 0xd3fffffffc000000

def z831 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x067667fe31cccc72 0xc067667fe31cccc7

def z832 : W := mkw 0x3fefdfad8000501a 0x43fefdfad8000501 0x3fffffffc000f00f 0xd3fffffffc000f00

def z833 : W := mkw 0x423622f670cdccdc 0x0423622f670cdccd 0x46767ffff1cccffb 0xe46767ffff1cccff

def z834 : W := mkw 0x18587009360a0a00 0x018587009360a0a0 0xb878783ffe0f0f87 0xfb878783ffe0f0f8

def z835 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb9fff83ffe0f0f8f 0xfb9fff83ffe0f0f8

def z836 : W := mkw 0x18c85d0900000000 0x018c85d090000000 0x38787fffc0000007 0xd38787fffc000000

def z837 : W := mkw 0x3f6d518d00000000 0x43f6d518d0000000 0x3e7079ffc0000002 0x53e7079ffc000000

def z838 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xbfff80003ffff006 0x9bfff80003ffff00

def z839 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff87ffc03ff0ffff 0x7ff87ffc03ff0fff

def z840 : W := mkw 0x022682a480000000 0x0022682a48000000 0x067fe7ffc000000b 0xc067fe7ffc000000

def z841 : W := mkw 0x1aefdfad80000000 0x41aefdfad8000000 0x067fffffc000000b 0xc067fffffc000000

def z842 : W := mkw 0x27a78fa489300120 0x527a78fa48930012 0x078787c000300008 0x0078787c00030000

def z843 : W := mkw 0x3f6d518d00000000 0x43f6d518d0000000 0x3e7861ffc0000002 0x93e7861ffc000000

def z844 : W := mkw 0x67a78ee489f0f17e 0x267a78ee489f0f17 0x478787c001f0f078 0x0478787c001f0f07

def z845 : W := mkw 0x3fefdfad8d222000 0x63fefdfad8d22200 0xffffffffce3ff00f 0xfffffffffce3ff00

def z846 : W := mkw 0x18cadfad80000000 0x418cadfad8000000 0x39ffffffc000000f 0xd39ffffffc000000

def z847 : W := mkw 0x3dc95d090b300320 0x53dc95d090b30032 0xb98018000e300384 0x1b98018000e30038

def z848 : W := mkw 0x0000204010400840 0x0000020401040084 0x467067fe31c00c7b 0xe467067fe31c00c7

def z849 : W := mkw 0x022420c410400840 0x0022420c41040084 0x467067ce31c00c7b 0x6467067ce31c00c7

def z850 : W := mkw 0x3fefdfad89200000 0x43fefdfad8920000 0x7fffffffc1f0000f 0xd7fffffffc1f0000

def z851 : W := mkw 0xc23622f676cfcedc 0x0c23622f676cfced 0xc67e7fffffcfcfff 0xec67e7fffffcfcff

def z852 : W := mkw 0x9858705b764f0ec0 0x09858705b764f0ec 0xf878783fffcf0ff7 0xff878783fffcf0ff

def z853 : W := mkw 0x273500002daaa000 0x2273500002daaa00 0xff8780003ffff00f 0x3ff8780003ffff00

def z854 : W := mkw 0x022602e400400040 0x0022602e40040004 0x467667fe01c0007b 0xc467667fe01c0007

def z855 : W := mkw 0x422602f400c4c45c 0x0422602f400c4c45 0x467667fe01cccc7b 0xe467667fe01cccc7

def z856 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc1fffe3fc03fffff 0xec1fffe3fc03ffff

def z857 : W := mkw 0x2d02f370db655eda 0x12d02f370db655ed 0x3e0fe1f1ffcff002 0x93e0fe1f1ffcff00

def z858 : W := mkw 0x3fefdfad89200000 0x43fefdfad8920000 0xfffffffffffff00f 0xffffffffffffff00

def z859 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb870783ffe0f0f82 0x7b870783ffe0f0f8

def z860 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xf87e783ffe0fcf8f 0xff87e783ffe0fcf8

def z861 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0xc67e67fe31cfcc7f 0xec67e67fe31cfcc7

def z862 : W := mkw 0x0aa6dfad80000000 0x40aa6dfad8000000 0x07ffffffc000000f 0xc07ffffffc000000

def z863 : W := mkw 0x1a6fd2ad80000000 0x41a6fd2ad8000000 0x3e7fffffc000000f 0xd3e7fffffc000000

def z864 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xffff86003ffffc7f 0xfffff86003ffffc7

def z865 : W := mkw 0x1848701952050e80 0x01848701952050e8 0xb878783ffe0f0f87 0xfb878783ffe0f0f8

def z866 : W := mkw 0x423420c630c88844 0x0423420c630c8884 0x467067ce31c0007a 0x0467067ce31c0007

def z867 : W := mkw 0x376f82ad80000000 0x4376f82ad8000000 0x3fffe7ffc000000f 0xd3fffe7ffc000000

def z868 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3e787fffc0000007 0xd3e787fffc000000

def z869 : W := mkw 0x1848518d00000000 0x41848518d0000000 0x387879ffc0000007 0xd387879ffc000000

def z870 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3ff7ffffc000000a 0x53ff7ffffc000000

def z871 : W := mkw 0x27a78fa480000000 0x427a78fa48000000 0x07ffffffc000000f 0xc07ffffffc000000

def z872 : W := mkw 0x423722f630ccec5c 0x2423722f630ccec5 0x4677e7fe31ccfc7b 0xe4677e7fe31ccfc7

def z873 : W := mkw 0x184a52ad00000000 0x0184a52ad0000000 0x38787fffc0000007 0xd38787fffc000000

def z874 : W := mkw 0x3feddd8d80000000 0x43feddd8d8000000 0x3ff9f9ffc0000007 0xd3ff9f9ffc000000

def z875 : W := mkw 0xd858705b76cfcedc 0x0d858705b76cfced 0xfe787fffffcfcfff 0xffe787fffffcfcff

def z876 : W := mkw 0x3fefdfad8d222000 0x63fefdfad8d22200 0xfffffffffff3300f 0xffffffffffff3300

def z877 : W := mkw 0xbdc8dd09cf3313a2 0x1bdc8dd09cf3313a 0xb9899801ce333384 0x1b9899801ce33338

def z878 : W := mkw 0x1848500900000000 0x0184850090000000 0x3e787fffc000000f 0xd3e787fffc000000

def z879 : W := mkw 0x3dc9dd09cb3113a2 0x53dc9dd09cb3113a 0xb9899801ce333384 0x1b9899801ce33338

def z880 : W := mkw 0x423622e630c8c85c 0x0423622e630c8c85 0x467667fe31c0c07b 0xc467667fe31c0c07

def z881 : W := mkw 0x2d807d491b700b60 0x12d807d491b700b6 0xff807ffffff00fff 0x7ff807ffffff00ff

def z882 : W := mkw 0x2d807d4012400a40 0x02d807d4012400a4 0xff807fc03fc00fff 0x7ff807fc03fc00ff

def z883 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x47ffe7fe31cccc7f 0xe47ffe7fe31cccc7

def z884 : W := mkw 0x9058001b640f0480 0x09058001b640f048 0xb878183ffe0f0f87 0xfb878183ffe0f0f8

def z885 : W := mkw 0x2734000029a88000 0x02734000029a8800 0xffff80003ffff00f 0xbffff80003ffff00

def z886 : W := mkw 0x4236a2f6f0cddcde 0x04236a2f6f0cddcd 0x467667fff1cccc7b 0xe467667fff1cccc7

def z887 : W := mkw 0x42b4acc6f0d999e6 0x042b4acc6f0d999e 0x87f9f9cff1f33386 0x087f9f9cff1f3338

def z888 : W := mkw 0x0882dfad80000000 0x40882dfad8000000 0x00707fffc0000003 0xc00707fffc000000

def z889 : W := mkw 0x3f6fd3ad80000000 0x43f6fd3ad8000000 0x3e7061ffc0000002 0x13e7061ffc000000

def z890 : W := mkw 0x3fee5fad00000000 0x03fee5fad0000000 0x3ffe7fffc000000f 0xd3ffe7fffc000000

def z891 : W := mkw 0x3fefdfad80808000 0x43fefdfad8080800 0x7fffffffc1c0c00f 0xd7fffffffc1c0c00

def z892 : W := mkw 0x27a78fe48970517a 0x527a78fe48970517 0x478787c001f0f078 0x0478787c001f0f07

def z893 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xf98f9e31fe3fffff 0xff98f9e31fe3ffff

def z894 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467667ce31cccc7a 0x2467667ce31cccc7

def z895 : W := mkw 0x3fefdfad80100120 0x43fefdfad8010012 0x3fffffffc0000fff 0xd3fffffffc0000ff

def z896 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0xbfffffffc0000f8f 0xfbfffffffc0000f8

def z897 : W := mkw 0x022602a400000000 0x0022602a40000000 0x067e7fffc000000f 0xc067e7fffc000000

def z898 : W := mkw 0xd27f82bfe48fc49c 0x4d27f82bfe48fc49 0x007f803fc00fc000 0x8007f803fc00fc00

def z899 : W := mkw 0x1aefdfad80000000 0x41aefdfad8000000 0x00707fffc0000000 0x400707fffc000000

def z900 : W := mkw 0xc882feffd2555ffe 0x0c882feffd2555ff 0x00007fffc0000ff0 0x400007fffc0000ff

def z901 : W := mkw 0xbdc95d094f3323a0 0x3bdc95d094f3323a 0xb9899801ce333384 0x1b9899801ce33338

def z902 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0x7f807fc03ff00ffa 0x57f807fc03ff00ff

def z903 : W := mkw 0x2d81fd409b700b60 0x52d81fd409b700b6 0xff81ffc03ff00fff 0x7ff81ffc03ff00ff

def z904 : W := mkw 0x423622f634ceec5c 0x2423622f634ceec5 0x467667fe31cffc7b 0xe467667fe31cffc7

def z905 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc18f9e01c03ffffc 0x2c18f9e01c03ffff

def z906 : W := mkw 0x9848501946070680 0x0984850194607068 0xb878783fce0f0f87 0xfb878783fce0f0f8

def z907 : W := mkw 0x801020527fffafe0 0x3801020527fffafe 0xc00000003ffffff0 0x2c00000003ffffff

def z908 : W := mkw 0x67a78fe489f0c17c 0x567a78fe489f0c17 0x478787c001f0c078 0x0478787c001f0c07

def z909 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb878783ffe030f86 0x5b878783ffe030f8

def z910 : W := mkw 0xbf7d714b3feaaa40 0x3bf7d714b3feaaa4 0x3e7061ce3fc00002 0x13e7061ce3fc0000

def z911 : W := mkw 0x1848500902000200 0x0184850090200020 0xb878783fce000387 0xdb878783fce00038

def z912 : W := mkw 0xc01020527fefeedc 0x2c01020527fefeed 0xc00000003ffffff0 0x2c00000003ffffff

def z913 : W := mkw 0x3fefdfad89202000 0x63fefdfad8920200 0x3fffffffc030300f 0xd3fffffffc030300

def z914 : W := mkw 0x801020527f6f0ec0 0x1801020527f6f0ec 0x800000003fcf0f80 0x2800000003fcf0f8

def z915 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xf8787e3ffe0f0fff 0xff8787e3ffe0f0ff

def z916 : W := mkw 0x0882fffdd2555ffa 0x50882fffdd2555ff 0x00007fffc0000ff0 0x400007fffc0000ff

def z917 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0x3870783ffe0c0f83 0xf3870783ffe0c0f8

def z918 : W := mkw 0x37ef8ea480000000 0x037ef8ea48000000 0x3fffffffc000000f 0xd3fffffffc000000

def z919 : W := mkw 0x4236a2f6f0cddcde 0x04236a2f6f0cddcd 0xc67ffffff1cfffff 0xec67ffffff1cffff

def z920 : W := mkw 0x423420c630c88844 0x0423420c630c8884 0x067067ce31c00c72 0x4067067ce31c00c7

def z921 : W := mkw 0x3f6fd3ad80000000 0x43f6fd3ad8000000 0x3e7fe7ffc000000b 0xd3e7fe7ffc000000

def z922 : W := mkw 0x3fefdfad80100120 0x43fefdfad8010012 0xbfffffffc030038f 0xdbfffffffc030038

def z923 : W := mkw 0x3fefdfad80100120 0x43fefdfad8010012 0xffffffffc03fffff 0xfffffffffc03ffff

def z924 : W := mkw 0x8810701b720d0e80 0x08810701b720d0e8 0xb870783ffe0c0f87 0xfb870783ffe0c0f8

def z925 : W := mkw 0x423622f670cddcde 0x0423622f670cddcd 0x467667fe31cffc7b 0xe467667fe31cffc7

def z926 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb878183ffe0f0f84 0xbb878183ffe0f0f8

def z927 : W := mkw 0x9858501b660f0680 0x09858501b660f068 0xb878183fce0f0f85 0xfb878183fce0f0f8

def z928 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0xc7f667fe31fccc7f 0xec7f667fe31fccc7

def z929 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xff8f80003ffff00c 0x3ff8f80003ffff00

def z930 : W := mkw 0x00828eb4c01555ba 0x000828eb4c01555b 0xc18fffffc03ffffd 0xec18fffffc03ffff

def z931 : W := mkw 0x3fefdfad8010513a 0x43fefdfad8010513 0xffffffffc030ffff 0xfffffffffc030fff

def z932 : W := mkw 0x00808c10c01555ba 0x000808c10c01555b 0xc18f9801c03ffffd 0xac18f9801c03ffff

def z933 : W := mkw 0x3f6fd3ad80000000 0x43f6fd3ad8000000 0x3fffe1ffc000000f 0x93fffe1ffc000000

def z934 : W := mkw 0x423420d630cccc5c 0x0423420d630cccc5 0x467067ce31cccc7b 0x6467067ce31cccc7

def z935 : W := mkw 0x127c0000248a8000 0x0127c0000248a800 0xffff80003ffff00f 0xbffff80003ffff00

def z936 : W := mkw 0xc010205272cdcedc 0x0c010205272cdced 0x4000000031cccff0 0x24000000031cccff

def z937 : W := mkw 0x00122272304c4c58 0x000122272304c4c5 0x467667fe31cccc7b 0xe467667fe31cccc7

def z938 : W := mkw 0xd858705b764f4edc 0x0d858705b764f4ed 0xb878783ffe0f0ff7 0xfb878783ffe0f0ff

def z939 : W := mkw 0x376d000009200000 0x0376d00000920000 0xffff80003ffff00f 0xbffff80003ffff00

def z940 : W := mkw 0xd27f02bf648fe49c 0x2d27f02bf648fe49 0x007f803fc00ff000 0x8007f803fc00ff00

def z941 : W := mkw 0x1a6c508d00000000 0x01a6c508d0000000 0x3e7879ffc0000007 0xd3e7879ffc000000

def z942 : W := mkw 0x9858501b660f0680 0x09858501b660f068 0xb878183ffe0f0387 0xbb878183ffe0f038

def z943 : W := mkw 0x3fefdfad89a0a000 0x63fefdfad89a0a00 0xffffffffc1fff00f 0xfffffffffc1fff00

def z944 : W := mkw 0x3fefdfad8080a000 0x63fefdfad8080a00 0x3fffffffc000f00f 0xd3fffffffc000f00

def z945 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3e7fffffc0000002 0xd3e7fffffc000000

def z946 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x7fffffffc0000c7f 0xf7fffffffc0000c7

def z947 : W := mkw 0x2fa7dfad80000000 0x42fa7dfad8000000 0x07f7ffffc000000b 0xc07f7ffffc000000

def z948 : W := mkw 0x3fefdfad89b0f13a 0x63fefdfad89b0f13 0x7fffffffc1f0f07f 0xd7fffffffc1f0f07

def z949 : W := mkw 0x9858705b764f0ec0 0x09858705b764f0ec 0xb8787ffffe0f0ff7 0xfb8787ffffe0f0ff

def z950 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xfff07ffe3ff00fff 0xffff07ffe3ff00ff

def z951 : W := mkw 0x126f82ad80000000 0x4126f82ad8000000 0x007fe7ffc0000000 0xc007fe7ffc000000

def z952 : W := mkw 0x3fefdfad8010513a 0x43fefdfad8010513 0xffffffffc03ff07f 0xfffffffffc03ff07

def z953 : W := mkw 0x423622f670cdccdc 0x0423622f670cdccd 0x467e67fff1cfcc7b 0xe467e67fff1cfcc7

def z954 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0x3878783ffe000f87 0xd3878783ffe000f8

def z955 : W := mkw 0x2d0071401b600a40 0x12d0071401b600a4 0xfe007fc03fc00fff 0x7fe007fc03fc00ff

def z956 : W := mkw 0xc23622f674cfccdc 0x0c23622f674cfccd 0x467667fe31cfcc7b 0xe467667fe31cfcc7

def z957 : W := mkw 0x423420d630cc8c44 0x0423420d630cc8c4 0x467067fe31cc0c7b 0xe467067fe31cc0c7

def z958 : W := mkw 0x3fefdfad8b200200 0x53fefdfad8b20020 0x3fffffffce00000f 0xd3fffffffce00000

def z959 : W := mkw 0x2fa6dfad80000000 0x42fa6dfad8000000 0x3ff67fffc000000f 0xd3ff67fffc000000

def z960 : W := mkw 0x3dc9dd0980000000 0x43dc9dd098000000 0x3ff9ffffc000000f 0xd3ff9ffffc000000

def z961 : W := mkw 0x3fefdfad89200000 0x43fefdfad8920000 0xbfffffffce30000f 0xdbfffffffce30000

def z962 : W := mkw 0x9848700956030a80 0x09848700956030a8 0xb878783ffe030f87 0xfb878783ffe030f8

def z963 : W := mkw 0x3dcbdfad80000000 0x43dcbdfad8000000 0x39f9ffffc0000007 0xd39f9ffffc000000

def z964 : W := mkw 0xc01020527fffcffc 0x1c01020527fffcff 0xc00000003fffcff0 0x2c00000003fffcff

def z965 : W := mkw 0x423622f670cdccdc 0x0423622f670cdccd 0xc7fffffff1ffffff 0xec7fffffff1fffff

def z966 : W := mkw 0x3f6f53ad00000000 0x43f6f53ad0000000 0x3e7e7fffc000000f 0xd3e7e7fffc000000

def z967 : W := mkw 0x27a78fe489f0a160 0x727a78fe489f0a16 0x478787c001f0f078 0x0478787c001f0f07

def z968 : W := mkw 0x9848701b52050e80 0x09848701b52050e8 0xb878783ffe000f87 0xfb878783ffe000f8

def z969 : W := mkw 0x423622f632ccce5c 0x0423622f632ccce5 0xc67667fe3fcccffb 0xec67667fe3fcccff

def z970 : W := mkw 0x126e02ad00000000 0x0126e02ad0000000 0x067e67ffc000000b 0xc067e67ffc000000

def z971 : W := mkw 0x023602b4208cc418 0x0023602b4208cc41 0x467667fe31cccc7b 0xe467667fe31cccc7

def z972 : W := mkw 0x527f82b6e48ff49e 0x2527f82b6e48ff49 0x007f803fc00ff000 0x8007f803fc00ff00

def z973 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xbe007fc03fc00ff7 0x7be007fc03fc00ff

def z974 : W := mkw 0x3f6d518d00000000 0x43f6d518d0000000 0x3ffff9ffc000000f 0xd3ffff9ffc000000

def z975 : W := mkw 0xc010205276cf8ec4 0x0c010205276cf8ec 0x800000003fcf0f80 0x2800000003fcf0f8

def z976 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0xffffffffc030000f 0xfffffffffc030000

def z977 : W := mkw 0x3fefdfad80100120 0x43fefdfad8010012 0x7fffffffc030007f 0xd7fffffffc030007

def z978 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb9f9f83ffe3f3f87 0xfb9f9f83ffe3f3f8

def z979 : W := mkw 0xc23622f636cece5c 0x0c23622f636cece5 0x467667fe3fcccc7b 0xe467667fe3fcccc7

def z980 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xfe78783fffcf0f8f 0xffe78783fffcf0f8

def z981 : W := mkw 0x251000002daaa000 0x2251000002daaa00 0xff8f80003ffff00f 0xbff8f80003ffff00

def z982 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467e7ffff1cccc7f 0xe467e7ffff1cccc7

def z983 : W := mkw 0x3fefdfad80101122 0x43fefdfad8010112 0x3fffffffc030300f 0xd3fffffffc030300

def z984 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xbe787ffffe0f0f8f 0xfbe787ffffe0f0f8

def z985 : W := mkw 0x423622e630c8c85c 0x0423622e630c8c85 0x467667ce31c0cc7b 0x6467667ce31c0cc7

def z986 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x07ffffffc0000008 0xc07ffffffc000000

def z987 : W := mkw 0x00808c00c01111a2 0x000808c00c01111a 0xc18f9e01c03ffffd 0xec18f9e01c03ffff

def z988 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3e767fffc000000b 0xd3e767fffc000000

def z989 : W := mkw 0x3dc9dd09cd3331a2 0x63dc9dd09cd3331a 0xb9899801ce333384 0x1b9899801ce33338

def z990 : W := mkw 0x1a6fd3ad80000000 0x41a6fd3ad8000000 0x007fe1ffc0000000 0x8007fe1ffc000000

def z991 : W := mkw 0x9858701b760f4e98 0x09858701b760f4e9 0xf878783ffe0fcff7 0xff878783ffe0fcff

def z992 : W := mkw 0x25802c4019700960 0x025802c401970096 0xff807fc03ff00fff 0x7ff807fc03ff00ff

def z993 : W := mkw 0x423602e420c8c05c 0x0423602e420c8c05 0x467667fe31ccc07b 0xe467667fe31ccc07

def z994 : W := mkw 0x422622e410c0c85c 0x0422622e410c0c85 0x467667fe31c0cc7b 0xe467667fe31c0cc7

def z995 : W := mkw 0xb77d000b2daaa000 0x2b77d000b2daaa00 0xffff800e3ffff00f 0xbffff800e3ffff00

def z996 : W := mkw 0x4236a2f6b0ccdc5e 0x04236a2f6b0ccdc5 0x4677e7fe31ccfc7b 0xe4677e7fe31ccfc7

def z997 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xf878783ffe3fff87 0xff878783ffe3fff8

def z998 : W := mkw 0x00828e2080100120 0x000828e208010012 0xc18f9e31c03ffffd 0xec18f9e31c03ffff

def z999 : W := mkw 0x1aeedfad80000000 0x41aeedfad8000000 0x3e7e7fffc000000f 0xd3e7e7fffc000000

def z1000 : W := mkw 0x3fefdfad84022000 0x63fefdfad8402200 0x3fffffffc003300f 0xd3fffffffc003300

def z1001 : W := mkw 0x423602f620ccc45c 0x0423602f620ccc45 0x467667fe01ccc07b 0xc467667fe01ccc07

def z1002 : W := mkw 0x27a78fa489b0f13a 0x627a78fa489b0f13 0x478787c001f0f078 0x0478787c001f0f07

def z1003 : W := mkw 0x023622f6304c0c40 0x0023622f6304c0c4 0x467667fe31cc0c7b 0xe467667fe31cc0c7

def z1004 : W := mkw 0x3fed5d8d00000000 0x43fed5d8d0000000 0x3ff87fffc000000f 0xd3ff87fffc000000

def z1005 : W := mkw 0x022682ad80000000 0x4022682ad8000000 0x067667ffc000000b 0xc067667ffc000000

def z1006 : W := mkw 0x377d00092daaa000 0x2377d00092daaa00 0xffff803ffffff00f 0xbffff803ffffff00

def z1007 : W := mkw 0x080070401b700b60 0x1080070401b700b6 0xfe007fc03ff00fff 0x7fe007fc03ff00ff

def z1008 : W := mkw 0x3fefdfad89a0a000 0x63fefdfad89a0a00 0x3fffffffc1c0000f 0xd3fffffffc1c0000

def z1009 : W := mkw 0x9858701b760f5e9a 0x09858701b760f5e9 0xb878783ffe0fff87 0xfb878783ffe0fff8

def z1010 : W := mkw 0x423622e630c8c85c 0x0423622e630c8c85 0x467667ce31ccc07b 0xa467667ce31ccc07

def z1011 : W := mkw 0xd27e82bfe48fd49e 0x0d27e82bfe48fd49 0x007f803fc00ff000 0x8007f803fc00ff00

def z1012 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x7fffffffc00cc00f 0xf7fffffffc00cc00

def z1013 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0xbfffffffc00f000f 0xfbfffffffc00f000

def z1014 : W := mkw 0x3fefdfad82100320 0x53fefdfad8210032 0x3fffffffc000038f 0xd3fffffffc000038

def z1015 : W := mkw 0x67a68fe489f0d17e 0x167a68fe489f0d17 0x478787c001f0f078 0x0478787c001f0f07

def z1016 : W := mkw 0x423622e630c88844 0x0423622e630c8884 0x467667fe31c00c7b 0xe467667fe31c00c7

def z1017 : W := mkw 0x9858705b764f0ec0 0x09858705b764f0ec 0xbe7879ffffcf0f87 0xfbe7879ffffcf0f8

def z1018 : W := mkw 0x8882ff7bd2555ffa 0x18882ff7bd2555ff 0x00007fffc0000ff0 0x400007fffc0000ff

def z1019 : W := mkw 0x3fefdfad8010513a 0x43fefdfad8010513 0x3fffffffc000007f 0xd3fffffffc000007

def z1020 : W := mkw 0x422622f610444c5c 0x0422622f610444c5 0x467667fe31c00c7b 0xe467667fe31c00c7

def z1021 : W := mkw 0x18cadfad80000000 0x418cadfad8000000 0x38707fffc0000002 0x538707fffc000000

def z1022 : W := mkw 0x3fefdfad89200000 0x43fefdfad8920000 0x3fffffffffc0000f 0xd3fffffffffc0000

def z1023 : W := mkw 0x3fefdfad89300120 0x43fefdfad8930012 0xfffffffffff00fff 0xffffffffffff00ff

def z1024 : W := mkw 0x0aa6dfad80000000 0x40aa6dfad8000000 0x00767fffc0000000 0xc00767fffc000000

def z1025 : W := mkw 0x250020401b700b60 0x1250020401b700b6 0xff8067c03ff00fff 0x7ff8067c03ff00ff

def z1026 : W := mkw 0x08107012720d0e80 0x008107012720d0e8 0xb878783ffe0f0f87 0xfb878783ffe0f0f8

def z1027 : W := mkw 0x9858501b660f0680 0x09858501b660f068 0xb878783fce0f0387 0xdb878783fce0f038

def z1028 : W := mkw 0x801020527f7f5ffa 0x1801020527f7f5ff 0xc00000003ffffff0 0x2c00000003ffffff

def z1029 : W := mkw 0x401020527bfddffe 0x1401020527bfddff 0xc00000003ffffff0 0x2c00000003ffffff

def z1030 : W := mkw 0x423622e630c8c85c 0x0423622e630c8c85 0x067067ce31c00072 0x0067067ce31c0007

def z1031 : W := mkw 0x9858701b760f0e80 0x09858701b760f0e8 0xb870783ffe000f87 0x7b870783ffe000f8

def z1032 : W := mkw 0x2d80fd409b701b62 0x12d80fd409b701b6 0xff81ffc03ff03fff 0x7ff81ffc03ff03ff

def z1033 : W := mkw 0x4236a2f6b0cccc5c 0x04236a2f6b0cccc5 0x467fe7fff1cccc7b 0xe467fe7fff1cccc7

def z1034 : W := mkw 0x777d00862daaa004 0x2777d00862daaa00 0xffff800e3ffff00f 0xbffff800e3ffff00

def z1035 : W := mkw 0x401222f6304c4c5c 0x0401222f6304c4c5 0x467067fe31cc0c7b 0xe467067fe31cc0c7

def z1036 : W := mkw 0x2d0071401b700b60 0x12d0071401b700b6 0xfe0067c03ff00ffb 0x7fe0067c03ff00ff

def z1037 : W := mkw 0x00828e30c01555ba 0x000828e30c01555b 0xc78ffff1c03fffff 0xec78ffff1c03ffff

def z1038 : W := mkw 0x377d00842daaa000 0x2377d00842daaa00 0xffffe1ce3ffff00f 0xbffffe1ce3ffff00

def z1039 : W := mkw 0x3dc85d090b300320 0x13dc85d090b30032 0xb9881801ce300384 0x1b9881801ce30038

def z1040 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3ff07fffc000000f 0x53ff07fffc000000

def z1041 : W := mkw 0x0010204230480840 0x0001020423048084 0x467067ce31c00c7b 0x6467067ce31c00c7

def z1042 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0x3f807fc03fc00fff 0x53f807fc03fc00ff

def z1043 : W := mkw 0x4010205270ddddfe 0x04010205270ddddf 0x4000000031cccff0 0x24000000031cccff

def z1044 : W := mkw 0x4882fff6d2555ffe 0x14882fff6d2555ff 0x00007fffc0000ff0 0x400007fffc0000ff

def z1045 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x47f7e7fe31fcfc7b 0xe47f7e7fe31fcfc7

def z1046 : W := mkw 0x3fed5d0900000000 0x03fed5d090000000 0x3fffffffc000000f 0xd3fffffffc000000

def z1047 : W := mkw 0x7fefdfad8080c01c 0x47fefdfad8080c01 0x3fffffffc000c00f 0xd3fffffffc000c00

def z1048 : W := mkw 0x3fefdfad80000000 0x43fefdfad8000000 0x3ffff9ffc0000006 0x93ffff9ffc000000

def z1049 : W := mkw 0x377d01842daaa000 0x6377d01842daaa00 0xffff81c03ffff00f 0xbffff81c03ffff00

def z1050 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xffff9831fffff00f 0xfffff9831fffff00

def z1051 : W := mkw 0x355900002daaa000 0x2355900002daaa00 0xf98f80003ffff00d 0xbf98f80003ffff00

def z1052 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xffffe7c03ffff00f 0xfffffe7c03ffff00

def z1053 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0xfe7667fe3fcccc7f 0xffe7667fe3fcccc7

def z1054 : W := mkw 0x3fefdfad84020000 0x43fefdfad8402000 0xbfffffffce03000f 0xdbfffffffce03000

def z1055 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff807fc03fffffff 0x7ff807fc03ffffff

def z1056 : W := mkw 0x02a68ea480000000 0x002a68ea48000000 0x06767fffc000000b 0xc06767fffc000000

def z1057 : W := mkw 0x3fefdfad8b300320 0x53fefdfad8b30032 0xffffffffce300fff 0xfffffffffce300ff

def z1058 : W := mkw 0x2d80fd499b700b60 0x52d80fd499b700b6 0xff807fc1fff00fff 0x7ff807fc1fff00ff

def z1059 : W := mkw 0x0234205230cc8c40 0x00234205230cc8c4 0x467667fe31cccc7b 0xe467667fe31cccc7

def z1060 : W := mkw 0x3fefdfad89300120 0x53fefdfad8930012 0x3fffffffc030000f 0xd3fffffffc030000

def z1061 : W := mkw 0x1aefdfad80000000 0x41aefdfad8000000 0x01ffffffc000000d 0xc01ffffffc000000

def z1062 : W := mkw 0x2d817d401b702b60 0x32d817d401b702b6 0xff81ffc03ff03fff 0x7ff81ffc03ff03ff

def z1063 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0x7e007fc03fc00ffb 0x77e007fc03fc00ff

def z1064 : W := mkw 0x3dcadfad80000000 0x43dcadfad8000000 0x3ff87fffc000000f 0xd3ff87fffc000000

def z1065 : W := mkw 0xc23622f672cdcedc 0x0c23622f672cdced 0x467667fe31cccffb 0xe467667fe31cccff

def z1066 : W := mkw 0x2d80fd409b700b60 0x12d80fd409b700b6 0xff89ffc1fff00fff 0x7ff89ffc1fff00ff

def z1067 : W := mkw 0x37ef8fad80000000 0x437ef8fad8000000 0x07ffe7ffc000000b 0xc07ffe7ffc000000

def z1068 : W := mkw 0x423622f634cecc5c 0x0423622f634cecc5 0xc67667fe3fcfcc7b 0xec67667fe3fcfcc7

def z1069 : W := mkw 0x2d807d401b700b60 0x12d807d401b700b6 0xff887ff1fff00fff 0xfff887ff1fff00ff

def z1070 : W := mkw 0x377d00002daaa000 0x2377d00002daaa00 0xffff98003fffff8f 0xfffff98003fffff8

def z1071 : W := mkw 0x4237a2f6b0cccc5c 0x44237a2f6b0cccc5 0x4677e7fe31cccc7b 0xe4677e7fe31cccc7

def z1072 : W := mkw 0x08807d4012500b60 0x108807d4012500b6 0xfe007fc03fc00fff 0x7fe007fc03fc00ff

def z1073 : W := mkw 0x423622f630cccc5c 0x0423622f630cccc5 0x467fe7fe31cffc7b 0xe467fe7fe31cffc7

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z0,z8,z1,z2,z9,z4,z5]),(0,[z0,z1,z10,z2,z3,z11,z5])],[(0,[z0,z1,z2,z3,z12,z13,z5]),(0,[z0,z1,z2,z3,z14,z4,z5]),(0,[z0,z1,z2,z3,z15,z4,z5]),(0,[z16,z0,z1,z2,z3,z12,z5]),(0,[z16,z0,z1,z2,z3,z4,z17])],[(0,[z0,z18,z19,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z20]),(0,[z0,z1,z2,z3,z4,z21,z5]),(0,[z0,z18,z1,z2,z22,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z23])],[(0,[z0,z1,z2,z24,z3,z4,z5]),(0,[z0,z1,z2,z25,z4,z5,z26]),(0,[z0,z1,z2,z3,z4,z27,z5])],[(0,[z28,z0,z1,z2,z29,z4,z5]),(0,[z0,z1,z30,z2,z3,z4,z5]),(0,[z31,z0,z1,z2,z3,z32,z5]),(0,[z0,z33,z1,z2,z9,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z34]),(0,[z0,z1,z2,z35,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z36])],[(0,[z0,z37,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z38,z3,z4,z5]),(0,[z0,z39,z40,z1,z3,z4,z5]),(0,[z41,z0,z1,z2,z3,z4,z5]),(0,[z0,z33,z1,z2,z42,z4,z5]),(1,[z0,z18,z1,z2,z4,z43])],[(0,[z0,z44,z1,z2,z3,z4,z5]),(0,[z0,z1,z45,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z46,z5]),(0,[z0,z1,z2,z3,z4,z47,z5])],[(0,[z48,z0,z1,z2,z3,z4,z5]),(0,[z0,z49,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z50,z3,z4,z5])]],
   [[(0,[z51,z0,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z3,z4,z53,z5]),(0,[z0,z1,z54,z2,z3,z4,z5]),(0,[z0,z55,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z56])],[(0,[z0,z1,z2,z4,z5,z57,z58])],[(0,[z0,z59,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z60])],[(0,[z0,z61,z1,z2,z3,z4,z5]),(0,[z0,z62,z1,z10,z2,z4,z5]),(0,[z0,z63,z1,z2,z3,z4,z5])],[(0,[z64,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z65,z5]),(0,[z0,z1,z2,z3,z4,z66,z5]),(1,[z0,z61,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z68,z4,z5])],[(0,[z69,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z70,z4,z5])],[(0,[z0,z1,z2,z3,z4,z71,z5]),(0,[z0,z72,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z73,z4,z5]),(0,[z0,z1,z74,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z75,z5])],[(0,[z76,z77,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z78,z4,z5])]],
   [[(0,[z0,z79,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z80,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z81])],[(0,[z0,z1,z2,z3,z4,z82,z5]),(0,[z0,z1,z83,z2,z3,z4,z5]),(0,[z0,z1,z2,z84,z3,z4,z5]),(0,[z0,z85,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z86,z4,z87,z5]),(0,[z0,z1,z2,z3,z88,z4,z5]),(1,[z0,z1,z2,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z90]),(1,[z16,z0,z1,z2,z3,z58])],[(0,[z91,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z92,z3,z4,z5]),(0,[z0,z93,z1,z2,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z94,z5]),(0,[z0,z1,z2,z3,z4,z5,z95]),(0,[z96,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z97,z2,z3,z4,z5]),(0,[z0,z98,z1,z2,z4,z5,z58])],[(0,[z0,z1,z99,z2,z3,z4,z5]),(0,[z0,z100,z1,z2,z3,z4,z5]),(0,[z0,z101,z1,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z15,z5]),(0,[z0,z1,z2,z103,z3,z4,z5])],[(0,[z0,z1,z2,z3,z104,z4,z5]),(0,[z105,z0,z1,z2,z3,z4,z5]),(0,[z0,z106,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z107,z5])],[(0,[z108,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z109,z2,z3,z4,z5]),(0,[z0,z1,z110,z2,z3,z4,z5]),(0,[z0,z1,z10,z3,z11,z4,z5])],[(0,[z0,z1,z2,z3,z4,z111,z5]),(0,[z0,z112,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z113,z3,z4,z5]),(0,[z0,z1,z114,z2,z3,z4,z5]),(0,[z0,z1,z2,z115,z3,z4,z5]),(1,[z0,z1,z2,z3,z5,z116])]],
   [[(0,[z117,z0,z1,z2,z3,z4,z5]),(0,[z77,z0,z33,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z118,z4,z5]),(0,[z0,z1,z2,z3,z119,z4,z5]),(0,[z0,z120,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z121,z5]),(0,[z0,z1,z2,z3,z4,z87,z5]),(0,[z0,z1,z2,z3,z4,z122,z5]),(0,[z0,z1,z2,z3,z4,z5,z123])],[(0,[z0,z1,z2,z3,z4,z5,z124]),(0,[z0,z1,z2,z3,z4,z125,z5]),(0,[z126,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z127,z4,z5]),(0,[z0,z128,z1,z2,z3,z4,z5])],[(0,[z129,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z130,z3,z4,z5]),(0,[z0,z18,z1,z2,z86,z4,z5]),(1,[z31,z1,z2,z3,z4,z131]),(0,[z0,z132,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z133]),(0,[z134,z0,z1,z2,z3,z4,z5]),(1,[z135,z0,z8,z1,z4,z5]),(0,[z0,z1,z2,z3,z4,z136,z5]),(0,[z0,z137,z1,z2,z3,z4,z5])],[(0,[z138,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z139]),(1,[z0,z1,z2,z4,z140,z5]),(0,[z0,z141,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z142,z5]),(0,[z0,z143,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z144,z4,z5]),(0,[z0,z145,z1,z2,z3,z4,z5])],[(0,[z0,z1,z146,z2,z3,z4,z5]),(0,[z147,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z148,z5]),(0,[z0,z1,z2,z149,z3,z4,z5])],[(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z151,z5]),(0,[z0,z1,z2,z3,z13,z5,z58]),(0,[z0,z1,z2,z3,z152,z4,z5]),(1,[z134,z0,z1,z2,z3,z5]),(0,[z0,z153,z1,z2,z3,z4,z5])],[(0,[z0,z154,z1,z2,z3,z4,z5]),(0,[z0,z155,z1,z2,z3,z4,z5]),(0,[z0,z156,z1,z3,z4,z157,z5])]],
   [[(0,[z158,z0,z1,z2,z3,z4,z5]),(0,[z0,z159,z1,z2,z3,z4,z5])],[(0,[z160,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z161,z5]),(0,[z0,z1,z2,z3,z22,z4,z162])],[(0,[z0,z39,z40,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z163,z5])],[(0,[z64,z0,z164,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z165]),(0,[z0,z1,z2,z3,z4,z166,z5]),(0,[z0,z1,z2,z167,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z168])],[(0,[z0,z1,z2,z3,z169,z4,z5]),(0,[z0,z1,z170,z2,z3,z4,z5]),(0,[z0,z171,z1,z2,z3,z4,z5]),(0,[z0,z19,z2,z3,z9,z4,z5]),(0,[z0,z172,z1,z2,z3,z4,z5])],[(0,[z0,z1,z173,z2,z3,z4,z5]),(0,[z0,z1,z174,z2,z3,z4,z5]),(0,[z0,z175,z1,z2,z3,z4,z5]),(0,[z0,z176,z1,z2,z3,z4,z5])],[(1,[z0,z177,z1,z3,z4,z5]),(0,[z0,z178,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z179,z5]),(0,[z134,z0,z1,z2,z3,z5,z26])]],
   [[(0,[z180,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z181,z4,z5]),(0,[z182,z0,z1,z2,z3,z4,z5]),(0,[z102,z0,z2,z3,z4,z67,z5]),(0,[z0,z1,z2,z3,z4,z183,z5]),(0,[z0,z1,z3,z11,z4,z157,z5])],[(0,[z0,z1,z2,z3,z4,z184,z5]),(0,[z0,z1,z2,z3,z4,z5,z185]),(0,[z0,z1,z2,z3,z4,z5,z186])],[(0,[z187,z0,z39,z1,z3,z4,z5]),(0,[z0,z1,z188,z2,z3,z4,z5]),(0,[z0,z189,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z190,z5]),(0,[z191,z0,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z2,z3,z4,z192,z5])],[(0,[z0,z193,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z194,z5]),(0,[z0,z1,z2,z195,z9,z4,z5]),(0,[z0,z1,z2,z3,z196,z4,z5]),(0,[z0,z1,z2,z3,z4,z197,z5])],[(0,[z0,z1,z2,z195,z42,z4,z5]),(0,[z0,z1,z2,z3,z198,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z199]),(0,[z0,z19,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z42,z4,z87,z5])]],
   [[(0,[z0,z1,z200,z2,z3,z4,z5]),(0,[z0,z201,z1,z2,z3,z4,z5]),(0,[z202,z0,z1,z2,z3,z4,z5]),(0,[z203,z0,z1,z2,z204,z4,z5]),(0,[z205,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z206,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z12,z17])],[(0,[z0,z207,z1,z2,z3,z4,z5]),(0,[z0,z208,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z209,z3,z9,z5]),(0,[z0,z210,z1,z2,z3,z4,z5]),(0,[z211,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z212,z4,z5]),(0,[z0,z213,z1,z2,z3,z4,z5])],[(0,[z0,z214,z1,z2,z3,z4,z5]),(0,[z215,z0,z1,z2,z3,z4,z5]),(0,[z0,z216,z1,z2,z3,z4,z5]),(0,[z0,z217,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z218,z3,z12,z5])],[(0,[z0,z1,z2,z3,z219,z4,z5]),(0,[z0,z1,z220,z2,z3,z4,z5]),(0,[z221,z0,z1,z2,z3,z4,z5])],[],[(0,[z187,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z32,z5]),(0,[z0,z1,z2,z3,z4,z222,z5]),(1,[z0,z120,z2,z3,z4,z26]),(0,[z0,z1,z2,z3,z4,z5,z223]),(0,[z0,z224,z1,z2,z3,z4,z5]),(0,[z225,z0,z1,z2,z3,z4,z5])],[(0,[z226,z0,z1,z2,z3,z4,z5]),(0,[z31,z0,z1,z2,z3,z227,z5]),(0,[z0,z8,z55,z1,z2,z4,z5]),(0,[z0,z1,z228,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z17,z5,z58])]],
   [[(0,[z76,z0,z1,z2,z195,z4,z5]),(0,[z0,z229,z1,z2,z3,z4,z5]),(0,[z0,z61,z2,z3,z4,z67,z5]),(0,[z0,z1,z2,z3,z12,z4,z58])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z187,z0,z1,z220,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z4,z222]),(0,[z0,z1,z2,z3,z4,z5,z26])],[(0,[z230,z0,z1,z2,z3,z4,z5]),(0,[z187,z0,z231,z2,z3,z4,z5]),(0,[z0,z232,z1,z2,z3,z4,z5]),(0,[z0,z93,z1,z3,z233,z4,z5]),(0,[z0,z2,z3,z15,z4,z67,z5])],[(0,[z0,z1,z2,z3,z4,z234,z5]),(0,[z235,z0,z1,z2,z9,z4,z5]),(0,[z0,z33,z55,z1,z2,z4,z5])],[(0,[z0,z236,z1,z2,z3,z4,z5]),(0,[z0,z237,z1,z2,z3,z4,z5]),(0,[z238,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z239,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z240]),(0,[z0,z1,z2,z3,z4,z241,z5])],[(0,[z0,z177,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z242,z4,z5]),(0,[z243,z0,z1,z2,z3,z4,z5]),(0,[z244,z1,z2,z3,z4,z52,z5]),(0,[z0,z1,z2,z3,z4,z245,z5]),(0,[z31,z0,z1,z2,z3,z4,z5]),(0,[z0,z246,z1,z2,z3,z4,z5])],[(0,[z244,z51,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z247,z5]),(0,[z0,z120,z2,z3,z15,z4,z5])]],
   [[(0,[z248,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z12,z4,z5])],[],[(0,[z249,z0,z1,z2,z3,z4,z5]),(1,[z0,z101,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z67,z58]),(0,[z0,z250,z1,z2,z3,z4,z5]),(0,[z0,z251,z1,z2,z3,z4,z90]),(0,[z0,z1,z2,z252,z3,z4,z5]),(0,[z253,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z254,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z255])],[(0,[z0,z1,z2,z256,z3,z4,z5]),(0,[z0,z257,z1,z2,z3,z4,z5])],[(0,[z203,z0,z1,z2,z3,z4,z5]),(0,[z258,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z259,z5]),(0,[z0,z1,z2,z218,z22,z4,z5])],[(1,[z28,z173,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z260,z5]),(0,[z0,z1,z2,z3,z4,z261,z90]),(0,[z0,z1,z262,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z263,z5])],[(0,[z0,z264,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z265,z5]),(0,[z0,z1,z266,z2,z3,z4,z5])]],
   [[(0,[z64,z0,z1,z2,z3,z267,z5]),(0,[z0,z268,z1,z2,z3,z4,z5]),(0,[z0,z269,z1,z2,z3,z4,z5]),(1,[z0,z270,z1,z2,z3,z4]),(0,[z271,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z272,z5]),(0,[z0,z8,z1,z2,z4,z87,z5]),(0,[z0,z1,z2,z3,z4,z273,z5]),(0,[z0,z1,z274,z2,z3,z4,z5])],[(0,[z0,z120,z1,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z4,z5,z275]),(1,[z0,z1,z74,z42,z4,z5]),(0,[z0,z1,z2,z3,z4,z276,z5])],[(0,[z0,z1,z2,z3,z4,z5,z277]),(0,[z0,z1,z2,z3,z278,z4,z5]),(0,[z279,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z67,z5]),(0,[z0,z1,z2,z3,z4,z5,z280])],[(0,[z281,z0,z1,z2,z3,z4,z5])],[(0,[z282,z0,z1,z2,z3,z4,z5]),(0,[z187,z0,z1,z2,z283,z4,z5]),(0,[z0,z1,z2,z3,z4,z52,z5]),(0,[z284,z0,z1,z2,z3,z4,z5]),(0,[z0,z101,z1,z2,z3,z9,z5]),(0,[z0,z1,z2,z3,z4,z285,z5]),(0,[z0,z33,z1,z2,z4,z87,z5])],[(0,[z0,z286,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z287]),(0,[z0,z1,z2,z3,z4,z288,z5]),(0,[z0,z1,z289,z2,z3,z4,z5])],[(0,[z0,z290,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z291,z4,z5])]],
   [[(1,[z0,z1,z2,z292,z4,z5]),(0,[z0,z1,z2,z3,z4,z293,z5])],[(0,[z0,z1,z2,z294,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z162])],[(0,[z295,z0,z1,z2,z3,z4,z5]),(0,[z282,z1,z220,z2,z3,z4,z5]),(0,[z0,z210,z1,z2,z3,z52,z5]),(0,[z0,z210,z1,z2,z218,z3,z5]),(0,[z0,z296,z1,z2,z3,z4,z5]),(0,[z0,z297,z1,z2,z3,z4,z5]),(0,[z298,z0,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z299,z2,z3,z4,z5]),(0,[z0,z1,z300,z2,z3,z4,z5]),(0,[z31,z0,z1,z2,z3,z4,z131]),(0,[z0,z8,z1,z2,z3,z4,z5])],[(0,[z301,z0,z1,z2,z3,z4,z5]),(0,[z0,z302,z1,z2,z3,z4,z5]),(1,[z0,z98,z1,z2,z4,z5])],[(0,[z0,z231,z1,z2,z3,z4,z5]),(0,[z0,z303,z1,z2,z3,z4,z5]),(0,[z0,z1,z10,z2,z3,z4,z5])],[(0,[z1,z2,z3,z13,z4,z52,z5]),(0,[z0,z1,z304,z2,z3,z4,z5]),(0,[z0,z33,z8,z1,z2,z4,z5]),(0,[z0,z305,z251,z1,z3,z4,z5])]],
   [[(0,[z64,z0,z173,z2,z3,z4,z5]),(0,[z187,z0,z1,z2,z3,z4,z111]),(0,[z0,z55,z19,z1,z2,z4,z5]),(0,[z0,z55,z1,z2,z22,z4,z5]),(0,[z0,z1,z306,z2,z3,z4,z5]),(0,[z0,z305,z1,z2,z3,z4,z90]),(0,[z0,z33,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z218,z3,z288,z5]),(0,[z0,z1,z2,z3,z4,z5,z307])],[(0,[z0,z1,z2,z3,z4,z308,z5]),(0,[z0,z210,z2,z3,z15,z4,z5]),(0,[z0,z309,z1,z2,z3,z4,z5]),(0,[z0,z310,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z311,z3,z4,z5])],[(0,[z0,z1,z2,z312,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z313,z5]),(0,[z203,z0,z1,z2,z3,z4,z131]),(0,[z16,z0,z210,z1,z2,z3,z5]),(0,[z314,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z315])],[(0,[z0,z316,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z317]),(0,[z0,z318,z1,z2,z3,z4,z5]),(0,[z0,z8,z1,z74,z2,z4,z5]),(0,[z0,z319,z1,z2,z3,z4,z5])],[(0,[z0,z320,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z11,z52,z5]),(0,[z0,z1,z2,z3,z321,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z322]),(0,[z0,z1,z2,z3,z4,z323,z5]),(0,[z324,z0,z1,z2,z3,z4,z5])],[(1,[z64,z164,z2,z3,z4,z5]),(0,[z0,z1,z2,z325,z3,z4,z5])],[(0,[z326,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z88,z4,z5]),(0,[z0,z1,z2,z3,z327,z4,z5]),(0,[z0,z1,z2,z3,z328,z4,z5])],[(0,[z203,z0,z1,z2,z329,z4,z5]),(0,[z0,z18,z1,z2,z42,z4,z5]),(0,[z0,z330,z1,z2,z3,z4,z5]),(0,[z0,z251,z1,z2,z331,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z332,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z2,z3,z333,z4,z5]),(0,[z334,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z335,z5]),(0,[z0,z1,z336,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z162]),(0,[z0,z337,z1,z2,z3,z4,z5])],[(0,[z187,z0,z1,z2,z3,z4,z338]),(0,[z0,z1,z2,z3,z4,z339,z5]),(0,[z102,z16,z0,z1,z2,z3,z5]),(0,[z340,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z341,z5])],[(0,[z342,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z218,z3,z5,z58])],[(0,[z77,z0,z1,z2,z86,z4,z5]),(0,[z0,z18,z1,z2,z195,z4,z5]),(0,[z343,z0,z1,z2,z3,z4,z5]),(0,[z0,z8,z18,z1,z2,z4,z5]),(0,[z0,z62,z1,z2,z3,z4,z5]),(0,[z0,z344,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z22,z4,z288,z5]),(0,[z0,z345,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z346,z5])],[(0,[z0,z1,z2,z3,z4,z347,z5]),(1,[z282,z1,z220,z3,z4,z5]),(0,[z0,z1,z348,z2,z3,z4,z5]),(1,[z0,z290,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z349,z4,z5]),(0,[z0,z251,z1,z2,z3,z4,z341])],[(0,[z0,z1,z2,z3,z4,z5,z350]),(0,[z0,z19,z1,z2,z4,z87,z5]),(0,[z0,z1,z2,z351,z3,z4,z5]),(1,[z0,z1,z2,z25,z4,z5])],[(0,[z352,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z353,z5]),(0,[z0,z354,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z52,z5,z58]),(0,[z0,z355,z1,z2,z3,z4,z5]),(0,[z0,z356,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z357,z3,z4,z5]),(0,[z358,z0,z1,z2,z3,z4,z5]),(0,[z0,z33,z18,z1,z2,z4,z5]),(0,[z0,z1,z2,z218,z3,z22,z5]),(0,[z0,z1,z2,z359,z3,z4,z5])],[(0,[z0,z360,z1,z2,z3,z4,z5]),(0,[z0,z361,z1,z2,z3,z4,z5]),(0,[z51,z1,z2,z3,z13,z4,z5]),(1,[z0,z1,z2,z3,z227,z5]),(0,[z0,z270,z1,z2,z3,z9,z4]),(0,[z102,z0,z33,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z362,z4,z5])],[(1,[z76,z1,z2,z86,z4,z5]),(0,[z0,z363,z1,z2,z3,z4,z5]),(0,[z0,z364,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z13,z157,z5]),(0,[z0,z1,z2,z3,z4,z5,z365]),(0,[z0,z1,z2,z3,z4,z5,z57])],[(1,[z0,z19,z2,z9,z4,z5]),(0,[z0,z366,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z367,z5]),(0,[z0,z1,z2,z3,z368,z4,z5]),(0,[z369,z0,z1,z2,z3,z4,z5])],[(0,[z0,z370,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z371,z4,z5]),(0,[z0,z1,z2,z3,z4,z372,z5]),(0,[z0,z373,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z374,z3,z4,z5])],[(0,[z375,z0,z1,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z17,z5]),(0,[z0,z376,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z377,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z378])],[(0,[z379,z0,z1,z2,z3,z4,z5]),(0,[z0,z380,z1,z2,z3,z4,z5]),(0,[z0,z39,z1,z2,z3,z4,z5]),(0,[z381,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z382,z5]),(0,[z383,z0,z1,z2,z3,z4,z5]),(0,[z0,z156,z1,z2,z3,z157,z5]),(1,[z0,z1,z2,z218,z22,z5])]],
   [[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z55,z1,z2,z86,z4,z5]),(0,[z384,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z385,z5])],[(0,[z0,z1,z2,z3,z4,z386,z5]),(0,[z1,z220,z2,z387,z3,z4,z5]),(0,[z0,z1,z2,z3,z52,z157,z5]),(0,[z0,z1,z2,z388,z3,z4,z5]),(0,[z235,z0,z55,z1,z2,z4,z5]),(0,[z235,z0,z55,z2,z3,z4,z5]),(1,[z0,z389,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z390,z5]),(0,[z0,z1,z2,z3,z4,z5,z391]),(1,[z0,z305,z1,z3,z4,z90])],[(0,[z0,z392,z1,z2,z3,z4,z5]),(0,[z0,z1,z393,z2,z3,z4,z5]),(0,[z0,z18,z1,z2,z4,z5,z43])],[(1,[z0,z231,z2,z3,z4,z5]),(0,[z0,z394,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z395,z5]),(0,[z0,z1,z2,z3,z22,z4,z5])],[(0,[z0,z1,z396,z2,z3,z4,z5]),(0,[z0,z397,z1,z2,z3,z4,z5])],[(0,[z28,z0,z1,z2,z3,z4,z5]),(0,[z0,z398,z1,z2,z3,z4,z5]),(0,[z76,z1,z2,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z131]),(0,[z0,z1,z2,z399,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z400,z5])],[(0,[z0,z1,z2,z401,z3,z4,z5]),(0,[z0,z120,z2,z3,z4,z5,z26]),(0,[z0,z1,z2,z3,z4,z402,z5]),(0,[z16,z0,z1,z2,z3,z4,z58])]],
   [[(0,[z0,z1,z2,z3,z403,z4,z5]),(0,[z0,z1,z2,z3,z4,z341,z131]),(0,[z0,z404,z1,z2,z3,z4,z5]),(1,[z235,z0,z55,z2,z4,z5]),(0,[z102,z0,z210,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z405,z5]),(0,[z0,z1,z2,z3,z4,z17,z26]),(0,[z0,z1,z2,z3,z4,z406,z5])],[(0,[z0,z173,z2,z3,z233,z4,z5]),(0,[z0,z8,z1,z2,z86,z4,z5]),(0,[z102,z0,z1,z2,z3,z13,z5]),(0,[z0,z407,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z408,z5]),(0,[z0,z1,z2,z3,z409,z4,z5]),(0,[z0,z33,z1,z2,z3,z288,z5])],[(0,[z1,z2,z3,z4,z261,z5,z131]),(1,[z0,z145,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z410,z5]),(0,[z0,z305,z1,z2,z3,z4,z341])],[(0,[z0,z1,z2,z3,z411,z4,z5]),(0,[z0,z412,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z413,z4,z5])],[(0,[z0,z1,z2,z3,z414,z4,z5]),(0,[z0,z415,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z416,z3,z4,z5]),(0,[z0,z417,z1,z2,z3,z4,z5]),(0,[z0,z418,z1,z2,z3,z4,z58])],[(0,[z0,z419,z1,z2,z3,z4,z5]),(0,[z0,z420,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z421,z4,z5]),(0,[z0,z1,z2,z3,z422,z4,z5]),(0,[z0,z156,z1,z10,z3,z4,z5]),(0,[z0,z305,z1,z3,z4,z5,z90]),(0,[z16,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z12,z4,z17])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z423]),(0,[z0,z1,z2,z3,z424,z4,z5]),(1,[z0,z178,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z425])],[(0,[z0,z1,z2,z3,z4,z426,z5]),(0,[z0,z33,z1,z2,z4,z288,z5])],[(0,[z427,z0,z1,z2,z3,z4,z5]),(0,[z187,z0,z174,z2,z3,z4,z5]),(0,[z0,z40,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z331,z4,z5]),(0,[z0,z1,z428,z2,z3,z4,z5])],[(0,[z282,z0,z39,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z89,z4,z5]),(0,[z0,z429,z1,z2,z3,z4,z5]),(0,[z235,z0,z1,z2,z4,z87,z5]),(0,[z0,z210,z1,z2,z212,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z430]),(0,[z0,z33,z1,z2,z3,z5,z58])],[(0,[z0,z1,z2,z3,z4,z431,z5]),(0,[z0,z418,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z432,z3,z4,z5]),(1,[z0,z1,z2,z283,z4,z5]),(1,[z187,z1,z387,z3,z4,z5]),(0,[z76,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z433,z5]),(0,[z0,z1,z2,z3,z4,z5,z434]),(0,[z0,z1,z2,z3,z4,z435,z5])],[(0,[z0,z436,z1,z2,z3,z4,z5]),(0,[z102,z0,z2,z3,z4,z405,z5]),(0,[z0,z1,z437,z2,z3,z4,z5])]],
   [[(0,[z438,z0,z1,z2,z3,z4,z5])],[(0,[z439,z0,z1,z2,z3,z4,z5]),(0,[z440,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z67,z17]),(0,[z0,z1,z2,z3,z441,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z442]),(0,[z0,z1,z2,z3,z4,z443,z5])],[(0,[z0,z1,z2,z3,z4,z5,z444]),(1,[z0,z39,z40,z3,z4,z5]),(0,[z135,z0,z8,z1,z3,z4,z5]),(0,[z0,z1,z2,z445,z3,z4,z5]),(0,[z0,z1,z446,z2,z3,z4,z5])],[(0,[z187,z0,z1,z2,z3,z181,z5]),(1,[z0,z1,z2,z329,z4,z5]),(0,[z447,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z42,z22,z4,z5]),(0,[z0,z448,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z449,z4,z5]),(0,[z0,z1,z2,z3,z4,z450,z5]),(0,[z0,z1,z2,z3,z4,z5,z338]),(1,[z0,z210,z2,z3,z15,z5]),(1,[z0,z156,z1,z3,z157,z5])],[(0,[z64,z164,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z451,z5]),(0,[z452,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z204,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z453,z5])],[(0,[z0,z1,z2,z3,z454,z4,z5]),(0,[z0,z210,z1,z2,z3,z15,z5])],[(0,[z77,z0,z1,z2,z22,z4,z5]),(0,[z235,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z455]),(0,[z456,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z457,z2,z3,z4,z5])]],
   [[(0,[z0,z458,z1,z2,z3,z4,z5]),(0,[z0,z459,z1,z2,z3,z4,z5]),(0,[z0,z251,z1,z2,z3,z4,z5])],[(0,[z64,z0,z1,z2,z3,z460,z5]),(0,[z0,z1,z2,z3,z227,z4,z5]),(1,[z203,z1,z2,z3,z4,z261])],[(1,[z0,z1,z2,z3,z4,z111]),(0,[z282,z0,z1,z220,z3,z4,z5]),(0,[z461,z0,z1,z2,z3,z4,z5]),(0,[z462,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z195,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z463]),(1,[z51,z1,z2,z3,z13,z5]),(0,[z0,z1,z2,z3,z4,z261,z5]),(0,[z0,z464,z251,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z465])],[(0,[z0,z164,z2,z3,z233,z4,z5]),(0,[z0,z1,z2,z3,z466,z4,z5]),(0,[z0,z467,z1,z2,z3,z4,z5]),(0,[z0,z270,z1,z2,z3,z4,z5]),(0,[z468,z0,z1,z2,z3,z4,z5])],[(0,[z64,z28,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z469]),(0,[z0,z1,z2,z470,z3,z4,z5]),(0,[z187,z0,z1,z2,z3,z450,z5])],[(0,[z471,z0,z1,z2,z3,z4,z5]),(0,[z0,z472,z1,z2,z3,z4,z5]),(0,[z0,z33,z1,z2,z3,z12,z5]),(0,[z0,z1,z2,z3,z87,z5,z116])]],
   [[(0,[z0,z1,z473,z2,z3,z4,z5]),(0,[z0,z474,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z475]),(0,[z0,z476,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z477,z5]),(0,[z0,z1,z2,z3,z478,z4,z5]),(0,[z479,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z480,z5])],[(0,[z0,z177,z1,z173,z3,z4,z5]),(0,[z0,z93,z2,z3,z233,z4,z5]),(0,[z0,z481,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z15,z4,z405,z5]),(0,[z135,z0,z1,z2,z42,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z482])],[(0,[z0,z1,z2,z483,z3,z4,z5]),(0,[z0,z1,z2,z3,z484,z4,z5]),(0,[z0,z1,z2,z3,z4,z485,z5]),(0,[z0,z486,z1,z2,z3,z4,z5]),(0,[z0,z145,z2,z3,z4,z5,z58])],[(0,[z203,z0,z1,z2,z3,z4,z261]),(0,[z487,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z488]),(0,[z0,z489,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z58])],[(1,[z0,z1,z2,z3,z4,z338]),(0,[z0,z490,z1,z2,z3,z4,z5]),(0,[z0,z98,z1,z2,z3,z4,z5])],[(0,[z0,z491,z1,z2,z3,z4,z5]),(0,[z0,z120,z18,z1,z2,z3,z4]),(0,[z492,z0,z1,z2,z3,z4,z5])],[(0,[z244,z0,z1,z2,z3,z13,z5]),(0,[z0,z1,z2,z3,z4,z493,z5]),(0,[z0,z1,z10,z2,z368,z4,z5])],[(0,[z0,z1,z2,z3,z494,z4,z5]),(0,[z0,z1,z2,z495,z3,z4,z5]),(1,[z0,z1,z2,z204,z4,z5]),(0,[z235,z0,z18,z1,z2,z4,z5]),(1,[z0,z1,z2,z3,z4,z455]),(0,[z0,z1,z2,z496,z3,z4,z5]),(0,[z0,z497,z1,z2,z3,z4,z5]),(0,[z0,z418,z1,z2,z3,z4,z87])]],
   [[(0,[z0,z498,z1,z2,z3,z4,z5]),(0,[z0,z1,z499,z2,z3,z4,z5]),(0,[z0,z156,z1,z2,z3,z11,z5]),(0,[z0,z500,z1,z2,z3,z4,z5]),(0,[z0,z33,z1,z2,z218,z4,z5])],[(0,[z187,z0,z93,z1,z3,z4,z5]),(0,[z0,z61,z1,z2,z3,z4,z26])],[(0,[z501,z0,z1,z2,z3,z4,z5]),(0,[z76,z0,z33,z1,z2,z4,z5]),(1,[z0,z467,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z12,z52,z5]),(0,[z0,z1,z2,z3,z502,z4,z5]),(0,[z0,z61,z418,z1,z2,z3,z4]),(1,[z0,z1,z10,z3,z11,z5]),(0,[z0,z1,z2,z3,z4,z503,z5])],[(0,[z77,z1,z2,z3,z195,z4,z5]),(0,[z0,z1,z2,z3,z4,z131,z90]),(0,[z0,z8,z1,z2,z22,z4,z5]),(1,[z0,z62,z1,z2,z4,z5])],[(0,[z504,z0,z1,z2,z3,z4,z5]),(0,[z505,z0,z1,z2,z3,z4,z5]),(0,[z51,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z157,z5])],[(0,[z0,z506,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z26,z58]),(0,[z0,z1,z74,z3,z42,z4,z5]),(0,[z0,z305,z1,z2,z3,z4,z5])],[(1,[z0,z320,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z267,z4,z5]),(0,[z0,z507,z1,z2,z3,z4,z5])]],
   [[(0,[z508,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z509,z4,z5])],[(0,[z510,z0,z1,z2,z3,z4,z5]),(0,[z51,z0,z1,z2,z3,z13,z5]),(0,[z0,z1,z511,z2,z3,z4,z5]),(0,[z203,z1,z2,z3,z4,z261,z5]),(0,[z0,z1,z2,z3,z4,z405,z5]),(0,[z0,z8,z1,z3,z42,z4,z5]),(0,[z0,z512,z1,z2,z3,z4,z5])],[(0,[z0,z40,z2,z3,z233,z4,z5]),(0,[z0,z1,z2,z513,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z514]),(0,[z0,z1,z2,z3,z515,z4,z5]),(0,[z0,z18,z1,z2,z3,z4,z58])],[(0,[z0,z1,z2,z3,z4,z516,z5]),(1,[z77,z1,z2,z195,z4,z5])],[(0,[z517,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z267,z5]),(0,[z0,z1,z518,z2,z3,z4,z5]),(0,[z519,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z520,z5])],[(0,[z0,z1,z2,z4,z87,z5,z43])],[(0,[z521,z0,z1,z2,z3,z4,z5]),(0,[z77,z0,z1,z2,z195,z4,z5]),(0,[z0,z1,z2,z522,z3,z4,z5])],[(0,[z0,z164,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z523]),(0,[z524,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z525,z3,z4,z5]),(0,[z0,z526,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z178,z93,z1,z2,z4,z5]),(0,[z0,z120,z418,z1,z2,z3,z4])],[(0,[z28,z1,z173,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z460,z5]),(0,[z0,z1,z2,z527,z3,z4,z5]),(0,[z0,z2,z3,z4,z67,z5,z26]),(0,[z0,z1,z2,z3,z4,z5,z528])],[(0,[z0,z1,z2,z3,z4,z5,z529]),(0,[z0,z530,z1,z2,z3,z4,z5]),(0,[z531,z0,z1,z2,z3,z4,z5]),(0,[z0,z18,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z532,z4,z5]),(0,[z533,z0,z1,z2,z3,z4,z5]),(0,[z0,z534,z1,z2,z3,z4,z5]),(0,[z0,z535,z1,z2,z3,z4,z5]),(0,[z0,z536,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z537,z3,z4,z5])],[(1,[z0,z1,z2,z169,z4,z5]),(0,[z0,z93,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z538,z4,z5]),(0,[z0,z55,z1,z2,z42,z4,z5]),(0,[z539,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z540])],[(0,[z0,z1,z2,z3,z541,z4,z5]),(0,[z0,z542,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z543,z5])],[(0,[z0,z320,z1,z173,z3,z4,z5]),(0,[z282,z0,z93,z1,z3,z4,z5]),(0,[z544,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z545,z5])]],
   [[(0,[z546,z0,z1,z2,z3,z4,z5]),(0,[z0,z547,z1,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z195,z4,z87,z5]),(0,[z0,z548,z1,z2,z3,z4,z5]),(0,[z0,z549,z1,z2,z3,z4,z5]),(0,[z0,z251,z1,z3,z4,z341,z5])],[(0,[z28,z0,z1,z2,z169,z4,z5]),(0,[z0,z1,z2,z3,z550,z4,z5]),(0,[z0,z55,z1,z2,z195,z4,z5]),(0,[z551,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z29,z4,z5]),(0,[z552,z0,z1,z2,z3,z4,z5]),(0,[z0,z39,z173,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z553,z4,z5]),(0,[z0,z1,z2,z554,z3,z4,z5]),(0,[z0,z1,z74,z2,z42,z4,z5])],[(1,[z0,z174,z2,z3,z4,z5]),(0,[z0,z467,z1,z2,z4,z52,z5]),(0,[z0,z1,z2,z3,z555,z4,z5]),(0,[z0,z418,z1,z2,z4,z87,z5])],[(0,[z0,z1,z2,z3,z4,z556,z5])],[(0,[z0,z1,z2,z3,z4,z5,z557]),(0,[z0,z1,z2,z3,z4,z558,z5]),(0,[z0,z1,z2,z3,z4,z559,z5])],[(0,[z0,z560,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z233,z4,z5]),(0,[z0,z561,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z562,z4,z5])]],
   [[(0,[z563,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z564,z4,z5]),(0,[z0,z1,z2,z3,z75,z87,z5])],[(0,[z0,z565,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z212,z4,z5])],[(0,[z28,z0,z173,z2,z3,z4,z5]),(0,[z0,z1,z2,z566,z3,z4,z5]),(1,[z0,z93,z3,z233,z4,z5]),(0,[z0,z1,z2,z3,z4,z567,z5]),(0,[z0,z1,z2,z3,z4,z5,z568]),(0,[z569,z0,z1,z2,z3,z4,z5]),(1,[z102,z0,z2,z3,z405,z5])],[(0,[z0,z1,z2,z3,z570,z4,z5]),(0,[z0,z8,z1,z2,z195,z4,z5]),(0,[z571,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z140,z5,z26]),(0,[z0,z572,z1,z2,z3,z4,z5])],[(0,[z0,z573,z1,z2,z3,z4,z5]),(0,[z0,z464,z1,z2,z3,z4,z5]),(0,[z0,z418,z1,z2,z3,z4,z17])],[(1,[z0,z1,z2,z3,z181,z5]),(0,[z31,z203,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z574]),(0,[z0,z1,z2,z3,z575,z4,z5]),(0,[z0,z1,z2,z3,z576,z4,z5]),(0,[z0,z1,z577,z2,z3,z4,z5])],[(0,[z0,z120,z61,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z578,z5]),(0,[z1,z2,z86,z3,z195,z4,z5]),(0,[z579,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z580,z4,z5]),(0,[z0,z1,z2,z3,z4,z581,z5]),(0,[z0,z418,z1,z2,z3,z4,z43])]],
   [[(0,[z0,z582,z1,z2,z3,z4,z5])],[(0,[z31,z1,z2,z3,z4,z5,z131]),(0,[z0,z1,z2,z3,z4,z583,z5])],[(0,[z0,z39,z164,z2,z3,z4,z5]),(0,[z0,z1,z2,z86,z9,z4,z5]),(0,[z0,z1,z2,z3,z4,z584,z5]),(0,[z0,z585,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z586,z4,z5])],[(0,[z0,z1,z2,z29,z3,z4,z5]),(0,[z0,z587,z1,z2,z3,z4,z5]),(0,[z588,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z86,z42,z4,z5]),(0,[z0,z1,z2,z3,z4,z589,z5]),(0,[z0,z1,z2,z3,z4,z590,z5]),(0,[z0,z1,z2,z591,z3,z4,z5]),(0,[z0,z592,z1,z2,z3,z4,z5])],[(0,[z0,z33,z1,z2,z3,z22,z5]),(0,[z0,z18,z1,z2,z3,z4,z87])],[(0,[z593,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z594,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z595,z4,z5])],[(0,[z0,z596,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z597]),(1,[z0,z464,z1,z2,z4,z5])],[(1,[z244,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z3,z4,z598,z5]),(0,[z0,z1,z2,z3,z4,z140,z5]),(0,[z0,z1,z10,z2,z3,z157,z5]),(0,[z599,z0,z1,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z3,z450,z5]),(0,[z0,z1,z2,z3,z9,z4,z5]),(1,[z0,z1,z2,z3,z5,z275]),(0,[z0,z600,z1,z2,z3,z4,z5]),(0,[z601,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z602,z5]),(0,[z0,z603,z1,z2,z3,z4,z5])],[(0,[z28,z0,z164,z2,z3,z4,z5]),(0,[z164,z1,z173,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z604]),(0,[z0,z1,z2,z3,z42,z4,z5]),(0,[z605,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z22,z4,z81])],[(0,[z0,z1,z606,z2,z3,z4,z5]),(0,[z0,z607,z1,z2,z3,z4,z5]),(0,[z0,z608,z1,z2,z3,z4,z5])],[(0,[z609,z0,z1,z2,z3,z4,z5]),(0,[z187,z0,z1,z2,z292,z4,z5]),(0,[z610,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z116])],[(0,[z0,z1,z2,z3,z4,z5,z611]),(0,[z0,z1,z2,z3,z5,z275,z26]),(0,[z612,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z75,z4,z5])],[(0,[z0,z1,z2,z3,z4,z613,z5]),(0,[z0,z1,z614,z2,z3,z4,z5]),(0,[z0,z615,z1,z2,z3,z4,z5]),(0,[z0,z18,z61,z1,z2,z3,z4]),(0,[z135,z0,z1,z74,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z616,z5]),(0,[z0,z18,z418,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z617,z5])],[(0,[z618,z0,z1,z2,z3,z4,z5]),(0,[z76,z0,z1,z2,z22,z4,z5]),(0,[z0,z619,z1,z2,z3,z4,z5]),(0,[z0,z620,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z621,z3,z4,z5])]],
   [[(0,[z102,z0,z1,z2,z3,z52,z5]),(0,[z31,z0,z1,z2,z3,z4,z261]),(0,[z102,z0,z1,z2,z218,z3,z5]),(0,[z0,z1,z2,z622,z3,z4,z5])],[(0,[z0,z623,z1,z2,z3,z4,z5]),(0,[z0,z624,z1,z2,z3,z4,z5]),(0,[z0,z1,z625,z2,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z626,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z9,z22,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z627]),(0,[z628,z0,z1,z2,z3,z4,z5])],[(0,[z629,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z630,z4,z5]),(0,[z0,z19,z1,z2,z9,z4,z5])],[(0,[z0,z1,z2,z3,z4,z631,z5]),(0,[z0,z1,z2,z3,z4,z5,z632])],[(0,[z0,z633,z1,z2,z3,z4,z5]),(0,[z244,z0,z1,z2,z3,z4,z5]),(0,[z634,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z635,z5]),(0,[z636,z0,z1,z2,z3,z4,z5])],[(0,[z235,z0,z19,z2,z3,z4,z5]),(0,[z0,z1,z637,z2,z3,z4,z5])]],
   [[(0,[z187,z0,z1,z387,z3,z4,z5]),(0,[z638,z0,z1,z2,z3,z4,z5]),(0,[z0,z290,z1,z2,z3,z9,z4]),(0,[z639,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z209,z3,z5]),(0,[z0,z1,z2,z3,z640,z4,z5])],[(0,[z0,z1,z2,z3,z641,z4,z5]),(0,[z642,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z643,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z17,z5])],[(0,[z644,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z387,z3,z4,z5]),(0,[z0,z1,z2,z645,z3,z4,z5])],[(0,[z0,z1,z2,z646,z3,z4,z5])],[(0,[z187,z282,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z647,z5]),(0,[z0,z648,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z43])],[(0,[z0,z1,z649,z2,z3,z4,z5]),(0,[z0,z1,z650,z2,z3,z4,z5]),(0,[z0,z1,z651,z2,z3,z4,z5])],[(0,[z652,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z88,z4,z52,z5]),(0,[z102,z0,z1,z2,z3,z4,z455]),(0,[z0,z1,z2,z3,z653,z4,z5])]],
   [[(0,[z102,z0,z120,z2,z3,z4,z5]),(0,[z0,z210,z1,z2,z3,z17,z5])],[(0,[z0,z654,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z655,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z656]),(0,[z0,z1,z2,z3,z4,z5,z657])],[(0,[z658,z0,z1,z2,z3,z4,z5]),(0,[z0,z659,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z660])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z187,z1,z2,z387,z3,z4,z5]),(0,[z661,z0,z1,z2,z3,z4,z5]),(0,[z135,z0,z8,z1,z2,z4,z5]),(0,[z0,z662,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z663,z5]),(0,[z0,z1,z2,z664,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z665,z5]),(0,[z135,z0,z1,z2,z3,z4,z5]),(0,[z666,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z22,z4,z87,z5]),(0,[z0,z1,z2,z3,z4,z667,z5])],[(0,[z0,z668,z1,z2,z3,z4,z5]),(0,[z0,z40,z93,z1,z3,z4,z5])],[(0,[z669,z0,z1,z2,z3,z4,z5]),(0,[z76,z0,z1,z2,z86,z4,z5]),(0,[z0,z1,z2,z25,z3,z4,z5]),(0,[z0,z670,z1,z2,z3,z4,z5]),(0,[z16,z0,z1,z2,z3,z5,z58])],[(0,[z0,z1,z2,z3,z4,z671,z5]),(0,[z0,z672,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z673,z4,z5]),(0,[z0,z1,z2,z674,z3,z4,z5]),(0,[z675,z0,z1,z2,z3,z4,z5]),(0,[z0,z676,z1,z2,z3,z4,z5]),(0,[z0,z33,z210,z1,z2,z3,z5]),(1,[z0,z33,z1,z2,z288,z5]),(1,[z0,z418,z1,z2,z4,z87]),(1,[z0,z2,z3,z4,z5,z315])],[(1,[z0,z1,z2,z3,z4,z222]),(0,[z0,z120,z1,z2,z3,z4,z26]),(0,[z0,z18,z1,z2,z3,z4,z17])],[(0,[z0,z1,z2,z3,z13,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z5]),(0,[z0,z210,z1,z2,z3,z405,z5])],[(0,[z0,z677,z1,z2,z3,z4,z5]),(0,[z678,z0,z1,z2,z3,z4,z5]),(0,[z0,z210,z1,z2,z3,z13,z5]),(0,[z0,z1,z2,z679,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z680,z5]),(0,[z0,z1,z2,z3,z331,z4,z5])],[(0,[z0,z681,z1,z2,z3,z4,z5]),(0,[z682,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z9,z42,z4,z5]),(0,[z0,z389,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z218,z3,z4,z5]),(0,[z0,z18,z1,z2,z3,z4,z43])],[(1,[z0,z1,z2,z3,z460,z5]),(0,[z683,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z684,z4,z5]),(0,[z0,z39,z1,z3,z233,z4,z5])],[(0,[z282,z0,z1,z387,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z685,z5]),(0,[z0,z156,z1,z2,z3,z4,z5]),(1,[z0,z251,z1,z3,z4,z341]),(0,[z0,z1,z2,z3,z12,z17,z5])],[(0,[z686,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z283,z4,z5]),(0,[z0,z1,z2,z687,z3,z4,z5]),(0,[z0,z389,z210,z1,z2,z4,z5]),(0,[z0,z2,z3,z4,z5,z315,z58]),(0,[z0,z1,z2,z3,z4,z5,z688])]],
   [[(0,[z0,z689,z1,z2,z3,z4,z5]),(0,[z0,z1,z690,z2,z3,z4,z5]),(0,[z0,z39,z93,z2,z3,z4,z5])],[(0,[z691,z0,z1,z2,z3,z4,z5]),(0,[z692,z0,z1,z2,z3,z4,z5]),(0,[z0,z61,z1,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z11,z4,z5]),(0,[z0,z693,z1,z2,z3,z4,z5]),(0,[z0,z1,z694,z2,z3,z4,z5]),(0,[z695,z0,z1,z2,z3,z4,z5])],[(0,[z696,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z697]),(0,[z0,z1,z2,z209,z3,z4,z5]),(1,[z0,z1,z2,z4,z5,z57])],[(1,[z0,z1,z2,z368,z4,z5])],[(0,[z0,z1,z2,z292,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z698]),(0,[z77,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z699,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z329,z4,z5]),(0,[z0,z1,z2,z3,z4,z341,z261]),(0,[z0,z700,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z701,z5]),(0,[z244,z0,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z3,z11,z13,z5]),(0,[z0,z1,z3,z4,z341,z5,z90])],[(0,[z0,z1,z2,z3,z4,z702,z5]),(0,[z0,z55,z2,z3,z9,z4,z5]),(0,[z0,z703,z1,z2,z3,z4,z5]),(0,[z0,z1,z704,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z81,z5])],[(0,[z0,z1,z2,z3,z705,z4,z5]),(0,[z0,z1,z706,z2,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z642,z1,z2,z195,z4,z5]),(0,[z76,z1,z2,z707,z4,z5]),(0,[z0,z1,z2,z4,z708,z5])],[(0,[z544,z0,z8,z1,z4,z5]),(0,[z0,z1,z2,z709,z4,z5])],[(0,[z0,z33,z1,z2,z410,z5]),(0,[z134,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z710]),(0,[z0,z1,z2,z22,z711,z5])],[(0,[z0,z1,z2,z712,z4,z5]),(0,[z0,z498,z2,z9,z4,z5]),(0,[z0,z713,z1,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z714]),(0,[z298,z1,z2,z3,z4,z261]),(0,[z0,z210,z2,z212,z15,z5])],[],[(0,[z0,z1,z2,z3,z715,z5]),(0,[z0,z716,z2,z3,z4,z5])],[(0,[z187,z1,z387,z292,z4,z5]),(0,[z31,z1,z2,z3,z32,z131]),(0,[z717,z1,z2,z3,z4,z5]),(0,[z0,z718,z1,z2,z4,z5]),(0,[z0,z719,z19,z2,z4,z5])]],
   [[(0,[z281,z164,z2,z3,z4,z5]),(0,[z0,z720,z2,z3,z4,z5]),(0,[z0,z467,z1,z2,z12,z5]),(0,[z0,z721,z1,z2,z3,z5]),(0,[z0,z120,z2,z4,z140,z26])],[(0,[z64,z164,z2,z3,z460,z5])],[],[(0,[z0,z177,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z722]),(0,[z0,z1,z2,z3,z723,z5]),(0,[z0,z8,z1,z266,z4,z5]),(0,[z0,z1,z724,z3,z4,z5])],[(0,[z0,z1,z725,z3,z4,z5])],[(0,[z0,z1,z2,z726,z4,z5]),(0,[z28,z177,z173,z3,z4,z5]),(0,[z0,z1,z2,z283,z450,z5]),(0,[z0,z1,z2,z727,z4,z5]),(0,[z0,z290,z1,z2,z86,z4]),(0,[z0,z1,z2,z728,z4,z5])],[],[(0,[z0,z1,z729,z3,z4,z5]),(0,[z0,z730,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z731]),(0,[z0,z732,z1,z2,z4,z5])]],
   [[(0,[z0,z733,z2,z3,z4,z5]),(0,[z134,z0,z1,z2,z140,z5])],[],[(0,[z0,z1,z2,z734,z460,z5]),(0,[z0,z1,z2,z3,z4,z735]),(0,[z0,z1,z2,z736,z3,z5]),(0,[z0,z1,z10,z368,z11,z5])],[(0,[z0,z467,z210,z1,z2,z5]),(0,[z737,z1,z2,z3,z4,z5])],[(0,[z1,z2,z738,z3,z4,z5]),(0,[z0,z739,z1,z74,z4,z5])],[(0,[z0,z1,z2,z3,z12,z192]),(0,[z740,z1,z2,z3,z4,z5]),(0,[z102,z0,z2,z3,z121,z5]),(0,[z135,z0,z739,z1,z4,z5]),(0,[z0,z741,z2,z3,z4,z5])],[(0,[z0,z1,z742,z3,z4,z5]),(0,[z0,z1,z2,z3,z743,z5])],[(0,[z0,z1,z2,z744,z4,z5]),(0,[z0,z1,z2,z3,z745,z5]),(0,[z0,z8,z290,z1,z2,z4]),(0,[z0,z1,z2,z3,z5,z746]),(0,[z0,z33,z1,z2,z5,z116])]],
   [[(0,[z0,z1,z2,z3,z747,z5]),(0,[z0,z748,z1,z2,z4,z5]),(0,[z0,z1,z2,z749,z4,z5]),(0,[z0,z1,z2,z3,z4,z222]),(0,[z102,z0,z2,z3,z405,z455])],[(0,[z0,z1,z2,z3,z450,z111]),(0,[z0,z418,z1,z2,z87,z116])],[(0,[z0,z1,z2,z3,z5,z750])],[(0,[z0,z33,z1,z2,z209,z5]),(0,[z0,z1,z2,z3,z4,z751])],[(0,[z0,z1,z2,z3,z460,z5]),(0,[z0,z1,z2,z3,z4,z752]),(0,[z0,z1,z2,z3,z4,z753])],[(0,[z0,z1,z2,z3,z754,z5])],[(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z93,z174,z3,z4,z5]),(0,[z0,z1,z2,z3,z756,z5]),(0,[z0,z1,z2,z757,z4,z5]),(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z2,z218,z5,z57])],[(1,[z0,z719,z2,z4,z5]),(0,[z134,z0,z120,z2,z3,z26])]],
   [[(0,[z0,z1,z759,z3,z4,z5]),(0,[z0,z760,z1,z2,z4,z5]),(0,[z0,z178,z93,z233,z4,z5])],[(0,[z0,z1,z2,z761,z4,z5])],[(0,[z0,z762,z2,z3,z4,z5]),(0,[z0,z153,z2,z9,z4,z5]),(0,[z0,z210,z2,z3,z5,z688])],[(0,[z0,z1,z2,z3,z763,z5]),(0,[z0,z1,z2,z3,z450,z338])],[(0,[z0,z1,z2,z3,z4,z764]),(0,[z0,z765,z2,z3,z4,z5]),(0,[z0,z1,z2,z209,z212,z5])],[(0,[z102,z0,z2,z3,z647,z5])],[],[(0,[z0,z1,z2,z3,z766,z5]),(0,[z0,z177,z174,z3,z4,z5]),(0,[z0,z767,z2,z3,z4,z5])]],
   [[(0,[z0,z768,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z769,z5]),(0,[z1,z2,z707,z3,z4,z5])],[(0,[z0,z1,z2,z770,z4,z5])],[(0,[z0,z719,z1,z2,z4,z5]),(0,[z0,z719,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z87,z771])],[(0,[z0,z120,z1,z2,z25,z4]),(0,[z1,z2,z3,z4,z5,z772])],[(0,[z1,z2,z3,z773,z4,z5]),(0,[z0,z18,z1,z2,z4,z43])],[(0,[z0,z1,z2,z4,z5,z774]),(0,[z0,z1,z2,z3,z775,z5]),(0,[z0,z1,z2,z3,z776,z5]),(0,[z0,z1,z74,z42,z4,z5])],[(0,[z0,z1,z2,z3,z4,z777])],[(0,[z462,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z778,z4,z5]),(0,[z0,z39,z779,z3,z4,z5]),(0,[z0,z780,z1,z2,z3,z4]),(0,[z0,z1,z2,z781,z4,z5])]],
   [[(0,[z0,z782,z1,z2,z3,z5]),(0,[z0,z1,z783,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z2,z3,z4,z5,z785]),(0,[z0,z1,z786,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z787])],[(0,[z0,z1,z2,z788,z4,z5]),(0,[z134,z0,z1,z2,z3,z455]),(0,[z102,z0,z694,z2,z3,z5])],[(0,[z0,z1,z2,z789,z4,z5]),(0,[z0,z1,z2,z4,z5,z790])],[(0,[z0,z1,z2,z3,z791,z5]),(0,[z0,z1,z2,z792,z4,z5]),(0,[z1,z793,z387,z3,z4,z5]),(0,[z0,z61,z2,z3,z4,z67]),(0,[z794,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z292,z4,z5]),(0,[z0,z795,z1,z2,z3,z4]),(0,[z134,z0,z1,z2,z25,z5]),(0,[z0,z8,z1,z2,z75,z5])],[(0,[z0,z398,z1,z2,z4,z87]),(0,[z0,z1,z2,z3,z75,z5]),(0,[z16,z0,z145,z2,z3,z58])],[(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z1,z2,z4,z5,z797]),(0,[z0,z2,z3,z4,z67,z455]),(0,[z102,z0,z2,z3,z685,z5])],[(0,[z0,z1,z2,z3,z798,z5]),(0,[z0,z145,z2,z3,z4,z26]),(0,[z0,z1,z577,z42,z4,z5])]],
   [[(0,[z0,z231,z2,z292,z4,z5]),(0,[z0,z210,z2,z3,z584,z5]),(0,[z0,z1,z2,z799,z3,z5])],[(0,[z0,z800,z1,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z58])],[(0,[z0,z1,z801,z3,z4,z5]),(0,[z0,z1,z2,z3,z802,z5]),(0,[z0,z355,z1,z3,z4,z90]),(0,[z0,z1,z2,z3,z4,z803])],[(0,[z804,z1,z2,z3,z4,z5]),(0,[z0,z805,z2,z3,z4,z5])],[(0,[z0,z806,z2,z3,z4,z5])],[(0,[z0,z101,z270,z1,z2,z3]),(0,[z134,z0,z1,z2,z3,z58]),(0,[z0,z807,z2,z3,z4,z5]),(0,[z16,z0,z145,z2,z3,z5])],[(0,[z0,z808,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z5,z116])],[(0,[z0,z1,z2,z3,z4,z809])]],
   [[],[(0,[z31,z1,z2,z3,z4,z131]),(0,[z0,z1,z2,z810,z4,z5])],[(0,[z0,z1,z2,z4,z140,z5]),(0,[z0,z1,z2,z4,z811,z5]),(0,[z0,z1,z2,z140,z5,z275]),(0,[z0,z62,z1,z10,z11,z5])],[(0,[z0,z174,z2,z3,z450,z5]),(0,[z0,z1,z2,z812,z4,z5]),(0,[z813,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z814]),(0,[z0,z1,z10,z3,z815,z5]),(0,[z0,z1,z3,z4,z758,z90]),(0,[z0,z464,z251,z1,z4,z341])],[(0,[z0,z1,z793,z3,z4,z5]),(0,[z816,z1,z2,z3,z4,z5]),(0,[z0,z33,z145,z2,z3,z5]),(0,[z0,z1,z2,z218,z22,z162])],[(0,[z0,z1,z606,z42,z4,z5]),(0,[z102,z0,z2,z3,z817,z5]),(0,[z0,z1,z3,z4,z5,z758]),(0,[z0,z1,z2,z3,z4,z162]),(0,[z0,z1,z2,z3,z5,z818])],[(0,[z819,z1,z2,z3,z4,z5]),(0,[z134,z0,z120,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z18,z1,z2,z4,z771])],[(0,[z0,z821,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z341,z758])]],
   [[(0,[z0,z779,z3,z233,z4,z5]),(0,[z134,z0,z2,z3,z67,z5])],[(0,[z0,z822,z2,z3,z4,z5]),(0,[z0,z33,z1,z2,z422,z5])],[(0,[z1,z220,z793,z3,z4,z5]),(0,[z0,z1,z2,z823,z4,z5])],[(0,[z0,z1,z2,z824,z4,z5]),(0,[z0,z1,z2,z825,z4,z5]),(0,[z0,z120,z2,z3,z4,z751])],[(0,[z0,z1,z2,z4,z5,z826])],[(0,[z0,z827,z1,z2,z4,z5]),(0,[z0,z828,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z227,z5])],[],[(0,[z0,z39,z44,z3,z4,z5]),(0,[z1,z2,z793,z3,z4,z5]),(0,[z0,z829,z1,z2,z4,z5]),(0,[z102,z0,z446,z2,z3,z5]),(0,[z0,z1,z2,z830,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z831,z5]),(0,[z0,z1,z2,z832,z4,z5]),(0,[z0,z1,z2,z3,z833,z5]),(0,[z0,z834,z1,z2,z3,z4]),(0,[z102,z0,z128,z2,z3,z5]),(1,[z0,z2,z3,z4,z751]),(0,[z0,z739,z1,z42,z4,z5]),(0,[z0,z1,z2,z3,z12,z818])],[(0,[z0,z1,z2,z3,z4,z835])],[(1,[z0,z779,z3,z4,z5]),(0,[z0,z836,z1,z2,z4,z5]),(0,[z0,z1,z2,z837,z4,z5])],[(0,[z0,z120,z2,z25,z4,z26])],[(0,[z0,z1,z838,z3,z4,z5])],[(0,[z0,z18,z1,z2,z4,z162])],[(0,[z0,z1,z2,z292,z4,z111]),(0,[z0,z839,z2,z3,z4,z5]),(0,[z0,z526,z2,z3,z4,z67]),(1,[z0,z739,z1,z4,z5])],[(0,[z0,z840,z1,z2,z460,z5]),(0,[z0,z841,z1,z2,z4,z5]),(0,[z0,z145,z2,z3,z17,z5])]],
   [[(0,[z0,z842,z1,z2,z3,z4]),(0,[z0,z1,z2,z843,z4,z5]),(0,[z0,z1,z2,z3,z12,z17])],[(0,[z0,z1,z2,z3,z4,z844]),(0,[z588,z0,z55,z2,z4,z5]),(0,[z0,z1,z2,z845,z4,z5]),(0,[z0,z418,z1,z2,z4,z771])],[(0,[z0,z846,z1,z2,z4,z5])],[],[(0,[z0,z1,z2,z847,z3,z5]),(0,[z235,z0,z55,z2,z4,z5])],[(0,[z0,z1,z2,z3,z32,z5]),(0,[z0,z120,z2,z3,z4,z26]),(0,[z0,z156,z1,z3,z815,z5]),(0,[z848,z0,z1,z2,z3,z5]),(0,[z0,z18,z592,z1,z2,z4])],[(0,[z1,z2,z86,z707,z4,z5]),(0,[z0,z849,z1,z2,z3,z5]),(0,[z0,z1,z2,z850,z4,z5])],[(0,[z0,z1,z2,z3,z5,z851]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z853,z1,z3,z4,z5]),(0,[z0,z854,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z292,z4,z338]),(0,[z0,z1,z2,z3,z855,z5]),(0,[z856,z1,z2,z3,z4,z5])],[(1,[z857,z2,z3,z4,z5]),(0,[z0,z177,z1,z858,z4,z5]),(0,[z0,z1,z2,z3,z4,z859]),(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z1,z2,z3,z861,z5]),(0,[z0,z862,z1,z2,z4,z5]),(0,[z1,z2,z3,z4,z714,z131]),(0,[z203,z1,z2,z204,z4,z261]),(0,[z0,z779,z1,z3,z4,z5])],[(0,[z0,z145,z2,z3,z13,z5]),(0,[z0,z863,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z576,z58])],[(0,[z0,z1,z864,z3,z4,z5]),(0,[z0,z865,z1,z2,z3,z4]),(0,[z187,z607,z1,z3,z4,z5]),(0,[z0,z101,z19,z2,z9,z5]),(0,[z235,z0,z2,z4,z5,z123]),(0,[z0,z2,z3,z817,z405,z5]),(0,[z0,z1,z2,z3,z866,z5])],[(0,[z0,z178,z1,z2,z4,z5]),(0,[z0,z1,z867,z2,z4,z5]),(0,[z0,z1,z206,z42,z4,z5]),(0,[z0,z33,z1,z2,z212,z5])],[(0,[z0,z1,z2,z868,z4,z5]),(0,[z0,z869,z1,z2,z4,z5]),(0,[z0,z8,z132,z1,z4,z5]),(0,[z0,z1,z2,z218,z3,z162])],[(0,[z0,z1,z2,z870,z4,z5]),(0,[z0,z871,z1,z2,z4,z5]),(0,[z0,z1,z2,z331,z4,z5])],[(1,[z1,z793,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z872,z5]),(0,[z0,z1,z2,z4,z87,z240]),(0,[z0,z873,z1,z2,z4,z5])],[(0,[z0,z1,z2,z874,z4,z5]),(0,[z1,z2,z3,z4,z261,z714]),(0,[z0,z270,z19,z2,z9,z4]),(0,[z0,z101,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z875]),(0,[z0,z1,z2,z876,z4,z5])],[(0,[z0,z1,z2,z3,z5,z877]),(0,[z187,z1,z387,z3,z4,z5]),(1,[z1,z2,z3,z4,z714]),(0,[z0,z878,z1,z2,z4,z5]),(0,[z102,z0,z2,z3,z405,z222]),(0,[z0,z1,z3,z4,z815,z5])],[(0,[z0,z1,z2,z879,z3,z5]),(0,[z383,z1,z2,z3,z13,z5]),(0,[z0,z290,z1,z2,z22,z4]),(1,[z0,z1,z2,z4,z771])],[(0,[z28,z173,z2,z3,z4,z5]),(0,[z0,z290,z1,z2,z195,z4]),(0,[z0,z1,z2,z3,z880,z5])],[(0,[z28,z173,z2,z169,z4,z5])],[(0,[z187,z231,z387,z3,z4,z5]),(0,[z0,z1,z2,z707,z4,z5]),(0,[z0,z39,z40,z3,z4,z5]),(0,[z0,z881,z2,z3,z4,z5]),(0,[z0,z305,z1,z3,z4,z758]),(0,[z0,z882,z2,z3,z4,z5])],[(0,[z0,z1,z2,z329,z4,z5]),(0,[z0,z270,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z711,z5]),(0,[z0,z98,z2,z4,z5,z315])]],
   [[(0,[z0,z1,z2,z3,z883,z5]),(0,[z16,z0,z1,z2,z3,z455]),(0,[z0,z1,z2,z3,z817,z5])],[(0,[z0,z1,z2,z4,z811,z455])],[(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z33,z1,z2,z197,z5]),(0,[z0,z1,z2,z4,z5,z771]),(0,[z0,z418,z1,z2,z75,z87])],[(0,[z0,z885,z1,z3,z4,z5]),(0,[z0,z33,z1,z2,z665,z5]),(0,[z0,z210,z2,z3,z817,z5])],[(0,[z0,z1,z2,z3,z886,z5]),(0,[z244,z1,z2,z3,z887,z5]),(0,[z0,z842,z1,z2,z212,z4]),(0,[z0,z888,z1,z2,z4,z5])],[(0,[z203,z1,z2,z3,z4,z261]),(0,[z0,z19,z2,z209,z9,z5]),(0,[z0,z1,z2,z4,z771,z43])],[(0,[z0,z1,z2,z3,z4,z111]),(0,[z0,z1,z2,z889,z4,z5]),(0,[z0,z1,z2,z890,z4,z5]),(0,[z0,z1,z2,z891,z4,z5]),(0,[z324,z0,z1,z2,z3,z58])],[(0,[z0,z892,z1,z2,z3,z4]),(0,[z893,z1,z2,z3,z4,z5]),(0,[z0,z33,z1,z2,z3,z455]),(0,[z0,z1,z2,z4,z711,z5]),(0,[z0,z33,z18,z1,z2,z58])]],
   [[(0,[z0,z1,z2,z3,z894,z5]),(0,[z0,z1,z188,z3,z11,z5]),(0,[z16,z0,z1,z2,z3,z818])],[(0,[z0,z1,z2,z895,z4,z5]),(0,[z0,z1,z2,z896,z4,z5]),(0,[z438,z1,z2,z3,z52,z5]),(0,[z0,z897,z1,z2,z32,z5]),(0,[z1,z2,z3,z4,z5,z714])],[(0,[z0,z231,z2,z3,z4,z111]),(0,[z0,z1,z3,z11,z815,z5]),(0,[z0,z2,z3,z4,z5,z898])],[(0,[z0,z145,z18,z2,z3,z4]),(0,[z0,z145,z418,z2,z3,z4])],[(0,[z0,z899,z177,z1,z4,z5]),(0,[z164,z857,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z900]),(0,[z0,z1,z2,z3,z5,z901]),(0,[z0,z1,z2,z3,z17,z455]),(0,[z0,z98,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z87,z162])],[(0,[z0,z902,z2,z3,z4,z5]),(0,[z0,z903,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z904,z5]),(0,[z905,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z13,z887,z5]),(0,[z0,z779,z2,z3,z4,z5]),(0,[z571,z0,z18,z1,z2,z4])]],
   [[(0,[z0,z174,z2,z292,z4,z5]),(0,[z187,z1,z387,z283,z4,z5]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z0,z1,z2,z4,z907,z5]),(0,[z0,z1,z2,z3,z4,z908])],[(0,[z0,z155,z1,z3,z4,z341]),(0,[z0,z101,z290,z1,z2,z3])],[(0,[z0,z1,z2,z3,z4,z909]),(0,[z1,z2,z3,z4,z5,z910]),(0,[z0,z911,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z68,z17])],[(0,[z0,z1,z2,z204,z4,z5]),(0,[z0,z1,z274,z42,z4,z5]),(0,[z0,z1,z2,z4,z5,z912])],[(0,[z64,z164,z2,z3,z4,z5]),(0,[z28,z857,z2,z3,z4,z5]),(0,[z134,z0,z1,z2,z3,z17]),(0,[z0,z1,z2,z3,z17,z818])],[(0,[z0,z1,z2,z88,z4,z5]),(0,[z0,z1,z2,z25,z4,z58]),(0,[z0,z2,z4,z5,z57,z315])],[(0,[z0,z467,z1,z2,z4,z5]),(0,[z0,z290,z19,z2,z9,z4])],[(0,[z0,z1,z2,z3,z13,z455]),(0,[z0,z1,z2,z913,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z914,z5]),(0,[z0,z18,z1,z2,z4,z430])],[(0,[z0,z1,z2,z292,z181,z5]),(0,[z0,z19,z2,z84,z4,z5]),(0,[z0,z18,z1,z2,z4,z255])],[(0,[z0,z1,z2,z3,z4,z915])],[(0,[z0,z916,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z1,z2,z918,z4,z5]),(0,[z1,z2,z3,z887,z52,z5]),(0,[z203,z1,z2,z3,z4,z714]),(0,[z0,z1,z2,z3,z919,z5]),(0,[z0,z2,z3,z4,z67,z751]),(0,[z0,z330,z1,z2,z4,z87]),(0,[z0,z33,z1,z2,z711,z5])],[(0,[z282,z1,z220,z3,z4,z5]),(0,[z0,z1,z2,z283,z4,z111]),(0,[z187,z1,z387,z3,z4,z111]),(0,[z0,z1,z2,z3,z920,z5]),(0,[z0,z290,z1,z2,z3,z4]),(0,[z0,z251,z1,z3,z4,z758])],[(0,[z28,z320,z173,z3,z4,z5]),(0,[z0,z1,z2,z734,z4,z5]),(0,[z0,z1,z2,z25,z4,z5])],[(0,[z0,z1,z2,z921,z4,z5]),(0,[z569,z1,z2,z86,z4,z5]),(0,[z0,z1,z2,z22,z5,z116])],[(0,[z0,z1,z2,z922,z4,z5]),(0,[z857,z1,z2,z3,z4,z5]),(0,[z77,z1,z2,z195,z4,z5]),(0,[z0,z1,z2,z923,z4,z5]),(0,[z0,z1,z2,z3,z4,z924]),(0,[z0,z145,z2,z3,z4,z67])]],
   [[(0,[z0,z1,z2,z3,z925,z5]),(0,[z203,z1,z2,z329,z4,z261]),(0,[z0,z1,z2,z3,z4,z926])],[(0,[z0,z1,z2,z3,z4,z927]),(0,[z76,z1,z2,z86,z4,z5])],[(0,[z0,z1,z2,z3,z928,z5]),(0,[z0,z1,z929,z3,z4,z5])],[(0,[z0,z19,z2,z9,z4,z5]),(0,[z930,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z292,z450,z5]),(0,[z468,z1,z2,z86,z4,z5]),(0,[z0,z1,z2,z931,z4,z5]),(0,[z932,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z933,z4,z5]),(0,[z0,z1,z2,z283,z4,z338]),(0,[z187,z1,z387,z3,z4,z338]),(0,[z539,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z218,z22,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z934,z5]),(0,[z1,z2,z707,z195,z4,z5]),(0,[z0,z18,z1,z2,z4,z463]),(0,[z0,z935,z1,z3,z4,z5]),(0,[z0,z2,z3,z15,z817,z5])]],
   [[(0,[z0,z1,z2,z169,z4,z5]),(0,[z31,z1,z2,z3,z4,z714]),(0,[z0,z1,z2,z4,z5,z936])],[(0,[z937,z0,z1,z2,z3,z5]),(0,[z0,z389,z1,z2,z4,z5]),(0,[z0,z878,z1,z2,z4,z455]),(0,[z0,z1,z2,z3,z4,z938]),(0,[z0,z305,z1,z3,z4,z90])],[(0,[z0,z2,z3,z15,z5,z56])],[(0,[z0,z231,z2,z3,z4,z5]),(0,[z0,z1,z939,z3,z4,z5]),(0,[z0,z120,z2,z84,z3,z4])],[(0,[z0,z2,z3,z4,z5,z940]),(0,[z0,z33,z1,z2,z107,z5]),(0,[z0,z1,z2,z3,z818,z58])],[(0,[z0,z941,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z942])],[(0,[z0,z1,z2,z943,z4,z5])],[(0,[z0,z1,z2,z944,z4,z5]),(0,[z16,z0,z2,z3,z315,z58])]],
   [[(0,[z0,z1,z2,z945,z4,z5]),(0,[z0,z1,z2,z946,z4,z5]),(0,[z0,z174,z2,z3,z4,z5]),(0,[z0,z779,z93,z3,z4,z5]),(0,[z0,z33,z1,z2,z323,z5]),(0,[z0,z1,z947,z2,z4,z5])],[(0,[z77,z63,z1,z2,z4,z5]),(0,[z244,z1,z2,z88,z52,z5]),(0,[z0,z145,z2,z3,z4,z5]),(0,[z0,z1,z2,z42,z4,z81])],[(0,[z0,z8,z417,z1,z4,z5])],[(0,[z0,z1,z2,z948,z4,z5]),(0,[z0,z18,z1,z2,z4,z322]),(0,[z0,z418,z1,z2,z502,z4]),(0,[z0,z739,z1,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z949]),(0,[z0,z950,z2,z3,z4,z5])],[(1,[z0,z2,z3,z817,z5])],[(0,[z0,z93,z3,z233,z4,z5]),(0,[z0,z951,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z57,z162])],[(0,[z0,z39,z174,z3,z4,z5]),(0,[z0,z1,z2,z952,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z751,z26])],[(0,[z0,z61,z1,z2,z25,z4])],[(0,[z0,z1,z2,z25,z5,z275])],[(0,[z0,z1,z2,z3,z953,z5])],[(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z955,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z956])],[(0,[z0,z1,z2,z3,z957,z5]),(0,[z0,z1,z2,z958,z4,z5]),(0,[z0,z1,z2,z283,z4,z5]),(0,[z0,z1,z959,z2,z4,z5]),(0,[z0,z61,z457,z2,z3,z4])],[(0,[z0,z1,z2,z960,z4,z5])],[(0,[z0,z1,z2,z961,z4,z5]),(0,[z0,z1,z2,z3,z4,z962]),(0,[z0,z1,z2,z963,z4,z5]),(0,[z0,z33,z1,z2,z5,z57]),(0,[z0,z18,z1,z2,z3,z116])]],
   [[(0,[z187,z1,z793,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z964]),(0,[z0,z210,z2,z115,z3,z5]),(0,[z0,z1,z2,z3,z965,z5]),(0,[z0,z1,z2,z5,z57,z116])],[(0,[z0,z231,z2,z283,z4,z5]),(0,[z0,z1,z2,z966,z4,z5]),(0,[z0,z270,z1,z2,z209,z3])],[(0,[z0,z464,z1,z2,z4,z5]),(0,[z0,z18,z1,z2,z4,z57])],[(0,[z244,z1,z2,z3,z52,z5]),(0,[z0,z897,z1,z2,z4,z5]),(0,[z0,z967,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z968]),(0,[z0,z1,z2,z3,z969,z5]),(0,[z0,z210,z2,z3,z15,z5]),(0,[z0,z970,z1,z2,z4,z5]),(0,[z0,z156,z1,z3,z157,z5])],[(0,[z0,z899,z1,z2,z4,z5]),(0,[z0,z971,z1,z2,z3,z5]),(0,[z0,z2,z3,z4,z972,z5]),(0,[z0,z1,z2,z3,z5,z275]),(0,[z0,z1,z2,z3,z17,z60])],[(0,[z0,z973,z2,z3,z4,z5]),(0,[z0,z1,z2,z974,z4,z5]),(0,[z221,z0,z1,z2,z3,z58]),(0,[z0,z1,z2,z4,z5,z975])],[(0,[z0,z1,z2,z976,z4,z5]),(0,[z0,z1,z2,z977,z4,z5]),(0,[z0,z174,z2,z283,z4,z5]),(0,[z187,z174,z387,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z978]),(0,[z0,z1,z2,z3,z5,z979]),(0,[z0,z459,z2,z9,z4,z5])],[(0,[z28,z173,z2,z29,z4,z5]),(0,[z628,z1,z2,z3,z13,z5]),(0,[z0,z1,z2,z218,z711,z5])]],
   [[(0,[z0,z1,z2,z22,z701,z5]),(0,[z0,z1,z2,z3,z12,z259])],[(0,[z1,z2,z3,z4,z887,z5]),(0,[z0,z1,z2,z3,z4,z980])],[(0,[z0,z981,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z982,z5]),(0,[z51,z1,z2,z3,z13,z5]),(0,[z0,z1,z2,z3,z815,z5]),(0,[z0,z1,z2,z3,z478,z17]),(0,[z16,z0,z1,z2,z57,z58])],[(0,[z0,z1,z2,z3,z887,z5]),(0,[z0,z1,z2,z983,z4,z5]),(0,[z0,z1,z2,z3,z4,z984])],[],[(0,[z0,z1,z2,z3,z985,z5]),(0,[z0,z1,z2,z986,z4,z5]),(0,[z987,z1,z2,z3,z4,z5]),(0,[z0,z55,z670,z2,z4,z5]),(0,[z0,z145,z98,z2,z4,z5])],[(0,[z0,z1,z2,z988,z4,z5]),(0,[z0,z1,z2,z989,z3,z5])],[(0,[z0,z1,z2,z283,z181,z5]),(0,[z187,z1,z387,z3,z181,z5])]],
   [[(0,[z64,z164,z2,z3,z267,z5]),(0,[z0,z990,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z991]),(0,[z599,z1,z2,z3,z4,z131])],[(0,[z0,z992,z2,z3,z4,z5]),(0,[z0,z145,z2,z3,z52,z5]),(0,[z0,z739,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z993,z5]),(0,[z0,z145,z2,z218,z3,z5])],[(0,[z0,z174,z2,z3,z4,z111]),(0,[z0,z1,z2,z3,z994,z5]),(0,[z235,z0,z719,z2,z4,z5]),(0,[z0,z2,z3,z4,z817,z5]),(0,[z0,z418,z1,z2,z3,z116])],[(0,[z0,z1,z3,z4,z5,z995]),(0,[z0,z1,z2,z3,z4,z338]),(0,[z461,z1,z2,z195,z4,z5])],[],[(0,[z0,z1,z2,z3,z996,z5]),(0,[z282,z363,z1,z3,z4,z5]),(0,[z0,z1,z2,z209,z3,z5]),(0,[z0,z18,z1,z2,z73,z4]),(0,[z0,z418,z1,z2,z4,z57])],[(0,[z0,z1,z2,z3,z4,z997]),(0,[z998,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z455]),(0,[z0,z999,z1,z2,z4,z5])],[(0,[z0,z231,z2,z3,z4,z338]),(0,[z0,z1,z2,z1000,z4,z5]),(0,[z0,z1,z2,z3,z1001,z5])]],
   [[(0,[z0,z1002,z1,z2,z3,z4])],[(0,[z639,z1,z2,z86,z4,z5]),(0,[z0,z1003,z1,z2,z3,z5]),(0,[z102,z0,z2,z3,z67,z17]),(0,[z0,z61,z2,z3,z4,z751])],[(0,[z0,z1,z2,z1004,z4,z5]),(0,[z187,z1,z387,z3,z450,z5]),(0,[z0,z1005,z1,z2,z4,z5]),(0,[z0,z1,z1006,z3,z4,z5]),(0,[z0,z1,z10,z3,z11,z5]),(0,[z0,z1007,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z181,z111]),(0,[z0,z1,z2,z1008,z4,z5]),(0,[z0,z62,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z174,z2,z3,z4,z338]),(0,[z0,z1,z2,z3,z1010,z5]),(0,[z0,z1,z2,z25,z4,z17])],[(0,[z0,z2,z3,z4,z5,z1011]),(0,[z0,z55,z719,z2,z4,z5])],[(0,[z0,z320,z1,z3,z4,z5]),(0,[z0,z1,z2,z1012,z4,z5]),(0,[z0,z290,z1,z2,z209,z3]),(0,[z0,z1,z2,z3,z4,z818])],[(0,[z0,z1,z2,z1013,z4,z5])]],
   [[(0,[z64,z857,z2,z3,z4,z5]),(0,[z0,z1,z2,z1014,z4,z5]),(0,[z0,z145,z2,z3,z4,z455]),(0,[z0,z2,z3,z4,z67,z186])],[(0,[z0,z40,z779,z3,z4,z5]),(1,[z0,z1,z3,z815,z5])],[(0,[z0,z840,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z267,z5]),(0,[z0,z1,z2,z3,z4,z1015]),(0,[z0,z1,z2,z3,z1016,z5]),(0,[z0,z1,z2,z3,z4,z1017]),(0,[z0,z1,z2,z218,z212,z5]),(0,[z0,z1,z2,z359,z3,z58])],[(0,[z0,z1,z3,z4,z1018,z5]),(0,[z0,z1,z2,z1019,z4,z5]),(1,[z1,z2,z707,z4,z5]),(0,[z0,z1,z2,z3,z1020,z5]),(0,[z0,z2,z3,z4,z5,z315]),(0,[z0,z33,z1,z2,z288,z5]),(0,[z0,z418,z1,z2,z4,z87])],[(0,[z0,z1,z2,z3,z181,z338]),(0,[z102,z0,z467,z1,z2,z5]),(0,[z0,z1,z2,z711,z288,z5])],[(0,[z0,z1021,z1,z2,z4,z5]),(0,[z0,z719,z2,z9,z4,z5])],[(0,[z0,z1,z2,z1022,z4,z5]),(0,[z0,z101,z1,z2,z42,z5])]],
   [[(0,[z0,z1,z2,z1023,z4,z5]),(0,[z0,z389,z210,z2,z15,z5]),(0,[z0,z1024,z1,z2,z4,z5])],[(0,[z0,z1025,z2,z3,z4,z5])],[(0,[z51,z1,z2,z3,z887,z5]),(0,[z0,z251,z1,z3,z4,z341]),(0,[z0,z1,z2,z3,z402,z58])],[(0,[z857,z173,z2,z3,z4,z5]),(0,[z0,z1026,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z818])],[(0,[z0,z1,z2,z3,z4,z1027])],[(0,[z0,z1,z2,z4,z1028,z5]),(0,[z601,z1,z2,z195,z4,z5]),(0,[z0,z93,z89,z233,z4,z5]),(0,[z0,z8,z739,z1,z4,z5])],[(0,[z0,z1,z2,z1029,z4,z5]),(1,[z1,z2,z3,z887,z5]),(0,[z0,z1,z2,z50,z22,z5]),(0,[z0,z1,z2,z3,z1030,z5]),(0,[z0,z1,z2,z4,z5,z57])],[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z0,z1032,z2,z3,z4,z5]),(0,[z0,z1,z2,z368,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z1033,z5])],[(0,[z0,z911,z1,z2,z212,z4])],[(0,[z0,z1,z2,z29,z4,z5]),(0,[z0,z1,z3,z4,z1034,z5]),(0,[z0,z1,z2,z3,z1035,z5]),(0,[z0,z1,z2,z42,z75,z5])],[(0,[z0,z1036,z2,z3,z4,z5])],[(0,[z0,z624,z1,z3,z157,z5]),(0,[z0,z1,z2,z757,z32,z5]),(0,[z1037,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z751]),(0,[z16,z0,z98,z1,z2,z58])],[(0,[z0,z1,z1038,z3,z4,z5]),(0,[z244,z467,z1,z2,z52,z5]),(0,[z369,z1,z2,z3,z13,z5])],[(0,[z0,z39,z177,z3,z4,z5]),(0,[z0,z1,z2,z3,z52,z455]),(0,[z0,z1,z2,z218,z3,z455])],[(0,[z0,z1,z2,z209,z22,z5]),(0,[z0,z120,z2,z3,z275,z26]),(1,[z0,z1,z2,z711,z5]),(0,[z0,z1,z2,z1039,z3,z5])]],
   [[(0,[z0,z1,z2,z1040,z4,z5]),(0,[z0,z39,z146,z3,z4,z5]),(0,[z1041,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z212,z4,z5]),(0,[z0,z55,z703,z2,z4,z5]),(0,[z0,z145,z2,z4,z5,z57])],[(0,[z0,z1042,z2,z3,z4,z5]),(0,[z0,z1,z2,z1043,z4,z5]),(0,[z102,z0,z2,z3,z405,z5])],[(0,[z0,z1,z3,z4,z1044,z5]),(0,[z0,z1,z2,z3,z1045,z5]),(0,[z0,z1,z2,z1046,z4,z5]),(0,[z0,z1,z2,z4,z1047,z5])],[(0,[z0,z1,z2,z1048,z4,z5]),(0,[z0,z1,z1049,z3,z4,z5])],[(0,[z0,z1,z2,z3,z181,z5]),(0,[z0,z1,z1050,z3,z4,z5]),(0,[z0,z251,z1,z331,z4,z341])],[(0,[z0,z1,z2,z858,z4,z5]),(0,[z0,z1,z1051,z3,z4,z5]),(0,[z0,z1,z1052,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z1053,z5]),(0,[z0,z1,z2,z1054,z4,z5])]],
   [[(0,[z0,z231,z2,z3,z181,z5]),(0,[z0,z1055,z2,z3,z4,z5]),(0,[z0,z1056,z1,z2,z4,z5]),(0,[z235,z0,z290,z1,z2,z4])],[(0,[z0,z1,z2,z1057,z4,z5]),(0,[z0,z33,z290,z1,z2,z4]),(0,[z0,z1058,z2,z3,z4,z5]),(0,[z0,z18,z1,z2,z4,z514])],[(0,[z0,z177,z3,z233,z4,z5]),(0,[z76,z1,z2,z515,z4,z5]),(0,[z0,z1059,z1,z2,z3,z5]),(0,[z0,z1,z2,z1060,z4,z5]),(1,[z0,z1,z3,z4,z758])],[(0,[z282,z1,z793,z3,z4,z5]),(0,[z0,z8,z1,z2,z4,z81]),(0,[z0,z1,z2,z218,z22,z81]),(0,[z0,z1,z2,z3,z4,z771])],[(0,[z0,z1,z2,z3,z4,z81])],[(0,[z0,z1061,z1,z2,z4,z5]),(0,[z0,z174,z2,z3,z181,z5]),(0,[z0,z467,z1,z2,z5,z58]),(0,[z0,z1062,z2,z3,z4,z5])],[(0,[z126,z173,z2,z3,z4,z5]),(0,[z0,z1063,z2,z3,z4,z5]),(0,[z0,z1,z2,z89,z4,z5]),(0,[z0,z120,z2,z3,z4,z455]),(0,[z0,z33,z1,z2,z3,z162])],[(0,[z0,z1,z2,z3,z450,z5]),(0,[z77,z1,z2,z707,z4,z5]),(0,[z31,z1,z2,z3,z227,z131]),(0,[z0,z1,z2,z1064,z4,z5])]],
   [[(0,[z0,z290,z19,z1,z2,z4]),(0,[z0,z1,z2,z3,z5,z1065])],[(0,[z0,z1066,z2,z3,z4,z5]),(0,[z0,z1,z2,z1067,z4,z5]),(0,[z0,z1,z2,z3,z1068,z5])],[(0,[z0,z1069,z2,z3,z4,z5]),(0,[z0,z290,z1,z2,z42,z4])],[(0,[z0,z1,z1070,z3,z4,z5]),(0,[z0,z857,z2,z3,z4,z5]),(0,[z0,z231,z2,z3,z450,z5]),(0,[z0,z1,z2,z3,z1071,z5]),(0,[z0,z1072,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1073,z5])],[(0,[z0,z1,z3,z815,z157,z5])],[(0,[z0,z101,z8,z1,z2,z5]),(0,[z135,z0,z8,z1,z4,z5])],[]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 553) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 553).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1042)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [553, 489] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 179).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 179).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [179, 77] = true :=
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

end PEqualNP.Outside.L_meta_41096

theorem PEqualNP.Outside.L_meta_41096 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4272596992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4272596992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41096.solve