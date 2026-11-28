import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41366

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4241006592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x008910c2ac630dba#64 ++ 0x0008910c2ac630db#64 ++ 0xc19f31c7ec631ffd#64 ++ 0xec19f31c7ec631ff#64 : BitVec 256),
   (0x42245659902d778c#64 ++ 0x042245659902d778#64 ++ 0xc664de79907fff8b#64 ++ 0xfc664de79907fff8#64 : BitVec 256),
   (0x1858e06e1583a2d0#64 ++ 0x11858e06e1583a2d#64 ++ 0x7878e07e1f83e3f7#64 ++ 0xf7878e07e1f83e3f#64 : BitVec 256),
   (0xad80fb801af40360#64 ++ 0x0ad80fb801af4036#64 ++ 0xbf80ff801ffc03ff#64 ++ 0x7bf80ff801ffc03f#64 : BitVec 256),
   (0x37ff00000f5ad800#64 ++ 0x237ff00000f5ad80#64 ++ 0x3fff00001ffffc0f#64 ++ 0xa3fff00001ffffc0#64 : BitVec 256),
   (0x3f76ad3540000000#64 ++ 0x43f76ad354000000#64 ++ 0xffffffffe000000f#64 ++ 0xdffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc19f31c7ec631ffd 0xec19f31c7ec631ff

def z1 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7878e07e1f83e3f7 0xf7878e07e1f83e3f

def z2 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3fff00001ffffc0f 0xa3fff00001ffffc0

def z3 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xffffffffe000000f 0xdffffffffe000000

def z4 : W := mkw 0x42245248902d778c 0x042245248902d778 0x06640000107fff8b 0xa06640000107fff8

def z5 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc664de79907fff8b 0xfc664de79907fff8

def z6 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf80ff801ffc03ff 0x7bf80ff801ffc03f

def z7 : W := mkw 0x127f0000050ad800 0x2127f0000050ad80 0x007f00000003fc00 0x8007f00000003fc0

def z8 : W := mkw 0x67a456599a7d778c 0x067a456599a7d778 0xffe4de799fffff8f 0xfffe4de799fffff8

def z9 : W := mkw 0x008900000c420800 0x0008900000c42080 0x019b00000c000004 0x0019b00000c00000

def z10 : W := mkw 0x0800ad3540000000 0x40800ad354000000 0xc19fffffe000000d 0xdc19fffffe000000

def z11 : W := mkw 0x42a51691a86c5d2e 0x042a51691a86c5d2 0x87871f81e07c1c08 0x087871f81e07c1c0

def z12 : W := mkw 0x00090042a4030c9a 0x000090042a4030c9 0x401f0047e0031c00 0x8401f0047e0031c0

def z13 : W := mkw 0xad89fbc2bef70ffa 0x0ad89fbc2bef70ff 0xff9fffc7ffff1fff 0xfff9fffc7ffff1ff

def z14 : W := mkw 0x40005248902d778c 0x040005248902d778 0x00000000107fff80 0x200000000107fff8

def z15 : W := mkw 0x7f76ff7dd02d778c 0x47f76ff7dd02d778 0xfffffffff07fff8f 0xffffffffff07fff8

def z16 : W := mkw 0x0800e048108122c0 0x00800e048108122c 0x7860e0781f83e3f7 0xf7860e0781f83e3f

def z17 : W := mkw 0x35db00000f528800 0x235db00000f52880 0x399b00000f800004 0x0399b00000f80000

def z18 : W := mkw 0x77ff56599f7fff8c 0x277ff56599f7fff8 0xffffde799fffff8f 0xfffffde799fffff8

def z19 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0x7e78ee7e00000007 0xd7e78ee7e0000000

def z20 : W := mkw 0xa5805b801a740320 0x0a5805b801a74032 0x8780df80107c038b 0x78780df80107c038

def z21 : W := mkw 0x3d52a92440000000 0x43d52a9244000000 0x79fbe1fe60000007 0xd79fbe1fe6000000

def z22 : W := mkw 0x1058006e0503a090 0x11058006e0503a09 0x4078007e0003e000 0x84078007e0003e00

def z23 : W := mkw 0xa5801b800a740120 0x0a5801b800a74012 0x87801f80007c0008 0x087801f80007c000

def z24 : W := mkw 0xef24ff5992bd77cc 0x0ef24ff5992bd77c 0xfe64de7993ffff8b 0xffe64de7993ffff8

def z25 : W := mkw 0x0800e06e108122d0 0x10800e06e108122d 0x4000e07e000003f0 0x54000e07e000003f

def z26 : W := mkw 0x1058000005028000 0x0105800000502800 0x387800001f83e007 0xa387800001f83e00

def z27 : W := mkw 0x3ff7ad354a585800 0x63ff7ad354a58580 0xffffffffe07c1c0f 0xdffffffffe07c1c0

def z28 : W := mkw 0x18d9a0a62dc28872 0x118d9a0a62dc2887 0x399b21866f800074 0x0399b21866f80007

def z29 : W := mkw 0x1858f0eeb5a3a7fa 0x11858f0eeb5a3a7f 0xf878f1ffff83e3f7 0xff878f1ffff83e3f

def z30 : W := mkw 0x0224145180210588 0x0022414518021058 0xc664de7980631f8b 0xfc664de7980631f8

def z31 : W := mkw 0xad00eb0012940240 0x0ad00eb001294024 0x3e00ce00139c0002 0x13e00ce00139c000

def z32 : W := mkw 0xffffffd99fffffec 0x2ffffffd99fffffe 0xfffffff99fffffff 0xffffffff99ffffff

def z33 : W := mkw 0x3d52a92440000000 0x43d52a9244000000 0x399b218660000004 0x0399b21866000000

def z34 : W := mkw 0x7ffff67f9fffffdc 0x37ffff67f9fffffd 0xfffffe7f9fffffff 0xffffffe7f9ffffff

def z35 : W := mkw 0x10d900000f5ad800 0x210d900000f5ad80 0x387800001ffffc07 0xa387800001ffffc0

def z36 : W := mkw 0x18d9f0eebde3affa 0x118d9f0eebde3aff 0xf9fff1ffffe3ffff 0xff9fff1ffffe3fff

def z37 : W := mkw 0x0081000008400800 0x0008100000840080 0x0187000000601c08 0x00187000000601c0

def z38 : W := mkw 0x0224000000085000 0x0022400000008500 0x06600000101ce002 0x006600000101ce00

def z39 : W := mkw 0x42245659902d778c 0x042245659902d778 0x0660ce38107fff82 0x30660ce38107fff8

def z40 : W := mkw 0x0800e00010800240 0x00800e0001080024 0x3800e0001f8003f7 0x73800e0001f8003f

def z41 : W := mkw 0x42241611802c550c 0x042241611802c550 0x86041e01807c1c08 0x086041e01807c1c0

def z42 : W := mkw 0x40005659902d778c 0x040005659902d778 0xc000de79907fff80 0x7c000de79907fff8

def z43 : W := mkw 0x1858a02605828050 0x11858a0260582805 0x387820061f83e077 0xa387820061f83e07

def z44 : W := mkw 0x008900822c420832 0x0008900822c42083 0x019b21866c000074 0x0019b21866c00007

def z45 : W := mkw 0x377600000318d000 0x2377600000318d00 0x3e64000013fffc0b 0xa3e64000013fffc0

def z46 : W := mkw 0x42244619100c7204 0x042244619100c720 0x0660ce38101ce002 0x10660ce38101ce00

def z47 : W := mkw 0x008010c2a86105ba 0x0008010c2a86105b 0xc18031c7ec6003fd 0x6c18031c7ec6003f

def z48 : W := mkw 0x4800f67f90a527dc 0x14800f67f90a527d 0xc000fe7f800003f0 0x5c000fe7f800003f

def z49 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x000000000c631ff0 0x2000000000c631ff

def z50 : W := mkw 0x10d910c2ad638dba 0x010d910c2ad638db 0xf9ff31c7ffe3ffff 0xef9ff31c7ffe3fff

def z51 : W := mkw 0x0224041100000000 0x0022404110000000 0xc664de798000000b 0xdc664de798000000

def z52 : W := mkw 0x0008000205828050 0x1000800020582805 0x000000000f800070 0x0000000000f80007

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004000000631c09 0xa0004000000631c0

def z54 : W := mkw 0x3fffad354f5ad800 0x63fffad354f5ad80 0xfffffffffffffc0f 0xffffffffffffffc0

def z55 : W := mkw 0x42241659802d758c 0x042241659802d758 0xc6641e79807ffc08 0x8c6641e79807ffc0

def z56 : W := mkw 0x527c567f952ff79c 0x1527c567f952ff79 0xc67cde7f907fff8b 0xfc67cde7f907fff8

def z57 : W := mkw 0x008900000f5ad800 0x2008900000f5ad80 0x000000001ffffc00 0x2000000001ffffc0

def z58 : W := mkw 0x0800ad3540000000 0x40800ad354000000 0xc000ffffe0000000 0x5c000ffffe000000

def z59 : W := mkw 0x258900000f5ad800 0x2258900000f5ad80 0x3f8000001ffffc0f 0x23f8000001ffffc0

def z60 : W := mkw 0xad80bb800af40160 0x0ad80bb800af4016 0xbf803f800ffc007c 0x0bf803f800ffc007

def z61 : W := mkw 0x8880fb801af40360 0x08880fb801af4036 0x8000ff801ffc03f0 0x78000ff801ffc03f

def z62 : W := mkw 0x02ad00000f5ad800 0x202ad00000f5ad80 0x066400001ffffc0b 0xa066400001ffffc0

def z63 : W := mkw 0x7f76ef3d500c7204 0x47f76ef3d500c720 0xfffffffff01ce00f 0xdfffffffff01ce00

def z64 : W := mkw 0x4800ff7dd025278c 0x44800ff7dd025278 0xc000ffffe0000380 0x5c000ffffe000038

def z65 : W := mkw 0x1276043540000000 0x4127604354000000 0x407f007fe0000000 0x8407f007fe000000

def z66 : W := mkw 0x808052801af40360 0x0808052801af4036 0x000000001ffc03f0 0x2000000001ffc03f

def z67 : W := mkw 0x1058406e1503a290 0x11058406e1503a29 0x4078c07e1003e383 0xf4078c07e1003e38

def z68 : W := mkw 0x3552000000000000 0x0355200000000000 0x399b000000000004 0x0399b00000000000

def z69 : W := mkw 0x2500000000000000 0x0250000000000000 0x3f8000000000000f 0x03f8000000000000

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0xc19f31c7e000000d 0xcc19f31c7e000000

def z71 : W := mkw 0x3fffbdf7ec630dba 0x43fffbdf7ec630db 0xffffffffec631fff 0xfffffffffec631ff

def z72 : W := mkw 0x27260d1140000000 0x427260d114000000 0x87871f81e0000008 0x087871f81e000000

def z73 : W := mkw 0x00090000050ad800 0x200090000050ad80 0x000000000003fc00 0x0000000000003fc0

def z74 : W := mkw 0x0a24ad3540000000 0x40a24ad354000000 0xc664ffffe000000b 0xdc664ffffe000000

def z75 : W := mkw 0x37ff04354f5ad800 0x637ff04354f5ad80 0x7fff007ffffffc0f 0xa7fff007ffffffc0

def z76 : W := mkw 0xef24ef19129c7244 0x0ef24ef19129c724 0x3e60ce38139ce002 0x13e60ce38139ce00

def z77 : W := mkw 0x1850e02c1180a240 0x11850e02c1180a24 0x3860c0381380e002 0x13860c0381380e00

def z78 : W := mkw 0x008900822c420832 0x0008900822c42083 0x019f21866c631c7d 0xa019f21866c631c7

def z79 : W := mkw 0x3ddbb9e6ec630dba 0x43ddbb9e6ec630db 0xf99f31c7ec631ffd 0xef99f31c7ec631ff

def z80 : W := mkw 0x2726000002185000 0x2272600000218500 0x06000000001c0000 0x006000000001c000

def z81 : W := mkw 0x0800e00010800240 0x00800e0001080024 0x3800c00013800002 0x13800c0001380000

def z82 : W := mkw 0x0000104080210588 0x0000010408021058 0xc004104180631f89 0xec004104180631f8

def z83 : W := mkw 0x42ad56dbbc6f7fbe 0x042ad56dbbc6f7fb 0xc7fffffffc7fffff 0xfc7fffffffc7ffff

def z84 : W := mkw 0x27a700000a585800 0x227a700000a58580 0x07870000007c1c08 0x007870000007c1c0

def z85 : W := mkw 0xca24ffd990ad77ec 0x0ca24ffd990ad77e 0xc664fff9907ffffb 0xfc664fff9907ffff

def z86 : W := mkw 0x0008404a1583a2d0 0x10008404a1583a2d 0x000000001f83e3f0 0x2000000001f83e3f

def z87 : W := mkw 0x0000400810002200 0x0000040081000220 0x0060c0381000e002 0x10060c0381000e00

def z88 : W := mkw 0x0000000000085000 0x0000000000008500 0x00000000107ffc00 0x200000000107ffc0

def z89 : W := mkw 0x00890042ac430c9a 0x000890042ac430c9 0x419f0047ec631c0d 0xa419f0047ec631c0

def z90 : W := mkw 0x0008404a1583a2d0 0x10008404a1583a2d 0x401820461f83e3f5 0xe401820461f83e3f

def z91 : W := mkw 0x400056599025278c 0x0400056599025278 0xc000de7980000380 0x5c000de798000038

def z92 : W := mkw 0x0008404a1583a2d0 0x10008404a1583a2d 0x4060c0781f83e3f3 0xf4060c0781f83e3f

def z93 : W := mkw 0x3fffa9244f5ad800 0x63fffa9244f5ad80 0x3fff21867ffffc0f 0xa3fff21867ffffc0

def z94 : W := mkw 0xbff6ffb55af40360 0x4bff6ffb55af4036 0xfffffffffffc03ff 0xffffffffffffc03f

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004104180000009 0xcc00410418000000

def z96 : W := mkw 0x4224041900087004 0x0422404190008700 0x006000380000e000 0x0006000380000e00

def z97 : W := mkw 0x127f006e050bf890 0x3127f006e050bf89 0x407f007e0003fc00 0x8407f007e0003fc0

def z98 : W := mkw 0x0224000000085000 0x0022400000008500 0x06640000107ffc0b 0xa06640000107ffc0

def z99 : W := mkw 0x1850a02400000000 0x01850a0240000000 0xf9fff1ffe000000f 0xdf9fff1ffe000000

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x81871181e0000008 0x081871181e000000

def z101 : W := mkw 0x377600000318d000 0x2377600000318d00 0x3e600000139ce002 0x03e600000139ce00

def z102 : W := mkw 0x422456dbb02d77be 0x0422456dbb02d77b 0xc664fffff07ffffb 0xfc664fffff07ffff

def z103 : W := mkw 0x1858a02605828050 0x11858a0260582805 0x381820060f800074 0x0381820060f80007

def z104 : W := mkw 0x5a7cf67f95aff7dc 0x15a7cf67f95aff7d 0xfe7cfe7f9fffffff 0xffe7cfe7f9ffffff

def z105 : W := mkw 0x35db10c2af738dba 0x235db10c2af738db 0xf99f31c7efe31ffd 0xef99f31c7efe31ff

def z106 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x401f0047ec631ff0 0xa401f0047ec631ff

def z107 : W := mkw 0x3ff7bdb5e8600d2a 0x43ff7bdb5e8600d2 0xffffffffe0601c0f 0xdffffffffe0601c0

def z108 : W := mkw 0x422c565b95aff7dc 0x1422c565b95aff7d 0xc664de799ffffffb 0xfc664de799ffffff

def z109 : W := mkw 0xad80bb800a740120 0x0ad80bb800a74012 0xbf80ff80007c000f 0x5bf80ff80007c000

def z110 : W := mkw 0x37f700000b58d800 0x237f700000b58d80 0x3fe7000013fcfc0a 0x03fe7000013fcfc0

def z111 : W := mkw 0x42245619902c770c 0x042245619902c770 0x8664de39907cfc0a 0x18664de39907cfc0

def z112 : W := mkw 0x1850e06e1181a2d0 0x11850e06e1181a2d 0x7860e07e1380e3f2 0x57860e07e1380e3f

def z113 : W := mkw 0x0008004204030090 0x0000800420403009 0x401820460c0303f5 0xe401820460c0303f

def z114 : W := mkw 0x1859e06eb583aeda 0x11859e06eb583aed 0x787fe07fff83fff7 0xf787fe07fff83fff

def z115 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc7fffffff07fff8f 0xfc7fffffff07fff8

def z116 : W := mkw 0x42245659902d778c 0x042245659902d778 0x86041e01907fff88 0x286041e01907fff8

def z117 : W := mkw 0x0000404810012280 0x0000040481001228 0x4060c0781003e383 0xf4060c0781003e38

def z118 : W := mkw 0x3f76ed3d5180a240 0x53f76ed3d5180a24 0x3e60ce381380e002 0x13e60ce381380e00

def z119 : W := mkw 0x4008524a95aff7dc 0x14008524a95aff7d 0x000000001ffffff0 0x2000000001ffffff

def z120 : W := mkw 0x000010c2a02105ba 0x0000010c2a02105b 0x00000000000003f0 0x000000000000003f

def z121 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0x3fffce380000000f 0x93fffce380000000

def z122 : W := mkw 0x008900000c420800 0x0008900000c42080 0xc19f31c7ec631c0d 0xec19f31c7ec631c0

def z123 : W := mkw 0x8000528010a40360 0x08000528010a4036 0x00000000000003f0 0x000000000000003f

def z124 : W := mkw 0x02245200102c5300 0x002245200102c530 0x8664de00107fff8b 0xf8664de00107fff8

def z125 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xbfe7dfb9e000000a 0x1bfe7dfb9e000000

def z126 : W := mkw 0x3ddba9244f528800 0x63ddba9244f52880 0x399b21866f800004 0x0399b21866f80000

def z127 : W := mkw 0x8889fbc2bce70ffa 0x08889fbc2bce70ff 0xc19fffc7ec631ffd 0xfc19fffc7ec631ff

def z128 : W := mkw 0x808952c2bef70ffa 0x0808952c2bef70ff 0xc19f31c7ffff1ffd 0xec19f31c7ffff1ff

def z129 : W := mkw 0x0000104080210588 0x0000010408021058 0x0000000000631f80 0x20000000000631f8

def z130 : W := mkw 0x7f7eff7fd5aff7dc 0x57f7eff7fd5aff7d 0xffffffffffffffff 0xffffffffffffffff

def z131 : W := mkw 0x008910c2af7bddba 0x2008910c2af7bddb 0xc19f31c7fffffffd 0xec19f31c7fffffff

def z132 : W := mkw 0xad80ffb55af40360 0x4ad80ffb55af4036 0xff80fffffffc03ff 0x7ff80fffffffc03f

def z133 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x4078e07e0003e3f0 0xd4078e07e0003e3f

def z134 : W := mkw 0x37ff10800f7ad920 0x237ff10800f7ad92 0xbfff31801fffffff 0xebfff31801ffffff

def z135 : W := mkw 0x1850e02c1180a240 0x11850e02c1180a24 0x3860e0381f80e3f7 0x73860e0381f80e3f

def z136 : W := mkw 0x1058000005028000 0x0105800000502800 0x381800000f800004 0x0381800000f80000

def z137 : W := mkw 0x0008004a0503a090 0x10008004a0503a09 0x000000000003e000 0x0000000000003e00

def z138 : W := mkw 0x3fffe0001fdada40 0x23fffe0001fdada4 0x3fffe0001fffffff 0xf3fffe0001ffffff

def z139 : W := mkw 0xad88fbc21ef703f0 0x0ad88fbc21ef703f 0xff98ffc61fff03ff 0xfff98ffc61fff03f

def z140 : W := mkw 0x27a70d114a585800 0x627a70d114a58580 0x87871f81e07c1c08 0x087871f81e07c1c0

def z141 : W := mkw 0x400000488009748c 0x0400000488009748 0x000000000003fc00 0x0000000000003fc0

def z142 : W := mkw 0x00811080a8600d2a 0x000811080a8600d2 0x81871181e0601c08 0x081871181e0601c0

def z143 : W := mkw 0x377600000318d000 0x2377600000318d00 0x3fff0000139ce00f 0x83fff0000139ce00

def z144 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc00031c7ec631ff0 0x6c00031c7ec631ff

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0x006000001003e003 0xa006000001003e00

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000001f800007 0x2380000001f80000

def z147 : W := mkw 0x3d52a92440000000 0x43d52a9244000000 0xbf9bff866000000f 0x5bf9bff866000000

def z148 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0xffff31c7fffffc0f 0xeffff31c7fffffc0

def z149 : W := mkw 0x2f26ad1140000000 0x42f26ad114000000 0xbf87ff81e000000f 0x5bf87ff81e000000

def z150 : W := mkw 0x8800fb8010a40360 0x08800fb8010a4036 0x8000ff80000003f0 0x58000ff80000003f

def z151 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x019b21866c631ff4 0x2019b21866c631ff

def z152 : W := mkw 0x0000404a108122d0 0x10000404a108122d 0x00000000000003f0 0x000000000000003f

def z153 : W := mkw 0x0000108000200120 0x0000010800020012 0x80003180000003f0 0x480003180000003f

def z154 : W := mkw 0x3f7ee06e179bf2d0 0x33f7ee06e179bf2d 0x7e78e07e1f9fe3f7 0xf7e78e07e1f9fe3f

def z155 : W := mkw 0x422d045ba40b7c9e 0x0422d045ba40b7c9 0x407f007fe003fc00 0x8407f007fe003fc0

def z156 : W := mkw 0x008100000a585800 0x2008100000a58580 0x00000000007c1c00 0x000000000007c1c0

def z157 : W := mkw 0x527f5659952fff8c 0x2527f5659952fff8 0xc67fde79907fff8b 0xfc67fde79907fff8

def z158 : W := mkw 0x42245659902d778c 0x042245659902d778 0x40640079907fff80 0xa40640079907fff8

def z159 : W := mkw 0x3f7eed7f5583a2d0 0x53f7eed7f5583a2d 0xffffffffff83e3ff 0xfffffffffff83e3f

def z160 : W := mkw 0x0000104080210588 0x0000010408021058 0xc000104180000380 0x4c00010418000038

def z161 : W := mkw 0xbdd8fbee1ff7a3f0 0x1bdd8fbee1ff7a3f 0xfff8fffe1fffe3ff 0xffff8fffe1fffe3f

def z162 : W := mkw 0x2d00a90000000000 0x02d00a9000000000 0x3980218000000004 0x0398021800000000

def z163 : W := mkw 0x27a71080aa785d2a 0x227a71080aa785d2 0x87871181e07c1c08 0x087871181e07c1c0

def z164 : W := mkw 0x4000461910042204 0x0400046191004220 0x0000ce3800000000 0x10000ce380000000

def z165 : W := mkw 0x527c5659952ff78c 0x0527c5659952ff78 0xfe7cde799fffff8f 0xffe7cde799fffff8

def z166 : W := mkw 0x3fffe06e1fdbfad0 0x33fffe06e1fdbfad 0x7fffe07e1fffffff 0xf7fffe07e1ffffff

def z167 : W := mkw 0xafa4fb801afc5360 0x0afa4fb801afc536 0xbfe4ff801fffffff 0xfbfe4ff801ffffff

def z168 : W := mkw 0x27af00000e5a5800 0x227af00000e5a580 0x079f00000c7f1c0d 0xa079f00000c7f1c0

def z169 : W := mkw 0x0000520010240300 0x0000052001024030 0x8600de00107c038b 0x78600de00107c038

def z170 : W := mkw 0xbffffb801ffedb60 0x2bffffb801ffedb6 0xbfffff801fffffff 0xfbfffff801ffffff

def z171 : W := mkw 0x42244659100d7284 0x042244659100d728 0x4660ce78101fe383 0xf4660ce78101fe38

def z172 : W := mkw 0x42ad56dbbc6f7fbe 0x042ad56dbbc6f7fb 0xc664de799c7ffffb 0xfc664de799c7ffff

def z173 : W := mkw 0x0080108008600120 0x0008010800860012 0x818031800c6003fd 0x6818031800c6003f

def z174 : W := mkw 0x67a716118a7c5d0c 0x267a716118a7c5d0 0x87871e01807c1c08 0x087871e01807c1c0

def z175 : W := mkw 0x3776000000085000 0x0377600000008500 0x3fff0000107ffc0f 0xa3fff0000107ffc0

def z176 : W := mkw 0x377e0000071ad000 0x2377e0000071ad00 0x3e7800001f9fe007 0xa3e7800001f9fe00

def z177 : W := mkw 0x18d8f0ee1de3a3f0 0x118d8f0ee1de3a3f 0xf9f8f1fe1fe3e3ff 0xff9f8f1fe1fe3e3f

def z178 : W := mkw 0x0224000000085000 0x0022400000008500 0x06040000007c1c08 0x006040000007c1c0

def z179 : W := mkw 0x0224041100085000 0x0022404110008500 0xc664de79907ffc0b 0xfc664de79907ffc0

def z180 : W := mkw 0x3ffff0eebffbfffa 0x33ffff0eebffbfff 0xfffff1ffffffffff 0xffffff1fffffffff

def z181 : W := mkw 0x12ff00000d4ad800 0x212ff00000d4ad80 0x01ff00000c63fc0d 0xa01ff00000c63fc0

def z182 : W := mkw 0xad89fb823ef60b72 0x0ad89fb823ef60b7 0xbf9bff867ffc03ff 0x7bf9bff867ffc03f

def z183 : W := mkw 0x258000000a500000 0x0258000000a50000 0x3f8000001ffc000f 0x23f8000001ffc000

def z184 : W := mkw 0x000010c2a02105ba 0x0000010c2a02105b 0xc00031c7e00003f0 0x4c00031c7e00003f

def z185 : W := mkw 0x0000041100000000 0x0000004110000000 0xc000de7980000000 0x5c000de798000000

def z186 : W := mkw 0x8800a98000800060 0x08800a9800080006 0x0000218000000070 0x0000021800000007

def z187 : W := mkw 0xad80a9800ad00060 0x0ad80a9800ad0006 0x398021800f800074 0x0398021800f80007

def z188 : W := mkw 0xefa4ffd99afd77ec 0x0efa4ffd99afd77e 0xffe4fff99fffffff 0xfffe4fff99ffffff

def z189 : W := mkw 0x3fffe02c1fdafa40 0x33fffe02c1fdafa4 0x3fffc0381ffffc0f 0xb3fffc0381ffffc0

def z190 : W := mkw 0xad00eb0012940240 0x0ad00eb001294024 0xbf80ff80139c000f 0x5bf80ff80139c000

def z191 : W := mkw 0x3ff6bdb548600120 0x43ff6bdb54860012 0xffffffffec6003ff 0xfffffffffec6003f

def z192 : W := mkw 0x0808e042148302d0 0x00808e042148302d 0x7818e0461f8303f7 0xf7818e0461f8303f

def z193 : W := mkw 0xfffcffff9ffff7fc 0x1fffcffff9ffff7f 0xfffcffff9fffffff 0xffffcffff9ffffff

def z194 : W := mkw 0x3d52ad3540000000 0x43d52ad354000000 0xf99bffffe0000004 0x5f99bffffe000000

def z195 : W := mkw 0x8800eb0010840240 0x08800eb001084024 0x0000ce0000000000 0x10000ce000000000

def z196 : W := mkw 0x8800fb8010a40360 0x08800fb8010a4036 0xb800ff801f8003f7 0x7b800ff801f8003f

def z197 : W := mkw 0x5858f26e95aff7dc 0x15858f26e95aff7d 0x7878e07e1ffffff7 0xf7878e07e1ffffff

def z198 : W := mkw 0x37ff0d114f5ad800 0x637ff0d114f5ad80 0xbfff1f81fffffc0f 0xabfff1f81fffffc0

def z199 : W := mkw 0x77764619131cf204 0x277764619131cf20 0x3e60ce38139ce002 0x13e60ce38139ce00

def z200 : W := mkw 0x0000006e00012090 0x10000006e0001209 0x4000007e00000000 0x04000007e0000000

def z201 : W := mkw 0x000810c2a42305ba 0x0000810c2a42305b 0xc01831c7ec0303f5 0xec01831c7ec0303f

def z202 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0x8780ff80007c03f8 0x58780ff80007c03f

def z203 : W := mkw 0x1a7fe06e158bfad0 0x31a7fe06e158bfad 0x787fe07e1f83fff7 0xf787fe07e1f83fff

def z204 : W := mkw 0x1858a06e0503a090 0x11858a06e0503a09 0x7878e07e0003e007 0xd7878e07e0003e00

def z205 : W := mkw 0x0889f0eebce32ffa 0x10889f0eebce32ff 0xc19ff1ffec631ffd 0xfc19ff1ffec631ff

def z206 : W := mkw 0x3f76ed7f508122d0 0x53f76ed7f508122d 0xffffffffe00003ff 0xdffffffffe00003f

def z207 : W := mkw 0x77ff52489f7fff8c 0x277ff52489f7fff8 0x3fff00001fffff8f 0xa3fff00001fffff8

def z208 : W := mkw 0xbffffbc2bfffdffa 0x2bffffbc2bfffdff 0xffffffc7ffffffff 0xfffffffc7fffffff

def z209 : W := mkw 0x0224041100000000 0x0022404110000000 0x0660ce3800000002 0x10660ce380000000

def z210 : W := mkw 0x408952cabc6f7fbe 0x0408952cabc6f7fb 0x000000001c7ffff0 0x2000000001c7ffff

def z211 : W := mkw 0x0089404a1fdbfad0 0x30089404a1fdbfad 0x000000001ffffff0 0x2000000001ffffff

def z212 : W := mkw 0x02ad14d3ac630dba 0x002ad14d3ac630db 0xc7ffffffec631fff 0xfc7ffffffec631ff

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x8600de000000000b 0x58600de000000000

def z214 : W := mkw 0x1858ed7f5583a2d0 0x51858ed7f5583a2d 0xf878ffffff83e3f7 0xff878ffffff83e3f

def z215 : W := mkw 0x37ff10c2af7bddba 0x237ff10c2af7bddb 0xffff31c7ffffffff 0xeffff31c7fffffff

def z216 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc604de79807c1f88 0x5c604de79807c1f8

def z217 : W := mkw 0x3fffed7f5fdbfad0 0x73fffed7f5fdbfad 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0xbfffffb55ffedb60 0x6bfffffb55ffedb6 0xffffffffffffffff 0xffffffffffffffff

def z219 : W := mkw 0x27a400000a585000 0x027a400000a58500 0x3fe400001ffffc0f 0xa3fe400001ffffc0

def z220 : W := mkw 0xa5811b80aa740d2a 0x0a5811b80aa740d2 0x87871f81e07c1c08 0x087871f81e07c1c0

def z221 : W := mkw 0x0800ed7f508122d0 0x50800ed7f508122d 0xc000ffffe00003f0 0x5c000ffffe00003f

def z222 : W := mkw 0x527c047f850bf49c 0x1527c047f850bf49 0x407c007f8003fc00 0x8407c007f8003fc0

def z223 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xff9fffc7fffc03ff 0xfff9fffc7fffc03f

def z224 : W := mkw 0x3ddba9a66c420832 0x43ddba9a66c42083 0x399b21866c000074 0x0399b21866c00007

def z225 : W := mkw 0x2d00a90000000000 0x02d00a9000000000 0xbf80ff800000000f 0x5bf80ff800000000

def z226 : W := mkw 0x008900000c420800 0x0008900000c42080 0x019f00000c631c0d 0xa019f00000c631c0

def z227 : W := mkw 0x1050002400000000 0x0105000240000000 0x4078007e00000000 0x84078007e0000000

def z228 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x39ff00000f83fc04 0x839ff00000f83fc0

def z229 : W := mkw 0x1850e02c1180a240 0x11850e02c1180a24 0x7878e07e1380e007 0xd7878e07e1380e00

def z230 : W := mkw 0xefa4ff919afc576c 0x0efa4ff919afc576 0xbf84ff819ffc1fff 0x7bf84ff819ffc1ff

def z231 : W := mkw 0x105840481503a280 0x0105840481503a28 0x7878c0781f83e387 0xf7878c0781f83e38

def z232 : W := mkw 0xbdd9fbeebff7affa 0x1bdd9fbeebff7aff 0xffffffffffffffff 0xffffffffffffffff

def z233 : W := mkw 0xad80fbc09af507e8 0x0ad80fbc09af507e 0xff84ffc19fff1fff 0xfff84ffc19fff1ff

def z234 : W := mkw 0x2726000000000000 0x0272600000000000 0x0787000000000008 0x0078700000000000

def z235 : W := mkw 0x0800a00000000000 0x00800a0000000000 0x3800e00000000007 0x53800e0000000000

def z236 : W := mkw 0x0800f20010a40340 0x00800f20010a4034 0xbe00fe001ffc03ff 0x7be00fe001ffc03f

def z237 : W := mkw 0x77765659933df78c 0x277765659933df78 0xfe64de7993ffff8b 0xffe64de7993ffff8

def z238 : W := mkw 0x1850a02400000000 0x01850a0240000000 0x7878e07e00000007 0xd7878e07e0000000

def z239 : W := mkw 0x0808e06e1583a2d0 0x10808e06e1583a2d 0x4000e07e1f83e3f0 0x74000e07e1f83e3f

def z240 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc064de798003ff80 0xdc064de798003ff8

def z241 : W := mkw 0x2d00a90000000000 0x02d00a9000000000 0x3e00ce0000000002 0x13e00ce000000000

def z242 : W := mkw 0x37ff10408f7bdd88 0x237ff10408f7bdd8 0xffff10419fffff8f 0xeffff10419fffff8

def z243 : W := mkw 0x2d00a90000000000 0x02d00a9000000000 0xff9fffc7e000000f 0xdff9fffc7e000000

def z244 : W := mkw 0x2d89b9c2ac630dba 0x02d89b9c2ac630db 0xff9fffc7ec631fff 0xfff9fffc7ec631ff

def z245 : W := mkw 0x35db00000f528800 0x235db00000f52880 0x3f9b00001ffc000f 0x23f9b00001ffc000

def z246 : W := mkw 0xbfffeb001fdeda40 0x2bfffeb001fdeda4 0x3fffce001ffffc0f 0xb3fffce001ffffc0

def z247 : W := mkw 0x422414598029758c 0x0422414598029758 0xc06410798063ff89 0xec06410798063ff8

def z248 : W := mkw 0xad80fbee1af523f0 0x1ad80fbee1af523f 0xff80fffe1ffc03ff 0x7ff80fffe1ffc03f

def z249 : W := mkw 0xe7a45fd99a7d77ac 0x0e7a45fd99a7d77a 0xc7e4dff9907fff8b 0xfc7e4dff9907fff8

def z250 : W := mkw 0xad89fb801ffedb60 0x2ad89fb801ffedb6 0xbf80ff801fffffff 0x7bf80ff801ffffff

def z251 : W := mkw 0x3f76ad3540085000 0x43f76ad354008500 0xfffffffff07ffc0f 0xffffffffff07ffc0

def z252 : W := mkw 0x127f0000050ad800 0x2127f0000050ad80 0x067f0000107ffc0b 0xa067f0000107ffc0

def z253 : W := mkw 0x67261f11c02c550c 0x467261f11c02c550 0x87871f81e07c1c08 0x087871f81e07c1c0

def z254 : W := mkw 0x1050000001008000 0x0105000000100800 0x386000001380e002 0x0386000001380e00

def z255 : W := mkw 0x18d9f0eebde3affa 0x118d9f0eebde3aff 0x7878e07e1fe3fff7 0xf7878e07e1fe3fff

def z256 : W := mkw 0x3f7eed7f5583a2d0 0x53f7eed7f5583a2d 0x7e78ee7e1f83e3f7 0xf7e78ee7e1f83e3f

def z257 : W := mkw 0x3f7ee06e1583a2d0 0x13f7ee06e1583a2d 0x7fffe07e1f83e3ff 0xf7fffe07e1f83e3f

def z258 : W := mkw 0xfff6fffddafd77ec 0x4fff6fffddafd77e 0xffffffffffffffff 0xffffffffffffffff

def z259 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0x3e60ce3800000002 0x13e60ce380000000

def z260 : W := mkw 0x2d80b98008600120 0x02d80b9800860012 0xbf80ff800c6003ff 0x7bf80ff800c6003f

def z261 : W := mkw 0x8800fbee10a523f0 0x18800fbee10a523f 0xc000fffe000003f0 0x5c000fffe000003f

def z262 : W := mkw 0xbffeffff5ff7a3f0 0x5bffeffff5ff7a3f 0xffffffffffffe3ff 0xfffffffffffffe3f

def z263 : W := mkw 0x127e047f4503a090 0x5127e047f4503a09 0x407f007fe003e000 0x8407f007fe003e00

def z264 : W := mkw 0x1858a02605828050 0x11858a0260582805 0x7878e07e0f800077 0xd7878e07e0f80007

def z265 : W := mkw 0x000000000318d000 0x2000000000318d00 0x00000000139ce000 0x000000000139ce00

def z266 : W := mkw 0x3f76a02400000000 0x03f76a0240000000 0x7fffe07e0000000f 0xd7fffe07e0000000

def z267 : W := mkw 0xbd58eb6e1797a2d0 0x1bd58eb6e1797a2d 0x7e78ee7e1f9fe3f7 0xf7e78ee7e1f9fe3f

def z268 : W := mkw 0x0224404810097280 0x0022440481009728 0x4664c078107fff8b 0xf4664c078107fff8

def z269 : W := mkw 0xbdd0fba41af40360 0x0bdd0fba41af4036 0xfff8fffe1ffc03ff 0xffff8fffe1ffc03f

def z270 : W := mkw 0x1058000005028000 0x0105800000502800 0x007800000003e000 0x8007800000003e00

def z271 : W := mkw 0xad81fb80baf40f6a 0x0ad81fb80baf40f6 0xbf87ff81fffc1fff 0x7bf87ff81fffc1ff

def z272 : W := mkw 0x0800e06e108122d0 0x10800e06e108122d 0x7800e07e1f8003f7 0x77800e07e1f8003f

def z273 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0x79ff21ffe0000004 0x879ff21ffe000000

def z274 : W := mkw 0x400016118024050c 0x0400016118024050 0x80001e0180000000 0x080001e018000000

def z275 : W := mkw 0xbdd8e9ee1fd3a2f0 0x1bdd8e9ee1fd3a2f 0x79f8e1fe1f83e3f7 0xf79f8e1fe1f83e3f

def z276 : W := mkw 0x27af10c2ae7b5dba 0x227af10c2ae7b5db 0xc79f31c7ec7f1ffd 0xec79f31c7ec7f1ff

def z277 : W := mkw 0x37ff04110f5ad800 0x237ff04110f5ad80 0xffffde799ffffc0f 0xfffffde799ffffc0

def z278 : W := mkw 0x1059006ea503ac9a 0x11059006ea503ac9 0x407f007fe003fc00 0x8407f007fe003fc0

def z279 : W := mkw 0x400052489025278c 0x0400052489025278 0x0000000000000380 0x0000000000000038

def z280 : W := mkw 0xad89fb801ef60b60 0x0ad89fb801ef60b6 0xbf9fff801fff1fff 0xfbf9fff801fff1ff

def z281 : W := mkw 0x9858fbee15a7a3f0 0x19858fbee15a7a3f 0xf878fffe1f83e3f7 0xff878fffe1f83e3f

def z282 : W := mkw 0x3f76ad354318d000 0x63f76ad354318d00 0x3e60ce38139ce002 0x13e60ce38139ce00

def z283 : W := mkw 0x408952489f7fff8c 0x2408952489f7fff8 0x000000001fffff80 0x2000000001fffff8

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x019f00000000000d 0x8019f00000000000

def z285 : W := mkw 0x4a24f67f90ad77dc 0x14a24f67f90ad77d 0xc664fe7f907ffffb 0xfc664fe7f907ffff

def z286 : W := mkw 0x422404598009748c 0x0422404598009748 0xc664de798003fc0b 0xdc664de798003fc0

def z287 : W := mkw 0x37ff00822f5ad832 0x237ff00822f5ad83 0x3fff21867ffffc7f 0xa3fff21867ffffc7

def z288 : W := mkw 0xed80fbc89afd77ec 0x0ed80fbc89afd77e 0xbf80ff801fffffff 0x7bf80ff801ffffff

def z289 : W := mkw 0x40004208100c7204 0x040004208100c720 0x00000000101ce000 0x000000000101ce00

def z290 : W := mkw 0x02ad00000c4a5800 0x002ad00000c4a580 0x07ff00001c7ffc0f 0xa07ff00001c7ffc0

def z291 : W := mkw 0x808952c2bef70ffa 0x0808952c2bef70ff 0x000000001fff1ff0 0x2000000001fff1ff

def z292 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc00410418c631ff9 0xec00410418c631ff

def z293 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x81871181ec631ff8 0x281871181ec631ff

def z294 : W := mkw 0xad88fbca1ff7a3f0 0x1ad88fbca1ff7a3f 0xbf80ff801fffe3ff 0x7bf80ff801fffe3f

def z295 : W := mkw 0x0008104284230598 0x0000810428423059 0xc01c30478c631ffd 0xec01c30478c631ff

def z296 : W := mkw 0xafa6ff915af40360 0x4afa6ff915af4036 0xbf87ff81fffc03ff 0x7bf87ff81fffc03f

def z297 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc19f11c7e0631c08 0x8c19f11c7e0631c0

def z298 : W := mkw 0x258000000a500000 0x0258000000a50000 0x398000000f800004 0x0398000000f80000

def z299 : W := mkw 0x008900822c420832 0x0008900822c42083 0xc19f31c7ec00007d 0xcc19f31c7ec00007

def z300 : W := mkw 0x400056599025278c 0x0400056599025278 0xc004de7980631f89 0xfc004de7980631f8

def z301 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0x3e00ce001ffc03f2 0x33e00ce001ffc03f

def z302 : W := mkw 0x1276043540000000 0x4127604354000000 0xc1ff31ffe000000d 0xcc1ff31ffe000000

def z303 : W := mkw 0xad00fb8010a40360 0x0ad00fb8010a4036 0xbf80ff80000003ff 0x5bf80ff80000003f

def z304 : W := mkw 0x0800a90000000000 0x00800a9000000000 0x8000ff8000000000 0x58000ff800000000

def z305 : W := mkw 0x1052002440000000 0x4105200244000000 0x001b000660000000 0x0001b00066000000

def z306 : W := mkw 0x10d900000d428800 0x010d900000d42880 0x39ff00001fe3fc0f 0xa39ff00001fe3fc0

def z307 : W := mkw 0x422404598009748c 0x0422404598009748 0x406400798003fc00 0x8406400798003fc0

def z308 : W := mkw 0x1058406e1583a2d0 0x11058406e1583a2d 0x4078007e1f83e3f0 0xa4078007e1f83e3f

def z309 : W := mkw 0x77ff56dbbf7fffbe 0x277ff56dbbf7fffb 0xffffffffffffffff 0xffffffffffffffff

def z310 : W := mkw 0x0000524090250788 0x0000052409025078 0xc604de41907f1f8b 0xfc604de41907f1f8

def z311 : W := mkw 0x0800a02600800050 0x10800a0260080005 0x0000200600000070 0x0000020060000007

def z312 : W := mkw 0x377e000005028000 0x0377e00000502800 0x3fff00001f83e00f 0xa3fff00001f83e00

def z313 : W := mkw 0xbf76ef3552940240 0x4bf76ef355294024 0x3e60ce38139c0002 0x13e60ce38139c000

def z314 : W := mkw 0xbffffbee1ffffbf0 0x3bffffbee1ffffbf 0xfffffffe1fffffff 0xffffffffe1ffffff

def z315 : W := mkw 0x37f700000a585800 0x237f700000a58580 0x3fff0000007c1c0f 0x83fff0000007c1c0

def z316 : W := mkw 0xad80e9801ad00260 0x0ad80e9801ad0026 0x3980e1801f8003f7 0x73980e1801f8003f

def z317 : W := mkw 0xbdd8fb801ff68360 0x0bdd8fb801ff6836 0xbff8ff801fffe3ff 0xfbff8ff801fffe3f

def z318 : W := mkw 0x0227000000085800 0x2022700000008580 0x0007000000001c00 0x00007000000001c0

def z319 : W := mkw 0x3f76ed3550800240 0x43f76ed355080024 0xffffffffff8003ff 0xfffffffffff8003f

def z320 : W := mkw 0xbff6ffb55af40360 0x4bff6ffb55af4036 0xbfe0ffb81ffc03ff 0x7bfe0ffb81ffc03f

def z321 : W := mkw 0x3f7ead3545028000 0x43f7ead354502800 0xffffffffff83e00f 0xfffffffffff83e00

def z322 : W := mkw 0x0808e04a1583a2d0 0x10808e04a1583a2d 0x3800e0001f83e3f7 0x73800e0001f83e3f

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x818031800000000d 0x4818031800000000

def z324 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x401820460c631ff5 0xe401820460c631ff

def z325 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3e6000001ffffc02 0x23e6000001ffffc0

def z326 : W := mkw 0x18d9b0e6ade38dfa 0x118d9b0e6ade38df 0xf99f31c7efe31ffd 0xef99f31c7efe31ff

def z327 : W := mkw 0x1858e02615828250 0x11858e0261582825 0x3818e0061f8003f7 0x73818e0061f8003f

def z328 : W := mkw 0x0000404810012280 0x0000040481001228 0x4000c07800000380 0x54000c0780000038

def z329 : W := mkw 0xb7ff1b800f7ed920 0x2b7ff1b800f7ed92 0xbfff1f801ffffc0f 0xabfff1f801ffffc0

def z330 : W := mkw 0x008910800c620920 0x0008910800c62092 0x819f31800c631ffd 0xe819f31800c631ff

def z331 : W := mkw 0x35db00000f5ad800 0x235db00000f5ad80 0x399b00001ffffc04 0x2399b00001ffffc0

def z332 : W := mkw 0x3f7ead3745828050 0x53f7ead374582805 0xffffffffef80007f 0xdffffffffef80007

def z333 : W := mkw 0xbff6adb54ad00060 0x4bff6adb54ad0006 0xffffffffef80007f 0xdffffffffef80007

def z334 : W := mkw 0x27260d1140000000 0x427260d114000000 0xc7e7dff9e000000b 0xdc7e7dff9e000000

def z335 : W := mkw 0x42ad56599f7fff8c 0x242ad56599f7fff8 0xc664de799fffff8b 0xfc664de799fffff8

def z336 : W := mkw 0x35db00822f528832 0x235db00822f52883 0x399b21866f800074 0x0399b21866f80007

def z337 : W := mkw 0x400056dbb02527be 0x0400056dbb02527b 0xc000ffffe00003f0 0x5c000ffffe00003f

def z338 : W := mkw 0x008950cabde3affa 0x1008950cabde3aff 0x000000001fe3fff0 0x2000000001fe3fff

def z339 : W := mkw 0x1058004205038090 0x0105800420503809 0x787820461f83e3f7 0xe787820461f83e3f

def z340 : W := mkw 0x42244619100c7204 0x042244619100c720 0x0664ce38107ffc0b 0xb0664ce38107ffc0

def z341 : W := mkw 0x37ff40481f5bfa80 0x237ff40481f5bfa8 0x7fffc0781fffff8f 0xf7fffc0781fffff8

def z342 : W := mkw 0x000040081180a240 0x1000040081180a24 0x000000001380e000 0x0000000001380e00

def z343 : W := mkw 0x0000004080010488 0x0000000408001048 0x4004004180031c00 0x84004004180031c0

def z344 : W := mkw 0x0800e00010800240 0x00800e0001080024 0x0000e000000003f0 0x50000e000000003f

def z345 : W := mkw 0x5a7ce47f958bf6dc 0x15a7ce47f958bf6d 0x787ce07f9f83fff7 0xf787ce07f9f83fff

def z346 : W := mkw 0x77ff04598f5bfc8c 0x277ff04598f5bfc8 0x7fff00799ffffc0f 0xa7fff00799ffffc0

def z347 : W := mkw 0x3fffad354c420800 0x43fffad354c42080 0xffffffffec631c0f 0xfffffffffec631c0

def z348 : W := mkw 0x127f0435450ad800 0x6127f0435450ad80 0x407f007fe003fc00 0x8407f007fe003fc0

def z349 : W := mkw 0x1850e06e108122d0 0x11850e06e108122d 0x7878e07e000003f7 0xd7878e07e000003f

def z350 : W := mkw 0x10d910eead63adba 0x110d910eead63adb 0xc1ff31ffec63fffd 0xec1ff31ffec63fff

def z351 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc19b31c7ec0003f4 0x4c19b31c7ec0003f

def z352 : W := mkw 0x1a7ce06e158bf2d0 0x11a7ce06e158bf2d 0x7e7ce07e1fffffff 0xf7e7ce07e1ffffff

def z353 : W := mkw 0x422404118008540c 0x0422404118008540 0x0004000180001c00 0x00004000180001c0

def z354 : W := mkw 0x422d565bb42f7f9e 0x0422d565bb42f7f9 0xc67fde7ff07fff8b 0xfc67fde7ff07fff8

def z355 : W := mkw 0x77765659902d778c 0x077765659902d778 0xffffde79907fff8f 0xfffffde79907fff8

def z356 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc660de79901ce382 0x5c660de79901ce38

def z357 : W := mkw 0x3f76bd75c0210588 0x43f76bd75c021058 0xffffffffe0631f8f 0xfffffffffe0631f8

def z358 : W := mkw 0x008900c2ac430cba 0x0008900c2ac430cb 0x419f21c7ec031c74 0x8419f21c7ec031c7

def z359 : W := mkw 0x3f76ed7d50012280 0x43f76ed7d5001228 0xfffffffff003e38f 0xffffffffff003e38

def z360 : W := mkw 0x3776000000000000 0x0377600000000000 0x3fff00000000000f 0x83fff00000000000

def z361 : W := mkw 0x0009000004020800 0x0000900000402080 0x001f000000031c00 0x8001f000000031c0

def z362 : W := mkw 0x7ffffffffc6f7fbe 0x47ffffffffc6f7fb 0xfffffffffc7fffff 0xffffffffffc7ffff

def z363 : W := mkw 0x37ff404a1fdbfad0 0x337ff404a1fdbfad 0x3fff00001fffffff 0xa3fff00001ffffff

def z364 : W := mkw 0x1058006e0503a090 0x11058006e0503a09 0x7878007e1f83e007 0xa7878007e1f83e00

def z365 : W := mkw 0x1850ad3540000000 0x41850ad354000000 0xf878ffffe0000007 0xdf878ffffe000000

def z366 : W := mkw 0x00090042a4030c9a 0x000090042a4030c9 0x0000000000031c00 0x00000000000031c0

def z367 : W := mkw 0x00000d1140000000 0x400000d114000000 0x80001f81e0000000 0x080001f81e000000

def z368 : W := mkw 0x77ff16118f7edd0c 0x277ff16118f7edd0 0xbfff1e019ffffc0f 0xabfff1e019ffffc0

def z369 : W := mkw 0xc2a456d99afd77ec 0x0c2a456d99afd77e 0xc664de799ffffffb 0xfc664de799ffffff

def z370 : W := mkw 0x0800e02c10802240 0x10800e02c1080224 0x0000c03800000000 0x10000c0380000000

def z371 : W := mkw 0x008110c2a8610dba 0x0008110c2a8610db 0xc18731c7e0601ff8 0x4c18731c7e0601ff

def z372 : W := mkw 0x3f7fad35450ad800 0x63f7fad35450ad80 0xffffffffe003fc0f 0xdffffffffe003fc0

def z373 : W := mkw 0x0224041100000000 0x0022404110000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z374 : W := mkw 0x5a7ce67f158ff2d4 0x15a7ce67f158ff2d 0x7e78ee7e1f9fe3f7 0xf7e78ee7e1f9fe3f

def z375 : W := mkw 0x3f7ead7f4503a090 0x53f7ead7f4503a09 0xffffffffe003e00f 0xdffffffffe003e00

def z376 : W := mkw 0x42244659900d768c 0x042244659900d768 0x4664ce79901ffc02 0x94664ce79901ffc0

def z377 : W := mkw 0x008810c20c6301b0 0x0008810c20c6301b 0xc19831c60c6303fd 0xec19831c60c6303f

def z378 : W := mkw 0x0000520010240300 0x0000052001024030 0x00000000107c0380 0x200000000107c038

def z379 : W := mkw 0x3f76ad354318d000 0x63f76ad354318d00 0xfffffffff39ce00f 0xdfffffffff39ce00

def z380 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xbfe0ffb80000000f 0x5bfe0ffb80000000

def z381 : W := mkw 0x8800fb8010a40360 0x08800fb8010a4036 0x8600ff80107c03fb 0x78600ff80107c03f

def z382 : W := mkw 0x0224041100000000 0x0022404110000000 0x4064007980000000 0x8406400798000000

def z383 : W := mkw 0x00811080a8600d2a 0x000811080a8600d2 0x0000000000601c00 0x00000000000601c0

def z384 : W := mkw 0x808852ca1ff7a3f0 0x1808852ca1ff7a3f 0x000000001fffe3f0 0x2000000001fffe3f

def z385 : W := mkw 0x0800a92440000000 0x40800a9244000000 0x0000218660000000 0x0000021866000000

def z386 : W := mkw 0x422404598009748c 0x0422404598009748 0x46640079907ffc0b 0xa46640079907ffc0

def z387 : W := mkw 0x0000504890212788 0x0000050489021278 0xc064d0799063ff8b 0xfc064d0799063ff8

def z388 : W := mkw 0xbff6fb801bfcd360 0x2bff6fb801bfcd36 0xbfe0ff801ffce3ff 0x7bfe0ff801ffce3f

def z389 : W := mkw 0x000010c2a02105ba 0x0000010c2a02105b 0xc00431c7e0631ff9 0xec00431c7e0631ff

def z390 : W := mkw 0x3d58e96e1583a2d0 0x13d58e96e1583a2d 0xfff8fffe1f83e3ff 0xffff8fffe1f83e3f

def z391 : W := mkw 0x42a556d9b86d7fae 0x042a556d9b86d7fa 0xc7e7dff9f07fff8b 0xfc7e7dff9f07fff8

def z392 : W := mkw 0xa5801b800a740120 0x0a5801b800a74012 0x87803f800c7c03fd 0x687803f800c7c03f

def z393 : W := mkw 0x80001b8000240120 0x080001b800024012 0x80001f8000000000 0x080001f800000000

def z394 : W := mkw 0x1850a02400000000 0x01850a0240000000 0x3818200600000004 0x0381820060000000

def z395 : W := mkw 0x1858a02405028000 0x01858a0240502800 0x7878e07e1f83e007 0xf7878e07e1f83e00

def z396 : W := mkw 0x808000800ad00060 0x0808000800ad0006 0x000000000f800070 0x0000000000f80007

def z397 : W := mkw 0x37ff52001f7edb00 0x237ff52001f7edb0 0xbfffde001fffff8f 0xfbfffde001fffff8

def z398 : W := mkw 0xc800ffd990a527ec 0x0c800ffd990a527e 0xc000fff9800003f0 0x5c000fff9800003f

def z399 : W := mkw 0xb7ff52801ffedb60 0x2b7ff52801ffedb6 0x3fff00001fffffff 0xa3fff00001ffffff

def z400 : W := mkw 0xad80eb001ad40240 0x0ad80eb001ad4024 0x3f80ce001ffc000f 0x33f80ce001ffc000

def z401 : W := mkw 0xe7a41f918a7c552c 0x0e7a41f918a7c552 0x87841f81807c1c08 0x087841f81807c1c0

def z402 : W := mkw 0xad80eb801ad40260 0x0ad80eb801ad4026 0x3f80ef801f9c0076 0x13f80ef801f9c007

def z403 : W := mkw 0xefadffdbbeff7ffe 0x0efadffdbbeff7ff 0xffffffffffffffff 0xffffffffffffffff

def z404 : W := mkw 0x3fffadb76c420832 0x43fffadb76c42083 0xffffffffec00007f 0xdffffffffec00007

def z405 : W := mkw 0x42245619102c7304 0x042245619102c730 0x8660de38107ce38b 0x78660de38107ce38

def z406 : W := mkw 0x8880f2801af40360 0x08880f2801af4036 0x3800e0001ffc03f7 0x73800e0001ffc03f

def z407 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf80df8013fc000a 0x1bf80df8013fc000

def z408 : W := mkw 0x5276047dc009748c 0x45276047dc009748 0x407f007fe003fc00 0x8407f007fe003fc0

def z409 : W := mkw 0x258300000a500800 0x2258300000a50080 0x0183000000000000 0x0018300000000000

def z410 : W := mkw 0x1858a06e0583a0d0 0x11858a06e0583a0d 0x7878207e0f83e074 0x87878207e0f83e07

def z411 : W := mkw 0x00091042a4230d9a 0x000091042a4230d9 0xc01f1047e0631f89 0xec01f1047e0631f8

def z412 : W := mkw 0x0008004204030090 0x0000800420403009 0x000000000c0303f0 0x2000000000c0303f

def z413 : W := mkw 0xbdd0fbac1bf4a360 0x1bdd0fbac1bf4a36 0xbfe0ffb81ffce3ff 0x7bfe0ffb81ffce3f

def z414 : W := mkw 0x3f76bdf7e02105ba 0x43f76bdf7e02105b 0xffffffffe00003ff 0xdffffffffe00003f

def z415 : W := mkw 0x8880fb8018e40360 0x08880fb8018e4036 0x8180ff800c6003fd 0x78180ff800c6003f

def z416 : W := mkw 0x808052801af40360 0x0808052801af4036 0x818031801ffc03fd 0x6818031801ffc03f

def z417 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0x3ffbefbe60000006 0x13ffbefbe6000000

def z418 : W := mkw 0x0008004204030090 0x0000800420403009 0x4018004600030000 0x8401800460003000

def z419 : W := mkw 0x0080000008400000 0x0008000000840000 0x018000000c60000d 0x2018000000c60000

def z420 : W := mkw 0x127c0000050ad000 0x0127c0000050ad00 0x3e7c00001ffffc0f 0xa3e7c00001ffffc0

def z421 : W := mkw 0x000010c2a02105ba 0x0000010c2a02105b 0xc19f31c7e00003fd 0xcc19f31c7e00003f

def z422 : W := mkw 0x3dd8e06e1fd3a2d0 0x13dd8e06e1fd3a2d 0x7ff8e07e1fffe3ff 0xf7ff8e07e1fffe3f

def z423 : W := mkw 0x7f76ef3d500c7204 0x47f76ef3d500c720 0x3e60ce38101ce002 0x13e60ce38101ce00

def z424 : W := mkw 0x3fffbdf7ef7bddba 0x63fffbdf7ef7bddb 0xffffffffffffffff 0xffffffffffffffff

def z425 : W := mkw 0x40005248902d778c 0x040005248902d778 0xc0041041907fff89 0xec0041041907fff8

def z426 : W := mkw 0x008110c0a8610daa 0x0008110c0a8610da 0xc18711c1e0631f89 0xec18711c1e0631f8

def z427 : W := mkw 0xbff6fb801af40360 0x0bff6fb801af4036 0xbfffff801ffc03ff 0xfbfffff801ffc03f

def z428 : W := mkw 0x1850a02400000000 0x01850a0240000000 0x3860c03800000002 0x13860c0380000000

def z429 : W := mkw 0x400056599025278c 0x0400056599025278 0xc600de79907c038b 0x7c600de79907c038

def z430 : W := mkw 0x0000104080210588 0x0000010408021058 0xc19f31c7e0631f8d 0xec19f31c7e0631f8

def z431 : W := mkw 0x2d00fb0010240300 0x02d00fb001024030 0xbf80ff80107c038f 0x7bf80ff80107c038

def z432 : W := mkw 0x008900000f5ad800 0x2008900000f5ad80 0x019f00001ffffc0d 0xa019f00001ffffc0

def z433 : W := mkw 0x1858f06e95a3a7d8 0x11858f06e95a3a7d 0xf87cf07f9fe3ffff 0xff87cf07f9fe3fff

def z434 : W := mkw 0xad00a90002900040 0x0ad00a9000290004 0x3800000003800000 0x0380000000380000

def z435 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xfe64de798000000b 0xdfe64de798000000

def z436 : W := mkw 0x42ad16d3ac6f5dbe 0x042ad16d3ac6f5db 0xc79f3fc7ec7f1ffd 0xec79f3fc7ec7f1ff

def z437 : W := mkw 0x37ff006e0f5bf890 0x337ff006e0f5bf89 0x7fff007e1ffffc0f 0xa7fff007e1ffffc0

def z438 : W := mkw 0x00001080a020052a 0x000001080a020052 0x80001181e0000000 0x080001181e000000

def z439 : W := mkw 0x0080108008600120 0x0008010800860012 0x000000000c6003f0 0x2000000000c6003f

def z440 : W := mkw 0x3fffad354f5ad800 0x63fffad354f5ad80 0x3fffce381ffffc0f 0xb3fffce381ffffc0

def z441 : W := mkw 0x1850a02401808040 0x11850a0240180804 0x3800000003800000 0x0380000000380000

def z442 : W := mkw 0x40005248902d778c 0x040005248902d778 0x8600de00107fff8b 0x78600de00107fff8

def z443 : W := mkw 0x2500090000000000 0x0250009000000000 0x87801f8000000008 0x087801f800000000

def z444 : W := mkw 0x12ff10c2ad6bddba 0x212ff10c2ad6bddb 0xc1ff31c7ec63fffd 0xec1ff31c7ec63fff

def z445 : W := mkw 0x3ffffdfffde3affa 0x53ffffdfffde3aff 0xffffffffffe3ffff 0xfffffffffffe3fff

def z446 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0xf9fff1ffff83e3ff 0xff9fff1ffff83e3f

def z447 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x3860c0381f83e3f2 0x33860c0381f83e3f

def z448 : W := mkw 0x12ff14f7ec630dba 0x412ff14f7ec630db 0xc1ff31ffec631ffd 0xec1ff31ffec631ff

def z449 : W := mkw 0x0000400010800240 0x0000040001080024 0x000000001f8003f0 0x2000000001f8003f

def z450 : W := mkw 0x0800a00000800040 0x00800a0000080004 0x380020000f800074 0x0380020000f80007

def z451 : W := mkw 0xad00eb0012940240 0x0ad00eb001294024 0x3e00ee001f9c03f7 0x73e00ee001f9c03f

def z452 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3ffb00001f9ce006 0x03ffb00001f9ce00

def z453 : W := mkw 0x008910c2af7bddba 0x2008910c2af7bddb 0x000000001ffffff0 0x2000000001ffffff

def z454 : W := mkw 0x400056599025278c 0x0400056599025278 0xc060de799003e383 0xfc060de799003e38

def z455 : W := mkw 0x3d50a92400000000 0x03d50a9240000000 0xfff8fffe0000000f 0xdfff8fffe0000000

def z456 : W := mkw 0x8800ffb550a40360 0x48800ffb550a4036 0xc000ffffe00003f0 0x5c000ffffe00003f

def z457 : W := mkw 0x42ad56599c6f7f8c 0x042ad56599c6f7f8 0xc7ffde799c7fff8f 0xfc7ffde799c7fff8

def z458 : W := mkw 0x2500000002100000 0x0250000000210000 0x3e000000139c0002 0x03e000000139c000

def z459 : W := mkw 0xad00fb0012b40340 0x0ad00fb0012b4034 0xbe00de0013fc038b 0x7be00de0013fc038

def z460 : W := mkw 0xad00fb8012b40360 0x0ad00fb8012b4036 0xbe00ff80139c03f2 0x5be00ff80139c03f

def z461 : W := mkw 0x37760d3540000000 0x437760d354000000 0xc7ff1fffe0000008 0x8c7ff1fffe000000

def z462 : W := mkw 0x0808e06e148322d0 0x10808e06e148322d 0x4018e07e0c0303f5 0xf4018e07e0c0303f

def z463 : W := mkw 0x0800bdf7e02105ba 0x40800bdf7e02105b 0xc000ffffe00003f0 0x5c000ffffe00003f

def z464 : W := mkw 0x7f76ff7dd02d778c 0x47f76ff7dd02d778 0xfe64de79907fff8b 0xffe64de79907fff8

def z465 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0x7e7fce7fe0000002 0x97e7fce7fe000000

def z466 : W := mkw 0x40001200802c550c 0x040001200802c550 0x00000000007c1c00 0x000000000007c1c0

def z467 : W := mkw 0x27a700000a585800 0x227a700000a58580 0x3f8700001ffc1c0f 0x23f8700001ffc1c0

def z468 : W := mkw 0xbf76ffb550a40360 0x4bf76ffb550a4036 0xffffffffe00003ff 0xdffffffffe00003f

def z469 : W := mkw 0x18d9e0ee3dc3aaf2 0x118d9e0ee3dc3aaf 0x79fbe1fe7f83e3f7 0xf79fbe1fe7f83e3f

def z470 : W := mkw 0x0226041140000000 0x4022604114000000 0x00070001e0000000 0x000070001e000000

def z471 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x019f00000c631ffd 0xa019f00000c631ff

def z472 : W := mkw 0x37760d1140000000 0x437760d114000000 0xbfff1f81e000000f 0x8bfff1f81e000000

def z473 : W := mkw 0x1a76ad3540000000 0x41a76ad354000000 0xc07fffffe0000000 0xdc07fffffe000000

def z474 : W := mkw 0x1050000000000000 0x0105000000000000 0x3878000000000007 0x8387800000000000

def z475 : W := mkw 0x3d5aa92645828050 0x53d5aa9264582805 0x399b21866f800074 0x0399b21866f80007

def z476 : W := mkw 0x00090042a4030c9a 0x000090042a4030c9 0x401f2047ec031ff5 0xe401f2047ec031ff

def z477 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x381820061f83e3f4 0x2381820061f83e3f

def z478 : W := mkw 0x1850e06c10012280 0x01850e06c1001228 0x7878e07e1003e387 0xf7878e07e1003e38

def z479 : W := mkw 0x008010c0886105a8 0x0008010c0886105a 0xc18431c18c631ffd 0xec18431c18c631ff

def z480 : W := mkw 0x3d52a92440000000 0x43d52a9244000000 0x3800000000000000 0x0380000000000000

def z481 : W := mkw 0x408956dbbc672fbe 0x0408956dbbc672fb 0xc19fffffec631ffd 0xfc19fffffec631ff

def z482 : W := mkw 0x2d00ad3540000000 0x42d00ad354000000 0xff80ffffe000000f 0x5ff80ffffe000000

def z483 : W := mkw 0x3fffad354f528800 0x63fffad354f52880 0xffffffffef80000f 0xdffffffffef80000

def z484 : W := mkw 0x5858f67f95a7a7dc 0x15858f67f95a7a7d 0xf878fe7f9f83e3f7 0xff878fe7f9f83e3f

def z485 : W := mkw 0x35db00000f528800 0x235db00000f52880 0x39fb00001f83e007 0xa39fb00001f83e00

def z486 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xb980ff800f8003f4 0x5b980ff800f8003f

def z487 : W := mkw 0x0000004200010090 0x0000000420001009 0x40002046000003f0 0x440002046000003f

def z488 : W := mkw 0x27a700000a585800 0x227a700000a58580 0x07e70000107ffc0b 0xa07e70000107ffc0

def z489 : W := mkw 0x2d80a9000a500000 0x02d80a9000a50000 0xbf80ff801ffc000f 0x7bf80ff801ffc000

def z490 : W := mkw 0x6f24ff59902d778c 0x06f24ff59902d778 0xffe4fff9907fff8f 0xfffe4fff9907fff8

def z491 : W := mkw 0x98d8f2ee1ff7a3f0 0x198d8f2ee1ff7a3f 0x7878e07e1fffe3f7 0xf7878e07e1fffe3f

def z492 : W := mkw 0x1276043540000000 0x4127604354000000 0xc67fde7fe000000b 0xdc67fde7fe000000

def z493 : W := mkw 0x008900000c420800 0x0008900000c42080 0x000000000c631c00 0x2000000000c631c0

def z494 : W := mkw 0x2502090040000000 0x4250209004000000 0x0183018060000000 0x0018301806000000

def z495 : W := mkw 0x1276000000000000 0x0127600000000000 0x007f000000000000 0x8007f00000000000

def z496 : W := mkw 0xbddbfb801ff68b60 0x2bddbfb801ff68b6 0xbf9bff801ffc03ff 0x7bf9bff801ffc03f

def z497 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0x398021801ffc03f4 0x2398021801ffc03f

def z498 : W := mkw 0xbff6bfb54a740120 0x4bff6bfb54a74012 0xffffffffe07c000f 0xdffffffffe07c000

def z499 : W := mkw 0x008910408c630d88 0x0008910408c630d8 0xc19f10418c631f8d 0xec19f10418c631f8

def z500 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x818031800c631ffd 0x6818031800c631ff

def z501 : W := mkw 0x0000404810012280 0x0000040481001228 0x000000001003e380 0x2000000001003e38

def z502 : W := mkw 0xbddba9800fd28860 0x2bddba9800fd2886 0x399b21800f800074 0x0399b21800f80007

def z503 : W := mkw 0x5a74f67d902d778c 0x05a74f67d902d778 0xfe7cfe7f907fff8f 0xffe7cfe7f907fff8

def z504 : W := mkw 0x1858a06604030090 0x01858a0660403009 0x7878e07e0c0303f7 0xf7878e07e0c0303f

def z505 : W := mkw 0xa58009800a500020 0x0a58009800a50002 0x0180018000000000 0x0018001800000000

def z506 : W := mkw 0x0889bdf7ec630dba 0x40889bdf7ec630db 0xc19fffffec631ffd 0xfc19fffffec631ff

def z507 : W := mkw 0xa58052801af40360 0x0a58052801af4036 0x3f8000001ffc03ff 0x23f8000001ffc03f

def z508 : W := mkw 0x3fffa9000f5ad800 0x23fffa9000f5ad80 0xbfffff801ffffc0f 0xfbfffff801ffffc0

def z509 : W := mkw 0x27a71d91e8600d2a 0x427a71d91e8600d2 0x87871f81e0601c08 0x087871f81e0601c0

def z510 : W := mkw 0x67a756599a7d7f8c 0x267a756599a7d7f8 0xc7e7de79907fff8b 0xfc7e7de79907fff8

def z511 : W := mkw 0x0000004800012080 0x0000000480001208 0x406000780003e000 0x8406000780003e00

def z512 : W := mkw 0x1050002c0100a000 0x11050002c0100a00 0x006000380000e000 0x0006000380000e00

def z513 : W := mkw 0x7fffff7ddf7fff8c 0x67fffff7ddf7fff8 0xffffffffffffff8f 0xfffffffffffffff8

def z514 : W := mkw 0x0008404a14032290 0x00008404a1403229 0x4078e07e1c03e3f7 0xf4078e07e1c03e3f

def z515 : W := mkw 0x1858a066058380d0 0x11858a066058380d 0x781820460f8303f5 0xe781820460f8303f

def z516 : W := mkw 0xafa7fb801afc5b60 0x2afa7fb801afc5b6 0xbf87ff801ffc1fff 0x7bf87ff801ffc1ff

def z517 : W := mkw 0x3fffa0260fdad850 0x33fffa0260fdad85 0x3fff20061ffffc7f 0xa3fff20061ffffc7

def z518 : W := mkw 0x258900000e520800 0x0258900000e52080 0x3f9f00001fff1c0f 0xa3f9f00001fff1c0

def z519 : W := mkw 0x7f76bf35c02c550c 0x47f76bf35c02c550 0xffffffffe07c1c0f 0xdffffffffe07c1c0

def z520 : W := mkw 0xafa4ff911af40360 0x0afa4ff911af4036 0xffe4fff99ffc03ff 0xfffe4fff99ffc03f

def z521 : W := mkw 0x0000100080200508 0x0000010008020050 0x8004100180601c08 0x08004100180601c0

def z522 : W := mkw 0x3f76ed3d5180a240 0x53f76ed3d5180a24 0xfffffffff380e00f 0xdfffffffff380e00

def z523 : W := mkw 0x77ff46191f5efa04 0x277ff46191f5efa0 0x3fffce381ffffc0f 0xb3fffce381ffffc0

def z524 : W := mkw 0x18d9e06e1fdbfad0 0x318d9e06e1fdbfad 0x7878e07e1ffffff7 0xf7878e07e1ffffff

def z525 : W := mkw 0x0008004204030090 0x0000800420403009 0xc19f31c7ec0303fd 0xec19f31c7ec0303f

def z526 : W := mkw 0x422444599009768c 0x0422444599009768 0x4064c0799003ff83 0xf4064c0799003ff8

def z527 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xbf9f3f87e000000c 0x0bf9f3f87e000000

def z528 : W := mkw 0x00010000a0000c0a 0x000010000a0000c0 0x00070001e0001c00 0x000070001e0001c0

def z529 : W := mkw 0x127f0042a50bdc9a 0x2127f0042a50bdc9 0x407f0047e003fc00 0x8407f0047e003fc0

def z530 : W := mkw 0x1850e02410800240 0x01850e0241080024 0x7878e07e1f8003f7 0xf7878e07e1f8003f

def z531 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xfe60ffffe0000002 0x5fe60ffffe000000

def z532 : W := mkw 0x127f0477e4030c9a 0x4127f0477e4030c9 0x407f007fe0031c00 0x8407f007fe0031c0

def z533 : W := mkw 0x0000004000010080 0x0000000400001008 0x4000004000030381 0xe400000400003038

def z534 : W := mkw 0x4a24f65990ad77cc 0x04a24f65990ad77c 0xfe64fe799fffffff 0xffe64fe799ffffff

def z535 : W := mkw 0x0008000004020000 0x0000800000402000 0x001800000c030005 0xa001800000c03000

def z536 : W := mkw 0x00891082ac620d3a 0x000891082ac620d3 0x819f3187ec601c7c 0x0819f3187ec601c7

def z537 : W := mkw 0x377f0000071ad800 0x2377f0000071ad80 0x3e7f0000139ffc02 0x83e7f0000139ffc0

def z538 : W := mkw 0x0080108008600120 0x0008010800860012 0xc19f31c7ec6003fd 0xec19f31c7ec6003f

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z540 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7878c07e1383e002 0x97878c07e1383e00

def z541 : W := mkw 0x1a74a43500000000 0x01a74a4350000000 0xfe7cfe7f8000000f 0xdfe7cfe7f8000000

def z542 : W := mkw 0x02ad10c2ac6b5dba 0x002ad10c2ac6b5db 0xc7ff31c7fc7fffff 0xec7ff31c7fc7ffff

def z543 : W := mkw 0xbf76eb00139cd240 0x2bf76eb00139cd24 0x3e60ce00139ce002 0x13e60ce00139ce00

def z544 : W := mkw 0xa7a61f914a740120 0x4a7a61f914a74012 0x87871f81e07c0008 0x087871f81e07c000

def z545 : W := mkw 0x0224561110240300 0x0022456111024030 0xc664de79907c038b 0xfc664de79907c038

def z546 : W := mkw 0x12ff00000f5ad800 0x212ff00000f5ad80 0x007f00001ffffc00 0xa007f00001ffffc0

def z547 : W := mkw 0x0224041100000000 0x0022404110000000 0x86041e0180000008 0x086041e018000000

def z548 : W := mkw 0x42ad14dbac6b7dbe 0x042ad14dbac6b7db 0xc1ff31ffec63fffd 0xec1ff31ffec63fff

def z549 : W := mkw 0x0000100000200100 0x0000010000020010 0x8000100000600389 0x6800010000060038

def z550 : W := mkw 0x008900c22c4308b2 0x0008900c22c4308b 0x419b21c66c0303f5 0xe419b21c66c0303f

def z551 : W := mkw 0x127f0000050ad800 0x2127f0000050ad80 0x387f00001f83fc07 0xa387f00001f83fc0

def z552 : W := mkw 0x258052001a740300 0x0258052001a74030 0xbf80de001ffc038f 0x7bf80de001ffc038

def z553 : W := mkw 0xad80a9800ad00060 0x0ad80a9800ad0006 0xbf80ff800f80007f 0x5bf80ff800f80007

def z554 : W := mkw 0x1058404a1583a2d0 0x11058404a1583a2d 0x387800001f83e3f7 0xa387800001f83e3f

def z555 : W := mkw 0x258000000a500000 0x0258000000a50000 0x07800000007c0008 0x007800000007c000

def z556 : W := mkw 0x0800e06e108122d0 0x10800e06e108122d 0x4060e07e1003e3f3 0xf4060e07e1003e3f

def z557 : W := mkw 0xad80a9800ad00060 0x0ad80a9800ad0006 0x3f8021801ffc007f 0x23f8021801ffc007

def z558 : W := mkw 0xc08052c89afd77ec 0x0c08052c89afd77e 0x000000001ffffff0 0x2000000001ffffff

def z559 : W := mkw 0x4a24ff7dd02d778c 0x44a24ff7dd02d778 0xc664fffff07fff8b 0xfc664fffff07fff8

def z560 : W := mkw 0x3776000000000000 0x0377600000000000 0xffff31c7e000000f 0xcffff31c7e000000

def z561 : W := mkw 0x3776000000000000 0x0377600000000000 0x3e60000000000002 0x03e6000000000000

def z562 : W := mkw 0x3f7fad77e4030c9a 0x43f7fad77e4030c9 0xffffffffe0031c0f 0xdffffffffe0031c0

def z563 : W := mkw 0x008910822c620932 0x0008910822c62093 0x819b31866c6003fd 0x6819b31866c6003f

def z564 : W := mkw 0x37f600000b58d000 0x237f600000b58d00 0x3fe000001ffce00f 0x23fe000001ffce00

def z565 : W := mkw 0x7f76ad7dc009748c 0x47f76ad7dc009748 0xffffffffe003fc0f 0xdffffffffe003fc0

def z566 : W := mkw 0x0224104080295588 0x0022410408029558 0xc6641041907fff8b 0xec6641041907fff8

def z567 : W := mkw 0xbd50eb2c1394a240 0x1bd50eb2c1394a24 0x3e60ce38139ce002 0x13e60ce38139ce00

def z568 : W := mkw 0x3776041100000000 0x0377604110000000 0xffffde798000000f 0xdffffde798000000

def z569 : W := mkw 0x0889f0c2bce30ffa 0x00889f0c2bce30ff 0xf99ff1c7ffe31fff 0xff99ff1c7ffe31ff

def z570 : W := mkw 0x0000008220000032 0x0000000822000003 0x0000218660000070 0x0000021866000007

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x401f0047e0000000 0x8401f0047e000000

def z572 : W := mkw 0xefa4ff991afc7364 0x0efa4ff991afc736 0xbfe0ffb81ffce3ff 0x7bfe0ffb81ffce3f

def z573 : W := mkw 0x1858e00015828240 0x01858e0001582824 0x3878e0001f83e3f7 0xf3878e0001f83e3f

def z574 : W := mkw 0x808052801af40360 0x0808052801af4036 0x8600de001ffc03fb 0x78600de001ffc03f

def z575 : W := mkw 0x67265f59d02d778c 0x467265f59d02d778 0xc7e7dff9f07fff8b 0xfc7e7dff9f07fff8

def z576 : W := mkw 0x5afdf6ffbdeffffe 0x15afdf6ffbdeffff 0xffffffffffffffff 0xffffffffffffffff

def z577 : W := mkw 0x00000042a001049a 0x000000042a001049 0x40000047e0000000 0x040000047e000000

def z578 : W := mkw 0xad80fbc81af523e0 0x0ad80fbc81af523e 0xffe0fff81fffe3ff 0xfffe0fff81fffe3f

def z579 : W := mkw 0xa5891bc2ae770dba 0x0a5891bc2ae770db 0xc79f3fc7ec7f1ffd 0xec79f3fc7ec7f1ff

def z580 : W := mkw 0x422456599025278c 0x0422456599025278 0xc664de798000038b 0xdc664de798000038

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000000107c000b 0x206000000107c000

def z582 : W := mkw 0x422c565b942f779c 0x0422c565b942f779 0xc67cfe7f9c7fffff 0xfc67cfe7f9c7ffff

def z583 : W := mkw 0x3552000003108000 0x2355200000310800 0x3800000003800000 0x0380000000380000

def z584 : W := mkw 0x3fffa0240f5ad800 0x23fffa0240f5ad80 0x7fffe07e1ffffc0f 0xf7fffe07e1ffffc0

def z585 : W := mkw 0x3776043540000000 0x4377604354000000 0x7fff007fe000000f 0x87fff007fe000000

def z586 : W := mkw 0x1a7ce47f1583a2d0 0x11a7ce47f1583a2d 0xfe7cfe7f9f83e3ff 0xffe7cfe7f9f83e3f

def z587 : W := mkw 0x00891080ac620d2a 0x000891080ac620d2 0x819f1181ec631c0d 0xa819f1181ec631c0

def z588 : W := mkw 0x0008000005028000 0x0000800000502800 0x000000001f83e000 0x2000000001f83e00

def z589 : W := mkw 0xa5801b800a740120 0x0a5801b800a74012 0xbf801f801ffc000f 0x2bf801f801ffc000

def z590 : W := mkw 0x18d9b0e6ac630dba 0x018d9b0e6ac630db 0xf9fff1ffec631fff 0xff9fff1ffec631ff

def z591 : W := mkw 0x808012800a740120 0x0808012800a74012 0x00000000007c0000 0x000000000007c000

def z592 : W := mkw 0x42241611802c550c 0x042241611802c550 0xc664de79807c1c0b 0xdc664de79807c1c0

def z593 : W := mkw 0x408952cabc6f7fbe 0x0408952cabc6f7fb 0xc19f31c7fc7ffffd 0xec19f31c7fc7ffff

def z594 : W := mkw 0x37f600000a500000 0x037f600000a50000 0x3fff00001ffc000f 0xa3fff00001ffc000

def z595 : W := mkw 0x5276567dd02d778c 0x45276567dd02d778 0xc67fde7ff07fff8b 0xfc67fde7ff07fff8

def z596 : W := mkw 0x42244619100c7204 0x042244619100c720 0xc664de79901ce00b 0xdc664de79901ce00

def z597 : W := mkw 0x1058006e0503a090 0x11058006e0503a09 0x4078207e0c03e3f5 0xe4078207e0c03e3f

def z598 : W := mkw 0x42241651802d558c 0x042241651802d558 0xc6041e41807f1f89 0xec6041e41807f1f8

def z599 : W := mkw 0x127600000108d000 0x2127600000108d00 0x006000000000e000 0x0006000000000e00

def z600 : W := mkw 0x2d80e0001ad00240 0x02d80e0001ad0024 0x3f80e0001ffc03ff 0x73f80e0001ffc03f

def z601 : W := mkw 0x1a76a43540000000 0x41a76a4354000000 0x787fe07fe0000007 0xd787fe07fe000000

def z602 : W := mkw 0x1276043540000000 0x4127604354000000 0x0060003800000000 0x0006000380000000

def z603 : W := mkw 0x0009000224020812 0x0000900022402081 0x001b000660000000 0x0001b00066000000

def z604 : W := mkw 0x0000400010000200 0x0000040001000020 0x0000c00010000383 0x70000c0001000038

def z605 : W := mkw 0x008952c2bc670fba 0x0008952c2bc670fb 0xc79fffc7fc7f1fff 0xfc79fffc7fc7f1ff

def z606 : W := mkw 0x0080108008600120 0x0008010800860012 0x8180118000600008 0x0818011800060000

def z607 : W := mkw 0x1858e02c1582a240 0x11858e02c1582a24 0x3878c0381f83e007 0xb3878c0381f83e00

def z608 : W := mkw 0xad80fbc2baf507fa 0x0ad80fbc2baf507f 0xff80ffc7fffc03ff 0x7ff80ffc7fffc03f

def z609 : W := mkw 0xbffffff7fef70ffa 0x4bffffff7fef70ff 0xffffffffffff1fff 0xfffffffffffff1ff

def z610 : W := mkw 0x0224000000085000 0x0022400000008500 0x006400000003fc00 0x8006400000003fc0

def z611 : W := mkw 0x527f0459850bfc8c 0x2527f0459850bfc8 0x407f00798003fc00 0x8407f00798003fc0

def z612 : W := mkw 0x3f76a92440000000 0x43f76a9244000000 0x3fff21866000000f 0x83fff21866000000

def z613 : W := mkw 0x400004598001248c 0x0400004598001248 0x4000007980000000 0x0400000798000000

def z614 : W := mkw 0x37ff00000f528800 0x237ff00000f52880 0x3fff00000f80000f 0x83fff00000f80000

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x000020000c0003f5 0x6000020000c0003f

def z616 : W := mkw 0x27260d1140000000 0x427260d114000000 0x06000e0000000000 0x006000e000000000

def z617 : W := mkw 0x27260d1140000000 0x427260d114000000 0xc79f3fc7e000000d 0xcc79f3fc7e000000

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00031c7e0000000 0x4c00031c7e000000

def z619 : W := mkw 0x2f26ad3540000000 0x42f26ad354000000 0xc787ffffe0000008 0x5c787ffffe000000

def z620 : W := mkw 0x105b000005028800 0x2105b00000502880 0x001b000000000000 0x0001b00000000000

def z621 : W := mkw 0x37ff00420f5bd890 0x237ff00420f5bd89 0x7fff20461fffffff 0xe7fff20461ffffff

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018204600000005 0xc401820460000000

def z623 : W := mkw 0x0081008028400822 0x0008100802840082 0x0183018060000000 0x0018301806000000

def z624 : W := mkw 0x8800fbc2b0a507fa 0x08800fbc2b0a507f 0xc000ffc7e00003f0 0x5c000ffc7e00003f

def z625 : W := mkw 0x27af1dd3ec630dba 0x427af1dd3ec630db 0xc79f3fc7ec631ffd 0xec79f3fc7ec631ff

def z626 : W := mkw 0xbdd8fba61ff68370 0x1bdd8fba61ff6837 0xbf98ff861ffc03ff 0x7bf98ff861ffc03f

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x019b218660000004 0x0019b21866000000

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060c07800000003 0xd4060c0780000000

def z629 : W := mkw 0x0000120000240100 0x0000012000024010 0x86001e00007c0008 0x086001e00007c000

def z630 : W := mkw 0xa7a71b800a7c5920 0x2a7a71b800a7c592 0x87871f80007c1c08 0x087871f80007c1c0

def z631 : W := mkw 0x3f76a90000000000 0x03f76a9000000000 0xbfffff800000000f 0xdbfffff800000000

def z632 : W := mkw 0x42a456d9986d77ac 0x042a456d9986d77a 0xc7e4fff99c7fffff 0xfc7e4fff99c7ffff

def z633 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3f9f00000ffc1c0c 0x03f9f00000ffc1c0

def z634 : W := mkw 0x258910c2ae730dba 0x0258910c2ae730db 0xff9f31c7ffff1fff 0xeff9f31c7ffff1ff

def z635 : W := mkw 0x0800f0eeb0a127fa 0x10800f0eeb0a127f 0xc000f1ffe00003f0 0x5c000f1ffe00003f

def z636 : W := mkw 0x0800a02400000000 0x00800a0240000000 0x4000e07e00000000 0x54000e07e0000000

def z637 : W := mkw 0xbdd8a9a60fd28070 0x1bdd8a9a60fd2807 0x399821860f800074 0x0399821860f80007

def z638 : W := mkw 0x1858f26e15a7a3d0 0x11858f26e15a7a3d 0xfe78fe7e1fffe3ff 0xffe78fe7e1fffe3f

def z639 : W := mkw 0x27af00000f5ad800 0x227af00000f5ad80 0x078700001ffffc08 0x2078700001ffffc0

def z640 : W := mkw 0xad89b9c2aef30dfa 0x0ad89b9c2aef30df 0xf99f31c7efe31ffd 0xef99f31c7efe31ff

def z641 : W := mkw 0x0080528018640320 0x0008052801864032 0x8780ff801c7c03ff 0x78780ff801c7c03f

def z642 : W := mkw 0x40005248902d778c 0x040005248902d778 0x4060c078107fff83 0xf4060c078107fff8

def z643 : W := mkw 0x35d800000f528000 0x035d800000f52800 0x3ff800001fffe00f 0xa3ff800001fffe00

def z644 : W := mkw 0x3f7ead7744030090 0x43f7ead774403009 0xffffffffec0303ff 0xfffffffffec0303f

def z645 : W := mkw 0x0224445910012280 0x0022444591001228 0xc664de799003e38b 0xfc664de799003e38

def z646 : W := mkw 0x258010800a700120 0x0258010800a70012 0xbf8031801ffc03ff 0x6bf8031801ffc03f

def z647 : W := mkw 0x37ff00000c420800 0x037ff00000c42080 0x3fff00000c631c0f 0xa3fff00000c631c0

def z648 : W := mkw 0x42245611902c570c 0x042245611902c570 0x8604de01907c1f8b 0x78604de01907c1f8

def z649 : W := mkw 0x0000520010240300 0x0000052001024030 0x8000de0000000380 0x58000de000000038

def z650 : W := mkw 0x3d5ae96e5583a2d0 0x53d5ae96e5583a2d 0x79fbe1fe7f83e3f7 0xf79fbe1fe7f83e3f

def z651 : W := mkw 0xa5000b0002140000 0x0a5000b000214000 0x06000e00001c0000 0x006000e00001c000

def z652 : W := mkw 0x37ff10c2af7bddba 0x237ff10c2af7bddb 0x3fff00001fffffff 0xa3fff00001ffffff

def z653 : W := mkw 0x5a74e63d118cf244 0x15a74e63d118cf24 0x3e60ce38139ce002 0x13e60ce38139ce00

def z654 : W := mkw 0xed80ffd99af527ec 0x0ed80ffd99af527e 0xff80fff99ffc03ff 0x7ff80fff99ffc03f

def z655 : W := mkw 0x42240611000c5004 0x042240611000c500 0x06000e00001c0000 0x006000e00001c000

def z656 : W := mkw 0xbfffa9800fdad860 0x2bfffa9800fdad86 0x3fff21801ffffc7f 0xa3fff21801ffffc7

def z657 : W := mkw 0xad89fbc2bef70ffa 0x0ad89fbc2bef70ff 0xbf80ff801fff1fff 0x7bf80ff801fff1ff

def z658 : W := mkw 0xad80b9800af00160 0x0ad80b9800af0016 0xb98031800fe003fd 0x6b98031800fe003f

def z659 : W := mkw 0x0000524810252380 0x0000052481025238 0xc660de78107fe38b 0xfc660de78107fe38

def z660 : W := mkw 0x7f76ff7dd025278c 0x47f76ff7dd025278 0xffffffffe000038f 0xdffffffffe000038

def z661 : W := mkw 0x808952801ffedb60 0x2808952801ffedb6 0x000000001ffffff0 0x2000000001ffffff

def z662 : W := mkw 0x1a7ee47f5583a2d0 0x51a7ee47f5583a2d 0x787fe07fff83e3f7 0xf787fe07fff83e3f

def z663 : W := mkw 0x2f24ad1100000000 0x02f24ad110000000 0xffe4fff98000000f 0xdffe4fff98000000

def z664 : W := mkw 0x0880f08018e00360 0x00880f08018e0036 0xb980f1801fe003ff 0x7b980f1801fe003f

def z665 : W := mkw 0x2d00e90010800240 0x02d00e9001080024 0xbf80ff801f8003ff 0x7bf80ff801f8003f

def z666 : W := mkw 0x008900000f528800 0x2008900000f52880 0x000000000f800000 0x0000000000f80000

def z667 : W := mkw 0x3d52a92440000000 0x43d52a9244000000 0xf99f31c7e000000d 0xcf99f31c7e000000

def z668 : W := mkw 0x37ff0042af5bdc9a 0x237ff0042af5bdc9 0x7fff0047fffffc0f 0xa7fff0047fffffc0

def z669 : W := mkw 0x008900420c430890 0x0008900420c43089 0x419f20460c631ffd 0xe419f20460c631ff

def z670 : W := mkw 0x1058002605028010 0x1105800260502801 0x0018000600000000 0x0001800060000000

def z671 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x07ff0000007ffc08 0x807ff0000007ffc0

def z672 : W := mkw 0x3ff6ad354a500000 0x43ff6ad354a50000 0xfffffffffffc000f 0xffffffffffffc000

def z673 : W := mkw 0x00090042a4030c9a 0x000090042a4030c9 0xc19f31c7e0031c0d 0xcc19f31c7e0031c0

def z674 : W := mkw 0x37ff1080af7add2a 0x237ff1080af7add2 0xbfff1181fffffc0f 0xabfff1181fffffc0

def z675 : W := mkw 0x18d9e06e1dc3aad0 0x118d9e06e1dc3aad 0x79ffe07e1fe3ffff 0xf79ffe07e1fe3fff

def z676 : W := mkw 0x3ddba0260fd28850 0x33ddba0260fd2885 0x399b20060f800074 0x0399b20060f80007

def z677 : W := mkw 0x3ddbe06e1fd3aad0 0x33ddbe06e1fd3aad 0x79fbe07e1f83e3f7 0xf79fbe07e1f83e3f

def z678 : W := mkw 0x008900822c420832 0x0008900822c42083 0x000000000c000070 0x0000000000c00007

def z679 : W := mkw 0xbf76ef3552940240 0x4bf76ef355294024 0xfffffffff39c000f 0xdfffffffff39c000

def z680 : W := mkw 0x37ff10c2ac630dba 0x037ff10c2ac630db 0xffff31c7ec631fff 0xeffff31c7ec631ff

def z681 : W := mkw 0x008000000a500000 0x0008000000a50000 0x000000001ffc0000 0x2000000001ffc000

def z682 : W := mkw 0x0008000204020010 0x0000800020402001 0x001820060c000074 0x0001820060c00007

def z683 : W := mkw 0x35db00000f528800 0x235db00000f52880 0x399f00000fe31c0d 0xa399f00000fe31c0

def z684 : W := mkw 0x008950cabc632fba 0x0008950cabc632fb 0xc1fff1fffc63ffff 0xfc1fff1fffc63fff

def z685 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7818e07e0f8003f4 0x57818e07e0f8003f

def z686 : W := mkw 0x000910c2a4230dba 0x0000910c2a4230db 0xc01f31c7e0031ff0 0xcc01f31c7e0031ff

def z687 : W := mkw 0x00811080a8600d2a 0x000811080a8600d2 0x81873181ec601ffd 0x681873181ec601ff

def z688 : W := mkw 0x377f0000050ad800 0x2377f0000050ad80 0x3fff00000003fc0f 0x83fff00000003fc0

def z689 : W := mkw 0x8000420012940240 0x0800042001294024 0x00000000139c0000 0x000000000139c000

def z690 : W := mkw 0xad89a9822ed20872 0x0ad89a9822ed2087 0x399b21866f800074 0x0399b21866f80007

def z691 : W := mkw 0x00811080a8600d2a 0x000811080a8600d2 0xc19f31c7e0601c0d 0xcc19f31c7e0601c0

def z692 : W := mkw 0x0080008008400020 0x0008000800840002 0x018021800c000074 0x0018021800c00007

def z693 : W := mkw 0x0000420010040200 0x0000042001004020 0x0600ce00101c0002 0x10600ce00101c000

def z694 : W := mkw 0xa5805b801af40360 0x0a5805b801af4036 0x87801f801ffc03f8 0x287801f801ffc03f

def z695 : W := mkw 0x008950cabde3affa 0x1008950cabde3aff 0xc19f31c7ffe3fffd 0xec19f31c7ffe3fff

def z696 : W := mkw 0x0000043540000000 0x4000004354000000 0x4000007fe0000000 0x04000007fe000000

def z697 : W := mkw 0x3f76ff3550240300 0x43f76ff355024030 0xfffffffff07c038f 0xffffffffff07c038

def z698 : W := mkw 0x0800ad3540000000 0x40800ad354000000 0x0000ce3800000000 0x10000ce380000000

def z699 : W := mkw 0x0224000000000000 0x0022400000000000 0x066400000000000b 0x8066400000000000

def z700 : W := mkw 0x5a74f67d91adf7cc 0x15a74f67d91adf7c 0xfe64de7993ffff8b 0xffe64de7993ffff8

def z701 : W := mkw 0xbdd2fba45af40360 0x4bdd2fba45af4036 0xbf9bff867ffc03ff 0x7bf9bff867ffc03f

def z702 : W := mkw 0x1850e06c1181a2c0 0x11850e06c1181a2c 0x7860c0781383e383 0xf7860c0781383e38

def z703 : W := mkw 0x3f76e02c1398f240 0x33f76e02c1398f24 0x3e60c038139ce002 0x13e60c038139ce00

def z704 : W := mkw 0x42241611802c550c 0x042241611802c550 0x86641e01907ffc0b 0xa86641e01907ffc0

def z705 : W := mkw 0x1858e02e1582a250 0x11858e02e1582a25 0x3878e03e1f80e076 0x13878e03e1f80e07

def z706 : W := mkw 0xbdd2a9a44ad00060 0x4bdd2a9a44ad0006 0x399b21866f800074 0x0399b21866f80007

def z707 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xffffdfffe000000a 0x9ffffdfffe000000

def z708 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x79ffe07e1f83e3ff 0xf79ffe07e1f83e3f

def z709 : W := mkw 0x3fffbdf7ec630dba 0x43fffbdf7ec630db 0x3e60ce380c631ff2 0x33e60ce380c631ff

def z710 : W := mkw 0x37ff04354f5ad800 0x637ff04354f5ad80 0xffff31fffffffc0f 0xeffff31fffffffc0

def z711 : W := mkw 0x7d52fb6cd02d778c 0x47d52fb6cd02d778 0x399b2186707fff84 0x2399b2186707fff8

def z712 : W := mkw 0x27ad00000f5ad800 0x227ad00000f5ad80 0x3fe400001ffffc0f 0xa3fe400001ffffc0

def z713 : W := mkw 0x42245619102c7304 0x042245619102c730 0x8664de38107fff8b 0xf8664de38107fff8

def z714 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf9bff867ffc03ff 0x7bf9bff867ffc03f

def z715 : W := mkw 0x3f76ad3540800040 0x43f76ad354080004 0xffffffffef80007f 0xdffffffffef80007

def z716 : W := mkw 0x000910c2a4230dba 0x0000910c2a4230db 0xc19f31c7e0031ffd 0xcc19f31c7e0031ff

def z717 : W := mkw 0x75db56599f77af8c 0x275db56599f77af8 0xf99bde798f800384 0x5f99bde798f80038

def z718 : W := mkw 0x18d1f0acb9e0af6a 0x118d1f0acb9e0af6 0xb9e7d1b9f3e0fc0a 0x1b9e7d1b9f3e0fc0

def z719 : W := mkw 0x808952cabff7affa 0x1808952cabff7aff 0x000000001ffffff0 0x2000000001ffffff

def z720 : W := mkw 0x377610c2a339d5ba 0x2377610c2a339d5b 0xfe6031c7f39ce3f2 0x4fe6031c7f39ce3f

def z721 : W := mkw 0x1858e06e9583a6d8 0x11858e06e9583a6d 0x787ce07f9f83fff7 0xf787ce07f9f83fff

def z722 : W := mkw 0x5a7cb63785aed55c 0x15a7cb63785aed55 0xbe1c3e078ffc1c7c 0x0be1c3e078ffc1c7

def z723 : W := mkw 0x92f656b55af40360 0x492f656b55af4036 0x407f007ffffc03f0 0xa407f007ffffc03f

def z724 : W := mkw 0x2fa7e06e1ad97ad0 0x32fa7e06e1ad97ad 0x4787e07e007c1ff8 0x54787e07e007c1ff

def z725 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3fe700001ffffc0a 0x23fe700001ffffc0

def z726 : W := mkw 0x0800e20010840240 0x00800e2001084024 0x3e00ee001f9c03f7 0x73e00ee001f9c03f

def z727 : W := mkw 0xc800ff5990a527cc 0x0c800ff5990a527c 0xc000de7980000380 0x5c000de798000038

def z728 : W := mkw 0x10d900000f5ad800 0x210d900000f5ad80 0x381800001ffffc04 0x2381800001ffffc0

def z729 : W := mkw 0x4800f26e90a527dc 0x14800f26e90a527d 0x4000e07e000003f0 0x54000e07e000003f

def z730 : W := mkw 0x35db00000f5ad800 0x235db00000f5ad80 0x380000001ffffc00 0x2380000001ffffc0

def z731 : W := mkw 0x008910c2ae730dba 0x0008910c2ae730db 0xc19f31c7ffff1ffd 0xec19f31c7ffff1ff

def z732 : W := mkw 0x3f76ad3540085000 0x43f76ad354008500 0xffffffffe003fc0f 0xdffffffffe003fc0

def z733 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0xbfff1181fffffc0f 0xabfff1181fffffc0

def z734 : W := mkw 0xad80bb800af40160 0x0ad80bb800af4016 0xbf803f800ffc03fd 0x6bf803f800ffc03f

def z735 : W := mkw 0x2d80b9800a700120 0x02d80b9800a70012 0xbf80ff801ffc03ff 0x7bf80ff801ffc03f

def z736 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0xf878f1ffff83e3f7 0xff878f1ffff83e3f

def z737 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc19f31c7e0631ff8 0xcc19f31c7e0631ff

def z738 : W := mkw 0xad09eb42b6970eda 0x0ad09eb42b6970ed 0x7e1fce47f39f1c02 0x97e1fce47f39f1c0

def z739 : W := mkw 0x272e4d5b5583a2d0 0x5272e4d5b5583a2d 0x87871f81ff83e3f8 0x287871f81ff83e3f

def z740 : W := mkw 0xc800ffdbb0a527fe 0x0c800ffdbb0a527f 0xc000ffffe00003f0 0x5c000ffffe00003f

def z741 : W := mkw 0x1858e96e5583a2d0 0x51858e96e5583a2d 0x7878e1fe7f83e3f7 0xf7878e1fe7f83e3f

def z742 : W := mkw 0x0808e04a1583a2d0 0x10808e04a1583a2d 0x7860e0781f83e3f7 0xf7860e0781f83e3f

def z743 : W := mkw 0x42ad469b3c4e7a36 0x042ad469b3c4e7a3 0x07fbefbe7c1ce076 0x107fbefbe7c1ce07

def z744 : W := mkw 0x12fd00000f5ad800 0x212fd00000f5ad80 0x3e7c00001ffffc0f 0xa3e7c00001ffffc0

def z745 : W := mkw 0x42244619100c7204 0x042244619100c720 0x0660ce38107ffc02 0x30660ce38107ffc0

def z746 : W := mkw 0x422456dbb02d77be 0x0422456dbb02d77b 0xc7fffffff07fffff 0xfc7fffffff07ffff

def z747 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc664fe799c7fffff 0xfc664fe799c7ffff

def z748 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf9fff801ffc03ff 0xfbf9fff801ffc03f

def z749 : W := mkw 0x37ff04354f5ad800 0x637ff04354f5ad80 0x3fff00381ffffc0f 0xa3fff00381ffffc0

def z750 : W := mkw 0x258900000f5ad800 0x2258900000f5ad80 0x398000001ffffc04 0x2398000001ffffc0

def z751 : W := mkw 0x37ff04110f5ad800 0x237ff04110f5ad80 0xfffffffffffffc0f 0xffffffffffffffc0

def z752 : W := mkw 0x37f600000b58d000 0x237f600000b58d00 0x3fe400001ffffc0f 0xa3fe400001ffffc0

def z753 : W := mkw 0x008910caac632dba 0x0008910caac632db 0xc1ff31ffec63fffd 0xec1ff31ffec63fff

def z754 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xffffffffec0003ff 0xfffffffffec0003f

def z755 : W := mkw 0x9858eb6e1587a2d0 0x19858eb6e1587a2d 0x7878ee7e1f83e3f7 0xf7878ee7e1f83e3f

def z756 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0x3f80ce001ffc03ff 0x33f80ce001ffc03f

def z757 : W := mkw 0xc800ffff90a527fc 0x1c800ffff90a527f 0xc000ffff800003f0 0x5c000ffff800003f

def z758 : W := mkw 0x258000000a585000 0x0258000000a58500 0x3f8000001ffffc0f 0x23f8000001ffffc0

def z759 : W := mkw 0x1276043540000000 0x4127604354000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z760 : W := mkw 0x1850e06c1181a2c0 0x11850e06c1181a2c 0x7860e0781f83e3f7 0xf7860e0781f83e3f

def z761 : W := mkw 0x2f24ad1100000000 0x02f24ad110000000 0xffffffffe000000f 0xdffffffffe000000

def z762 : W := mkw 0x42265659d02d778c 0x442265659d02d778 0xc667de79f07fff8b 0xfc667de79f07fff8

def z763 : W := mkw 0x9a7ffb8015aedb60 0x29a7ffb8015aedb6 0x807fff800003fff0 0xd807fff800003fff

def z764 : W := mkw 0x008010c0886105a8 0x0008010c0886105a 0xc19f31c7ec631ffd 0xec19f31c7ec631ff

def z765 : W := mkw 0x37ff04354f5ad800 0x637ff04354f5ad80 0xffffde7ffffffc0f 0xfffffde7ffffffc0

def z766 : W := mkw 0x67a71691aa7c5d2e 0x267a71691aa7c5d2 0x87871f81e07c1c08 0x087871f81e07c1c0

def z767 : W := mkw 0x2724000002185000 0x0272400000218500 0x3e64000013fffc0b 0xa3e64000013fffc0

def z768 : W := mkw 0x377600000318d000 0x2377600000318d00 0x3e60000013fffc02 0x23e60000013fffc0

def z769 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3fff000013fffc0a 0x83fff000013fffc0

def z770 : W := mkw 0x1858e02c1582a240 0x11858e02c1582a24 0x3878e0381f83e3f7 0xf3878e0381f83e3f

def z771 : W := mkw 0x0808e04a148322d0 0x00808e04a148322d 0x7878e07e1f83e3f7 0xf7878e07e1f83e3f

def z772 : W := mkw 0xefa4add98ad974ec 0x0efa4add98ad974e 0x79e421f98f83fc74 0x879e421f98f83fc7

def z773 : W := mkw 0x1850e06e1181a2d0 0x11850e06e1181a2d 0x7860e07e1f80e3f7 0x77860e07e1f80e3f

def z774 : W := mkw 0x1058404a1503a290 0x01058404a1503a29 0x7878e07e1f83e3f7 0xf7878e07e1f83e3f

def z775 : W := mkw 0x527f047f850bfc9c 0x3527f047f850bfc9 0x407f007f8003fc00 0x8407f007f8003fc0

def z776 : W := mkw 0x008910c2af738dba 0x2008910c2af738db 0xc19f31c7efe31ffd 0xec19f31c7efe31ff

def z777 : W := mkw 0x408952cabc672fbe 0x0408952cabc672fb 0x000000000c631ff0 0x2000000000c631ff

def z778 : W := mkw 0x27a71d91ea785d2a 0x627a71d91ea785d2 0x87871f81e07c1c08 0x087871f81e07c1c0

def z779 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3ffb00001ffffc06 0x23ffb00001ffffc0

def z780 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3e7f00001ffffc02 0xa3e7f00001ffffc0

def z781 : W := mkw 0x37ff00244f5ad800 0x637ff00244f5ad80 0x3fff00067ffffc0f 0xa3fff00067ffffc0

def z782 : W := mkw 0x42245659902d778c 0x042245659902d778 0x4660ce78107fff83 0xf4660ce78107fff8

def z783 : W := mkw 0x258900000f5ad800 0x2258900000f5ad80 0x3f9f00001ffffc0f 0xa3f9f00001ffffc0

def z784 : W := mkw 0x008900c2ac430cba 0x0008900c2ac430cb 0x419f21c7ec031ff5 0xe419f21c7ec031ff

def z785 : W := mkw 0x0000041100000000 0x0000004110000000 0xc19fffffe000000d 0xdc19fffffe000000

def z786 : W := mkw 0x1850e06c108122c0 0x01850e06c108122c 0x7878e07e1f83e3f7 0xf7878e07e1f83e3f

def z787 : W := mkw 0x3d50a92400000000 0x03d50a9240000000 0xffffffffe000000f 0xdffffffffe000000

def z788 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0xffff10419ffffc0f 0xeffff10419ffffc0

def z789 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xffffffffff80000f 0xfffffffffff80000

def z790 : W := mkw 0xa58052801af40360 0x0a58052801af4036 0xbf80de001ffc03ff 0x7bf80de001ffc03f

def z791 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xffffffffe0631c0f 0xfffffffffe0631c0

def z792 : W := mkw 0x527c047f050bf094 0x1527c047f050bf09 0x4078007e0003e000 0x84078007e0003e00

def z793 : W := mkw 0x0224445910097280 0x0022444591009728 0xc664de79907fff8b 0xfc664de79907fff8

def z794 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xff98ffc61ffc03ff 0xfff98ffc61ffc03f

def z795 : W := mkw 0x3f76ad3540085000 0x43f76ad354008500 0xfffffffff01ce00f 0xdfffffffff01ce00

def z796 : W := mkw 0x37ff00800f5ad820 0x237ff00800f5ad82 0x3fff21801ffffc7f 0xa3fff21801ffffc7

def z797 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xff9fffffe000000c 0x5ff9fffffe000000

def z798 : W := mkw 0xbddba9a60fd28870 0x3bddba9a60fd2887 0x399b21860f800074 0x0399b21860f80007

def z799 : W := mkw 0x40005248902d778c 0x040005248902d778 0xc660de78107fff8b 0xfc660de78107fff8

def z800 : W := mkw 0x1858a06605038090 0x01858a0660503809 0x7878e07e1f83e3f7 0xf7878e07e1f83e3f

def z801 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xfffffffff003e00f 0xffffffffff003e00

def z802 : W := mkw 0x008900420c430890 0x0008900420c43089 0xc19f31c7ec631ffd 0xec19f31c7ec631ff

def z803 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0xf9f8f1fe1f83e3ff 0xff9f8f1fe1f83e3f

def z804 : W := mkw 0x1859e06e3583aad2 0x11859e06e3583aad 0x787be07e7f83e3f7 0xf787be07e7f83e3f

def z805 : W := mkw 0x4224565990ad77cc 0x04224565990ad77c 0xc664de799ffffffb 0xfc664de799ffffff

def z806 : W := mkw 0x422404598009748c 0x0422404598009748 0xc664de79907ffc0b 0xfc664de79907ffc0

def z807 : W := mkw 0x8800fbeeb0a527fa 0x18800fbeeb0a527f 0xc000ffffe00003f0 0x5c000ffffe00003f

def z808 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc664fffff07fff8b 0xfc664fffff07fff8

def z809 : W := mkw 0x1850e02c1180a240 0x11850e02c1180a24 0x7878e07e1f80e3f7 0xf7878e07e1f80e3f

def z810 : W := mkw 0x37ff00240f5ad800 0x237ff00240f5ad80 0x7fff007e1ffffc0f 0xa7fff007e1ffffc0

def z811 : W := mkw 0x0008104284230598 0x0000810428423059 0xc19f31c7ec631ffd 0xec19f31c7ec631ff

def z812 : W := mkw 0x37ff04114f5ad800 0x637ff04114f5ad80 0x3fff0001fffffc0f 0xa3fff0001fffffc0

def z813 : W := mkw 0x3f76ad3541008000 0x43f76ad354100800 0xfffffffff380e00f 0xdfffffffff380e00

def z814 : W := mkw 0x3ddba9244f528800 0x63ddba9244f52880 0x399b00000f800004 0x0399b00000f80000

def z815 : W := mkw 0x0889ad354f5ad800 0x60889ad354f5ad80 0xc000fffffffffc00 0x7c000fffffffffc0

def z816 : W := mkw 0xe7a71f918a7c5d2c 0x2e7a71f918a7c5d2 0x87871f81807c1c08 0x087871f81807c1c0

def z817 : W := mkw 0x1850ad3540000000 0x41850ad354000000 0xf9ffffffe000000f 0xdf9ffffffe000000

def z818 : W := mkw 0x0224145180295588 0x0022414518029558 0xc664de79907fff8b 0xfc664de79907fff8

def z819 : W := mkw 0x8880f2801af40360 0x08880f2801af4036 0xbe00fe001ffc03ff 0x7be00fe001ffc03f

def z820 : W := mkw 0xbddba9a44fd28860 0x6bddba9a44fd2886 0x399b21866f800074 0x0399b21866f80007

def z821 : W := mkw 0x10d900000f5ad800 0x210d900000f5ad80 0x39ff00001ffffc0f 0xa39ff00001ffffc0

def z822 : W := mkw 0x808912c2ae770dba 0x0808912c2ae770db 0xc19f31c7ec7f1ffd 0xec19f31c7ec7f1ff

def z823 : W := mkw 0x1858e02415828240 0x01858e0241582824 0x7878e07e1f83e3f7 0xf7878e07e1f83e3f

def z824 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf80ff800ffc03fc 0x5bf80ff800ffc03f

def z825 : W := mkw 0x527e047fc50bf49c 0x5527e047fc50bf49 0x407f007fe003fc00 0x8407f007fe003fc0

def z826 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3fff20001fffffff 0xe3fff20001ffffff

def z827 : W := mkw 0x42245659902d778c 0x042245659902d778 0x4664ce79907fff82 0xb4664ce79907fff8

def z828 : W := mkw 0x1858a06e0583a0d0 0x11858a06e0583a0d 0x7878207e0f83e3f5 0xe7878207e0f83e3f

def z829 : W := mkw 0x42245659902d778c 0x042245659902d778 0xfe64de799fffff8f 0xffe64de799fffff8

def z830 : W := mkw 0x42244659100d7284 0x042244659100d728 0x4664ce78107fff8b 0xf4664ce78107fff8

def z831 : W := mkw 0x37760d3540000000 0x437760d354000000 0xc7ffdfffe000000b 0xdc7ffdfffe000000

def z832 : W := mkw 0x1058404a1583a2d0 0x11058404a1583a2d 0x7878c0781f83e3f7 0xf7878c0781f83e3f

def z833 : W := mkw 0x3f76ad3541808040 0x53f76ad354180804 0xffffffffe380000f 0xdffffffffe380000

def z834 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7860c0781f83e3f3 0xf7860c0781f83e3f

def z835 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc1ff31c7fc63ffff 0xec1ff31c7fc63fff

def z836 : W := mkw 0x0800e00810802240 0x00800e0081080224 0x3860e0381f80e3f7 0x73860e0381f80e3f

def z837 : W := mkw 0x008900000f5ad800 0x2008900000f5ad80 0x380000001ffffc07 0x2380000001ffffc0

def z838 : W := mkw 0x37ff00802f5ad822 0x237ff00802f5ad82 0x3fff01807ffffc0f 0xa3fff01807ffffc0

def z839 : W := mkw 0x37ff09000f5ad800 0x237ff09000f5ad80 0xbfff1f801ffffc0f 0xabfff1f801ffffc0

def z840 : W := mkw 0x37ff00822f5ad832 0x237ff00822f5ad83 0xffff31c7fffffc7f 0xeffff31c7fffffc7

def z841 : W := mkw 0x185be06e1583aad0 0x3185be06e1583aad 0x787be07e1f83e3f7 0xf787be07e1f83e3f

def z842 : W := mkw 0x4800f65990a527cc 0x04800f65990a527c 0xc000fe79800003f0 0x5c000fe79800003f

def z843 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc79f31c7fc7f1fff 0xec79f31c7fc7f1ff

def z844 : W := mkw 0x527d047fa50bfc9e 0x1527d047fa50bfc9 0x407f007fe003fc00 0x8407f007fe003fc0

def z845 : W := mkw 0xc22456d990ad77ec 0x0c22456d990ad77e 0xc664de79907ffffb 0xfc664de79907ffff

def z846 : W := mkw 0xad80fba45af40360 0x4ad80fba45af4036 0xbf80ff867ffc03ff 0x7bf80ff867ffc03f

def z847 : W := mkw 0x42245619902c770c 0x042245619902c770 0x8664de39907ffc0b 0xb8664de39907ffc0

def z848 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3e7800001ffffc07 0xa3e7800001ffffc0

def z849 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xfffffffff07c000f 0xffffffffff07c000

def z850 : W := mkw 0xc08952cabeff7ffe 0x0c08952cabeff7ff 0x000000001ffffff0 0x2000000001ffffff

def z851 : W := mkw 0x1858e96e1583a2d0 0x11858e96e1583a2d 0xf878fffe1f83e3f7 0xff878fffe1f83e3f

def z852 : W := mkw 0x127f0477e50bdc9a 0x6127f0477e50bdc9 0x407f007fe003fc00 0x8407f007fe003fc0

def z853 : W := mkw 0xad83fb801af40b60 0x2ad83fb801af40b6 0xbf83ff801ffc03ff 0x7bf83ff801ffc03f

def z854 : W := mkw 0x408952cabf7fffbe 0x2408952cabf7fffb 0x000000001ffffff0 0x2000000001ffffff

def z855 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0xf87cf07f9f83e3ff 0xff87cf07f9f83e3f

def z856 : W := mkw 0x42241659802d758c 0x042241659802d758 0xc664de79807ffc0b 0xdc664de79807ffc0

def z857 : W := mkw 0x37ff00260f5ad810 0x337ff00260f5ad81 0x3fff00061ffffc0f 0xa3fff00061ffffc0

def z858 : W := mkw 0x35db00000f5ad800 0x235db00000f5ad80 0x3f9b00001ffffc0f 0x23f9b00001ffffc0

def z859 : W := mkw 0xc800fbc890a527ec 0x0c800fbc890a527e 0x8000ff80000003f0 0x58000ff80000003f

def z860 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x7fff20461ffffc0f 0xe7fff20461ffffc0

def z861 : W := mkw 0x2d00ad3540000000 0x42d00ad354000000 0xff9fffffe000000f 0xdff9fffffe000000

def z862 : W := mkw 0x3f76ad354318d000 0x63f76ad354318d00 0xfffffffff3fffc0f 0xffffffffff3fffc0

def z863 : W := mkw 0x0800e06e108122d0 0x10800e06e108122d 0x7860e07e1f83e3f7 0xf7860e07e1f83e3f

def z864 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x419f21c7ec631ff4 0xa419f21c7ec631ff

def z865 : W := mkw 0x4224565b902d779c 0x04224565b902d779 0xc664fe7f907ffffb 0xfc664fe7f907ffff

def z866 : W := mkw 0xad80eb801ad40260 0x0ad80eb801ad4026 0x3f80ef801f9c03f7 0x73f80ef801f9c03f

def z867 : W := mkw 0x008912c2ac670dba 0x0008912c2ac670db 0xc79f3fc7ec7f1ffd 0xec79f3fc7ec7f1ff

def z868 : W := mkw 0x377f0000071ad800 0x2377f0000071ad80 0x3e7f000013fffc0b 0xa3e7f000013fffc0

def z869 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf87ff81fffc03ff 0x7bf87ff81fffc03f

def z870 : W := mkw 0x37ff0d114f5ad800 0x637ff0d114f5ad80 0xffff3fc7fffffc0f 0xeffff3fc7fffffc0

def z871 : W := mkw 0x4800f67d90a527cc 0x14800f67d90a527c 0xc000de7980000380 0x5c000de798000038

def z872 : W := mkw 0x37ff00822f5ad832 0x237ff00822f5ad83 0x3fff00001ffffc7f 0xa3fff00001ffffc7

def z873 : W := mkw 0x1859e06eb583aeda 0x11859e06eb583aed 0x7878e07e1f83fff7 0xf7878e07e1f83fff

def z874 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x7fffc0781ffffc0f 0xf7fffc0781ffffc0

def z875 : W := mkw 0x4800ff7fd0a527dc 0x54800ff7fd0a527d 0xc000ffffe00003f0 0x5c000ffffe00003f

def z876 : W := mkw 0x377e0000050ad000 0x0377e0000050ad00 0x3fff00001ffffc0f 0xa3fff00001ffffc0

def z877 : W := mkw 0xb5d81bee0f77a1b0 0x1b5d81bee0f77a1b 0xc7f81ffe007fe008 0x8c7f81ffe007fe00

def z878 : W := mkw 0x3776041100000000 0x0377604110000000 0xffffffffe000000f 0xdffffffffe000000

def z879 : W := mkw 0x3d52ad3540000000 0x43d52ad354000000 0xf99fffffe000000d 0xdf99fffffe000000

def z880 : W := mkw 0x008110c2a8610dba 0x0008110c2a8610db 0xc19f31c7e0601ffd 0xcc19f31c7e0601ff

def z881 : W := mkw 0x2d00fb0010a40340 0x02d00fb0010a4034 0xbf80ff801ffc03ff 0x7bf80ff801ffc03f

def z882 : W := mkw 0x37ff0d114f5ad800 0x637ff0d114f5ad80 0xffffdff9fffffc0f 0xfffffdff9fffffc0

def z883 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbe00ff801ffc03f2 0x7be00ff801ffc03f

def z884 : W := mkw 0x35db00000f5ad800 0x235db00000f5ad80 0x399f00001ffffc0d 0xa399f00001ffffc0

def z885 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc79fffc7ec631fff 0xfc79fffc7ec631ff

def z886 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7878e07e1f80e3f6 0x57878e07e1f80e3f

def z887 : W := mkw 0x3f76ad3542100000 0x43f76ad354210000 0xfffffffff39c000f 0xdfffffffff39c000

def z888 : W := mkw 0xad80eb001ad40240 0x0ad80eb001ad4024 0x3f80ee001ffc03ff 0x73f80ee001ffc03f

def z889 : W := mkw 0x37ff00022f5ad812 0x237ff00022f5ad81 0x3fff00067ffffc0f 0xa3fff00067ffffc0

def z890 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0x3e00ee001ffc03f7 0x73e00ee001ffc03f

def z891 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x3860e0381f83e3f7 0x73860e0381f83e3f

def z892 : W := mkw 0x258900000f5ad800 0x2258900000f5ad80 0x3e0000001ffffc02 0x23e0000001ffffc0

def z893 : W := mkw 0x37ff04110f5ad800 0x237ff04110f5ad80 0xbfff1e019ffffc0f 0xabfff1e019ffffc0

def z894 : W := mkw 0xa7a71f914a7c5920 0x6a7a71f914a7c592 0x87871f81e07c1c08 0x087871f81e07c1c0

def z895 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf80df801ffc03fa 0x3bf80df801ffc03f

def z896 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf80ff801f9c03f6 0x5bf80ff801f9c03f

def z897 : W := mkw 0x37ff09004f5ad800 0x637ff09004f5ad80 0x3fff01807ffffc0f 0xa3fff01807ffffc0

def z898 : W := mkw 0xad82fb805af40360 0x4ad82fb805af4036 0xbf83ff807ffc03ff 0x7bf83ff807ffc03f

def z899 : W := mkw 0xa5805b801af40360 0x0a5805b801af4036 0xbf801f801ffc03ff 0x2bf801f801ffc03f

def z900 : W := mkw 0x37ff0d114f5ad800 0x637ff0d114f5ad80 0x3fff0e001ffffc0f 0xa3fff0e001ffffc0

def z901 : W := mkw 0xad80fb80baf4076a 0x0ad80fb80baf4076 0xbf80ff81fffc03ff 0x7bf80ff81fffc03f

def z902 : W := mkw 0x00891082ac620d3a 0x000891082ac620d3 0x819f3187ec601ffd 0x6819f3187ec601ff

def z903 : W := mkw 0x10580000050ad000 0x010580000050ad00 0x387800001ffffc07 0xa387800001ffffc0

def z904 : W := mkw 0x0880f28018e40360 0x00880f28018e4036 0xbf80ff801ffc03ff 0x7bf80ff801ffc03f

def z905 : W := mkw 0x422456d9b02d77ae 0x0422456d9b02d77a 0xc664dff9f07fff8b 0xfc664dff9f07fff8

def z906 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf84ff801fff1fff 0xfbf84ff801fff1ff

def z907 : W := mkw 0x12ff00000f5ad800 0x212ff00000f5ad80 0x387f00001ffffc07 0xa387f00001ffffc0

def z908 : W := mkw 0x185ae06e5583a2d0 0x5185ae06e5583a2d 0x787be07e7f83e3f7 0xf787be07e7f83e3f

def z909 : W := mkw 0x3f76ad3542185000 0x63f76ad354218500 0xffffffffe01c000f 0xdffffffffe01c000

def z910 : W := mkw 0xad80fb809af40768 0x0ad80fb809af4076 0xbf84ff819ffc1fff 0x7bf84ff819ffc1ff

def z911 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xff80ffc7fffc03ff 0x7ff80ffc7fffc03f

def z912 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0xbfff31801ffffc0f 0xebfff31801ffffc0

def z913 : W := mkw 0x42245659902d778c 0x042245659902d778 0x8660de38107fff8b 0x78660de38107fff8

def z914 : W := mkw 0xad80fba41af40360 0x0ad80fba41af4036 0xff80fffe1ffc03ff 0x7ff80fffe1ffc03f

def z915 : W := mkw 0xb7ff09800f5ad820 0x2b7ff09800f5ad82 0x3fff01801ffffc0f 0xa3fff01801ffffc0

def z916 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x79fbe1fe7f83e3f7 0xf79fbe1fe7f83e3f

def z917 : W := mkw 0x27a700000a585800 0x227a700000a58580 0x3fe700001ffffc0f 0xa3fe700001ffffc0

def z918 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xf99f31c7ffe31fff 0xef99f31c7ffe31ff

def z919 : W := mkw 0x27af00000f5ad800 0x227af00000f5ad80 0x3f8700001ffffc0f 0x23f8700001ffffc0

def z920 : W := mkw 0x127400000108d000 0x0127400000108d00 0x3e64000013fffc0b 0xa3e64000013fffc0

def z921 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x3878c0381f83e3f7 0xb3878c0381f83e3f

def z922 : W := mkw 0x1858e26e1587a2d0 0x11858e26e1587a2d 0x7e78ee7e1f9fe3f7 0xf7e78ee7e1f9fe3f

def z923 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc7ffde79907fff8f 0xfc7ffde79907fff8

def z924 : W := mkw 0x3f76ad3543108000 0x63f76ad354310800 0xffffffffe380000f 0xdffffffffe380000

def z925 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbf803f801ffc03fc 0x2bf803f801ffc03f

def z926 : W := mkw 0xad81fb803af40b62 0x0ad81fb803af40b6 0xbf83ff807ffc03ff 0x7bf83ff807ffc03f

def z927 : W := mkw 0x27ad00000e5a5800 0x027ad00000e5a580 0x3fff00001ffffc0f 0xa3fff00001ffffc0

def z928 : W := mkw 0x008910caad63adba 0x1008910caad63adb 0xc19f31c7ec63fffd 0xec19f31c7ec63fff

def z929 : W := mkw 0x127f0000050ad800 0x2127f0000050ad80 0x3e7f00001ffffc0f 0xa3e7f00001ffffc0

def z930 : W := mkw 0x12fd00000d4ad800 0x012fd00000d4ad80 0x3fff00001ffffc0f 0xa3fff00001ffffc0

def z931 : W := mkw 0x408952cabdeffffe 0x1408952cabdeffff 0x000000001ffffff0 0x2000000001ffffff

def z932 : W := mkw 0x527f045ba50bfc9e 0x2527f045ba50bfc9 0x407f007fe003fc00 0x8407f007fe003fc0

def z933 : W := mkw 0x37fc00000f5ad000 0x037fc00000f5ad00 0x3ffc00001ffffc0f 0xa3ffc00001ffffc0

def z934 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xfffbffffe0000006 0x5fffbffffe000000

def z935 : W := mkw 0x008910800c620920 0x0008910800c62092 0xc19f31c7ec631ffd 0xec19f31c7ec631ff

def z936 : W := mkw 0x422456d9902d77ac 0x0422456d9902d77a 0xc664fff9907ffffb 0xfc664fff9907ffff

def z937 : W := mkw 0x0224041100085000 0x0022404110008500 0x0664ce38107ffc0b 0xb0664ce38107ffc0

def z938 : W := mkw 0xad81fb801af40b60 0x0ad81fb801af40b6 0xbf87ff801ffc1fff 0x7bf87ff801ffc1ff

def z939 : W := mkw 0x1858e02e1582a250 0x11858e02e1582a25 0x3878e03e1f80e3f7 0x73878e03e1f80e3f

def z940 : W := mkw 0x3f76ad3540085000 0x43f76ad354008500 0xffffffffe07c1c0f 0xdffffffffe07c1c0

def z941 : W := mkw 0x7f76ef3d518cf244 0x57f76ef3d518cf24 0x3e60ce38139ce002 0x13e60ce38139ce00

def z942 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc664de79907ffc0a 0x9c664de79907ffc0

def z943 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xff84ffc19ffc03ff 0xfff84ffc19ffc03f

def z944 : W := mkw 0xc800fffdd0a527ec 0x4c800fffdd0a527e 0xc000ffffe00003f0 0x5c000ffffe00003f

def z945 : W := mkw 0x1058006e0503a090 0x11058006e0503a09 0x7878207e1f83e3f7 0xe7878207e1f83e3f

def z946 : W := mkw 0x3d52ad3540000000 0x43d52ad354000000 0xff9bffffe000000f 0x5ff9bffffe000000

def z947 : W := mkw 0xff76ef3d529c7244 0x4ff76ef3d529c724 0x3e60ce38139ce002 0x13e60ce38139ce00

def z948 : W := mkw 0xad80fb881af42360 0x0ad80fb881af4236 0xbfe0ffb81ffce3ff 0x7bfe0ffb81ffce3f

def z949 : W := mkw 0x42241611802c550c 0x042241611802c550 0xc664de79907ffc0b 0xfc664de79907ffc0

def z950 : W := mkw 0x1058406e1583a2d0 0x11058406e1583a2d 0x7878007e1f83e3f7 0xa7878007e1f83e3f

def z951 : W := mkw 0x1850e02c1180a240 0x11850e02c1180a24 0x3860c0381f80e3f2 0x33860c0381f80e3f

def z952 : W := mkw 0x42245659902d778c 0x042245659902d778 0x8664de39907fff8a 0x38664de39907fff8

def z953 : W := mkw 0x10d900000f5ad800 0x210d900000f5ad80 0x386000001ffffc02 0x2386000001ffffc0

def z954 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x3878e03e1f83e3f6 0x33878e03e1f83e3f

def z955 : W := mkw 0x2f26ad3540000000 0x42f26ad354000000 0xc79fffffe000000d 0xdc79fffffe000000

def z956 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x787ce07e1fe3ffff 0xf787ce07e1fe3fff

def z957 : W := mkw 0x42244659900d768c 0x042244659900d768 0x4664ce79907ffc0b 0xb4664ce79907ffc0

def z958 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbe00de001ffc03fb 0x7be00de001ffc03f

def z959 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xc7ffffffe0000008 0xdc7ffffffe000000

def z960 : W := mkw 0x0224000000085000 0x0022400000008500 0x3e6400001ffffc0f 0xa3e6400001ffffc0

def z961 : W := mkw 0x37f700000b58d800 0x237f700000b58d80 0x3fe7000013fffc0b 0xa3fe7000013fffc0

def z962 : W := mkw 0x35d900000f528800 0x035d900000f52880 0x3fff00001ffffc0f 0xa3fff00001ffffc0

def z963 : W := mkw 0x0000524890252788 0x0000052489025278 0xc664de79907fff8b 0xfc664de79907fff8

def z964 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xffe0fff81ffc03ff 0xfffe0fff81ffc03f

def z965 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0xbfffde001ffffc0f 0xfbfffde001ffffc0

def z966 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x39ff00001ffffc04 0xa39ff00001ffffc0

def z967 : W := mkw 0x02245248102d7380 0x002245248102d738 0xc664de78107fff8b 0xfc664de78107fff8

def z968 : W := mkw 0x8800fb8010a40360 0x08800fb8010a4036 0xbe00ff801ffc03ff 0x7be00ff801ffc03f

def z969 : W := mkw 0x1a74a43500000000 0x01a74a4350000000 0xffffffffe000000f 0xdffffffffe000000

def z970 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc664de79807fff88 0xdc664de79807fff8

def z971 : W := mkw 0x37f600000a585000 0x037f600000a58500 0x3fff00001ffffc0f 0xa3fff00001ffffc0

def z972 : W := mkw 0x4224565b90ad77dc 0x14224565b90ad77d 0xc664de79907ffffb 0xfc664de79907ffff

def z973 : W := mkw 0x37ff0d354f5ad800 0x637ff0d354f5ad80 0xffff1ffffffffc0f 0xaffff1ffffffffc0

def z974 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3fff21867ffffc0f 0xa3fff21867ffffc0

def z975 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3fe000001ffffc0f 0x23fe000001ffffc0

def z976 : W := mkw 0x42244619100c7204 0x042244619100c720 0xc664de79907ffc0b 0xfc664de79907ffc0

def z977 : W := mkw 0x1858e06eb583a6da 0x11858e06eb583a6d 0x7878e07fff83e3f7 0xf7878e07fff83e3f

def z978 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3e6400001ffffc0b 0xa3e6400001ffffc0

def z979 : W := mkw 0x2d80e9001ad00240 0x02d80e9001ad0024 0xbf80ff801ffc03ff 0x7bf80ff801ffc03f

def z980 : W := mkw 0x00811080a8600d2a 0x000811080a8600d2 0xc19f31c7ec601ffd 0xec19f31c7ec601ff

def z981 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc19f31c7ec031ff4 0xcc19f31c7ec031ff

def z982 : W := mkw 0xad81fb80baf40f6a 0x0ad81fb80baf40f6 0xbf80ff801ffc1fff 0x7bf80ff801ffc1ff

def z983 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0x819f3187ec631ffc 0x2819f3187ec631ff

def z984 : W := mkw 0xa5801b800a740120 0x0a5801b800a74012 0xbf803f801ffc03ff 0x6bf803f801ffc03f

def z985 : W := mkw 0x422456dbb02d77be 0x0422456dbb02d77b 0xc664de79907ffffb 0xfc664de79907ffff

def z986 : W := mkw 0x377600000318d000 0x2377600000318d00 0x3fff000013fffc0f 0xa3fff000013fffc0

def z987 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x787fe07fff83e3f7 0xf787fe07fff83e3f

def z988 : W := mkw 0xe7a41f910a7c5124 0x0e7a41f910a7c512 0x87801f80007c0008 0x087801f80007c000

def z989 : W := mkw 0x37ff04110f5ad800 0x237ff04110f5ad80 0x3fffce381ffffc0f 0xb3fffce381ffffc0

def z990 : W := mkw 0x3ddba9264fd28850 0x73ddba9264fd2885 0x399b21866f800074 0x0399b21866f80007

def z991 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x3f9f00001ffffc0c 0x23f9f00001ffffc0

def z992 : W := mkw 0x37ff04110f5ad800 0x237ff04110f5ad80 0x7fff00799ffffc0f 0xa7fff00799ffffc0

def z993 : W := mkw 0xad00eb0012940240 0x0ad00eb001294024 0xbf80ff801f9c03ff 0x7bf80ff801f9c03f

def z994 : W := mkw 0x35d900000f5ad800 0x235d900000f5ad80 0x3ff800001ffffc0f 0xa3ff800001ffffc0

def z995 : W := mkw 0xbf76ef35539cd240 0x6bf76ef35539cd24 0x3e60ce38139ce002 0x13e60ce38139ce00

def z996 : W := mkw 0xad00fb8012b40360 0x0ad00fb8012b4036 0xbe00ff801f9c03f7 0x7be00ff801f9c03f

def z997 : W := mkw 0x3f76ad354108d000 0x63f76ad354108d00 0xffffffffe000e00f 0xdffffffffe000e00

def z998 : W := mkw 0x127f047f450bf890 0x7127f047f450bf89 0x407f007fe003fc00 0x8407f007fe003fc0

def z999 : W := mkw 0x02245611102c5300 0x002245611102c530 0xc664de79907fff8b 0xfc664de79907fff8

def z1000 : W := mkw 0xad00eb0012940240 0x0ad00eb001294024 0x3e00ce001f9c03f2 0x33e00ce001f9c03f

def z1001 : W := mkw 0x1858e0481583a2c0 0x01858e0481583a2c 0x7878e0781f83e3f7 0xf7878e0781f83e3f

def z1002 : W := mkw 0x377e0000071ad000 0x2377e0000071ad00 0x3e7c00001ffffc0f 0xa3e7c00001ffffc0

def z1003 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc1fff1ffec631fff 0xfc1fff1ffec631ff

def z1004 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7e78e07e1fffe3ff 0xf7e78e07e1fffe3f

def z1005 : W := mkw 0x37ff00020f5ad810 0x237ff00020f5ad81 0x3fff20061ffffc7f 0xa3fff20061ffffc7

def z1006 : W := mkw 0x008910c2ac630dba 0x0008910c2ac630db 0xc19f31c7ec601ffc 0x4c19f31c7ec601ff

def z1007 : W := mkw 0x00090042a4030c9a 0x000090042a4030c9 0xc19f31c7ec031ffd 0xec19f31c7ec031ff

def z1008 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0xbfe0ff801fffe3ff 0xfbfe0ff801fffe3f

def z1009 : W := mkw 0x3f76ed3d5398f240 0x73f76ed3d5398f24 0x3e60ce38139ce002 0x13e60ce38139ce00

def z1010 : W := mkw 0xad81fb80baf40f6a 0x0ad81fb80baf40f6 0xff9fffc7fffc1fff 0xfff9fffc7fffc1ff

def z1011 : W := mkw 0xe7a61f91ca7c552c 0x4e7a61f91ca7c552 0x87871f81e07c1c08 0x087871f81e07c1c0

def z1012 : W := mkw 0x0800ad3540000000 0x40800ad354000000 0xc19bffffe0000004 0x5c19bffffe000000

def z1013 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7860e07e1f83e3f2 0x77860e07e1f83e3f

def z1014 : W := mkw 0x35db00000f5ad800 0x235db00000f5ad80 0x39fb00001ffffc07 0xa39fb00001ffffc0

def z1015 : W := mkw 0xad00fb0012b40340 0x0ad00fb0012b4034 0xbe00fe001ffc03ff 0x7be00fe001ffc03f

def z1016 : W := mkw 0x4224565bb02d779e 0x04224565bb02d779 0xc664de7ff07fff8b 0xfc664de7ff07fff8

def z1017 : W := mkw 0xad80fb801af40360 0x0ad80fb801af4036 0x3f80ef801ffc03f6 0x33f80ef801ffc03f

def z1018 : W := mkw 0x37ff00000f5ad800 0x237ff00000f5ad80 0x7fff0047fffffc0f 0xa7fff0047fffffc0

def z1019 : W := mkw 0xad80fbac1af42360 0x1ad80fbac1af4236 0xbf80ffb81ffc03ff 0x7bf80ffb81ffc03f

def z1020 : W := mkw 0x27260d1140000000 0x427260d114000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z1021 : W := mkw 0x4800f6ffb0a527fe 0x14800f6ffb0a527f 0xc000ffffe00003f0 0x5c000ffffe00003f

def z1022 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc7e4fff9907fff8f 0xfc7e4fff9907fff8

def z1023 : W := mkw 0xbf76ad3542900040 0x4bf76ad354290004 0xffffffffe380000f 0xdffffffffe380000

def z1024 : W := mkw 0x1859e06eb583aeda 0x11859e06eb583aed 0xf9fff1ffff83ffff 0xff9fff1ffff83fff

def z1025 : W := mkw 0xbdd9a9a62fd28872 0x1bdd9a9a62fd2887 0x399b21866f800074 0x0399b21866f80007

def z1026 : W := mkw 0x3ddba9a66f528832 0x63ddba9a66f52883 0x399b21866f800074 0x0399b21866f80007

def z1027 : W := mkw 0x000010c2a02105ba 0x0000010c2a02105b 0xc19f31c7e0631ffd 0xec19f31c7e0631ff

def z1028 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc7e7dff9f07fff8b 0xfc7e7dff9f07fff8

def z1029 : W := mkw 0x0a24ad3540000000 0x40a24ad354000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z1030 : W := mkw 0x3d52ad3540000000 0x43d52ad354000000 0xf9fbffffe0000007 0xdf9fbffffe000000

def z1031 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0xfe78fe7e1f83e3ff 0xffe78fe7e1f83e3f

def z1032 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc660de79907fff82 0x7c660de79907fff8

def z1033 : W := mkw 0x42245659902d778c 0x042245659902d778 0x0664ce38107fff8b 0xb0664ce38107fff8

def z1034 : W := mkw 0x008910c2ad638dba 0x0008910c2ad638db 0xc19f31c7ffe3fffd 0xec19f31c7ffe3fff

def z1035 : W := mkw 0x2d80f2001af40340 0x02d80f2001af4034 0xbf80fe001ffc03ff 0x7bf80fe001ffc03f

def z1036 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7878e07e0f83e3f4 0xd7878e07e0f83e3f

def z1037 : W := mkw 0x1a76ad3540000000 0x41a76ad354000000 0xc1ffffffe000000d 0xdc1ffffffe000000

def z1038 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc67cfe7f907fff8f 0xfc67cfe7f907fff8

def z1039 : W := mkw 0x1859e06e1583aad0 0x11859e06e1583aad 0x787fe07e1f83fff7 0xf787fe07e1f83fff

def z1040 : W := mkw 0xe7a51f91aa7c5d2e 0x0e7a51f91aa7c5d2 0x87871f81e07c1c08 0x087871f81e07c1c0

def z1041 : W := mkw 0x258052801a740320 0x0258052801a74032 0xbf80ff801ffc03ff 0x7bf80ff801ffc03f

def z1042 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7878207e1f83e3f4 0xa7878207e1f83e3f

def z1043 : W := mkw 0x1858e06e1583a2d0 0x11858e06e1583a2d 0x7878c07e1f83e3f2 0xb7878c07e1f83e3f

def z1044 : W := mkw 0x42245659902d778c 0x042245659902d778 0xc67fde7ff07fff8b 0xfc67fde7ff07fff8

def z1045 : W := mkw 0x3f76ad3540000000 0x43f76ad354000000 0xf9ffffffe0000004 0xdf9ffffffe000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z6])],[(0,[z9,z0,z1,z2,z3,z5,z6]),(1,[z0,z10,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z6])],[(0,[z12,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z14,z5,z15,z6]),(0,[z0,z16,z1,z2,z3,z5,z6])],[(0,[z0,z1,z17,z2,z3,z18,z6])],[(0,[z0,z1,z2,z19,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z20,z6]),(0,[z0,z1,z2,z21,z3,z5,z6]),(0,[z0,z22,z1,z2,z3,z5,z23])],[(0,[z0,z1,z2,z3,z5,z6,z24]),(0,[z0,z25,z26,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z27,z5,z6])],[(0,[z0,z1,z28,z2,z3,z5,z6]),(0,[z0,z1,z29,z2,z3,z5,z6]),(0,[z0,z30,z1,z2,z3,z5,z6]),(1,[z12,z1,z2,z3,z5,z31])],[(0,[z0,z1,z2,z3,z5,z6,z32]),(0,[z0,z1,z17,z2,z33,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z34,z6]),(1,[z0,z35,z1,z3,z5,z6])],[(0,[z0,z1,z36,z2,z3,z5,z6]),(0,[z37,z0,z1,z2,z3,z5,z6]),(0,[z0,z38,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z39,z6]),(0,[z0,z40,z2,z3,z41,z5,z6]),(0,[z0,z1,z2,z3,z42,z5,z6]),(0,[z0,z43,z1,z2,z3,z5,z6])],[(0,[z44,z0,z1,z45,z3,z5,z6]),(1,[z44,z1,z2,z3,z46,z6]),(0,[z47,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z3,z5,z48,z6])],[],[(0,[z49,z0,z1,z2,z3,z5,z6]),(0,[z0,z50,z1,z2,z3,z5,z6]),(0,[z0,z51,z1,z2,z3,z5,z6])],[(0,[z52,z0,z1,z2,z3,z5,z6])],[(0,[z53,z0,z1,z2,z3,z5,z6]),(0,[z44,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z46,z5,z6])]],
   [[(0,[z49,z0,z1,z2,z54,z5,z6]),(0,[z0,z1,z2,z3,z55,z5,z6]),(0,[z0,z1,z2,z3,z5,z56,z6]),(0,[z57,z0,z58,z1,z3,z5,z6]),(1,[z0,z1,z59,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z60,z6]),(0,[z0,z1,z2,z3,z5,z61,z6]),(0,[z0,z62,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z63,z6]),(0,[z0,z1,z2,z3,z5,z64,z6]),(1,[z0,z65,z1,z2,z5,z66]),(0,[z0,z65,z1,z2,z5,z66,z6]),(0,[z0,z67,z1,z2,z3,z5,z6])],[(0,[z0,z1,z68,z2,z3,z5,z6]),(0,[z0,z1,z69,z2,z3,z5,z6])],[(0,[z70,z0,z1,z2,z71,z5,z6]),(0,[z0,z35,z1,z72,z3,z5,z6]),(0,[z73,z0,z1,z2,z3,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z6]),(1,[z0,z1,z75,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z76])],[(0,[z0,z40,z77,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z79,z3,z5,z6])],[(0,[z0,z40,z36,z2,z3,z5,z6]),(0,[z0,z1,z80,z2,z3,z5,z6]),(0,[z0,z81,z1,z2,z3,z5,z6]),(0,[z82,z1,z2,z3,z5,z83,z6]),(0,[z0,z1,z2,z3,z46,z15,z6]),(1,[z0,z25,z84,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z85])],[(0,[z86,z0,z36,z2,z3,z5,z6]),(0,[z87,z0,z1,z2,z3,z5,z6]),(0,[z88,z0,z1,z2,z3,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z54,z5,z6]),(1,[z0,z1,z17,z3,z91,z6])],[(0,[z0,z1,z84,z2,z3,z5,z6]),(0,[z92,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z93,z5,z6]),(0,[z0,z65,z1,z2,z3,z5,z94])],[(0,[z95,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z96,z5,z6]),(0,[z0,z97,z1,z2,z3,z5,z6]),(0,[z0,z98,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z33,z3,z14,z6])],[(0,[z0,z99,z1,z2,z3,z5,z6]),(0,[z100,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z101,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z102,z6]),(0,[z0,z103,z1,z2,z3,z104,z6]),(0,[z0,z1,z105,z2,z3,z5,z6]),(0,[z106,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z83,z6])],[(0,[z0,z1,z2,z3,z107,z5,z6]),(0,[z0,z1,z2,z3,z5,z108,z6]),(0,[z0,z1,z2,z3,z5,z109,z6])],[(0,[z0,z1,z110,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z111,z5,z6]),(0,[z0,z112,z1,z2,z3,z5,z6]),(0,[z0,z98,z1,z2,z33,z3,z6])],[(1,[z113,z36,z2,z3,z5,z6]),(0,[z12,z0,z114,z2,z3,z5,z6])]],
   [[(0,[z70,z0,z1,z2,z3,z115,z6]),(0,[z0,z1,z2,z3,z116,z5,z6]),(0,[z117,z0,z1,z2,z3,z104,z6]),(1,[z0,z22,z2,z3,z5,z23])],[(0,[z0,z1,z2,z3,z118,z5,z6]),(0,[z0,z1,z2,z3,z119,z5,z6])],[(0,[z120,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z121,z3,z5,z6]),(0,[z122,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z123,z6]),(0,[z0,z124,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z125,z3,z5,z6]),(0,[z0,z1,z2,z126,z3,z54,z6]),(0,[z0,z1,z2,z3,z5,z127,z6]),(0,[z0,z1,z2,z3,z5,z128,z6])],[(0,[z129,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z130,z6])],[(0,[z0,z131,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z132]),(0,[z0,z98,z1,z3,z5,z18,z6]),(0,[z0,z133,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z134,z3,z5,z6]),(0,[z12,z0,z135,z2,z3,z5,z6]),(0,[z0,z136,z1,z2,z3,z5,z6]),(0,[z137,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z41,z5,z104,z6]),(0,[z0,z1,z2,z3,z138,z5,z6]),(1,[z0,z1,z2,z126,z3,z6]),(1,[z0,z98,z1,z3,z18,z6])],[(0,[z0,z1,z2,z3,z5,z6,z139]),(0,[z0,z1,z140,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z141,z5,z6]),(0,[z0,z65,z1,z2,z3,z5,z6])]],
   [[(0,[z142,z77,z1,z2,z3,z5,z6]),(0,[z0,z1,z143,z2,z3,z5,z6]),(0,[z144,z0,z1,z2,z3,z5,z6])],[(0,[z0,z22,z1,z2,z3,z5,z13]),(0,[z145,z0,z1,z2,z3,z5,z6]),(0,[z146,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z147,z3,z5,z6])],[(0,[z70,z0,z1,z148,z3,z5,z6]),(0,[z0,z1,z2,z148,z3,z5,z6]),(0,[z0,z1,z149,z2,z3,z5,z6]),(0,[z0,z98,z1,z3,z5,z150,z6]),(0,[z151,z0,z1,z2,z3,z5,z6])],[],[(0,[z152,z0,z1,z2,z3,z5,z6]),(0,[z0,z40,z22,z2,z3,z5,z6])],[(0,[z153,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z154,z5,z6]),(0,[z0,z1,z2,z3,z5,z155,z6]),(0,[z156,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z157,z6]),(0,[z0,z1,z2,z3,z158,z5,z6])],[(0,[z0,z36,z2,z3,z159,z5,z6])],[(0,[z160,z0,z1,z2,z3,z5,z6]),(0,[z0,z40,z1,z2,z3,z5,z161]),(0,[z0,z1,z2,z126,z3,z5,z6]),(0,[z0,z1,z162,z2,z3,z5,z6])]],
   [[],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z1,z163,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z164,z5,z6]),(0,[z0,z1,z2,z3,z5,z165,z6]),(0,[z0,z26,z2,z3,z166,z5,z6]),(0,[z117,z0,z2,z3,z5,z104,z6]),(0,[z0,z1,z2,z3,z5,z6,z167])],[(0,[z0,z1,z168,z2,z3,z5,z6]),(0,[z169,z0,z22,z1,z2,z3,z5]),(0,[z57,z0,z1,z17,z3,z5,z6]),(0,[z0,z1,z3,z5,z150,z6,z170])],[(0,[z0,z1,z2,z3,z171,z5,z6]),(0,[z0,z1,z2,z3,z5,z172,z6]),(0,[z173,z1,z2,z3,z5,z6,z13]),(0,[z117,z0,z103,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z161]),(0,[z0,z1,z2,z3,z5,z174,z6]),(0,[z0,z1,z175,z2,z3,z5,z6])],[(0,[z0,z1,z176,z2,z3,z5,z6]),(0,[z0,z1,z17,z2,z3,z83,z6]),(0,[z0,z1,z177,z2,z3,z5,z6]),(0,[z0,z178,z1,z2,z3,z5,z6]),(0,[z0,z179,z1,z2,z3,z54,z6]),(0,[z0,z7,z1,z2,z3,z5,z150])],[(0,[z0,z1,z2,z3,z180,z5,z6]),(0,[z0,z181,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z182]),(0,[z0,z1,z183,z3,z54,z5,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z184,z0,z1,z101,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z186,z6]),(0,[z0,z1,z2,z3,z187,z6,z188])]],
   [[(0,[z113,z1,z36,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z189,z5,z6]),(0,[z0,z1,z2,z3,z5,z190,z6]),(0,[z0,z1,z2,z3,z191,z5,z6]),(0,[z0,z192,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z193]),(0,[z0,z98,z1,z2,z194,z5,z6]),(0,[z0,z1,z2,z3,z5,z187,z6]),(1,[z0,z16,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z195,z6]),(0,[z0,z1,z2,z3,z5,z196,z6]),(0,[z0,z1,z2,z3,z5,z197,z6])],[(0,[z57,z0,z1,z101,z3,z5,z6]),(0,[z70,z0,z1,z2,z54,z5,z6]),(0,[z173,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z198,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z199,z6])],[(0,[z200,z0,z1,z2,z3,z5,z6]),(0,[z201,z0,z1,z2,z3,z5,z6]),(0,[z117,z0,z40,z2,z3,z5,z6]),(0,[z0,z1,z17,z3,z54,z5,z6])],[(0,[z0,z1,z2,z3,z5,z202,z6]),(0,[z0,z1,z203,z2,z3,z5,z6]),(0,[z0,z204,z1,z2,z3,z5,z6])],[(0,[z184,z0,z1,z2,z3,z5,z6]),(0,[z0,z205,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z206,z5,z6]),(1,[z0,z40,z2,z3,z5,z161]),(0,[z0,z1,z2,z3,z5,z207,z6])],[(0,[z0,z1,z2,z3,z5,z6,z208]),(0,[z0,z209,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z210,z5,z6]),(0,[z0,z211,z1,z2,z3,z5,z6]),(0,[z0,z40,z1,z2,z3,z5,z6]),(0,[z0,z212,z1,z2,z3,z5,z6]),(0,[z213,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z101,z3,z54,z5,z6]),(0,[z0,z1,z214,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z215,z3,z54,z5,z6]),(0,[z0,z1,z2,z3,z216,z5,z6]),(0,[z0,z1,z2,z3,z217,z5,z6]),(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z218]),(0,[z0,z1,z219,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z220,z6]),(0,[z0,z221,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z222]),(0,[z0,z51,z1,z2,z5,z15,z6])],[(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z3,z54,z5,z18,z6])],[(0,[z70,z0,z1,z2,z3,z5,z223]),(0,[z0,z1,z2,z224,z3,z5,z6]),(0,[z57,z0,z1,z2,z54,z5,z6]),(0,[z0,z65,z1,z225,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z66,z6])],[(0,[z226,z0,z1,z101,z3,z5,z6]),(0,[z0,z26,z1,z3,z54,z5,z6]),(0,[z0,z227,z1,z2,z3,z5,z6])],[(1,[z70,z1,z2,z71,z5,z6]),(0,[z57,z0,z25,z1,z3,z5,z6]),(0,[z0,z1,z228,z2,z3,z5,z6])],[(0,[z0,z229,z1,z2,z3,z5,z6]),(0,[z0,z103,z1,z2,z3,z41,z6]),(0,[z0,z1,z183,z2,z3,z5,z150])],[(0,[z0,z1,z2,z3,z5,z6,z230]),(0,[z0,z1,z3,z54,z5,z150,z6])]],
   [[(0,[z0,z231,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z232]),(0,[z0,z1,z2,z3,z5,z6,z233]),(0,[z0,z1,z234,z2,z3,z5,z6]),(0,[z0,z235,z1,z2,z3,z5,z6]),(1,[z0,z236,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z15,z6])],[(0,[z226,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z237,z6]),(0,[z0,z1,z17,z2,z3,z46,z6]),(0,[z0,z238,z1,z2,z159,z5,z6]),(0,[z0,z239,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z240,z5,z6])],[(0,[z0,z1,z241,z2,z3,z5,z6]),(0,[z0,z1,z2,z242,z3,z5,z6]),(0,[z0,z98,z1,z2,z3,z83,z6]),(0,[z0,z1,z243,z2,z3,z5,z6]),(0,[z117,z0,z1,z2,z3,z41,z6])],[(0,[z0,z1,z244,z2,z3,z5,z6]),(0,[z0,z1,z245,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z246]),(0,[z0,z1,z2,z3,z247,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z223]),(0,[z0,z1,z2,z3,z5,z6,z248]),(0,[z0,z1,z2,z3,z5,z6,z249]),(0,[z0,z1,z2,z3,z5,z6,z250]),(1,[z0,z1,z2,z251,z5,z6]),(0,[z0,z252,z1,z2,z3,z5,z6])],[(1,[z0,z238,z2,z159,z5,z6]),(0,[z0,z1,z2,z3,z5,z253,z6])]],
   [[(0,[z77,z1,z36,z2,z3,z5,z6]),(0,[z0,z254,z1,z2,z3,z5,z6]),(0,[z0,z1,z255,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z256,z5,z6])],[(0,[z169,z0,z1,z2,z3,z5,z188]),(0,[z169,z0,z1,z2,z3,z6,z188])],[(0,[z82,z0,z1,z2,z3,z83,z6]),(0,[z0,z1,z2,z3,z257,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z258])],[(0,[z1,z2,z259,z3,z71,z5,z6]),(0,[z0,z1,z260,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z261,z6])],[(0,[z0,z1,z2,z3,z5,z6,z262]),(0,[z0,z263,z1,z2,z3,z5,z6]),(0,[z0,z264,z1,z2,z3,z5,z6])],[(0,[z265,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z266,z3,z5,z6]),(0,[z0,z1,z183,z2,z3,z5,z6]),(0,[z0,z65,z1,z59,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z267]),(0,[z0,z268,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z269]),(0,[z0,z22,z2,z3,z5,z23,z6])],[(0,[z0,z270,z1,z2,z3,z5,z6]),(0,[z0,z25,z1,z3,z166,z5,z6]),(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z0,z51,z1,z2,z3,z15,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z271]),(0,[z0,z272,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z33,z14,z6]),(0,[z0,z1,z2,z273,z3,z5,z6])],[(0,[z0,z1,z2,z3,z274,z5,z6]),(0,[z0,z65,z1,z75,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z275])],[(0,[z0,z1,z276,z2,z3,z5,z6]),(0,[z0,z1,z72,z198,z3,z5,z6]),(0,[z0,z1,z17,z2,z3,z5,z6]),(1,[z0,z1,z277,z3,z5,z6])],[(0,[z0,z278,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z279,z5,z6]),(0,[z0,z1,z17,z2,z3,z91,z6])],[(0,[z0,z1,z2,z3,z5,z6,z280]),(0,[z0,z1,z2,z3,z5,z281,z6])],[(0,[z44,z1,z2,z3,z46,z5,z6]),(0,[z0,z1,z2,z3,z282,z5,z6])],[(0,[z70,z0,z1,z2,z3,z39,z6]),(0,[z0,z1,z2,z3,z283,z5,z6]),(0,[z0,z7,z1,z2,z3,z5,z170])],[(0,[z284,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z285,z6]),(0,[z0,z58,z1,z2,z33,z5,z6]),(0,[z0,z1,z225,z2,z3,z5,z94]),(0,[z0,z1,z2,z3,z286,z5,z6])]],
   [[(0,[z44,z0,z1,z287,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z288]),(1,[z169,z0,z1,z2,z3,z188])],[(0,[z0,z1,z2,z3,z289,z5,z6]),(0,[z0,z290,z1,z2,z3,z5,z6]),(0,[z0,z98,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z5,z291,z6]),(0,[z292,z0,z1,z2,z3,z5,z6])],[(0,[z49,z0,z58,z1,z2,z5,z6]),(0,[z293,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z294]),(0,[z295,z0,z1,z2,z3,z5,z6]),(0,[z0,z22,z1,z2,z3,z5,z161])],[(0,[z0,z26,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z296]),(0,[z297,z0,z1,z2,z3,z5,z6]),(0,[z0,z98,z1,z17,z3,z5,z6]),(0,[z0,z1,z298,z2,z3,z5,z6]),(0,[z299,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z300,z5,z6]),(1,[z0,z1,z2,z3,z5,z301]),(0,[z0,z302,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z303,z6]),(0,[z0,z304,z1,z2,z3,z5,z6]),(0,[z0,z305,z1,z2,z3,z5,z6])],[(0,[z0,z306,z1,z2,z3,z5,z6]),(0,[z86,z0,z72,z2,z3,z5,z6]),(1,[z0,z51,z1,z2,z15,z6])],[(0,[z0,z22,z1,z2,z3,z307,z5]),(0,[z0,z308,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z309,z6]),(0,[z310,z0,z1,z2,z3,z5,z6]),(0,[z0,z311,z1,z2,z3,z5,z6]),(0,[z0,z1,z312,z2,z3,z5,z6])]],
   [[(0,[z226,z1,z2,z215,z3,z5,z6]),(0,[z82,z0,z1,z2,z3,z46,z6]),(0,[z0,z2,z3,z41,z5,z23,z6]),(0,[z0,z1,z2,z3,z5,z6,z313])],[(0,[z0,z1,z2,z210,z5,z83,z6]),(0,[z0,z1,z2,z3,z5,z6,z314]),(0,[z0,z1,z315,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z316,z6]),(0,[z0,z51,z1,z17,z2,z3,z6])],[(0,[z0,z1,z2,z3,z5,z6,z317]),(0,[z0,z318,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z319,z5,z6])],[(0,[z0,z98,z1,z101,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z320]),(0,[z0,z1,z2,z3,z321,z5,z6]),(0,[z0,z322,z1,z2,z3,z5,z6])],[(0,[z323,z0,z1,z2,z3,z5,z6]),(0,[z324,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z33,z3,z5,z6])],[(0,[z0,z1,z325,z2,z3,z5,z6]),(0,[z0,z1,z326,z2,z3,z5,z6]),(0,[z0,z1,z225,z2,z3,z5,z6]),(0,[z0,z327,z1,z2,z3,z5,z6])],[(0,[z0,z36,z2,z3,z5,z23,z6]),(0,[z0,z77,z2,z3,z5,z23,z6]),(0,[z328,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z329]),(0,[z330,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z331,z3,z5,z6])],[(0,[z173,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z332,z5,z6]),(0,[z0,z1,z2,z33,z54,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z333])]],
   [[(0,[z49,z0,z1,z2,z259,z5,z6]),(0,[z0,z25,z1,z3,z54,z5,z6]),(0,[z0,z1,z334,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z335,z6])],[(0,[z0,z77,z2,z3,z159,z5,z6]),(0,[z0,z1,z336,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z337,z5,z6]),(0,[z0,z238,z2,z3,z159,z5,z6]),(0,[z0,z98,z1,z2,z3,z5,z6])],[(0,[z0,z338,z1,z2,z3,z5,z6]),(0,[z0,z339,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z340,z6]),(0,[z0,z26,z1,z84,z3,z5,z6]),(0,[z0,z98,z1,z2,z3,z91,z6])],[(0,[z0,z1,z2,z341,z3,z5,z6]),(0,[z117,z0,z2,z3,z5,z23,z6]),(1,[z0,z7,z1,z3,z5,z150]),(0,[z0,z1,z2,z33,z3,z15,z6])],[(0,[z342,z0,z1,z2,z3,z5,z6]),(1,[z0,z114,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z39,z5,z6]),(0,[z343,z0,z1,z2,z3,z5,z6]),(0,[z0,z344,z1,z2,z3,z5,z6]),(1,[z0,z1,z219,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z345,z6]),(0,[z0,z1,z2,z3,z5,z346,z6])],[(0,[z0,z1,z2,z3,z347,z5,z6]),(0,[z184,z0,z1,z2,z3,z102,z6]),(1,[z0,z1,z287,z3,z5,z6]),(0,[z0,z98,z25,z1,z3,z5,z6]),(0,[z0,z348,z1,z2,z3,z5,z6]),(0,[z0,z349,z1,z2,z3,z5,z6])],[(0,[z0,z350,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z94])]],
   [[(0,[z82,z0,z1,z2,z3,z5,z6]),(0,[z351,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z352,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z353,z5,z6])],[(0,[z0,z1,z2,z3,z5,z354,z6]),(0,[z86,z0,z1,z2,z159,z5,z6]),(0,[z0,z1,z2,z3,z5,z355,z6])],[(0,[z0,z1,z2,z3,z356,z5,z6]),(0,[z0,z1,z2,z3,z5,z102,z6]),(0,[z0,z1,z2,z3,z357,z5,z6]),(1,[z86,z0,z72,z2,z5,z6]),(0,[z0,z35,z1,z2,z3,z5,z6]),(0,[z358,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z359,z5,z6]),(0,[z0,z58,z1,z360,z2,z5,z6]),(0,[z0,z1,z3,z91,z5,z18,z6])],[(0,[z361,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z362,z6]),(0,[z0,z1,z2,z363,z3,z5,z6]),(0,[z0,z364,z1,z2,z3,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z40,z1,z2,z3,z5,z31]),(0,[z0,z365,z1,z2,z3,z5,z6])],[(0,[z366,z0,z1,z2,z3,z5,z6]),(0,[z367,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z368,z6]),(0,[z0,z1,z2,z3,z5,z6,z369])]],
   [[(0,[z0,z370,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z5,z6]),(0,[z371,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z372,z5,z6])],[(0,[z0,z1,z101,z3,z91,z5,z6]),(1,[z0,z373,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z374,z6]),(0,[z0,z1,z2,z3,z375,z5,z6]),(0,[z0,z1,z3,z91,z5,z150,z6])],[(0,[z0,z1,z2,z3,z376,z5,z6])],[(0,[z0,z1,z2,z3,z5,z66,z31]),(0,[z0,z40,z2,z3,z5,z6,z161]),(0,[z377,z0,z1,z2,z3,z5,z6]),(0,[z0,z179,z1,z2,z3,z5,z6]),(0,[z378,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z307,z187,z6])],[(0,[z113,z0,z77,z2,z3,z5,z6]),(1,[z0,z1,z2,z379,z5,z6]),(0,[z0,z1,z2,z380,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z381,z6]),(0,[z0,z382,z1,z2,z3,z5,z6])],[(0,[z113,z0,z36,z2,z3,z5,z6]),(0,[z383,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z384,z6]),(0,[z0,z385,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z386,z5,z6]),(0,[z0,z51,z1,z277,z3,z5,z6])],[(0,[z387,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z388]),(0,[z0,z26,z1,z3,z91,z5,z6]),(0,[z389,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z390,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z391,z6]),(0,[z0,z1,z2,z3,z5,z392,z6]),(0,[z0,z1,z2,z3,z5,z393,z6]),(0,[z0,z394,z1,z2,z3,z5,z6]),(0,[z0,z395,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z396,z6])]],
   [[(1,[z0,z1,z2,z3,z115,z6]),(1,[z0,z1,z360,z54,z5,z6]),(0,[z0,z1,z2,z397,z3,z5,z6]),(1,[z0,z1,z3,z5,z6,z398])],[(0,[z49,z0,z51,z1,z2,z5,z6])],[(0,[z12,z0,z1,z2,z3,z5,z31]),(0,[z0,z1,z2,z5,z66,z6,z94]),(0,[z0,z1,z2,z3,z5,z6,z399])],[(0,[z113,z142,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z400,z6]),(1,[z0,z2,z3,z5,z6,z401])],[(0,[z70,z0,z58,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z402,z6]),(0,[z0,z1,z2,z3,z5,z6,z403]),(0,[z0,z1,z2,z3,z404,z5,z6]),(0,[z0,z1,z2,z3,z405,z5,z6]),(0,[z0,z1,z225,z2,z5,z6,z94])],[(0,[z12,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z406,z6]),(0,[z0,z1,z2,z3,z307,z5,z6])],[(0,[z0,z1,z2,z3,z5,z407,z6]),(0,[z0,z40,z1,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z5,z408,z6])],[(1,[z0,z1,z325,z3,z5,z6]),(0,[z0,z25,z1,z2,z3,z5,z6]),(0,[z0,z1,z409,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z83,z15,z6]),(0,[z0,z1,z2,z3,z5,z23,z6]),(0,[z0,z410,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z307,z5,z187]),(0,[z411,z0,z1,z2,z3,z5,z6])],[(0,[z412,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z413]),(0,[z0,z1,z2,z3,z414,z5,z6]),(0,[z0,z1,z2,z3,z5,z415,z6]),(0,[z0,z1,z2,z3,z5,z416,z6]),(0,[z0,z1,z2,z417,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z104,z6])],[(0,[z418,z0,z1,z2,z3,z5,z6])],[(0,[z419,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z159,z5,z6]),(0,[z0,z420,z1,z2,z3,z5,z6]),(0,[z421,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z422,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z423,z6]),(0,[z0,z65,z1,z2,z3,z5,z66])],[(0,[z0,z1,z2,z3,z424,z5,z6]),(0,[z0,z1,z2,z3,z425,z5,z6]),(0,[z426,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z427])],[(0,[z0,z428,z1,z2,z3,z5,z6]),(0,[z184,z226,z1,z2,z3,z5,z6]),(0,[z57,z0,z58,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z429,z5,z6]),(0,[z430,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z431,z2,z3,z5,z6])],[(0,[z432,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z433,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z434,z6]),(0,[z0,z1,z2,z435,z3,z5,z6]),(0,[z57,z0,z26,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z436,z6]),(0,[z0,z1,z2,z437,z3,z5,z6])],[(0,[z438,z0,z1,z2,z3,z5,z6]),(1,[z142,z77,z2,z3,z5,z6]),(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z440,z5,z6]),(0,[z0,z103,z2,z3,z41,z5,z6]),(0,[z0,z58,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z188]),(1,[z0,z1,z2,z3,z307,z187])],[(0,[z0,z441,z1,z2,z3,z5,z6]),(0,[z0,z1,z360,z2,z3,z5,z6]),(0,[z0,z51,z1,z331,z3,z5,z6]),(0,[z0,z1,z2,z3,z442,z5,z6])],[(0,[z70,z0,z1,z2,z259,z5,z6]),(0,[z0,z1,z443,z2,z3,z5,z6]),(1,[z0,z179,z1,z2,z3,z6]),(0,[z0,z444,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z445,z5,z6]),(1,[z0,z446,z2,z3,z5,z6]),(1,[z0,z447,z2,z3,z5,z6]),(0,[z0,z448,z1,z2,z3,z5,z6])],[(0,[z449,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z360,z2,z54,z5,z6])],[(0,[z0,z450,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z91,z5,z6])],[(0,[z0,z1,z2,z3,z5,z451,z6]),(0,[z0,z1,z452,z2,z3,z5,z6])],[(0,[z0,z453,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z454,z5,z6]),(0,[z0,z1,z2,z455,z3,z5,z6]),(1,[z57,z0,z58,z1,z5,z6]),(0,[z0,z1,z2,z3,z5,z456,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z457,z6]),(0,[z0,z1,z458,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z459,z6]),(0,[z57,z0,z1,z360,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z170])],[(0,[z0,z1,z2,z3,z5,z460,z6]),(0,[z49,z1,z2,z259,z3,z5,z6]),(0,[z0,z1,z461,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z401,z188])],[(0,[z184,z0,z1,z215,z3,z5,z6]),(0,[z0,z462,z1,z2,z3,z5,z6]),(0,[z0,z463,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z464,z6]),(0,[z0,z1,z2,z465,z3,z5,z6]),(0,[z0,z1,z2,z3,z466,z5,z6]),(0,[z0,z1,z2,z3,z5,z48,z6]),(0,[z0,z1,z467,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z468])],[(0,[z0,z1,z469,z2,z3,z5,z6]),(0,[z0,z470,z1,z2,z3,z5,z6])],[(0,[z57,z0,z1,z215,z3,z5,z6])],[(0,[z0,z1,z2,z54,z5,z15,z6]),(0,[z471,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z446,z2,z3,z5,z6]),(0,[z0,z1,z472,z2,z3,z5,z6]),(0,[z0,z238,z1,z72,z2,z5,z6]),(0,[z0,z1,z473,z2,z3,z5,z6])]],
   [[(0,[z0,z474,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z475,z3,z5,z6]),(0,[z476,z0,z1,z2,z3,z5,z6])],[(0,[z12,z173,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z183,z3,z5,z6]),(1,[z0,z1,z2,z194,z5,z6]),(1,[z0,z1,z183,z3,z5,z170]),(0,[z0,z477,z1,z2,z3,z5,z6]),(0,[z0,z478,z1,z2,z3,z5,z6]),(0,[z479,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z480,z3,z5,z6])],[(0,[z70,z1,z2,z3,z71,z5,z6]),(0,[z0,z1,z2,z3,z481,z5,z6]),(0,[z0,z1,z482,z2,z3,z5,z6])],[(0,[z0,z1,z3,z5,z48,z104,z6]),(0,[z0,z1,z2,z3,z5,z222,z104]),(0,[z0,z1,z2,z3,z483,z5,z6]),(0,[z0,z1,z2,z3,z5,z484,z6]),(0,[z0,z7,z1,z183,z3,z5,z6]),(0,[z0,z1,z2,z75,z3,z5,z6]),(0,[z0,z16,z2,z3,z5,z6,z188])],[(0,[z113,z0,z1,z2,z3,z5,z6]),(0,[z142,z0,z1,z2,z3,z5,z271]),(0,[z0,z1,z485,z2,z3,z5,z6])],[(0,[z169,z0,z40,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z486,z6]),(0,[z169,z0,z1,z2,z3,z307,z6])],[(0,[z487,z0,z1,z2,z3,z5,z6]),(0,[z226,z0,z1,z215,z3,z5,z6]),(0,[z0,z1,z488,z2,z3,z5,z6]),(0,[z0,z1,z489,z2,z3,z5,z6]),(0,[z0,z1,z2,z277,z3,z5,z6])]],
   [[(0,[z82,z44,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z490,z6]),(0,[z0,z1,z2,z3,z5,z491,z6]),(0,[z0,z492,z1,z2,z3,z5,z6])],[(0,[z142,z0,z77,z2,z3,z5,z6]),(0,[z493,z0,z1,z2,z3,z5,z6]),(0,[z70,z49,z1,z2,z3,z5,z6]),(0,[z0,z22,z1,z2,z3,z5,z31]),(0,[z0,z1,z494,z2,z3,z5,z6]),(0,[z0,z495,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z496]),(0,[z0,z1,z331,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z497,z6]),(0,[z0,z1,z59,z2,z3,z5,z6])],[(0,[z142,z0,z36,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z498]),(0,[z0,z1,z3,z5,z6,z398,z188])],[(0,[z70,z0,z51,z1,z2,z5,z6]),(0,[z0,z40,z1,z2,z3,z5,z13]),(0,[z499,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z183,z2,z3,z5,z170]),(0,[z500,z0,z1,z2,z3,z5,z6])],[(0,[z501,z0,z1,z2,z3,z5,z6]),(0,[z0,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z502])],[(1,[z0,z1,z2,z3,z5,z271])],[(1,[z173,z1,z2,z3,z5,z13]),(0,[z12,z1,z2,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z503,z6]),(0,[z57,z0,z1,z3,z5,z150,z6])],[(0,[z0,z447,z1,z2,z3,z5,z6]),(0,[z0,z504,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z14,z46,z6]),(0,[z0,z1,z2,z3,z5,z505,z6]),(0,[z0,z506,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z507,z6]),(0,[z0,z1,z2,z3,z508,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z66,z13])],[(0,[z70,z0,z1,z2,z3,z5,z301]),(0,[z0,z1,z509,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z510,z6]),(0,[z511,z0,z1,z2,z3,z5,z6]),(0,[z0,z7,z1,z3,z5,z150,z6])],[(0,[z142,z0,z1,z2,z3,z5,z451]),(0,[z0,z512,z1,z2,z3,z5,z6]),(0,[z0,z25,z84,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z513,z6])],[(0,[z514,z0,z1,z2,z3,z5,z6]),(0,[z0,z515,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z516]),(0,[z0,z1,z2,z3,z517,z5,z6]),(0,[z0,z58,z1,z3,z54,z5,z6]),(0,[z0,z1,z183,z3,z91,z5,z6]),(0,[z169,z0,z1,z2,z3,z5,z187])],[(0,[z0,z1,z518,z2,z3,z5,z6])],[(0,[z0,z1,z101,z2,z379,z5,z6]),(0,[z0,z1,z2,z3,z5,z519,z6]),(0,[z0,z1,z360,z3,z54,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z520])],[(0,[z521,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z522,z5,z6]),(0,[z0,z1,z2,z3,z5,z523,z6]),(1,[z0,z135,z2,z3,z5,z6]),(1,[z0,z103,z2,z3,z41,z6]),(0,[z0,z1,z524,z2,z3,z5,z6]),(0,[z0,z1,z183,z3,z5,z6,z170])],[(1,[z49,z1,z2,z259,z5,z6]),(0,[z49,z0,z1,z2,z14,z5,z6]),(0,[z525,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z526,z5,z6])]],
   [[(0,[z0,z1,z2,z527,z3,z5,z6]),(0,[z0,z1,z17,z3,z91,z5,z6])],[(0,[z528,z0,z1,z2,z3,z5,z6]),(0,[z0,z529,z1,z2,z3,z5,z6]),(0,[z0,z530,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z451]),(0,[z0,z1,z2,z531,z3,z5,z6]),(0,[z0,z532,z1,z2,z3,z5,z6]),(1,[z0,z420,z1,z3,z5,z6])],[(0,[z533,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z114,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z222,z6]),(0,[z0,z1,z2,z3,z5,z534,z6])],[(0,[z535,z0,z1,z2,z3,z5,z6]),(0,[z0,z373,z1,z2,z3,z5,z6]),(0,[z0,z72,z2,z3,z159,z5,z6]),(0,[z536,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z251,z5,z6])],[(0,[z0,z1,z215,z3,z91,z5,z6]),(0,[z0,z1,z537,z2,z3,z5,z6]),(0,[z538,z0,z1,z2,z3,z5,z6])],[(0,[z539,z0,z1,z2,z3,z5,z6]),(0,[z0,z540,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z13,z94]),(0,[z0,z1,z541,z2,z3,z5,z6]),(0,[z0,z542,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z543]),(0,[z0,z1,z2,z3,z5,z544,z6]),(0,[z0,z545,z1,z2,z3,z5,z6])],[(1,[z184,z1,z101,z3,z5,z6]),(1,[z82,z1,z2,z3,z83,z6]),(0,[z0,z98,z26,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z14,z5,z6]),(0,[z0,z546,z1,z2,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z210,z5,z6]),(0,[z0,z547,z1,z2,z3,z5,z6]),(0,[z0,z236,z1,z2,z3,z5,z104]),(0,[z0,z1,z2,z3,z5,z548,z6])],[(0,[z549,z0,z1,z2,z3,z5,z6]),(0,[z550,z0,z1,z2,z3,z5,z6]),(0,[z0,z551,z1,z2,z3,z5,z6]),(0,[z0,z1,z552,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z553,z6])],[(0,[z1,z2,z3,z46,z5,z83,z6]),(0,[z0,z554,z1,z2,z3,z5,z6])],[(0,[z0,z373,z1,z2,z5,z83,z6]),(0,[z0,z1,z2,z287,z3,z5,z6]),(0,[z0,z1,z555,z2,z3,z5,z6]),(0,[z0,z58,z1,z2,z5,z15,z6])],[(0,[z0,z77,z1,z2,z3,z5,z6]),(0,[z0,z238,z1,z2,z3,z5,z6]),(0,[z0,z103,z1,z2,z3,z5,z6]),(0,[z0,z556,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z557,z6]),(0,[z0,z1,z2,z3,z5,z6,z558])],[(0,[z184,z0,z1,z2,z3,z340,z6])],[(0,[z0,z1,z2,z3,z5,z559,z6])],[(0,[z0,z1,z560,z2,z3,z5,z6]),(0,[z0,z1,z561,z2,z3,z5,z6]),(0,[z0,z1,z2,z259,z3,z5,z6]),(0,[z0,z1,z2,z3,z562,z5,z6]),(0,[z563,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z564,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z565,z6])],[(0,[z0,z566,z1,z2,z3,z5,z6]),(0,[z117,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z567]),(0,[z0,z2,z3,z5,z23,z6,z161])],[(0,[z0,z98,z51,z1,z2,z3,z6]),(0,[z0,z1,z568,z2,z3,z5,z6])],[(0,[z86,z0,z77,z2,z3,z5,z6]),(0,[z0,z569,z1,z2,z3,z5,z6])],[(0,[z570,z0,z1,z2,z3,z5,z6]),(0,[z571,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z572]),(0,[z0,z573,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z574,z6])],[(1,[z0,z1,z148,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z575,z6]),(0,[z0,z51,z1,z2,z33,z5,z6])],[(0,[z0,z1,z2,z3,z5,z576,z6]),(0,[z0,z98,z1,z215,z3,z5,z6]),(0,[z0,z1,z2,z3,z340,z5,z6]),(0,[z577,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z578]),(0,[z0,z1,z2,z3,z5,z579,z6]),(0,[z0,z1,z2,z3,z580,z5,z6]),(0,[z581,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z582,z6]),(0,[z0,z1,z583,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z584,z5,z6]),(0,[z86,z0,z1,z72,z2,z5,z6]),(0,[z0,z1,z585,z2,z3,z5,z6]),(0,[z0,z1,z586,z2,z3,z5,z6])]],
   [[(0,[z587,z0,z1,z2,z3,z5,z6])],[(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z0,z84,z2,z3,z166,z5,z6]),(0,[z0,z1,z2,z3,z5,z589,z6]),(0,[z0,z1,z225,z2,z3,z5,z66])],[(0,[z142,z0,z1,z2,z3,z5,z6]),(0,[z184,z1,z101,z2,z3,z5,z6]),(0,[z0,z1,z590,z2,z3,z5,z6]),(0,[z0,z98,z1,z183,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z401])],[(0,[z0,z1,z2,z3,z5,z591,z6]),(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z0,z1,z2,z33,z14,z5,z6]),(0,[z0,z1,z2,z3,z593,z5,z6]),(0,[z0,z1,z594,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z595,z6])],[(0,[z0,z1,z2,z3,z596,z5,z6]),(0,[z0,z597,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z94])],[(0,[z0,z1,z2,z3,z598,z5,z6]),(0,[z0,z599,z1,z2,z3,z5,z6]),(1,[z0,z1,z45,z3,z5,z6]),(1,[z0,z26,z3,z166,z5,z6]),(0,[z0,z1,z600,z2,z3,z5,z6]),(0,[z0,z1,z601,z2,z3,z5,z6]),(0,[z0,z98,z1,z2,z251,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z398])],[(0,[z0,z602,z1,z2,z3,z5,z6]),(0,[z603,z0,z1,z2,z3,z5,z6]),(0,[z604,z0,z1,z2,z3,z5,z6]),(0,[z0,z605,z1,z2,z3,z5,z6])],[(0,[z606,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z215,z3,z5,z6]),(0,[z0,z607,z1,z2,z3,z5,z6]),(0,[z0,z236,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z608]),(0,[z0,z1,z2,z3,z5,z6,z609]),(0,[z0,z610,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z611,z6]),(0,[z0,z1,z2,z612,z3,z5,z6]),(0,[z0,z1,z2,z3,z613,z5,z6]),(0,[z0,z1,z614,z2,z3,z5,z6])],[(0,[z615,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z616,z2,z3,z5,z6]),(0,[z0,z1,z617,z2,z3,z5,z6]),(0,[z618,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z619,z2,z3,z5,z6]),(0,[z0,z25,z1,z84,z3,z5,z6]),(0,[z0,z620,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z621,z3,z5,z6]),(0,[z622,z0,z1,z2,z3,z5,z6]),(0,[z623,z0,z1,z2,z3,z5,z6]),(1,[z226,z1,z215,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z624,z6]),(0,[z0,z1,z625,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z626])],[(0,[z627,z0,z1,z2,z3,z5,z6]),(0,[z628,z0,z1,z2,z3,z5,z6]),(0,[z629,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z630,z6]),(0,[z0,z1,z2,z631,z3,z5,z6]),(0,[z0,z1,z2,z3,z307,z5,z188])],[(0,[z70,z0,z1,z325,z3,z5,z6]),(0,[z0,z1,z2,z3,z14,z83,z6]),(0,[z0,z1,z2,z3,z5,z632,z6]),(0,[z0,z1,z633,z2,z3,z5,z6]),(0,[z0,z1,z2,z194,z3,z5,z6]),(0,[z0,z1,z634,z2,z3,z5,z6]),(0,[z0,z1,z219,z3,z5,z6,z188])],[(0,[z0,z635,z1,z2,z3,z5,z6]),(0,[z0,z636,z1,z2,z3,z5,z6]),(1,[z0,z1,z198,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z637]),(0,[z0,z1,z638,z2,z3,z5,z6])],[],[(0,[z0,z1,z639,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z640])]],
   [[(0,[z0,z1,z2,z3,z5,z115,z6]),(0,[z0,z26,z1,z3,z166,z5,z6])],[(0,[z70,z0,z1,z2,z14,z5,z6]),(0,[z44,z0,z1,z2,z3,z83,z6]),(0,[z641,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z642,z5,z6]),(0,[z0,z1,z643,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z644,z5,z6]),(0,[z49,z0,z1,z2,z71,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z6]),(0,[z1,z2,z3,z5,z31,z6,z13]),(0,[z0,z645,z1,z2,z3,z5,z6])],[(0,[z0,z1,z646,z2,z3,z5,z6]),(0,[z0,z1,z647,z2,z3,z5,z6]),(0,[z86,z0,z238,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z648,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z6]),(0,[z649,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z650,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z651,z6]),(0,[z0,z1,z2,z652,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z653,z6]),(0,[z0,z1,z2,z3,z5,z6,z654])],[(0,[z0,z1,z2,z3,z655,z5,z6]),(0,[z0,z420,z1,z3,z5,z104,z6]),(0,[z0,z1,z2,z3,z5,z6,z656])],[(0,[z1,z101,z2,z215,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z223]),(0,[z0,z1,z2,z3,z5,z6,z657]),(0,[z0,z1,z2,z3,z5,z658,z6]),(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z660,z6]),(0,[z0,z1,z2,z3,z5,z661,z6]),(0,[z0,z1,z662,z2,z3,z5,z6]),(0,[z0,z1,z663,z2,z3,z5,z6])],[(0,[z0,z664,z1,z2,z3,z5,z6]),(0,[z0,z1,z665,z2,z3,z5,z6]),(1,[z117,z0,z2,z3,z104,z6]),(0,[z666,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z70,z0,z446,z2,z3,z5,z6]),(0,[z70,z0,z447,z2,z3,z5,z6]),(0,[z0,z1,z2,z667,z3,z5,z6]),(0,[z0,z1,z2,z668,z3,z5,z6]),(0,[z669,z0,z1,z2,z3,z5,z6]),(0,[z0,z670,z1,z2,z3,z5,z6]),(0,[z0,z1,z671,z2,z3,z5,z6]),(0,[z0,z40,z1,z2,z3,z307,z5]),(0,[z0,z1,z2,z3,z672,z5,z6]),(0,[z0,z1,z2,z3,z5,z150,z6]),(1,[z0,z1,z225,z2,z5,z94]),(0,[z673,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z674,z3,z5,z6]),(0,[z0,z1,z675,z2,z3,z5,z6]),(0,[z0,z1,z2,z676,z3,z5,z6]),(0,[z0,z1,z2,z677,z3,z5,z6])],[(0,[z0,z1,z2,z3,z71,z5,z6]),(0,[z678,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z679]),(0,[z0,z1,z2,z680,z3,z5,z6]),(0,[z681,z0,z1,z2,z3,z5,z6])],[(0,[z682,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z683,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z301,z6]),(0,[z0,z135,z1,z2,z3,z5,z6]),(0,[z0,z684,z1,z2,z3,z5,z6]),(0,[z57,z0,z1,z3,z5,z18,z6]),(0,[z0,z685,z1,z2,z3,z5,z6]),(0,[z686,z0,z1,z2,z3,z5,z6])],[(0,[z0,z25,z1,z3,z91,z5,z6]),(0,[z687,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z688,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z689,z6]),(0,[z0,z1,z2,z3,z5,z6,z690]),(0,[z691,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z45,z2,z3,z5,z6]),(0,[z692,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z693,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z694,z6]),(0,[z0,z695,z1,z2,z3,z5,z6]),(0,[z696,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z697,z5,z6])],[],[(0,[z0,z698,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z379,z5,z6]),(0,[z173,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z13])],[(0,[z0,z699,z1,z2,z3,z5,z6]),(0,[z169,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z700,z6]),(0,[z86,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z41,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z701])],[],[(0,[z0,z702,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z703,z5,z6]),(0,[z0,z1,z2,z3,z704,z5,z6]),(0,[z0,z51,z1,z2,z3,z14,z6])],[(0,[z0,z10,z1,z101,z2,z5,z6]),(0,[z0,z705,z1,z2,z3,z5,z6]),(0,[z44,z0,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z166,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z5,z6]),(0,[z0,z708,z2,z3,z5,z6]),(0,[z49,z1,z2,z709,z5,z6]),(0,[z0,z1,z710,z3,z5,z6])],[(0,[z0,z179,z1,z215,z3,z6]),(0,[z0,z446,z2,z3,z5,z301]),(0,[z0,z447,z2,z3,z5,z301]),(0,[z0,z40,z2,z3,z5,z578]),(0,[z0,z1,z2,z3,z711,z6]),(0,[z0,z1,z712,z3,z5,z6])],[(0,[z0,z1,z2,z3,z713,z6]),(0,[z0,z1,z2,z3,z5,z714]),(0,[z44,z1,z287,z3,z46,z6]),(0,[z0,z1,z2,z715,z5,z6]),(0,[z716,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z717,z18,z6])],[(1,[z718,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z719,z6]),(0,[z226,z1,z720,z3,z5,z6]),(0,[z49,z0,z1,z277,z5,z6]),(0,[z0,z721,z2,z3,z5,z6]),(0,[z0,z2,z3,z722,z104,z6]),(0,[z117,z0,z236,z2,z3,z104]),(0,[z0,z179,z1,z277,z3,z6]),(0,[z0,z1,z225,z2,z5,z723])]],
   [[(0,[z0,z36,z2,z3,z5,z451]),(0,[z0,z1,z45,z3,z5,z6]),(0,[z0,z58,z1,z2,z115,z6]),(0,[z687,z1,z2,z3,z5,z13]),(0,[z0,z26,z3,z166,z5,z6]),(0,[z0,z84,z724,z3,z5,z6]),(0,[z169,z0,z16,z2,z3,z5])],[(0,[z0,z1,z725,z3,z5,z6]),(0,[z1,z101,z720,z3,z5,z6]),(0,[z0,z726,z1,z2,z3,z5]),(0,[z0,z1,z3,z5,z6,z727]),(0,[z0,z728,z1,z3,z5,z6]),(0,[z0,z1,z3,z5,z729,z6]),(0,[z0,z16,z3,z5,z6,z398])],[(0,[z77,z718,z2,z3,z5,z6]),(0,[z0,z98,z1,z3,z309,z6]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z49,z1,z2,z593,z5,z6]),(0,[z0,z373,z1,z730,z5,z6]),(0,[z0,z1,z175,z54,z5,z6]),(0,[z731,z1,z2,z3,z5,z6]),(0,[z0,z1,z277,z33,z5,z6]),(0,[z0,z1,z2,z33,z711,z6])],[(0,[z0,z179,z1,z101,z3,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z169,z0,z1,z2,z3,z188])]],
   [[(0,[z0,z1,z733,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z734]),(0,[z0,z1,z735,z2,z3,z5]),(0,[z0,z736,z2,z3,z5,z6]),(0,[z49,z1,z2,z282,z5,z6]),(0,[z737,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z667,z14,z6]),(1,[z1,z2,z3,z5,z738]),(0,[z86,z0,z739,z2,z5,z6]),(0,[z0,z3,z5,z6,z398,z401])],[(0,[z0,z1,z3,z5,z6,z740]),(0,[z0,z179,z1,z360,z54,z6]),(0,[z0,z1,z2,z126,z3,z6]),(0,[z0,z741,z2,z3,z5,z6]),(0,[z0,z98,z1,z3,z18,z6]),(1,[z0,z1,z2,z711,z6]),(0,[z0,z742,z2,z3,z5,z6])],[(0,[z1,z720,z2,z3,z5,z6]),(0,[z0,z446,z2,z3,z5,z223]),(0,[z0,z447,z2,z3,z5,z223]),(0,[z44,z1,z2,z3,z743,z6]),(0,[z0,z744,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z2,z5,z723,z6])]],
   [[(0,[z0,z1,z3,z91,z285,z6]),(0,[z0,z1,z2,z3,z746,z6]),(0,[z0,z51,z1,z2,z15,z6])],[(0,[z0,z1,z2,z3,z747,z6]),(0,[z0,z1,z2,z3,z5,z748]),(0,[z0,z1,z749,z3,z5,z6]),(0,[z0,z40,z2,z3,z353,z5]),(0,[z0,z1,z750,z3,z5,z6])],[(0,[z78,z1,z215,z3,z5,z6]),(0,[z0,z373,z1,z751,z5,z6]),(0,[z0,z1,z752,z3,z5,z6]),(0,[z753,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z754,z5,z6]),(0,[z0,z2,z3,z5,z755,z6]),(0,[z0,z1,z2,z3,z5,z756]),(0,[z70,z0,z1,z277,z5,z6]),(0,[z0,z1,z2,z3,z722,z6]),(0,[z0,z1,z3,z5,z6,z757]),(0,[z0,z1,z758,z3,z5,z6])]],
   [[(0,[z0,z1,z336,z3,z91,z6]),(0,[z0,z759,z1,z2,z5,z6]),(0,[z0,z760,z2,z3,z5,z6]),(0,[z117,z0,z2,z3,z722,z6]),(0,[z0,z236,z420,z1,z3,z5]),(0,[z0,z62,z58,z1,z5,z6])],[(0,[z142,z77,z2,z3,z5,z271]),(0,[z0,z1,z761,z2,z5,z6]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z0,z1,z3,z5,z48,z222]),(0,[z0,z1,z2,z33,z251,z6]),(0,[z0,z1,z3,z5,z150,z763]),(0,[z764,z1,z2,z3,z5,z6]),(0,[z0,z16,z2,z3,z307,z5]),(0,[z0,z1,z765,z3,z5,z6])],[(0,[z0,z2,z3,z5,z766,z6]),(0,[z70,z1,z2,z71,z115,z6]),(0,[z0,z1,z767,z3,z5,z6]),(0,[z0,z1,z3,z5,z763,z6])],[(0,[z0,z1,z101,z3,z340,z6]),(0,[z70,z1,z2,z71,z39,z6]),(0,[z0,z1,z768,z3,z5,z6])]],
   [[(0,[z0,z1,z769,z3,z5,z6]),(0,[z86,z0,z617,z2,z5,z6]),(0,[z421,z1,z101,z3,z5,z6]),(0,[z0,z1,z251,z5,z18,z6]),(0,[z0,z98,z1,z194,z18,z6])],[(0,[z0,z770,z2,z3,z5,z6]),(0,[z0,z771,z2,z3,z5,z6]),(0,[z0,z348,z1,z3,z5,z150]),(0,[z0,z1,z2,z3,z187,z772])],[(0,[z142,z718,z2,z3,z5,z6]),(0,[z0,z773,z2,z3,z5,z6]),(0,[z184,z10,z1,z101,z5,z6]),(0,[z117,z0,z2,z3,z104,z6])],[(0,[z0,z774,z2,z3,z5,z6]),(0,[z0,z135,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z775]),(0,[z776,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z777,z5,z6])]],
   [[(0,[z0,z778,z2,z3,z5,z6]),(0,[z0,z1,z779,z3,z5,z6]),(0,[z0,z302,z1,z2,z5,z66]),(0,[z0,z1,z2,z3,z307,z56])],[(0,[z0,z1,z2,z3,z340,z6]),(0,[z57,z0,z10,z1,z5,z6]),(0,[z70,z1,z325,z71,z5,z6]),(0,[z0,z1,z780,z3,z5,z6]),(0,[z1,z2,z709,z71,z5,z6]),(0,[z0,z1,z251,z5,z150,z6]),(0,[z0,z1,z3,z91,z717,z6]),(0,[z0,z1,z781,z3,z5,z6])],[(0,[z0,z1,z2,z3,z782,z6]),(0,[z0,z1,z325,z3,z39,z6]),(0,[z0,z1,z783,z3,z5,z6]),(0,[z0,z98,z1,z3,z523,z6]),(0,[z173,z1,z2,z3,z5,z13]),(0,[z0,z22,z2,z3,z5,z220]),(0,[z784,z1,z2,z3,z5,z6]),(0,[z0,z65,z1,z75,z5,z66])],[(0,[z0,z114,z2,z3,z5,z6]),(0,[z351,z1,z101,z3,z5,z6]),(0,[z82,z1,z2,z3,z743,z6]),(0,[z0,z26,z524,z3,z5,z6]),(0,[z785,z0,z1,z2,z5,z6]),(0,[z0,z786,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z787,z5,z6]),(0,[z0,z1,z788,z3,z5,z6]),(0,[z0,z1,z2,z789,z5,z6]),(0,[z0,z179,z1,z17,z3,z6]),(0,[z0,z179,z1,z2,z251,z6]),(0,[z0,z1,z2,z3,z5,z790]),(0,[z0,z1,z219,z3,z5,z6])],[(0,[z113,z718,z2,z3,z5,z6]),(0,[z0,z1,z2,z791,z5,z6]),(0,[z1,z2,z3,z709,z5,z6]),(0,[z0,z1,z2,z3,z5,z792]),(0,[z0,z793,z1,z2,z3,z6]),(0,[z0,z25,z3,z5,z484,z6]),(0,[z117,z0,z3,z48,z104,z6]),(0,[z0,z2,z3,z41,z6,z249]),(0,[z0,z1,z2,z33,z4,z6])],[(0,[z0,z1,z2,z3,z5,z794]),(0,[z142,z77,z2,z3,z5,z451]),(0,[z0,z1,z2,z795,z5,z6]),(1,[z1,z2,z3,z743,z6]),(0,[z0,z1,z796,z3,z5,z6]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z0,z1,z2,z3,z6,z798]),(0,[z0,z1,z2,z3,z799,z6])],[(0,[z0,z800,z2,z3,z5,z6]),(0,[z0,z98,z1,z3,z8,z6]),(1,[z0,z1,z3,z5,z763]),(0,[z0,z1,z2,z3,z5,z772])]],
   [[(0,[z0,z1,z2,z801,z5,z6]),(0,[z802,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z722,z6])],[(0,[z0,z803,z2,z3,z5,z6]),(0,[z0,z804,z2,z3,z5,z6]),(0,[z1,z2,z3,z46,z743,z6]),(0,[z0,z1,z2,z3,z805,z6]),(0,[z0,z40,z2,z3,z5,z161]),(0,[z0,z1,z2,z3,z806,z6])],[(0,[z0,z135,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z807,z6]),(0,[z0,z1,z2,z3,z808,z6]),(0,[z0,z1,z148,z3,z115,z6]),(0,[z0,z809,z2,z3,z5,z6]),(0,[z0,z1,z2,z251,z46,z6]),(0,[z12,z1,z2,z3,z5,z738]),(0,[z0,z1,z810,z3,z5,z6]),(0,[z811,z1,z2,z3,z5,z6]),(0,[z0,z1,z812,z3,z5,z6]),(0,[z0,z103,z2,z3,z41,z6])],[(0,[z0,z1,z2,z813,z5,z6]),(0,[z49,z1,z2,z259,z5,z6]),(0,[z0,z1,z2,z814,z3,z6]),(0,[z57,z0,z815,z1,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z816])],[(0,[z0,z817,z1,z2,z5,z6]),(0,[z0,z818,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z819]),(0,[z0,z1,z2,z3,z5,z222]),(0,[z0,z1,z2,z3,z6,z820])],[(0,[z0,z821,z1,z3,z5,z6]),(0,[z0,z10,z1,z54,z5,z6]),(0,[z0,z446,z2,z3,z39,z6]),(0,[z0,z447,z2,z3,z39,z6]),(0,[z1,z2,z3,z5,z822,z6]),(0,[z0,z823,z2,z3,z5,z6])],[(0,[z184,z1,z101,z3,z102,z6]),(0,[z0,z1,z2,z3,z5,z824]),(0,[z0,z1,z2,z3,z5,z825])]],
   [[(0,[z0,z1,z826,z3,z5,z6]),(0,[z1,z718,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z827,z6]),(0,[z0,z828,z2,z3,z5,z6])],[(0,[z0,z1,z54,z5,z355,z6])],[(0,[z0,z1,z2,z3,z829,z6])],[(0,[z0,z1,z2,z3,z830,z6]),(0,[z184,z1,z101,z3,z5,z6]),(0,[z0,z51,z1,z2,z115,z6]),(0,[z82,z1,z2,z3,z83,z6]),(0,[z0,z1,z831,z2,z5,z6]),(0,[z0,z832,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z833,z5,z6]),(0,[z0,z446,z325,z3,z5,z6]),(0,[z0,z447,z325,z3,z5,z6]),(0,[z0,z834,z2,z3,z5,z6]),(0,[z0,z1,z2,z14,z172,z6]),(0,[z44,z1,z45,z3,z46,z6])],[(0,[z12,z1,z2,z3,z5,z31]),(0,[z835,z1,z2,z3,z5,z6])],[(0,[z0,z836,z2,z3,z5,z6]),(0,[z837,z0,z1,z3,z5,z6])],[(0,[z0,z1,z2,z3,z115,z6]),(0,[z70,z212,z1,z2,z5,z6]),(0,[z0,z373,z1,z2,z15,z6]),(0,[z0,z35,z1,z3,z5,z6])]],
   [[(0,[z0,z1,z838,z3,z5,z6]),(0,[z0,z1,z839,z3,z5,z6]),(0,[z0,z1,z840,z3,z5,z6])],[(0,[z0,z1,z2,z3,z115,z301]),(0,[z117,z0,z2,z3,z222,z104]),(0,[z0,z841,z2,z3,z5,z6])],[(0,[z0,z1,z2,z54,z115,z6]),(0,[z0,z1,z3,z5,z48,z6]),(0,[z0,z2,z3,z5,z6,z401]),(0,[z0,z1,z3,z5,z842,z6]),(0,[z0,z1,z2,z251,z5,z6]),(0,[z0,z179,z1,z2,z33,z6]),(0,[z843,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z844]),(1,[z1,z720,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z845]),(0,[z0,z1,z2,z3,z5,z846])]],
   [[(0,[z0,z1,z2,z3,z847,z6]),(0,[z0,z1,z848,z3,z5,z6]),(0,[z0,z1,z2,z849,z5,z6])],[(0,[z0,z1,z2,z5,z6,z850]),(0,[z0,z851,z2,z3,z5,z6]),(0,[z0,z7,z1,z3,z5,z763])],[(0,[z0,z815,z1,z360,z5,z6])],[(0,[z0,z40,z2,z3,z5,z232]),(0,[z0,z852,z1,z2,z3,z5]),(0,[z0,z373,z1,z17,z2,z6]),(0,[z0,z25,z1,z251,z5,z6])]],
   [[(0,[z0,z718,z2,z3,z5,z6]),(0,[z297,z77,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z853])],[(0,[z0,z1,z148,z3,z5,z6]),(0,[z0,z1,z2,z854,z5,z6]),(0,[z0,z855,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z738,z13]),(0,[z0,z1,z2,z3,z856,z6]),(0,[z0,z1,z857,z3,z5,z6]),(0,[z0,z815,z1,z2,z5,z6]),(0,[z0,z1,z858,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z859])],[(0,[z0,z1,z860,z3,z5,z6]),(0,[z0,z1,z861,z2,z5,z6]),(0,[z0,z1,z45,z862,z5,z6]),(0,[z0,z238,z739,z2,z5,z6]),(0,[z57,z0,z74,z1,z5,z6]),(0,[z0,z863,z2,z3,z5,z6]),(0,[z864,z1,z2,z3,z5,z6]),(0,[z0,z51,z1,z2,z711,z6])],[(0,[z0,z1,z2,z3,z865,z6]),(0,[z0,z1,z2,z3,z5,z866]),(0,[z184,z1,z101,z3,z340,z6]),(0,[z0,z1,z148,z3,z5,z301]),(0,[z0,z1,z2,z3,z115,z223]),(0,[z0,z25,z724,z3,z5,z6]),(0,[z867,z1,z2,z3,z5,z6]),(0,[z0,z1,z75,z3,z5,z6]),(0,[z0,z1,z17,z3,z93,z6]),(0,[z0,z219,z3,z5,z6,z401])]],
   [[(0,[z0,z1,z868,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z869]),(0,[z0,z1,z870,z3,z5,z6]),(0,[z0,z1,z3,z5,z871,z6]),(0,[z0,z1,z872,z3,z5,z6]),(0,[z0,z873,z2,z3,z5,z6]),(0,[z299,z1,z2,z3,z46,z6]),(0,[z0,z1,z874,z3,z5,z6]),(0,[z0,z1,z3,z5,z875,z6]),(1,[z0,z1,z3,z717,z6])],[(0,[z0,z739,z2,z159,z5,z6]),(0,[z0,z1,z876,z3,z5,z6]),(0,[z0,z1,z277,z3,z5,z6]),(0,[z0,z1,z3,z5,z717,z6])],[(0,[z0,z1,z2,z862,z5,z6]),(0,[z12,z114,z2,z3,z5,z31]),(0,[z0,z40,z2,z3,z5,z567]),(0,[z0,z2,z3,z5,z877,z161])]],
   [[(0,[z0,z77,z2,z3,z5,z451]),(0,[z0,z1,z878,z2,z5,z6]),(0,[z0,z1,z2,z879,z5,z6]),(0,[z880,z1,z2,z3,z5,z6]),(0,[z0,z739,z2,z3,z5,z6]),(0,[z0,z1,z881,z2,z3,z5]),(0,[z0,z1,z882,z3,z5,z6])],[(0,[z0,z179,z1,z2,z3,z6]),(0,[z0,z1,z183,z3,z5,z763])],[(0,[z0,z1,z2,z3,z102,z6]),(0,[z0,z1,z2,z3,z5,z883]),(0,[z0,z58,z1,z325,z5,z6])],[(0,[z0,z1,z884,z3,z5,z6]),(0,[z0,z724,z3,z166,z5,z6]),(0,[z0,z22,z2,z3,z5,z345]),(0,[z0,z179,z1,z3,z18,z6]),(0,[z0,z1,z3,z91,z6,z85]),(0,[z885,z1,z2,z3,z5,z6]),(0,[z169,z0,z1,z219,z3,z188])]],
   [[(0,[z0,z886,z2,z3,z5,z6]),(0,[z0,z1,z2,z887,z5,z6]),(0,[z1,z2,z3,z5,z738,z6]),(0,[z0,z40,z2,z3,z5,z267])],[(0,[z0,z1,z2,z3,z5,z888]),(0,[z0,z1,z148,z3,z5,z223]),(0,[z0,z1,z889,z3,z5,z6]),(0,[z0,z51,z1,z2,z251,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z113,z36,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z890]),(0,[z226,z1,z215,z3,z5,z6]),(0,[z0,z891,z2,z3,z5,z6]),(0,[z12,z135,z2,z3,z5,z31]),(0,[z57,z0,z58,z1,z5,z6])],[(0,[z0,z1,z892,z3,z5,z6]),(0,[z0,z1,z893,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z23]),(0,[z0,z2,z3,z5,z894,z6]),(0,[z169,z0,z1,z2,z3,z772])]],
   [[(0,[z0,z1,z2,z3,z5,z895]),(0,[z0,z1,z2,z3,z5,z896]),(0,[z0,z1,z2,z3,z5,z301]),(0,[z0,z1,z897,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z898]),(0,[z117,z0,z2,z3,z534,z6]),(0,[z0,z420,z1,z3,z5,z222]),(0,[z0,z179,z1,z3,z150,z6])],[(0,[z0,z1,z198,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z899])],[(0,[z718,z36,z2,z3,z5,z6]),(0,[z0,z1,z900,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z901]),(0,[z82,z373,z1,z2,z83,z6]),(0,[z902,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z877]),(0,[z0,z98,z1,z277,z3,z6]),(0,[z0,z903,z1,z3,z5,z6]),(0,[z169,z0,z1,z3,z398,z188])],[(0,[z0,z904,z1,z2,z3,z5]),(0,[z0,z26,z1,z251,z5,z6]),(0,[z0,z1,z739,z2,z5,z6])]],
   [[],[(0,[z0,z1,z2,z3,z905,z6]),(0,[z0,z1,z2,z3,z5,z906]),(0,[z184,z1,z101,z379,z5,z6]),(0,[z0,z907,z1,z3,z5,z6]),(0,[z0,z908,z2,z3,z5,z6])],[(0,[z0,z1,z2,z909,z5,z6]),(0,[z0,z1,z2,z3,z5,z910]),(0,[z0,z1,z2,z3,z5,z911]),(0,[z0,z373,z1,z2,z115,z6]),(0,[z0,z1,z912,z3,z5,z6]),(0,[z0,z1,z2,z3,z913,z6]),(0,[z351,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z3,z5,z914]),(0,[z0,z1,z3,z5,z6,z915]),(0,[z0,z98,z1,z3,z717,z6]),(0,[z0,z51,z1,z277,z15,z6])],[(0,[z0,z10,z1,z325,z5,z6]),(0,[z0,z916,z2,z3,z5,z6]),(0,[z70,z1,z2,z709,z5,z6]),(0,[z0,z1,z2,z251,z83,z6]),(0,[z0,z26,z724,z3,z5,z6])]],
   [[(0,[z0,z98,z1,z3,z165,z6]),(0,[z0,z1,z917,z3,z5,z6]),(0,[z0,z40,z638,z2,z3,z5]),(0,[z0,z1,z2,z194,z5,z6]),(0,[z0,z179,z1,z183,z3,z6]),(0,[z0,z1,z183,z3,z5,z170]),(1,[z0,z1,z2,z3,z772])],[(1,[z1,z2,z709,z5,z6]),(0,[z918,z1,z2,z3,z5,z6]),(0,[z0,z1,z919,z3,z5,z6]),(0,[z0,z1,z2,z711,z15,z6])],[(0,[z525,z36,z2,z3,z5,z6]),(0,[z0,z920,z1,z3,z5,z6]),(0,[z0,z921,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z223]),(0,[z0,z922,z2,z3,z5,z6]),(0,[z0,z1,z331,z3,z5,z6]),(0,[z0,z1,z2,z5,z66,z723]),(0,[z0,z1,z2,z3,z307,z772])],[(0,[z0,z1,z2,z3,z923,z6]),(0,[z184,z1,z720,z3,z5,z6]),(0,[z0,z1,z2,z924,z5,z6]),(0,[z0,z1,z2,z3,z743,z6]),(0,[z0,z1,z2,z3,z5,z925]),(0,[z0,z51,z1,z331,z15,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z926]),(0,[z82,z1,z2,z210,z83,z6]),(0,[z1,z2,z3,z5,z743,z6]),(0,[z0,z1,z927,z3,z5,z6]),(0,[z928,z1,z2,z3,z5,z6]),(0,[z0,z929,z1,z3,z5,z6]),(0,[z0,z1,z225,z2,z5,z94])],[(0,[z0,z930,z1,z3,z5,z6]),(0,[z0,z1,z2,z931,z5,z6]),(0,[z0,z1,z2,z3,z5,z932]),(0,[z0,z1,z933,z3,z5,z6])],[(0,[z0,z1,z2,z934,z5,z6]),(0,[z0,z373,z1,z2,z14,z6]),(0,[z117,z0,z236,z2,z3,z5]),(0,[z935,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z936,z6]),(0,[z1,z2,z259,z709,z5,z6]),(0,[z0,z937,z1,z2,z3,z6]),(0,[z0,z7,z1,z3,z5,z150])]],
   [[(0,[z0,z1,z2,z3,z5,z938]),(0,[z0,z939,z2,z3,z5,z6]),(0,[z0,z1,z2,z940,z5,z6]),(0,[z1,z2,z3,z5,z941,z6]),(1,[z0,z815,z1,z5,z6]),(0,[z57,z0,z1,z473,z5,z6]),(0,[z0,z1,z2,z3,z5,z763])],[(0,[z0,z1,z2,z3,z942,z6]),(0,[z0,z278,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z5,z943]),(0,[z0,z1,z143,z54,z5,z6]),(0,[z0,z1,z724,z3,z5,z6]),(0,[z0,z98,z1,z3,z199,z6]),(0,[z0,z1,z3,z5,z6,z944])],[(0,[z0,z1,z215,z251,z5,z6]),(0,[z0,z1,z287,z3,z5,z6]),(0,[z0,z945,z2,z3,z5,z6]),(0,[z173,z1,z2,z3,z5,z738]),(0,[z0,z179,z26,z1,z3,z6]),(0,[z0,z2,z3,z41,z722,z6]),(0,[z0,z1,z2,z946,z5,z6]),(0,[z1,z2,z3,z5,z6,z947])],[(0,[z0,z1,z2,z3,z5,z948]),(0,[z0,z1,z751,z3,z5,z6]),(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z2,z3,z5,z6,z877]),(0,[z0,z950,z2,z3,z5,z6]),(0,[z0,z951,z2,z3,z5,z6]),(0,[z169,z0,z16,z2,z3,z188])]],
   [[(0,[z0,z1,z2,z3,z5,z271]),(0,[z0,z1,z2,z3,z952,z6]),(0,[z0,z953,z1,z3,z5,z6]),(0,[z0,z1,z325,z3,z115,z6]),(0,[z0,z954,z2,z3,z5,z6])],[(0,[z0,z1,z955,z2,z5,z6]),(0,[z0,z956,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z957,z6]),(0,[z0,z1,z2,z3,z5,z958]),(0,[z0,z1,z2,z959,z5,z6]),(0,[z0,z236,z2,z3,z41,z5]),(0,[z0,z960,z1,z3,z5,z6]),(0,[z0,z1,z17,z3,z580,z6]),(0,[z169,z0,z2,z3,z401,z188])],[(0,[z0,z1,z961,z3,z5,z6]),(0,[z0,z1,z45,z3,z83,z6]),(0,[z297,z1,z2,z3,z5,z31]),(0,[z0,z1,z183,z251,z5,z6])],[(0,[z0,z1,z962,z3,z5,z6]),(0,[z963,z0,z1,z2,z3,z6]),(0,[z0,z1,z560,z54,z5,z6]),(0,[z70,z1,z148,z71,z5,z6]),(0,[z86,z0,z72,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z964]),(0,[z0,z16,z2,z3,z5,z6]),(0,[z0,z1,z965,z3,z5,z6]),(0,[z0,z1,z966,z3,z5,z6])]],
   [[(0,[z0,z1,z148,z3,z39,z6]),(0,[z0,z967,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z968])],[(0,[z0,z1,z969,z2,z5,z6]),(0,[z0,z1,z2,z14,z115,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z236,z1,z3,z5,z48]),(0,[z0,z1,z585,z54,z5,z6]),(0,[z0,z58,z815,z1,z5,z6]),(0,[z0,z1,z183,z3,z5,z167]),(0,[z0,z1,z971,z3,z5,z6])],[(0,[z70,z446,z2,z71,z5,z6]),(0,[z70,z447,z2,z71,z5,z6]),(0,[z430,z1,z2,z3,z83,z6]),(0,[z0,z135,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z0,z1,z973,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z772])],[(0,[z122,z1,z215,z3,z5,z6]),(0,[z0,z1,z974,z3,z5,z6]),(0,[z0,z1,z975,z3,z5,z6]),(0,[z538,z1,z2,z3,z5,z13]),(0,[z86,z0,z72,z198,z5,z6]),(0,[z659,z0,z40,z2,z3,z5]),(0,[z0,z179,z1,z2,z15,z6])]],
   [[(0,[z0,z1,z2,z3,z976,z6]),(0,[z0,z977,z2,z3,z5,z6]),(0,[z0,z1,z978,z3,z5,z6]),(0,[z0,z1,z979,z2,z3,z5]),(0,[z980,z1,z2,z3,z5,z6]),(0,[z0,z1,z568,z54,z5,z6]),(0,[z981,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z33,z483,z6]),(0,[z0,z1,z17,z277,z3,z6])],[(0,[z0,z1,z2,z3,z5,z982]),(0,[z0,z373,z1,z2,z5,z6]),(0,[z0,z1,z243,z2,z5,z94]),(0,[z983,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z984]),(0,[z0,z1,z2,z3,z985,z6]),(0,[z0,z1,z986,z3,z5,z6]),(0,[z49,z0,z179,z1,z2,z6]),(0,[z0,z26,z352,z3,z5,z6]),(0,[z0,z1,z3,z5,z150,z654])],[(0,[z0,z987,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z988]),(0,[z1,z2,z3,z5,z31,z738]),(0,[z0,z1,z17,z251,z5,z6]),(0,[z0,z1,z2,z3,z5,z723])]],
   [[(0,[z0,z1,z2,z379,z5,z6]),(0,[z0,z1,z720,z3,z5,z6]),(0,[z0,z446,z2,z3,z115,z6]),(0,[z0,z447,z2,z3,z115,z6]),(0,[z0,z1,z989,z3,z5,z6]),(0,[z0,z1,z2,z990,z3,z6]),(0,[z0,z1,z991,z3,z5,z6]),(0,[z0,z1,z17,z3,z717,z6]),(0,[z0,z1,z992,z3,z5,z6]),(0,[z0,z65,z1,z2,z5,z723])],[(0,[z0,z1,z2,z3,z5,z451]),(0,[z0,z1,z2,z3,z5,z993]),(0,[z0,z98,z1,z3,z237,z6]),(0,[z0,z420,z1,z3,z5,z6]),(0,[z0,z1,z994,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z995])],[(0,[z0,z1,z2,z3,z5,z996]),(0,[z0,z1,z2,z997,z5,z6]),(0,[z673,z1,z2,z3,z5,z31]),(0,[z0,z998,z1,z2,z3,z5]),(0,[z0,z999,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z5,z1000]),(0,[z0,z1001,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z711,z6])]],
   [[(0,[z0,z99,z2,z159,z5,z6]),(0,[z0,z1,z1002,z3,z5,z6]),(0,[z70,z1,z2,z71,z5,z6]),(0,[z0,z2,z3,z5,z23,z877]),(0,[z0,z1,z360,z54,z5,z6]),(0,[z0,z1,z3,z5,z6,z398])],[(0,[z476,z36,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z39,z6]),(0,[z57,z0,z1,z619,z5,z6]),(0,[z0,z179,z25,z1,z3,z6]),(0,[z1003,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z23,z230]),(0,[z0,z1004,z2,z3,z5,z6])],[(0,[z70,z1,z2,z71,z5,z301]),(0,[z44,z1,z2,z3,z46,z6]),(1,[z0,z2,z3,z5,z877])],[(0,[z0,z1,z101,z251,z5,z6]),(0,[z0,z1,z2,z3,z39,z301]),(0,[z0,z1,z2,z210,z5,z6]),(0,[z0,z1,z472,z54,z5,z6]),(1,[z0,z739,z2,z5,z6])]],
   [[(0,[z0,z1,z1005,z3,z5,z6]),(0,[z1,z720,z215,z3,z5,z6]),(0,[z0,z98,z373,z1,z2,z6]),(0,[z0,z1,z730,z3,z5,z6]),(0,[z1006,z1,z2,z3,z5,z6]),(0,[z1007,z1,z2,z3,z5,z6]),(0,[z0,z236,z1,z2,z3,z5]),(0,[z0,z1,z3,z5,z763,z170]),(0,[z0,z1,z2,z14,z711,z6]),(1,[z0,z1,z2,z5,z723]),(0,[z0,z65,z1,z59,z5,z66])],[(0,[z0,z1,z2,z3,z5,z1008]),(0,[z1,z2,z3,z1009,z5,z6]),(0,[z0,z1,z2,z3,z5,z1010]),(0,[z0,z72,z739,z2,z5,z6]),(0,[z0,z103,z2,z3,z722,z6]),(0,[z0,z40,z2,z3,z5,z877]),(0,[z0,z2,z3,z5,z6,z1011])],[(0,[z0,z446,z148,z3,z5,z6]),(0,[z0,z447,z148,z3,z5,z6]),(0,[z70,z0,z179,z1,z2,z6]),(0,[z70,z506,z1,z2,z5,z6]),(0,[z0,z1012,z1,z2,z5,z6]),(0,[z0,z1,z277,z5,z15,z6]),(0,[z0,z16,z219,z3,z5,z6])],[(0,[z0,z1013,z2,z3,z5,z6]),(0,[z0,z1,z325,z3,z5,z6]),(0,[z389,z1,z2,z3,z83,z6]),(0,[z0,z1,z1014,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1015]),(0,[z0,z1,z2,z3,z1016,z6]),(0,[z0,z1,z2,z3,z5,z1017]),(0,[z0,z1,z1018,z3,z5,z6]),(0,[z0,z1,z45,z3,z46,z6]),(0,[z0,z1,z59,z3,z5,z6]),(0,[z0,z1,z17,z33,z54,z6])],[(0,[z0,z1,z2,z3,z5,z1019]),(0,[z0,z1,z1020,z2,z5,z6]),(0,[z691,z77,z2,z3,z5,z6]),(0,[z0,z1,z325,z3,z5,z301]),(0,[z0,z22,z2,z3,z5,z877])],[(0,[z0,z1,z3,z5,z1021,z6]),(0,[z0,z1,z325,z54,z5,z6]),(0,[z0,z1,z2,z3,z1022,z6]),(0,[z0,z1,z2,z5,z6,z1023]),(0,[z0,z238,z2,z159,z5,z6]),(1,[z0,z2,z3,z722,z6]),(0,[z0,z98,z1,z251,z18,z6]),(0,[z0,z1,z2,z3,z717,z6]),(0,[z0,z65,z1,z2,z5,z66]),(0,[z0,z1024,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z1025]),(0,[z0,z1,z2,z1026,z3,z6]),(0,[z0,z815,z1,z3,z5,z6]),(0,[z1027,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z1028,z6]),(0,[z0,z1029,z1,z2,z5,z6]),(0,[z70,z1,z2,z71,z5,z223]),(0,[z1,z2,z3,z743,z83,z6]),(0,[z0,z1,z17,z3,z337,z6]),(0,[z0,z1,z2,z1030,z5,z6]),(0,[z0,z1,z68,z54,z5,z6])],[(0,[z0,z1,z2,z3,z39,z223]),(0,[z0,z1,z360,z126,z54,z6]),(0,[z0,z1031,z2,z3,z5,z6])],[(0,[z0,z25,z84,z3,z5,z6]),(0,[z86,z0,z35,z72,z5,z6]),(0,[z169,z0,z1,z2,z3,z534]),(0,[z0,z815,z1,z54,z5,z6])],[(0,[z142,z77,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1032,z6]),(0,[z0,z1,z2,z3,z1033,z6]),(0,[z0,z1,z2,z3,z5,z738]),(0,[z1034,z1,z2,z3,z5,z6]),(0,[z0,z724,z2,z3,z5,z6]),(0,[z0,z1,z1035,z2,z3,z5]),(0,[z0,z1036,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z1037,z2,z5,z6]),(0,[z0,z1,z17,z3,z91,z6]),(0,[z0,z1,z2,z3,z307,z187]),(0,[z0,z1,z2,z3,z772,z188])],[(0,[z0,z1,z2,z3,z1038,z6]),(0,[z0,z1039,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1040]),(1,[z0,z724,z3,z5,z6]),(0,[z0,z25,z140,z3,z5,z6]),(0,[z0,z1,z2,z5,z723,z94])],[(0,[z0,z1,z215,z3,z340,z6]),(0,[z0,z1,z1041,z2,z3,z5]),(0,[z0,z1,z183,z3,z5,z250]),(0,[z0,z1042,z2,z3,z5,z6])],[(0,[z0,z447,z2,z3,z5,z6]),(0,[z0,z446,z2,z3,z5,z6]),(0,[z0,z40,z2,z3,z5,z413]),(0,[z0,z1,z325,z3,z5,z223]),(0,[z0,z1043,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1044,z6]),(0,[z0,z1012,z1,z45,z5,z6]),(0,[z117,z0,z420,z3,z104,z6]),(0,[z0,z1,z2,z1045,z5,z6]),(0,[z0,z1,z2,z33,z14,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 558) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 558).take 452) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1010)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [558, 452] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 104).take 24).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [104, 24] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_41366

theorem PEqualNP.Outside.L_meta_41366 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4241006592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4241006592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41366.solve