import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38731

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
  Nat.testBit (4276808424 * 2 ^ 32 + 4274055872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00015823710e0ae0#64 ++ 0x20002b046e21c15c#64 ++ 0xa813f9e7f11e1fe7#64 ++ 0xd5027f3cfe23c3fc#64 : BitVec 256),
   (0x0064c288a162a628#64 ++ 0x400c9851142c54c5#64 ++ 0xf8ecc698e1e7e67f#64 ++ 0xbf1d98d31c3cfccf#64 : BitVec 256),
   (0x0b0b051516055852#64 ++ 0x816160a2a2c0ab0a#64 ++ 0xff0f071f1e07f87f#64 ++ 0x7fe1e0e3e3c0ff0f#64 : BitVec 256),
   (0x05b007c00ab07503#64 ++ 0x00b600f801560ea0#64 ++ 0xdff007e01ff87f86#64 ++ 0xfbfe00fc03ff0ff0#64 : BitVec 256),
   (0x16dfe8001ddf8004#64 ++ 0x02dbfd0003bbf000#64 ++ 0x97fff8001fff8005#64 ++ 0xf2ffff0003fff000#64 : BitVec 256),
   (0x27feb7fec0000000#64 ++ 0x04ffd6ffd8000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa813f9e7f11e1fe7 0xd5027f3cfe23c3fc

def z1 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8ecc698e1e7e67f 0xbf1d98d31c3cfccf

def z2 : W := mkw 0x0065daabf16eaee8 0x600cbb557e2dd5dd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z3 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdff007e01ff87f86 0xfbfe00fc03ff0ff0

def z4 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff0f071f1e07f87f 0x7fe1e0e3e3c0ff0f

def z5 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97fff8001fff8005 0xf2ffff0003fff000

def z6 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0x200ff81fe0000001 0x0401ff03fc000000

def z7 : W := mkw 0x04b002c000000000 0x0096005800000000 0x00f000e000000000 0x801e001c00000000

def z8 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z9 : W := mkw 0x05f4c7c8a162a628 0x40be98f9142c54c5 0xfffcc7f8e1e7e67f 0xffff98ff1c3cfccf

def z10 : W := mkw 0x15b14fc01ffff507 0x02b629f803fffea0 0xdff007e01fffff86 0xfbfe00fc03fffff0

def z11 : W := mkw 0x0020028880202408 0x4004005110040481 0x4000061800006018 0x080000c300000c03

def z12 : W := mkw 0x05b107c11ab47d43 0x00b620f823568fa8 0xfff307e71ffe7fe7 0xfffe60fce3ffcffc

def z13 : W := mkw 0x0001000110040840 0x0000200022008108 0xa803010710061867 0x55006020e200c30c

def z14 : W := mkw 0x0b0b5d37770f5af2 0xa1616ba6eee1eb5e 0xff1fffffff1fffff 0xffe3ffffffe3ffff

def z15 : W := mkw 0x012007c002207503 0x002400f800440ea0 0xd8e007e001e07f86 0xbb1c00fc003c0ff0

def z16 : W := mkw 0x04b002c008b02501 0x00960058011604a0 0x97f000e01ff80784 0xf2fe001c03ff00f0

def z17 : W := mkw 0x0801000116055852 0x8100200022c0ab0a 0x180000001e07f87c 0x0300000003c0ff0f

def z18 : W := mkw 0x24f4b2eac0000000 0x049e965d58000000 0x00f0f8e0e0000000 0x801e1f1c1c000000

def z19 : W := mkw 0x16dff8227ddf82a4 0x22dbff044fbbf054 0x97fff8e0ffff8785 0xf2ffff1c1ffff0f0

def z20 : W := mkw 0x0000102240000000 0x0000020448000000 0xa013f9e7e0000003 0xd4027f3cfc000000

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0xf80c06180007e07f 0x3f0180c30000fc0f

def z22 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xfffffe181fffe07f 0xffffffc303fffc0f

def z23 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x070301071e001800 0x40e06020e3c00300

def z24 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z25 : W := mkw 0x14f4ea88a9faa62c 0x429e9d51153f54c5 0x00f0f880e1f80600 0x801e1f101c3f00c0

def z26 : W := mkw 0x00200288a0202628 0x40040051140404c5 0x68000698e000667a 0x0d0000d31c000ccf

def z27 : W := mkw 0x169b28001c9d0004 0x02d365000393a000 0x071338001e180000 0x40e2670003c30000

def z28 : W := mkw 0x04b002c008b02501 0x00960058011604a0 0x00f000e001f80780 0x801e001c003f00f0

def z29 : W := mkw 0x0a0b001514050850 0x81416002a280a10a 0x200f001f00078079 0x0401e003e000f00f

def z30 : W := mkw 0x236eb7fec0000000 0x046dd6ffd8000000 0x600fffffe0000003 0x0c01fffffc000000

def z31 : W := mkw 0x000000000ab07503 0x0000000001560ea0 0x180000001ff87f84 0x0300000003ff0ff0

def z32 : W := mkw 0x24f5faebf10e0ae0 0x249ebf5d7e21c15c 0xa8f3f9e7f11e1fe7 0xd51e7f3cfe23c3fc

def z33 : W := mkw 0x0b0b4d15170f5852 0x816169a2a2e1eb0a 0xff1fff1f1f1ff87f 0xffe3ffe3e3e3ff0f

def z34 : W := mkw 0x37feb7feccd18004 0x06ffd6ffd99a3000 0xf7ffffffeee18003 0xfefffffffddc3000

def z35 : W := mkw 0x012007c000000000 0x002400f800000000 0x400007e000000002 0x080000fc00000000

def z36 : W := mkw 0x05b007c000000000 0x00b600f800000000 0xc7f007e000000002 0xf8fe00fc00000000

def z37 : W := mkw 0x07dea51400000000 0x00fbd4a280000000 0xe7ffff1f00000003 0xfcffffe3e0000000

def z38 : W := mkw 0x16dff8237ddf8ae4 0x22dbff046fbbf15c 0xbffff9e7ffff9fe7 0xf7ffff3cfffff3fc

def z39 : W := mkw 0x1edfe8151ddf8854 0x83dbfd02a3bbf10a 0xb7fff81f1fff807d 0xf6ffff03e3fff00f

def z40 : W := mkw 0x27feb7fec2005002 0x04ffd6ffd8400a00 0xfffffffffe007807 0xffffffffffc00f00

def z41 : W := mkw 0x17ffefc01ffff507 0x02fffdf803fffea0 0xdfffffe01fffff87 0xfbfffffc03fffff0

def z42 : W := mkw 0x14f4eac009faa505 0x029e9d58013f54a0 0x00f0f8e001f80780 0x801e1f1c003f00f0

def z43 : W := mkw 0x1edfe8011fdfd856 0x83dbfd0023fbfb0a 0x9ffff8001ffff87d 0xf3ffff0003ffff0f

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x500c06180001e018 0x2a0180c300003c03

def z45 : W := mkw 0x0fba07d40eb17513 0x81f740fa81d62ea2 0xdffc07f81ff9ff9e 0xfbff80ff03ff3ff3

def z46 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x08000000111e1fe4 0x010000000223c3fc

def z47 : W := mkw 0x012007c002207503 0x002400f800440ea0 0x480007e000007f82 0x090000fc00000ff0

def z48 : W := mkw 0x0064d2aae162a628 0x400c9a555c2c54c5 0xf8ffffffe1e7e67f 0xff1ffffffc3cfccf

def z49 : W := mkw 0x2490306240000000 0x0492060c48000000 0x0010386000000000 0x0002070c00000000

def z50 : W := mkw 0x17fea7c00ef1f507 0x02ffd4f801de3ea0 0x57ec06000ee1e000 0x2afd80c001dc3c00

def z51 : W := mkw 0x0a0b001514050850 0x81416002a280a10a 0xa80f011f1007987f 0x5501e023e200f30f

def z52 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xa8e0c080e1e60667 0x951c18101c3cc0cc

def z53 : W := mkw 0x0000000120000ae0 0x200000002400015c 0x0800000000001fe0 0x01000000000003fc

def z54 : W := mkw 0x0044c00001428000 0x0008980000285000 0x90ecc00001e78005 0xb21d9800003cf000

def z55 : W := mkw 0x06dea00000000000 0x00dbd40000000000 0x87fff80000000001 0xf0ffff0000000000

def z56 : W := mkw 0x37fffffedddf8004 0x06ffffffdbbbf000 0xf7ffffffffff8007 0xfefffffffffff000

def z57 : W := mkw 0x16dee0000dd38004 0x02dbdc0001ba7000 0x97ecc0000fe78005 0xb2fd980001fcf000

def z58 : W := mkw 0x00005822610a02a0 0x20000b044c214054 0x0010f8e0e1180780 0x80021f1c1c2300f0

def z59 : W := mkw 0x00011823500c08c0 0x200023046a018118 0x0013396710181980 0x4002672ce2030330

def z60 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2003f807e0060061 0x04007f00fc00c00c

def z61 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x57e006000ee06000 0x2afc00c001dc0c00

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0xa003010700000003 0x54006020e0000000

def z63 : W := mkw 0x27fef7fee162a628 0x44ffdeffdc2c54c5 0xffffffffe1e7e67f 0xfffffffffc3cfccf

def z64 : W := mkw 0x05b11fe35abc7dc3 0x20b623fc6b578fb8 0xdff33fe71ff87f86 0xfbfe67fce3ff0ff0

def z65 : W := mkw 0x030a051400000000 0x006140a280000000 0x470c061800000000 0x28e180c300000000

def z66 : W := mkw 0x04f4c2c8a9f2a729 0x409e9859153e54e5 0x00f0c0e0e1f80780 0x801e181c1c3f00f0

def z67 : W := mkw 0x0044800000000000 0x0008900000000000 0x80ecc00000000001 0xb01d980000000000

def z68 : W := mkw 0x0b6fdfbff76ffefa 0xe16dfbf7feedffdf 0xffffffffffffffff 0xffffffffffffffff

def z69 : W := mkw 0x000040002bf2f72b 0x40000800057e5ee5 0x180000001ffffffc 0x0300000003ffffff

def z70 : W := mkw 0x124fe800154f8004 0x0249fd0002a9f000 0x90eff80001e78005 0xb21dff00003cf000

def z71 : W := mkw 0x0064828880000000 0x000c905110000000 0xe0ecc698e0000003 0xbc1d98d31c000000

def z72 : W := mkw 0x279a357640000000 0x04f346aec8000000 0x0713396700000000 0x40e2672ce0000000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x080001e000001f82 0x0100003c000003f0

def z74 : W := mkw 0x0920079da2207e7a 0xc12400f3b4440fcf 0x6800079fe0007e7a 0x0d0000f3fc000fcf

def z75 : W := mkw 0x16ffea88bdffa62c 0x42dffd5117bff4c5 0xfffffe98ffffe67f 0xffffffd31ffffccf

def z76 : W := mkw 0x1fdfed151fdfd856 0x83fbfda2a3fbfb0a 0xffffff1f1ffff87f 0xffffffe3e3ffff0f

def z77 : W := mkw 0x0000400021020220 0x0000080004204044 0xa800c080e1060667 0x950018101c20c0cc

def z78 : W := mkw 0x279a35764a905103 0x04f346aec9520a20 0x071339671e181980 0x40e2672ce3c30330

def z79 : W := mkw 0x0000102360000ae0 0x200002046c00015c 0x280001e7e0001fe2 0x0500003cfc0003fc

def z80 : W := mkw 0x27fffffff10e0ae0 0x24fffffffe21c15c 0xeffffffff11e1fe7 0xfdfffffffe23c3fc

def z81 : W := mkw 0x0020028000202400 0x0004005000040480 0xd8e0068001e06606 0xbb1c00d0003c0cc0

def z82 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xfffc07f81fffffff 0xffff80ff03ffffff

def z83 : W := mkw 0x169b28001c9d0004 0x02d365000393a000 0x971f38001e1f8005 0x72e3e70003c3f000

def z84 : W := mkw 0x0044c008a1428228 0x4008980114285045 0x200cc018e0078079 0x040198031c00f00f

def z85 : W := mkw 0x169b28001c9d0004 0x02d365000393a000 0x97f338001ff80004 0xf2fe670003ff0000

def z86 : W := mkw 0x0b6f879d96055852 0x816df0f3b2c0ab0a 0xffefc79ffe07f87f 0xfffdf8f3ffc0ff0f

def z87 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0xa800c080f11e1fe7 0x950018101e23c3fc

def z88 : W := mkw 0x10014800154f8004 0x0200290002a9f000 0x0000000000078000 0x000000000000f000

def z89 : W := mkw 0x020a000000000000 0x0041400000000000 0x870f000000000001 0x70e1e00000000000

def z90 : W := mkw 0x05b047c02bb27723 0x00b608f805764ee4 0xfff0c7e0fffe7fe7 0xfffe18fc1fffcffc

def z91 : W := mkw 0x05b15fe37bbe7fe3 0x20b62bfc6f77cffc 0xfff3ffe7fffe7fe7 0xfffe7ffcffffcffc

def z92 : W := mkw 0x24f4b2eac0000000 0x049e965d58000000 0xe0fcfef8e0000003 0xbc1f9fdf1c000000

def z93 : W := mkw 0x04b15ae379be2fe1 0x20962b5c6f37c5fc 0xa8f3f9e7f1fe1fe7 0xd51e7f3cfe3fc3fc

def z94 : W := mkw 0x0044c008a162a628 0x40089801142c54c5 0x380cc018e1e7e67d 0x070198031c3cfccf

def z95 : W := mkw 0x00014801316eaee8 0x60002900262dd5dd 0x1800000011fffffc 0x03000000023fffff

def z96 : W := mkw 0x000000000ab07503 0x0000000001560ea0 0x100000000ee06000 0x0200000001dc0c00

def z97 : W := mkw 0x0b0a051406015012 0x816140a280c02a02 0x570c06180e01e018 0x2ae180c301c03c03

def z98 : W := mkw 0x2ffeb7fec6015012 0x85ffd6ffd8c02a02 0xf7ffffffee01e01b 0xfefffffffdc03c03

def z99 : W := mkw 0x0f9b05551e955953 0x81f360aaa3d2ab2a 0x071301671e181980 0x40e2602ce3c30330

def z100 : W := mkw 0x25f4b7eac0000000 0x04be96fd58000000 0xc7f0ffe0e0000002 0xf8fe1ffc1c000000

def z101 : W := mkw 0x14d4e80009da8004 0x029a9d00013b5000 0x00f0f80001f80000 0x801e1f00003f0000

def z102 : W := mkw 0x25b017fecab07503 0x04b602ffd9560ea0 0xfff007fffff87f86 0xfffe00ffffff0ff0

def z103 : W := mkw 0x27feb7ffe0000ae0 0x24ffd6fffc00015c 0xefffffffe0001fe3 0xfdfffffffc0003fc

def z104 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa013f9e7e0060063 0xd4027f3cfc00c00c

def z105 : W := mkw 0x020b5823750f0ae0 0x20416b046ea1e15c 0xbf1ff9e7ff1f9fe7 0xf7e3ff3cffe3f3fc

def z106 : W := mkw 0x00010800100c0000 0x0000210002018000 0x0013380010180000 0x4002670002030000

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000e001180780 0x8002001c002300f0

def z108 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x17ec00000ee18000 0x22fd800001dc3000

def z109 : W := mkw 0x06dfe800110e0000 0x00dbfd000221c000 0x87fff800111e0005 0xf0ffff000223c000

def z110 : W := mkw 0x059005400a905103 0x00b200a801520a20 0x97f001601ff81984 0xf2fe002c03ff0330

def z111 : W := mkw 0x0b0b05151eb57d53 0x816160a2a3d6afaa 0xff0f071f1fffffff 0x7fe1e0e3e3ffffff

def z112 : W := mkw 0x002042802162a628 0x40040850042c54c5 0xd8e0068001e7e67e 0xbb1c00d0003cfccf

def z113 : W := mkw 0x002002800ab07503 0x0004005001560ea0 0xd8e006801ff87f86 0xbb1c00d003ff0ff0

def z114 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x20ecc098e1e78679 0x841d98131c3cf0cf

def z115 : W := mkw 0x049000000ab07503 0x0092000001560ea0 0x9ff000001ff87f84 0xf3fe000003ff0ff0

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000011181f84 0x01000000022303f0

def z117 : W := mkw 0x06deb02240000000 0x00dbd60448000000 0xa7fff9e7e0000003 0xf4ffff3cfc000000

def z118 : W := mkw 0x100000000cd18004 0x02000000019a3000 0x100000000ee18000 0x0200000001dc3000

def z119 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x90ecc080e1e78605 0xb21d98101c3cf0c0

def z120 : W := mkw 0x00015823716eaee8 0x60002b046e2dd5dd 0xb813f9e7f1ffffff 0xd7027f3cfe3fffff

def z121 : W := mkw 0x04f4c2c8a9f2a729 0x409e9859153e54e5 0xf8fcc6f8e1ffe7ff 0xbf1f98df1c3ffcff

def z122 : W := mkw 0x0044c00001428000 0x0008980000285000 0xf8ecc61801e7e07f 0xbf1d98c3003cfc0f

def z123 : W := mkw 0x0001000110040840 0x0000200022008108 0x0800000010061864 0x010000000200c30c

def z124 : W := mkw 0x010005000ab07503 0x002000a001560ea0 0xdf0007001ff87f86 0x7be000e003ff0ff0

def z125 : W := mkw 0x0000102240000000 0x0000020448000000 0x0013396700000000 0x4002672ce0000000

def z126 : W := mkw 0x27fea7dc80000000 0x04ffd4fb90000000 0x47ec061800000000 0x28fd80c300000000

def z127 : W := mkw 0x05b05fe26bba77a3 0x20b60bfc4d774ef4 0xdff0ffe0fff87f86 0xfbfe1ffc1fff0ff0

def z128 : W := mkw 0x00014800110e0000 0x000029000221c000 0x8013f800111e0005 0xd0027f000223c000

def z129 : W := mkw 0x0b0b153776055af2 0xa16162a6eec0ab5e 0xff0f07fffe07ffff 0x7fe1e0ffffc0ffff

def z130 : W := mkw 0x24f4b2eac8b02501 0x049e965d591604a0 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z131 : W := mkw 0x06fee288a162a628 0x40dfdc51142c54c5 0xfffffe98e1e7e67f 0xffffffd31c3cfccf

def z132 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xd7f007e00ee06002 0xfafe00fc01dc0c00

def z133 : W := mkw 0x1045c8001ddf8004 0x0208b90003bbf000 0x90ecc0001fff8005 0xb21d980003fff000

def z134 : W := mkw 0x00200288a0202628 0x40040051140404c5 0xf8e00698e1e0667e 0xbf1c00d31c3c0ccf

def z135 : W := mkw 0x1065ca88bdffa62c 0x420cb95117bff4c5 0xf8ecc698ffffe67f 0xbf1d98d31ffffccf

def z136 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x881001e0111e1fe6 0xd102003c0223c3fc

def z137 : W := mkw 0x100148001ddf8004 0x0200290003bbf000 0x100000001fff8004 0x0200000003fff000

def z138 : W := mkw 0x012007c002207503 0x002400f800440ea0 0xdf0007e01e007f86 0x7be000fc03c00ff0

def z139 : W := mkw 0x279a255400000000 0x04f344aa80000000 0x0700000000000000 0x00e0000000000000

def z140 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xffffffffe007e07f 0xfffffffffc00fc0f

def z141 : W := mkw 0x0900051502005852 0x812000a2a0400b0a 0x6800071f0000787a 0x0d0000e3e0000f0f

def z142 : W := mkw 0x16dff8235ddf88c4 0x22dbff046bbbf118 0x97fff9671fff9985 0xf2ffff2ce3fff330

def z143 : W := mkw 0x006482888060a408 0x400c9051100c1481 0x50ec061800e1e018 0x2a1d80c3001c3c03

def z144 : W := mkw 0x0065ca88b16ea628 0x400cb951162dd4c5 0xf8fffe98f1ffe67f 0xff1fffd31e3ffccf

def z145 : W := mkw 0x0b0b5d37770f5af2 0xa1616ba6eee1eb5e 0xaf13f9e7ff1e1fe7 0xd5e27f3cffe3c3fc

def z146 : W := mkw 0x05f5dfebfbfeffeb 0x60bebbfd7f7fdffd 0xffffffffffffffff 0xffffffffffffffff

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z148 : W := mkw 0x0490000008900000 0x0092000001120000 0x17e000000ee00000 0x22fc000001dc0000

def z149 : W := mkw 0x16dfe8011ddf8844 0x02dbfd0023bbf108 0xbffff9071fff9867 0xf7ffff20e3fff30c

def z150 : W := mkw 0x16fee288adf3a62c 0x42dfdc5115be74c5 0xffecc698efe7e67f 0xbffd98d31dfcfccf

def z151 : W := mkw 0x04d4c00009d28000 0x009a9800013a5000 0x97fcc0001fff8005 0xf2ff980003fff000

def z152 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x0013f9e7f1181f80 0xc0027f3cfe2303f0

def z153 : W := mkw 0x27ba37f64ab07503 0x04f746fec9560ea0 0xdff33fe71ff87f86 0xfbfe67fce3ff0ff0

def z154 : W := mkw 0x124fe800154f8004 0x0249fd0002a9f000 0x000ff80000078001 0x0001ff000000f000

def z155 : W := mkw 0x224ea01c80000000 0x0449d40390000000 0x000c001800000000 0x0001800300000000

def z156 : W := mkw 0x07bb07c01eb57503 0x00f760f803d6aea0 0xdfff07e01fffff87 0xfbffe0fc03fffff0

def z157 : W := mkw 0x15f4efc00bfaf507 0x02be9df8017f5ea0 0xdff0ffe01ff87f86 0xfbfe1ffc03ff0ff0

def z158 : W := mkw 0x27feb7fec060a408 0x44ffd6ffd80c1481 0xf7ffffffe0e1e01b 0xfefffffffc1c3c03

def z159 : W := mkw 0x0020428021222620 0x00040850042444c4 0xf8e0c680e1e66667 0xbf1c18d01c3ccccc

def z160 : W := mkw 0x08014801370f5af2 0xa100290026e1eb5e 0x180000001f1ffffc 0x0300000003e3ffff

def z161 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xdf0307071e007806 0x7be060e0e3c00f00

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x881001e011181f86 0xd102003c022303f0

def z163 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x70ecc618e0e7e079 0x2e1d98c31c1cfc0f

def z164 : W := mkw 0x14d4a00008d08004 0x029a9400011a1000 0x00e0000000e00000 0x001c0000001c0000

def z165 : W := mkw 0x05b007c000000000 0x00b600f800000000 0xcff007e011181f86 0xf9fe00fc022303f0

def z166 : W := mkw 0x05f4c7c8abf2f72b 0x40be98f9157e5ee5 0xfffcc7f8ffffffff 0xffff98ff1fffffff

def z167 : W := mkw 0x0120078002207402 0x002400f000440e80 0xdfe007801fe07e06 0xfbfc00f003fc0fc0

def z168 : W := mkw 0x00001023400008c0 0x2000020468000118 0x0000016700001980 0x0000002ce0000330

def z169 : W := mkw 0x0b6ec79ca763f63a 0xc16dd8f394ec7ec7 0xffecc698efe7e67f 0xbffd98d31dfcfccf

def z170 : W := mkw 0x0b6fc79db767fe7a 0xc16df8f3b6ecffcf 0xffefc79fffe7fe7f 0xfffdf8f3fffcffcf

def z171 : W := mkw 0x030a051400000000 0x006140a280000000 0x0703010700000000 0x40e06020e0000000

def z172 : W := mkw 0x080100011eb57d53 0x8100200023d6afaa 0x180000001ffffffc 0x0300000003ffffff

def z173 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff1f07ff1f1fffff 0xffe3e0ffe3e3ffff

def z174 : W := mkw 0x27fea7dc80000000 0x04ffd4fb90000000 0xe7ecc698e0000003 0xbcfd98d31c000000

def z175 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x00e0c080e1e00600 0x801c18101c3c00c0

def z176 : W := mkw 0x000040002162a628 0x40000800042c54c5 0x1800000001e7e67c 0x03000000003cfccf

def z177 : W := mkw 0x0000400021428228 0x4000080004285045 0x0000000000078078 0x000000000000f00f

def z178 : W := mkw 0x124ea00004418004 0x0249d40000883000 0x000c000000018000 0x0001800000003000

def z179 : W := mkw 0x05b017e24ab07503 0x00b602fc49560ea0 0xfff3ffe7fff87f87 0xfffe7ffcffff0ff0

def z180 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x1f0301071e07f87c 0x43e06020e3c0ff0f

def z181 : W := mkw 0x27deb57ec0000000 0x04fbd6afd8000000 0x271ff97fe0000001 0x44e3ff2ffc000000

def z182 : W := mkw 0x27fea7dc8060a408 0x44ffd4fb900c1481 0x57ec061800e1e018 0x2afd80c3001c3c03

def z183 : W := mkw 0x0000102240000000 0x0000020448000000 0xa813f9e7f1181f87 0xd5027f3cfe2303f0

def z184 : W := mkw 0x2b4fb53fd6055852 0x8569f6a7fac0ab0a 0xff0fff1ffe07f87f 0x7fe1ffe3ffc0ff0f

def z185 : W := mkw 0x0b2b079516257c52 0x816560f2a2c4af8a 0xffef079f1fe7fe7f 0xfffde0f3e3fcffcf

def z186 : W := mkw 0x05915d637b9e5be3 0x20b22bac6f73cb7c 0xaf13f9e7ff1e1fe7 0xd5e27f3cffe3c3fc

def z187 : W := mkw 0x1fdea5140ed1d016 0x83fbd4a281da3a02 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z188 : W := mkw 0x0fdfa51516055852 0x81fbf4a2a2c0ab0a 0xffffff1f1e07f87f 0xffffffe3e3c0ff0f

def z189 : W := mkw 0x36fffaeadddf8004 0x06dfff5d5bbbf000 0x97fff8e0ffff8005 0xf2ffff1c1ffff000

def z190 : W := mkw 0x00015822510e0000 0x00002b044a21c000 0xa013f9e7f11e0007 0xd4027f3cfe23c000

def z191 : W := mkw 0x0064d2abe162aee8 0x600c9a557c2c55dd 0xf8ecc7ffe1e7ffff 0xbf1d98fffc3cffff

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x90e0000001e00004 0xb21c0000003c0000

def z193 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x67effe1fe0000001 0x2cfdffc3fc000000

def z194 : W := mkw 0x212017fec2207503 0x042402ffd8440ea0 0x680007ffe0007f82 0x0d0000fffc000ff0

def z195 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x97fc00001ff98004 0xf2ff800003ff3000

def z196 : W := mkw 0x030a051400000000 0x006140a280000000 0xe70f071f00000003 0x7ce1e0e3e0000000

def z197 : W := mkw 0x120b2800140d0004 0x024165000281a000 0x0003380000000000 0x0000670000000000

def z198 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17eff8000ee78001 0x22fdff0001dcf000

def z199 : W := mkw 0x27fffffffbbe7fe3 0x24ffffffff77cffc 0xfffffffffffe7fe7 0xffffffffffffcffc

def z200 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xf7ffffffeee06003 0xfefffffffddc0c00

def z201 : W := mkw 0x2b2b17ffd6055852 0x856562fffac0ab0a 0xff0f07fffe07f87f 0x7fe1e0ffffc0ff0f

def z202 : W := mkw 0x0044c008a1428228 0x4008980114285045 0x0000c000e0000000 0x000018001c000000

def z203 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000007e07c 0x030000000000fc0f

def z204 : W := mkw 0x00011823700c0ae0 0x200023046e01815c 0x281339e7f0181fe2 0x4502673cfe0303fc

def z205 : W := mkw 0x030a051400000000 0x006140a280000000 0xff0f071f0007e07f 0x7fe1e0e3e000fc0f

def z206 : W := mkw 0x2f9b357756055852 0x85f366aeeac0ab0a 0xff1f3f7f1e07f87f 0x7fe3e7efe3c0ff0f

def z207 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x68e0c698e1e0667a 0x8d1c18d31c3c0ccf

def z208 : W := mkw 0x030b051414050000 0x006160a28280a000 0xf70f071f1e078007 0x7ee1e0e3e3c0f000

def z209 : W := mkw 0x0a0b000116055852 0x8141600022c0ab0a 0x9f0f00001e07f87d 0x73e1e00003c0ff0f

def z210 : W := mkw 0x00001022600002a0 0x200002044c000054 0x000000e0e0000780 0x0000001c1c0000f0

def z211 : W := mkw 0x2fffb7ffd6055852 0x85fff6fffac0ab0a 0xfffffffffe07f87f 0xffffffffffc0ff0f

def z212 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xd8e0c680e1e06606 0xbb1c18d01c3c0cc0

def z213 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8fcc7f8f1ffffff 0xff1f98ff1e3fffff

def z214 : W := mkw 0x17dfed141ddf8004 0x02fbfda283bbf000 0xf7ffff1f1fff8007 0xfeffffe3e3fff000

def z215 : W := mkw 0x27fef7fee1020220 0x04ffdeffdc204044 0xefffffffe1060667 0xfdfffffffc20c0cc

def z216 : W := mkw 0x234eb53ec0000000 0x0469d6a7d8000000 0xe70fff1fe0000003 0x7ce1ffe3fc000000

def z217 : W := mkw 0x0000102240000000 0x0000020448000000 0x2003f807e0000001 0x04007f00fc000000

def z218 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x9ffff9e01fff9f87 0xf3ffff3c03fff3f0

def z219 : W := mkw 0x27fffffff10e0ae0 0x24fffffffe21c15c 0xe7ffffffe0060063 0xfcfffffffc00c00c

def z220 : W := mkw 0x27feb7fec0202400 0x04ffd6ffd8040480 0xffffffffe1e06607 0xfffffffffc3c0cc0

def z221 : W := mkw 0x0fbb07d51eb57d53 0x81f760faa3d6afaa 0xffff07ff1fffffff 0xffffe0ffe3ffffff

def z222 : W := mkw 0x1044e800014a8004 0x02089d0000295000 0x0000f80000000000 0x00001f0000000000

def z223 : W := mkw 0x25f4b7fec0000000 0x04be96ffd8000000 0x60f0ffffe0000002 0x8c1e1ffffc000000

def z224 : W := mkw 0x04d4a00000000000 0x009a940000000000 0x00f0f80000000000 0x801e1f0000000000

def z225 : W := mkw 0x07ba07d40ab07503 0x00f740fa81560ea0 0xffff07ff1ff87f87 0xffffe0ffe3ff0ff0

def z226 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x58ec061801e7e67c 0x2b1d80c3003cfccf

def z227 : W := mkw 0x0900051402005012 0x812000a280400a02 0x4000061800006018 0x080000c300000c03

def z228 : W := mkw 0x04f4c288a9f2a628 0x409e9851153e54c5 0xfffcc698ffffe67f 0xffff98d31ffffccf

def z229 : W := mkw 0x05f4c7c8abf2f72b 0x40be98f9157e5ee5 0xdff0c7e0fff87f86 0xfbfe18fc1fff0ff0

def z230 : W := mkw 0x0044800880000000 0x0008900110000000 0x200cc018e0000001 0x040198031c000000

def z231 : W := mkw 0x37fea7dc8cd18004 0x06ffd4fb919a3000 0x57ec06180ee18000 0x2afd80c301dc3000

def z232 : W := mkw 0x212017fec0000000 0x042402ffd8000000 0x600007ffe0000002 0x0c0000fffc000000

def z233 : W := mkw 0x0801000114050850 0x810020002280a10a 0x0000000000078078 0x000000000000f00f

def z234 : W := mkw 0x2f9b357756055852 0x85f366aeeac0ab0a 0x071339671e001800 0x40e2672ce3c00300

def z235 : W := mkw 0x16dff8225ddf8004 0x02dbff044bbbf000 0xb7fff9e7ffff8007 0xf6ffff3cfffff000

def z236 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x071ff8001e1f8001 0x40e3ff0003c3f000

def z237 : W := mkw 0x0490004008900101 0x0092000801120020 0x0010006000180180 0x0002000c00030030

def z238 : W := mkw 0x14d4e80009da8004 0x029a9d00013b5000 0x97f0f8001ff80004 0xf2fe1f0003ff0000

def z239 : W := mkw 0x37fefffec9da8004 0x06ffdfffd93b5000 0xe7ffffffe1f80003 0xfcfffffffc3f0000

def z240 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x0000000000060060 0x000000000000c00c

def z241 : W := mkw 0x000040002162a628 0x40000800042c54c5 0x0000000001e00600 0x00000000003c00c0

def z242 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x48f007e001f87f82 0x891e00fc003f0ff0

def z243 : W := mkw 0x00014801110e0840 0x000029002221c108 0xa813f907111e1867 0xd5027f20e223c30c

def z244 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xaf0301071e061867 0x55e06020e3c0c30c

def z245 : W := mkw 0x0000400021020220 0x0000080004204044 0xf80cc698e107e67f 0xbf0198d31c20fccf

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013f80000000001 0xd0027f0000000000

def z247 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2013f967f01e19e1 0x44027f2cfe03c33c

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c001800078079 0x040180030000f00f

def z249 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x07f3f9e7e0000000 0xc0fe7f3cfc000000

def z250 : W := mkw 0x05b017e240000000 0x00b602fc48000000 0xe7f3ffe7e0000003 0xfcfe7ffcfc000000

def z251 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x07f001e01ff81f80 0xc0fe003c03ff03f0

def z252 : W := mkw 0x100108001c9d0004 0x020021000393a000 0x000000001e180000 0x0000000003c30000

def z253 : W := mkw 0x006482888060a408 0x400c9051100c1481 0xf0ecc698e0e1e01b 0xbe1d98d31c1c3c03

def z254 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdfe007001ee07806 0x7bfc00e003dc0f00

def z255 : W := mkw 0x0065daabf10e0ae0 0x200cbb557e21c15c 0xe8fffffff11e1fe7 0xfd1ffffffe23c3fc

def z256 : W := mkw 0x0045d82bf14e8ae8 0x6008bb057e29d15d 0xa81ff9fff11f9fff 0xd503ff3ffe23f3ff

def z257 : W := mkw 0x27feb7fec2207503 0x04ffd6ffd8440ea0 0xefffffffe0007f83 0xfdfffffffc000ff0

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x801001e000000002 0xd002003c00000000

def z259 : W := mkw 0x0065ca89b16eaee8 0x600cb951362dd5dd 0xf8ecc698f1ffffff 0xbf1d98d31e3fffff

def z260 : W := mkw 0x0db007d50ab07d53 0x81b600faa1560faa 0xfff007ff1ff87ffe 0xfffe00ffe3ff0fff

def z261 : W := mkw 0x0100050002005002 0x002000a000400a00 0xdf0007001e007806 0x7be000e003c00f00

def z262 : W := mkw 0x0590054000000000 0x00b200a800000000 0x0710016000000000 0x40e2002c00000000

def z263 : W := mkw 0x226ef2bee162a628 0x444dde57dc2c54c5 0xf8effe9fe1e7e67f 0xbf1dffd3fc3cfccf

def z264 : W := mkw 0x01215fe3732e7fe3 0x20242bfc6e65cffc 0xe813ffe7f11e7fe7 0xdd027ffcfe23cffc

def z265 : W := mkw 0x0064daaae16aa6a8 0x600c9b555c2d54d5 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z266 : W := mkw 0x0490000008900000 0x0092000001120000 0x97f000001ff80004 0xf2fe000003ff0000

def z267 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x67ec07ffe0000002 0x2cfd80fffc000000

def z268 : W := mkw 0x0020028000202400 0x0004005000040480 0x00e0008001e00600 0x801c0010003c00c0

def z269 : W := mkw 0x27feb7feca905103 0x04ffd6ffd9520a20 0xe7fffffffe181983 0xfcffffffffc30330

def z270 : W := mkw 0x00648288a060a628 0x400c9051140c14c5 0x78ec0698e0e1e67a 0x2f1d80d31c1c3ccf

def z271 : W := mkw 0x100148001ddf8004 0x0200290003bbf000 0x9013f8001fff8005 0xd2027f0003fff000

def z272 : W := mkw 0x00014800310e0220 0x000029000621c044 0xa813f880f11e0667 0xd5027f101e23c0cc

def z273 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xe0ecc698e1e00603 0xbc1d98d31c3c00c0

def z274 : W := mkw 0x16dfe8003ddf8224 0x02dbfd0007bbf044 0xbffff880ffff8667 0xf7ffff101ffff0cc

def z275 : W := mkw 0x04b002c008b02501 0x00960058011604a0 0xd8f006e001f86786 0xbb1e00dc003f0cf0

def z276 : W := mkw 0x05f487c880000000 0x00be90f910000000 0xe7fcc7f8e0000003 0xfcff98ff1c000000

def z277 : W := mkw 0x0044c00001428000 0x0008980000285000 0x000cc00000078001 0x000198000000f000

def z278 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00c061800000003 0x3c0180c300000000

def z279 : W := mkw 0x0064c288a1020220 0x000c985114204044 0xe8ecc698e1060667 0xbd1d98d31c20c0cc

def z280 : W := mkw 0x0064c2800162a400 0x000c9850002c5480 0xd8ecc68001e7e607 0xbb1d98d0003cfcc0

def z281 : W := mkw 0x202012eac0000000 0x0404025d58000000 0x000000e0e0000000 0x0000001c1c000000

def z282 : W := mkw 0x2ffea7dc86015012 0x85ffd4fb90c02a02 0x57ec06180e01e018 0x2afd80c301c03c03

def z283 : W := mkw 0x0000400021020220 0x0000080004204044 0x2000c000e0060061 0x040018001c00c00c

def z284 : W := mkw 0x0000502261020220 0x00000a044c204044 0xa813f9e7e1060667 0xd5027f3cfc20c0cc

def z285 : W := mkw 0x0800001500000850 0x81000002a000010a 0x2000001f00000078 0x04000003e000000f

def z286 : W := mkw 0x17ffefc01ffff507 0x02fffdf803fffea0 0xd7fffe001fffe005 0xfaffffc003fffc00

def z287 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa01ff9ffe0000003 0xd403ff3ffc000000

def z288 : W := mkw 0x00200288a0202628 0x40040051140404c5 0x00000080e0000600 0x000000101c0000c0

def z289 : W := mkw 0x26deb03ec0000000 0x04dbd607d8000000 0xa7fff81fe0000001 0xf4ffff03fc000000

def z290 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xeffffffff1181f87 0xfdfffffffe2303f0

def z291 : W := mkw 0x16dfe8013ddf8ae4 0x22dbfd0027bbf15c 0x9ffff8001fff9fe5 0xf3ffff0003fff3fc

def z292 : W := mkw 0x16dfe8003dffa62c 0x42dbfd0007bff4c5 0x9ffff8001fffe67d 0xf3ffff0003fffccf

def z293 : W := mkw 0x16dfa8001cdd8004 0x02dbf500039bb000 0x17ff38001ef98000 0x62ffe70003df3000

def z294 : W := mkw 0x16dfe808bddf822c 0x42dbfd0117bbf045 0xb7fff818ffff807d 0xf6ffff031ffff00f

def z295 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xf81ffffff11fffff 0xff03fffffe23ffff

def z296 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x680cc698e007e67b 0x0d0198d31c00fccf

def z297 : W := mkw 0x0b0b051514050850 0x816160a2a280a10a 0xe70f071f0007807b 0x7ce1e0e3e000f00f

def z298 : W := mkw 0x14f4ea88a9faa62c 0x429e9d51153f54c5 0xf8fcfe98e1ffe67f 0xbf1f9fd31c3ffccf

def z299 : W := mkw 0x036e879c80000000 0x006dd0f390000000 0xe7efc79fe0000003 0xfcfdf8f3fc000000

def z300 : W := mkw 0x0045c800114e8000 0x0008b9000229d000 0x90fff80011ff8005 0xf21fff00023ff000

def z301 : W := mkw 0x0064daaae16aa6a8 0x600c9b555c2d54d5 0xf8fcfef8e1ffe7ff 0xbf1f9fdf1c3ffcff

def z302 : W := mkw 0x24f4b2eac0000000 0x049e965d58000000 0xa0f3f9e7e0000003 0xd41e7f3cfc000000

def z303 : W := mkw 0x0064828880000000 0x000c905110000000 0x00e0c080e0000000 0x801c18101c000000

def z304 : W := mkw 0x27ba37f640000000 0x04f746fec8000000 0xc7f33fe700000002 0xf8fe67fce0000000

def z305 : W := mkw 0x00005822610a02a0 0x20000b044c214054 0xa013f9e7e1180783 0xd4027f3cfc2300f0

def z306 : W := mkw 0x0100050002005002 0x002000a000400a00 0x570006000e006000 0x2ae000c001c00c00

def z307 : W := mkw 0x14d5e80019de8004 0x029abd00033bd000 0x80f3f80011fe0005 0xd01e7f00023fc000

def z308 : W := mkw 0x2044b02ac0000000 0x0408960558000000 0x0000f800e0000000 0x00001f001c000000

def z309 : W := mkw 0x0901050116055852 0x812020a022c0ab0a 0xdf0007001e07f87e 0x7be000e003c0ff0f

def z310 : W := mkw 0x00648288a0202628 0x400c9051140404c5 0xe8ecc698e000667b 0xbd1d98d31c000ccf

def z311 : W := mkw 0x0800000006015012 0x8100000000c02a02 0x100000000e01e018 0x0200000001c03c03

def z312 : W := mkw 0x14d5e8001ddf8004 0x029abd0003bbf000 0x10f0f8001fff8004 0x821e1f0003fff000

def z313 : W := mkw 0x0000502361020ae0 0x20000a046c20415c 0xa800c1e7e1061fe7 0x9500183cfc20c3fc

def z314 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa803f907f0061867 0x55007f20fe00c30c

def z315 : W := mkw 0x180148011fdfd856 0x8300290023fbfb0a 0x180000001ffff87c 0x0300000003ffff0f

def z316 : W := mkw 0x124fe800154f8004 0x0249fd0002a9f000 0x801ff800111f8005 0xd003ff000223f000

def z317 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x5fe006001ff87f84 0x2bfc00c003ff0ff0

def z318 : W := mkw 0x0490000008900000 0x0092000001120000 0x071000001e180000 0x40e2000003c30000

def z319 : W := mkw 0x05b007c8aab0772b 0x40b600f915560ee5 0xfff007f8fff87ffe 0xfffe00ff1fff0fff

def z320 : W := mkw 0x0100050002005002 0x002000a000400a00 0x4800070000007802 0x090000e000000f00

def z321 : W := mkw 0x020b000014050000 0x004160000280a000 0x000f000000078001 0x0001e0000000f000

def z322 : W := mkw 0x00204288a162a628 0x40040851142c54c5 0x78000698e1e7e67e 0x0f0000d31c3cfccf

def z323 : W := mkw 0x0020028000202400 0x0004005000040480 0xd8f007e011f87f86 0xfb1e00fc023f0ff0

def z324 : W := mkw 0x0800000102005852 0x8100000020400b0a 0x0800000000007878 0x0100000000000f0f

def z325 : W := mkw 0x169b68001d9f0004 0x02d36d0003b3e000 0x8713f8001f1e0005 0xd0e27f0003e3c000

def z326 : W := mkw 0x27fea7dc80000000 0x04ffd4fb90000000 0xe7ef071f00000003 0x7cfde0e3e0000000

def z327 : W := mkw 0x0a0b001516055852 0x81416002a2c0ab0a 0x380f001f1e07f87d 0x0701e003e3c0ff0f

def z328 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x07f3f8001ff80000 0xc0fe7f0003ff0000

def z329 : W := mkw 0x27deb57640000000 0x04fbd6aec8000000 0x87fff96700000001 0xf0ffff2ce0000000

def z330 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa013f807f11e0065 0xd4027f00fe23c00c

def z331 : W := mkw 0x27fef7feebf2f72b 0x44ffdeffdd7e5ee5 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x0b0b451537075a72 0x816168a2a6e0eb4e 0xff0fc79fff07fe7f 0xffe1f8f3ffe0ffcf

def z333 : W := mkw 0x100148013ddf8ae4 0x2200290027bbf15c 0x180000001fff9fe4 0x0300000003fff3fc

def z334 : W := mkw 0x00004800010a0000 0x0000090000214000 0x0010f80001180000 0x80021f0000230000

def z335 : W := mkw 0x0900051502005852 0x812000a2a0400b0a 0x0000010700001800 0x00000020e0000300

def z336 : W := mkw 0x27ba37fec0000000 0x04f746ffd8000000 0x67133fffe0000002 0x4ce267fffc000000

def z337 : W := mkw 0x26feb2fec0000000 0x04dfd65fd8000000 0x20fff8ffe0000001 0x841fff1ffc000000

def z338 : W := mkw 0x0044c008a1428228 0x4008980114285045 0xf80cc618e007e07f 0x3f0198c31c00fc0f

def z339 : W := mkw 0x030a051402005002 0x006140a280400a00 0xff0f071f1e007807 0x7fe1e0e3e3c00f00

def z340 : W := mkw 0x00011823500c08c0 0x200023046a018118 0xa8133967101e19e7 0x5502672ce203c33c

def z341 : W := mkw 0x06fea28880000000 0x00dfd45110000000 0xe7fffe98e0000003 0xfcffffd31c000000

def z342 : W := mkw 0x0064828880202400 0x000c905110040480 0xf8ecc698e1e06607 0xbf1d98d31c3c0cc0

def z343 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x0810f8e0f11e1fe4 0x81021f1c1e23c3fc

def z344 : W := mkw 0x000000000ab07503 0x0000000001560ea0 0x981001e01ff87f86 0xd302003c03ff0ff0

def z345 : W := mkw 0x0490000008900000 0x0092000001120000 0x9ff001e01ff81f86 0xf3fe003c03ff03f0

def z346 : W := mkw 0x27fea7dc8ab07503 0x04ffd4fb91560ea0 0x57ec06180ee06000 0x2afd80c301dc0c00

def z347 : W := mkw 0x0064c288a1428228 0x400c985114285045 0xe0ecc698e007807b 0xbc1d98d31c00f00f

def z348 : W := mkw 0x0000102240000000 0x0000020448000000 0x200001e7e0000002 0x0400003cfc000000

def z349 : W := mkw 0x0fbb5ff77fbf7ff3 0xa1f76bfeeff7effe 0xffffffffffffffff 0xffffffffffffffff

def z350 : W := mkw 0x00204288a1222628 0x40040851142444c5 0xe800c698e106667f 0x9d0018d31c20cccf

def z351 : W := mkw 0x002012abe0202ee8 0x600402557c0405dd 0x680007ffe0007ffa 0x0d0000fffc000fff

def z352 : W := mkw 0x279a357640000000 0x04f346aec8000000 0xa713f9e7e0000003 0xd4e27f3cfc000000

def z353 : W := mkw 0x059005400a905103 0x00b200a801520a20 0x071001601e181980 0x40e2002c03c30330

def z354 : W := mkw 0x05b007c008900000 0x00b600f801120000 0xd7f007e01ff80006 0xfafe00fc03ff0000

def z355 : W := mkw 0x16dff8237ddf8ae4 0x22dbff046fbbf15c 0xb7fff807ffff8065 0xf6ffff00fffff00c

def z356 : W := mkw 0x04b0028008b02400 0x0096005001160480 0xdff006801ff86606 0xfbfe00d003ff0cc0

def z357 : W := mkw 0x06dea00008900000 0x00dbd40001120000 0x97fff8001ff80005 0xf2ffff0003ff0000

def z358 : W := mkw 0x220a303640000000 0x04414606c8000000 0x0003380700000000 0x00006700e0000000

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010016010181980 0x4002002c02030330

def z360 : W := mkw 0x0a0a001404010010 0x8141400280802002 0x000c001800018018 0x0001800300003003

def z361 : W := mkw 0x16fea2888cf1a40c 0x42dfd451119e3481 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z362 : W := mkw 0x05911d635a9c59c3 0x20b223ac6b538b38 0x071339671e181980 0x40e2672ce3c30330

def z363 : W := mkw 0x212017fec0000000 0x042402ffd8000000 0xe013ffffe0000003 0xdc027ffffc000000

def z364 : W := mkw 0x1fffefd51ffffd57 0x83fffdfaa3ffffaa 0xffffffff1fffffff 0xffffffffe3ffffff

def z365 : W := mkw 0x0001000110040840 0x0000200022008108 0x0003010710001800 0x40006020e2000300

def z366 : W := mkw 0x224ff83ff10e0ae0 0x2449ff07fe21c15c 0x200ff81fe0060061 0x0401ff03fc00c00c

def z367 : W := mkw 0x006492aac0000000 0x000c925558000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z368 : W := mkw 0x16ffea889dffa40c 0x42dffd5113bff481 0xd7fffe181fffe01d 0xfaffffc303fffc03

def z369 : W := mkw 0x17fea7c00ef1f507 0x02ffd4f801de3ea0 0xdffc07e01ff9ff86 0xfbff80fc03ff3ff0

def z370 : W := mkw 0x0b0a051406015012 0x816140a280c02a02 0xf70f071f0e01e01b 0x7ee1e0e3e1c03c03

def z371 : W := mkw 0x06dee00001428000 0x00dbdc0000285000 0x97fff80001e78005 0xf2ffff00003cf000

def z372 : W := mkw 0x100148001ffff507 0x0200290003fffea0 0x180000001fffff84 0x0300000003fffff0

def z373 : W := mkw 0x1fdfed141fdfd016 0x83fbfda283fbfa02 0xd7fffe181fffe01d 0xfaffffc303fffc03

def z374 : W := mkw 0x3fffffffdfdfd856 0x87fffffffbfbfb0a 0xfffffffffffff87f 0xffffffffffffff0f

def z375 : W := mkw 0x0b0b1d37560d58d2 0xa16163a6eac1ab1a 0x071339671e181980 0x40e2672ce3c30330

def z376 : W := mkw 0x16dfe800154f8004 0x02dbfd0002a9f000 0x87fff80000078001 0xf0ffff000000f000

def z377 : W := mkw 0x020b000014050000 0x004160000280a000 0x970f00001e078005 0x72e1e00003c0f000

def z378 : W := mkw 0x0100051400000000 0x002000a280000000 0x6000071f00000002 0x0c0000e3e0000000

def z379 : W := mkw 0x2164d7fee162a628 0x442c9affdc2c54c5 0xf8ecc7ffe1e7e67f 0xbf1d98fffc3cfccf

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800000000060067 0x150000000000c00c

def z381 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x97fff8000ee18001 0xf2ffff0001dc3000

def z382 : W := mkw 0x0b4fc5151747d852 0x8169f8a2a2e8fb0a 0xffefc71f1fe7f87f 0xfffdf8e3e3fcff0f

def z383 : W := mkw 0x069b00001c950000 0x00d360000392a000 0x97ff00001fff8005 0xf2ffe00003fff000

def z384 : W := mkw 0x0a6fc29db567ae78 0xc14df853b6acf5cf 0xf8efc69fe1e7e67f 0xbf1df8d3fc3cfccf

def z385 : W := mkw 0x0001102350040840 0x000022046a008108 0xa813f9e7f0061867 0xd5027f3cfe00c30c

def z386 : W := mkw 0x030a153640000000 0x006142a6c8000000 0xe71fffffe0000003 0xfce3fffffc000000

def z387 : W := mkw 0x27fffffed10e0000 0x04ffffffda21c000 0xe7fffffff11e0007 0xfcfffffffe23c000

def z388 : W := mkw 0x226eb2bec0000000 0x044dd657d8000000 0xe0effe9fe0000003 0xbc1dffd3fc000000

def z389 : W := mkw 0x1fffef9dbffffe7e 0xc3fffdf3b7ffffcf 0xffffff9ffffffe7f 0xfffffff3ffffffcf

def z390 : W := mkw 0x06dea00000000000 0x00dbd40000000000 0x07ec000000000000 0x20fd800000000000

def z391 : W := mkw 0x05f4c7c00bf2f503 0x00be98f8017e5ea0 0xdffcc7e01fffff87 0xfbff98fc03fffff0

def z392 : W := mkw 0x0000000008900000 0x0000000001120000 0x100000001ff80004 0x0200000003ff0000

def z393 : W := mkw 0x0fbb07d516055852 0x81f760faa2c0ab0a 0xffff07ff1e07f87f 0xffffe0ffe3c0ff0f

def z394 : W := mkw 0x0b0a051502005852 0x816140a2a0400b0a 0xef0f071f0000787b 0x7de1e0e3e0000f0f

def z395 : W := mkw 0x0000000100000840 0x0000000020000108 0x2800010700001862 0x05000020e000030c

def z396 : W := mkw 0x0900051502005852 0x812000a2a0400b0a 0xf80c071f0007f87f 0x3f0180e3e000ff0f

def z397 : W := mkw 0x0b6e879c8661f41a 0xc16dd0f390cc3e83 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z398 : W := mkw 0x27feb7fec8b02501 0x04ffd6ffd91604a0 0xe7ffffffe1f80783 0xfcfffffffc3f00f0

def z399 : W := mkw 0x0064c28881428000 0x000c985110285000 0xf0ecc698e1e78007 0xbe1d98d31c3cf000

def z400 : W := mkw 0x00215aa3712e2ee0 0x20042b546e25c5dc 0xf8f3ffe7f1fe7fe7 0xff1e7ffcfe3fcffc

def z401 : W := mkw 0x0020028000202400 0x0004005000040480 0xf8ec069801e7e67f 0xbf1d80d3003cfccf

def z402 : W := mkw 0x37fffffedffff507 0x06ffffffdbfffea0 0xffffffffffffff87 0xfffffffffffffff0

def z403 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x57f006e00ff86780 0xaafe00dc01ff0cf0

def z404 : W := mkw 0x00011823500c08c0 0x200023046a018118 0xa013f9e7f0181983 0xd4027f3cfe030330

def z405 : W := mkw 0x37fffffefdffa62c 0x46ffffffdfbff4c5 0xffffffffffffe67f 0xfffffffffffffccf

def z406 : W := mkw 0x059005000a905002 0x00b200a001520a00 0xdff007001ff87806 0xfbfe00e003ff0f00

def z407 : W := mkw 0x34f4faeac9da8004 0x069e9f5d593b5000 0x00f0f8e0e1f80000 0x801e1f1c1c3f0000

def z408 : W := mkw 0x0020028000202400 0x0004005000040480 0x50e0060000e06000 0x2a1c00c0001c0c00

def z409 : W := mkw 0x05b017e36ab07fe3 0x20b602fc6d560ffc 0xfff007e7fff87fe6 0xfffe00fcffff0ffc

def z410 : W := mkw 0x0001000014050000 0x000020000280a000 0x100000001e078004 0x0200000003c0f000

def z411 : W := mkw 0x16dfa0001cd58004 0x02dbf400039ab000 0x97ef00001ee78005 0x72fde00003dcf000

def z412 : W := mkw 0x05b14fc13bbe7fe3 0x20b629f82777cffc 0xdff007e01ffe7fe6 0xfbfe00fc03ffcffc

def z413 : W := mkw 0x2fffb7ffdeb57d53 0x85fff6fffbd6afaa 0xffffffffffffffff 0xffffffffffffffff

def z414 : W := mkw 0x00005822610a02a0 0x20000b044c214054 0x0000f800e0000000 0x00001f001c000000

def z415 : W := mkw 0x169b78237d9f0ae4 0x22d36f046fb3e15c 0xaf13f9e7ff1e1fe7 0xd5e27f3cffe3c3fc

def z416 : W := mkw 0x04b002c00ab07503 0x0096005801560ea0 0x18f000e01ff87f84 0x831e001c03ff0ff0

def z417 : W := mkw 0x05b007c002005002 0x00b600f800400a00 0xdff007e01e007806 0xfbfe00fc03c00f00

def z418 : W := mkw 0x292017ffc2005852 0x852402fff8400b0a 0x680007ffe000787a 0x0d0000fffc000f0f

def z419 : W := mkw 0x002002c000202501 0x00040058000404a0 0x000000e000000780 0x0000001c000000f0

def z420 : W := mkw 0x224ff83ff10e0ae0 0x2449ff07fe21c15c 0xa81ff9fff11e1fe7 0xd503ff3ffe23c3fc

def z421 : W := mkw 0x00200288a0202628 0x40040051140404c5 0xf80c0698e007e67f 0x3f0180d31c00fccf

def z422 : W := mkw 0x00014800110e0000 0x000029000221c000 0x0003f80000060001 0x00007f000000c000

def z423 : W := mkw 0x04b002c008b02501 0x00960058011604a0 0x00e0000000e00000 0x001c0000001c0000

def z424 : W := mkw 0x069a200000000000 0x00d3440000000000 0x0713380000000000 0x40e2670000000000

def z425 : W := mkw 0x07fea7c00ab07503 0x00ffd4f801560ea0 0xdfffffe01ff87f87 0xfbfffffc03ff0ff0

def z426 : W := mkw 0x05f4c7c8abf2f72b 0x40be98f9157e5ee5 0xffecc698efe7e67f 0xbffd98d31dfcfccf

def z427 : W := mkw 0x212017ffe0000ae0 0x242402fffc00015c 0x680007ffe0001fe2 0x0d0000fffc0003fc

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0xd800060000006006 0x3b0000c000000c00

def z429 : W := mkw 0x212017fee0202628 0x442402ffdc0404c5 0x680007ffe000667a 0x0d0000fffc000ccf

def z430 : W := mkw 0x27feb7fec8900000 0x04ffd6ffd9120000 0xf7fffffffff80007 0xfeffffffffff0000

def z431 : W := mkw 0x0865c289b767fe7a 0xc10cb85136ecffcf 0xf8ecc698ffe7fe7f 0xbf1d98d31ffcffcf

def z432 : W := mkw 0x012007c00ab07503 0x002400f801560ea0 0x580007e01ff87f86 0x0b0000fc03ff0ff0

def z433 : W := mkw 0x020a000004010000 0x0041400000802000 0x170c00000e018000 0x22e1800001c03000

def z434 : W := mkw 0x0000000000202400 0x0000000000040480 0x1800000001e06604 0x03000000003c0cc0

def z435 : W := mkw 0x37dffd765ddf8004 0x06fbffaecbbbf000 0x97fff9671fff8005 0xf2ffff2ce3fff000

def z436 : W := mkw 0x0000000020000220 0x0000000004000044 0x28000080e0000662 0x050000101c0000cc

def z437 : W := mkw 0x030b051510040840 0x006160a2a2008108 0xef0f071f10061867 0x7de1e0e3e200c30c

def z438 : W := mkw 0x0020028000202400 0x0004005000040480 0x4800068000006602 0x090000d000000cc0

def z439 : W := mkw 0x324ff83ed54f8004 0x0649ff07daa9f000 0x200ff81fe0078001 0x0401ff03fc00f000

def z440 : W := mkw 0x00000008a0000228 0x4000000114000045 0x20000018e0000078 0x040000031c00000f

def z441 : W := mkw 0x0064828880000000 0x000c905110000000 0xf8ecc698e007e07f 0xbf1d98d31c00fc0f

def z442 : W := mkw 0x21215ffff10e0ae0 0x24242bfffe21c15c 0xe813fffff11e1fe7 0xdd027ffffe23c3fc

def z443 : W := mkw 0x012007c8a220772b 0x402400f914440ee5 0x680007f8e0007ffa 0x0d0000ff1c000fff

def z444 : W := mkw 0x09015d37730e5af2 0xa1202ba6ee61cb5e 0xe813fffff11e7fff 0xdd027ffffe23cfff

def z445 : W := mkw 0x0044800880408008 0x4008900110081001 0x000c001800018018 0x0001800300003003

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800010010001806 0x5100002002000300

def z447 : W := mkw 0x0fbb07d51eb57d53 0x81f760faa3d6afaa 0xdff307e71ff87f86 0xfbfe60fce3ff0ff0

def z448 : W := mkw 0x36dff83edddf8004 0x06dbff07dbbbf000 0xb7fff81fffff8005 0xf6ffff03fffff000

def z449 : W := mkw 0x006482888060a408 0x400c9051100c1481 0xd8ec069801e1e61e 0xbb1d80d3003c3cc3

def z450 : W := mkw 0x124ff823754f8ae4 0x2249ff046ea9f15c 0x200ff807e0078061 0x0401ff00fc00f00c

def z451 : W := mkw 0x0064c2888162a408 0x400c9851102c5481 0xd0ecc61801e7e01d 0xba1d98c3003cfc03

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000c080e0000003 0x940018101c000000

def z453 : W := mkw 0x25b017fec0000000 0x04b602ffd8000000 0xe7f007ffe0000002 0xfcfe00fffc000000

def z454 : W := mkw 0x0101050112045842 0x002020a022408b08 0xff0307071e067867 0x7fe060e0e3c0cf0c

def z455 : W := mkw 0x27fef7fec1428000 0x04ffdeffd8285000 0xf7ffffffe1e78007 0xfefffffffc3cf000

def z456 : W := mkw 0x00011823500c08c0 0x200023046a018118 0x0003380700000000 0x00006700e0000000

def z457 : W := mkw 0x14d4f82269da82a4 0x229a9f044d3b5054 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z458 : W := mkw 0x2fffa7dd96055852 0x85fff4fbb2c0ab0a 0xffef071f1e07f87f 0x7ffde0e3e3c0ff0f

def z459 : W := mkw 0x379b3d765c9d0004 0x06f367aecb93a000 0x071339671e180000 0x40e2672ce3c30000

def z460 : W := mkw 0x17ffffe37fffffe7 0x22fffffc6ffffffc 0xffffffe7ffffffe7 0xfffffffcfffffffc

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010000011180004 0xd002000002230000

def z462 : W := mkw 0x07ba07d400000000 0x00f740fa80000000 0xe7ff07ff00000003 0xfcffe0ffe0000000

def z463 : W := mkw 0x124fe800154f8004 0x0249fd0002a9f000 0x970ff8001e078005 0x72e1ff0003c0f000

def z464 : W := mkw 0x224ef03ee1428228 0x4449de07dc285045 0x200ff81fe0078079 0x0401ff03fc00f00f

def z465 : W := mkw 0x0164c7c8a362f72b 0x402c98f9146c5ee5 0xf8ecc7f8e1e7ffff 0xbf1d98ff1c3cffff

def z466 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x680f071f0007f87b 0x0d01e0e3e000ff0f

def z467 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0xa8030107111e1fe7 0x55006020e223c3fc

def z468 : W := mkw 0x0901051512045852 0x812020a2a2408b0a 0xe803071f1006787f 0x5d0060e3e200cf0f

def z469 : W := mkw 0x0b2b079db6257e7a 0xc16560f3b6c4afcf 0xff0f079ffe07fe7f 0x7fe1e0f3ffc0ffcf

def z470 : W := mkw 0x169b68001ddf8004 0x02d36d0003bbf000 0x171338001fff8004 0x42e2670003fff000

def z471 : W := mkw 0x16dee8000ddb8004 0x02dbdd0001bb7000 0x17fcf8000ff98000 0xa2ff9f0001ff3000

def z472 : W := mkw 0x0b0b5d37770f5af2 0xa1616ba6eee1eb5e 0xff0fff1ffe07f87f 0x7fe1ffe3ffc0ff0f

def z473 : W := mkw 0x0b0a051506015852 0x816140a2a0c02b0a 0x7f0c071f0e01f87a 0x2fe180e3e1c03f0f

def z474 : W := mkw 0x14d4e80009da8004 0x029a9d00013b5000 0x90fcf80001ff8005 0xb21f9f00003ff000

def z475 : W := mkw 0x27fea7dc8ab07503 0x04ffd4fb91560ea0 0xdffc07f81ff87f86 0xfbff80ff03ff0ff0

def z476 : W := mkw 0x0b2b07d516257d53 0x816560faa2c4afaa 0xff0f07ff1e07ffff 0x7fe1e0ffe3c0ffff

def z477 : W := mkw 0x27ffbfffd00c08c0 0x24fff7fffa018118 0xe7fffffff0181983 0xfcfffffffe030330

def z478 : W := mkw 0x05b007c000202400 0x00b600f800040480 0xdff007e001e06606 0xfbfe00fc003c0cc0

def z479 : W := mkw 0x05b15fe3710e0ae0 0x20b62bfc6e21c15c 0xeff3ffe7f11e1fe7 0xfdfe7ffcfe23c3fc

def z480 : W := mkw 0x0020028000000000 0x0004005000000000 0xc0e0068000000002 0xb81c00d000000000

def z481 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x4f1007e01e187f82 0x49e200fc03c30ff0

def z482 : W := mkw 0x0900051502005852 0x812000a2a0400b0a 0xff00071f1e00787e 0x7fe000e3e3c00f0f

def z483 : W := mkw 0x27fef7fee1428228 0x44ffdeffdc285045 0xe7ffffffe007807b 0xfcfffffffc00f00f

def z484 : W := mkw 0x124fe808b54f822c 0x4249fd0116a9f045 0x200ff818e0078079 0x0401ff031c00f00f

def z485 : W := mkw 0x059005400a905103 0x00b200a801520a20 0x070000000e000000 0x00e0000001c00000

def z486 : W := mkw 0x000148013bbe7fe3 0x200029002777cffc 0x180000001ffe7fe4 0x0300000003ffcffc

def z487 : W := mkw 0x00014800110e0000 0x000029000221c000 0x00000000111e0004 0x000000000223c000

def z488 : W := mkw 0x0490000000000000 0x0092000000000000 0x87f0000000000000 0xf0fe000000000000

def z489 : W := mkw 0x0000102360000ae0 0x200002046c00015c 0x20000007e0000060 0x04000000fc00000c

def z490 : W := mkw 0x0100050002005002 0x002000a000400a00 0xdf1007e01f187f86 0xfbe200fc03e30ff0

def z491 : W := mkw 0x120b48001ddf8004 0x0241690003bbf000 0x970f00001fff8005 0x72e1e00003fff000

def z492 : W := mkw 0x0000102360000ae0 0x200002046c00015c 0xa813f9e7e0001fe3 0xd5027f3cfc0003fc

def z493 : W := mkw 0x0001000110040840 0x0000200022008108 0x2003000700060061 0x04006000e000c00c

def z494 : W := mkw 0x2fffb7ffd6055852 0x85fff6fffac0ab0a 0xe7fffffffe001803 0xfcffffffffc00300

def z495 : W := mkw 0x030b5d37710e0ae0 0x20616ba6ee21c15c 0xef1ffffff11e1fe7 0xfde3fffffe23c3fc

def z496 : W := mkw 0x24f4f2eae162a628 0x449e9e5d5c2c54c5 0x00f0f8e0e1e00600 0x801e1f1c1c3c00c0

def z497 : W := mkw 0x16dee80009da8004 0x02dbdd00013b5000 0x87fff80001f80001 0xf0ffff00003f0000

def z498 : W := mkw 0x0b0a051406015012 0x816140a280c02a02 0x070000000e000000 0x00e0000001c00000

def z499 : W := mkw 0x0000400021020220 0x0000080004204044 0xa810c1e0f11e1fe7 0xd502183c1e23c3fc

def z500 : W := mkw 0x2000103ec0000000 0x04000207d8000000 0x2000001fe0000000 0x04000003fc000000

def z501 : W := mkw 0x0001000110040840 0x0000200022008108 0xf80f071f1007f87f 0x7f01e0e3e200ff0f

def z502 : W := mkw 0x04914800199e0000 0x009229000333c000 0x97f3f8001ffe0005 0xf2fe7f0003ffc000

def z503 : W := mkw 0x0000102240000000 0x0000020448000000 0x0010f8e0e0000000 0x80021f1c1c000000

def z504 : W := mkw 0x080140013767fe7a 0xc100280026ecffcf 0x180000001fe7fe7c 0x0300000003fcffcf

def z505 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x5fe007e00ee07f82 0x2bfc00fc01dc0ff0

def z506 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x08133967111e1fe4 0x4102672ce223c3fc

def z507 : W := mkw 0x05b14fc01bbe7503 0x00b629f80377cea0 0xdff3ffe01ffe7f87 0xfbfe7ffc03ffcff0

def z508 : W := mkw 0x0001400131060a60 0x000028002620c14c 0xa803c187f1061e67 0xd5007830fe20c3cc

def z509 : W := mkw 0x279b7d77710e0ae0 0x24f36faeee21c15c 0xaf13f9e7f11e1fe7 0xd5e27f3cfe23c3fc

def z510 : W := mkw 0x0045d82bf14e8ae8 0x6008bb057e29d15d 0x200ff81fe0078079 0x0401ff03fc00f00f

def z511 : W := mkw 0x0f9b05551e955953 0x81f360aaa3d2ab2a 0xff1f077f1e1ff9ff 0x7fe3e0efe3c3ff3f

def z512 : W := mkw 0x1fdfed151fdfd856 0x83fbfda2a3fbfb0a 0x97fff9071fff9805 0xf2ffff20e3fff300

def z513 : W := mkw 0x279a357640000000 0x04f346aec8000000 0xe71f3f7f00000003 0x7ce3e7efe0000000

def z514 : W := mkw 0x0b6f879d9665fc5a 0xc16df0f3b2ccbf8b 0xffef071f1ee7f87f 0x7ffde0e3e3dcff0f

def z515 : W := mkw 0x0064c288abf2f72b 0x400c9851157e5ee5 0xf8ecc698ffffffff 0xbf1d98d31fffffff

def z516 : W := mkw 0x08015823770f5af2 0xa1002b046ee1eb5e 0xb813f9e7ff1fffff 0xd7027f3cffe3ffff

def z517 : W := mkw 0x006482888060a408 0x400c9051100c1481 0x00e0000000e00000 0x001c0000001c0000

def z518 : W := mkw 0x0044c00021428220 0x0008980004285044 0xb8ecc080e1e78667 0xb71d98101c3cf0cc

def z519 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x770f061f0e07e079 0x2ee1e0c3e1c0fc0f

def z520 : W := mkw 0x0000000008b02501 0x00000000011604a0 0x0000000001f80780 0x00000000003f00f0

def z521 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17ec00001fff8004 0x22fd800003fff000

def z522 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x570f071f1e01f818 0x6ae1e0e3e3c03f03

def z523 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdfe006800fe06606 0xbbfc00d001fc0cc0

def z524 : W := mkw 0x279b3d77500c08c0 0x24f367aeea018118 0x0713396710181980 0x40e2672ce2030330

def z525 : W := mkw 0x0000102360000ae0 0x200002046c00015c 0xa81001e7f1181fe6 0xd502003cfe2303fc

def z526 : W := mkw 0x0001000110040840 0x0000200022008108 0xa81301e7111e1fe7 0xd502603ce223c3fc

def z527 : W := mkw 0x024ea00000000000 0x0049d40000000000 0x000ff80000000001 0x0001ff0000000000

def z528 : W := mkw 0x100158237ddf8ae4 0x22002b046fbbf15c 0xb813f9e7ffff9fe7 0xd7027f3cfffff3fc

def z529 : W := mkw 0x16fffaabfdffaeec 0x62dfff557fbff5dd 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x0001000010040000 0x0000200002008000 0x8003000010060005 0x500060000200c000

def z531 : W := mkw 0x0fffc7ddbff7ff7b 0xc1fff8fbb7feffef 0xffffc7ffffffffff 0xfffff8ffffffffff

def z532 : W := mkw 0x1fdffd377fdfdaf6 0xa3fbffa6effbfb5e 0xffffffffffffffff 0xffffffffffffffff

def z533 : W := mkw 0x0b0b153756055852 0x816162a6eac0ab0a 0xff1ffffffe07f87f 0xffe3ffffffc0ff0f

def z534 : W := mkw 0x0164c788a362f62a 0x402c98f1146c5ec5 0xffecc798ffe7fe7f 0xfffd98f31ffcffcf

def z535 : W := mkw 0x27fea7dc80000000 0x04ffd4fb90000000 0xc7fffe1800000001 0xf8ffffc300000000

def z536 : W := mkw 0x0020028880000000 0x0004005110000000 0x60000698e0000002 0x0c0000d31c000000

def z537 : W := mkw 0x2100157640000000 0x042002aec8000000 0x0000016700000000 0x0000002ce0000000

def z538 : W := mkw 0x000040002162a628 0x40000800042c54c5 0xf80c061801e7e67f 0x3f0180c3003cfccf

def z539 : W := mkw 0x0100054002005103 0x002000a800400a20 0x0000016000001980 0x0000002c00000330

def z540 : W := mkw 0x04915823799e0ae0 0x20922b046f33c15c 0xbff3f9e7fffe1fe7 0xf7fe7f3cffffc3fc

def z541 : W := mkw 0x37fffffed54f8004 0x06ffffffdaa9f000 0xe7ffffffe0078003 0xfcfffffffc00f000

def z542 : W := mkw 0x17ffefc01ddf8004 0x02fffdf803bbf000 0xd7ffffe01fff8007 0xfafffffc03fff000

def z543 : W := mkw 0x0901051516055852 0x812020a2a2c0ab0a 0x7800071f1e07f87e 0x0f0000e3e3c0ff0f

def z544 : W := mkw 0x1f9b2d151e9d5856 0x83f365a2a3d3ab0a 0x071339071e181800 0x40e26720e3c30300

def z545 : W := mkw 0x0b0a051406015012 0x816140a280c02a02 0xff0c06180e07e07f 0x3fe180c301c0fc0f

def z546 : W := mkw 0x012017e362207fe3 0x202402fc6c440ffc 0x680007e7e0007fe2 0x0d0000fcfc000ffc

def z547 : W := mkw 0x0b0b4d15370f5af2 0xa16169a2a6e1eb5e 0xff0f071f1f1fffff 0x7fe1e0e3e3e3ffff

def z548 : W := mkw 0x179b2d401e9d5107 0x02f365a803d3aa20 0x071339601e181980 0x40e2672c03c30330

def z549 : W := mkw 0x0065c289b166ae68 0x400cb851362cd5cd 0xf8efc79ff1e7fe7f 0xff1df8f3fe3cffcf

def z550 : W := mkw 0x0b0a051406015012 0x816140a280c02a02 0xdf0c07181e01f81e 0x7be180e303c03f03

def z551 : W := mkw 0x012007c002207503 0x002400f800440ea0 0x4000060000006000 0x080000c000000c00

def z552 : W := mkw 0x2fffb7ffd4050850 0x85fff6fffa80a10a 0xe7ffffffe007807b 0xfcfffffffc00f00f

def z553 : W := mkw 0x1490280008980004 0x0292050001130000 0x0010380000180000 0x0002070000030000

def z554 : W := mkw 0x059005400a905103 0x00b200a801520a20 0xdf1007601e187986 0x7be200ec03c30f30

def z555 : W := mkw 0x0000000020202628 0x40000000040404c5 0x0800000000006678 0x0100000000000ccf

def z556 : W := mkw 0x0044c0002162a628 0x40089800042c54c5 0x98ecc00001e7e67d 0xb31d9800003cfccf

def z557 : W := mkw 0x00004800210a02a0 0x2000090004214054 0x0000000001180780 0x00000000002300f0

def z558 : W := mkw 0x17ffefc8bffff72f 0x42fffdf917fffee5 0xfffffff8ffffffff 0xffffffff1fffffff

def z559 : W := mkw 0x020a001400000000 0x0041400280000000 0x200f001f00000001 0x0401e003e0000000

def z560 : W := mkw 0x1fdfa5151ed5d856 0x83fbf4a2a3dabb0a 0xffef071f1ee7f87f 0x7ffde0e3e3dcff0f

def z561 : W := mkw 0x14d5f82379de8ae4 0x229abf046f3bd15c 0xa8f3f9e7f1fe1fe7 0xd51e7f3cfe3fc3fc

def z562 : W := mkw 0x24f4faeae10a02a0 0x249e9f5d5c214054 0x00f0f8e0e1180780 0x801e1f1c1c2300f0

def z563 : W := mkw 0x216497fec0000000 0x042c92ffd8000000 0xe0ecc7ffe0000003 0xbc1d98fffc000000

def z564 : W := mkw 0x0801000116055852 0x8100200022c0ab0a 0xf80c06181e07f87f 0x3f0180c303c0ff0f

def z565 : W := mkw 0x0a0b5837750f0af0 0xa1416b06eea1e15e 0xa81ff9fff11f9fff 0xd503ff3ffe23f3ff

def z566 : W := mkw 0x000000000060a408 0x40000000000c1481 0x1000000000e1e018 0x02000000001c3c03

def z567 : W := mkw 0x0000400021020220 0x0000080004204044 0x0800000001060664 0x010000000020c0cc

def z568 : W := mkw 0x00005822610a02a0 0x20000b044c214054 0xa810f8e0e11e07e7 0x95021f1c1c23c0fc

def z569 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xe70f071f1e001803 0x7ce1e0e3e3c00300

def z570 : W := mkw 0x05f487c88af0f50b 0x40be90f9115e1ea1 0xdffc07f81ff9ff9e 0xfbff80ff03ff3ff3

def z571 : W := mkw 0x024fc00015478000 0x0049f80002a8f000 0x97efc0001fe78005 0xf2fdf80003fcf000

def z572 : W := mkw 0x00215aabf12e2ee8 0x60042b557e25c5dd 0xe813fffff11e7fff 0xdd027ffffe23cfff

def z573 : W := mkw 0x124ff823754f8ae4 0x2249ff046ea9f15c 0xa81ff9e7f11f9fe7 0xd503ff3cfe23f3fc

def z574 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa803f887e1060667 0x95007f10fc20c0cc

def z575 : W := mkw 0x0065daabf16eaee8 0x600cbb557e2dd5dd 0xa8f3f9e7f1fe1fe7 0xd51e7f3cfe3fc3fc

def z576 : W := mkw 0x0db107c11eb57d53 0x81b620f823d6afaa 0xdff007e01ffffffe 0xfbfe00fc03ffffff

def z577 : W := mkw 0x020b000014050000 0x004160000280a000 0xff0f06181e07e07f 0x7fe1e0c303c0fc0f

def z578 : W := mkw 0x17bb2fc01ebd7507 0x02f765f803d7aea0 0xdff33fe01ff87f86 0xfbfe67fc03ff0ff0

def z579 : W := mkw 0x059005400ab07503 0x00b200a801560ea0 0x1f1001601ff87f84 0x43e2002c03ff0ff0

def z580 : W := mkw 0x00005823610a0ae0 0x20000b046c21415c 0x2810f9e7e1181fe2 0x85021f3cfc2303fc

def z581 : W := mkw 0x06dfa00014050000 0x00dbf4000280a000 0x97fff8001e078005 0xf2ffff0003c0f000

def z582 : W := mkw 0x05b007c008b02501 0x00b600f8011604a0 0xc7f007e001f80782 0xf8fe00fc003f00f0

def z583 : W := mkw 0x2ffeb7ffc2005852 0x85ffd6fff8400b0a 0xefffffffe000787b 0xfdfffffffc000f0f

def z584 : W := mkw 0x37fffffffddf8ae4 0x26ffffffffbbf15c 0xffffffffffff9fe7 0xfffffffffffff3fc

def z585 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x270f011f1e079879 0x44e1e023e3c0f30f

def z586 : W := mkw 0x16ffeac01dffa505 0x02dffd5803bff4a0 0x97fff8e01fff8785 0xf2ffff1c03fff0f0

def z587 : W := mkw 0x06dff823710e0ae0 0x20dbff046e21c15c 0xaffff9e7f11e1fe7 0xf5ffff3cfe23c3fc

def z588 : W := mkw 0x24f4a2c880000000 0x049e945910000000 0x00e0000000000000 0x001c000000000000

def z589 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x8813f800111e1fe5 0xd1027f000223c3fc

def z590 : W := mkw 0x04b002c008b02501 0x00960058011604a0 0x88f001e011f81f86 0xd11e003c023f03f0

def z591 : W := mkw 0x0000000002005002 0x0000000000400a00 0x180000001e007804 0x0300000003c00f00

def z592 : W := mkw 0x0000400021020220 0x0000080004204044 0x0000c080e1000600 0x800018101c2000c0

def z593 : W := mkw 0x0b0b051416055012 0x816160a282c0aa02 0xd70f06181e07e01d 0x7ae1e0c303c0fc03

def z594 : W := mkw 0x0001102370040ae0 0x200022046e00815c 0xa80301e7f0061fe7 0x5500603cfe00c3fc

def z595 : W := mkw 0x27fea7dc80000000 0x04ffd4fb90000000 0xc7fc07f800000002 0xf8ff80ff00000000

def z596 : W := mkw 0x16ffea88bdffa62c 0x42dffd5117bff4c5 0x97fff880ffff8605 0xf2ffff101ffff0c0

def z597 : W := mkw 0x126fea88b56fa62c 0x424dfd5116adf4c5 0xf8effe98e1e7e67f 0xbf1dffd31c3cfccf

def z598 : W := mkw 0x24f4f2eae162a628 0x449e9e5d5c2c54c5 0xf8fcfef8e1e7e67f 0xbf1f9fdf1c3cfccf

def z599 : W := mkw 0x2a4fb03fd4050850 0x8549f607fa80a10a 0x200ff81fe0078079 0x0401ff03fc00f00f

def z600 : W := mkw 0x0000182240080080 0x2000030448010010 0x0010386000180180 0x0002070c00030030

def z601 : W := mkw 0x27feb7fee0202628 0x44ffd6ffdc0404c5 0xefffffffe000667b 0xfdfffffffc000ccf

def z602 : W := mkw 0x16ffea801dffa404 0x02dffd5003bff480 0xdffffe801fffe607 0xfbffffd003fffcc0

def z603 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x57f007601ef87980 0x6afe00ec03df0f30

def z604 : W := mkw 0x0a0b5837750f0af0 0xa1416b06eea1e15e 0x200ff81fe0078079 0x0401ff03fc00f00f

def z605 : W := mkw 0x16ffea889ddf8004 0x02dffd5113bbf000 0xf7fffe98ffff8007 0xfeffffd31ffff000

def z606 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x47ff3f7f00000000 0x68ffe7efe0000000

def z607 : W := mkw 0x00005822610a02a0 0x20000b044c214054 0x8810f9e0f1181f86 0xd1021f3c1e2303f0

def z608 : W := mkw 0x169b38235c9d08c4 0x22d367046b93a118 0x071339671e181980 0x40e2672ce3c30330

def z609 : W := mkw 0x05f487c88af0f50b 0x40be90f9115e1ea1 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z610 : W := mkw 0x0100050002005002 0x002000a000400a00 0x070001001e001800 0x40e0002003c00300

def z611 : W := mkw 0x0fba07d40eb17513 0x81f740fa81d62ea2 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z612 : W := mkw 0x00014800110e0000 0x000029000221c000 0x8813f9e0111e1f87 0xd1027f3c0223c3f0

def z613 : W := mkw 0x27fee7dca162a628 0x44ffdcfb942c54c5 0xffecc698e1e7e67f 0xbffd98d31c3cfccf

def z614 : W := mkw 0x026fc288b567a628 0x404df85116acf4c5 0xffefc698ffe7e67f 0xfffdf8d31ffcfccf

def z615 : W := mkw 0x2ffffffff70f5af2 0xa5fffffffee1eb5e 0xffffffffff1fffff 0xffffffffffe3ffff

def z616 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xd7f006001ff86004 0xfafe00c003ff0c00

def z617 : W := mkw 0x124fe8001ddf8004 0x0249fd0003bbf000 0x100ff8001fff8005 0x0201ff0003fff000

def z618 : W := mkw 0x006482888060a408 0x400c9051100c1481 0xf8ec061800e7e07f 0x3f1d80c3001cfc0f

def z619 : W := mkw 0x030b050016055002 0x006160a002c0aa00 0xdf0f07001e07f807 0x7be1e0e003c0ff00

def z620 : W := mkw 0x05b007c002207503 0x00b600f800440ea0 0xcff007e000007f82 0xf9fe00fc00000ff0

def z621 : W := mkw 0x37ffefdc9ddf8004 0x06fffdfb93bbf000 0xd7fffe181fff8005 0xfaffffc303fff000

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z623 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x5f0c06181e07f87c 0x2be180c303c0ff0f

def z624 : W := mkw 0x0a0b001514050850 0x81416002a280a10a 0x0003000700000000 0x00006000e0000000

def z625 : W := mkw 0x07fea7c000000000 0x00ffd4f800000000 0xc7ffffe000000003 0xf8fffffc00000000

def z626 : W := mkw 0x149148001ddf8004 0x0292290003bbf000 0x97f000001fff8004 0xf2fe000003fff000

def z627 : W := mkw 0x0b4fc51db747da7a 0xc169f8a3b6e8fb4f 0xff0fc71ffe07f87f 0x7fe1f8e3ffc0ff0f

def z628 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x47fcfef8e0000000 0xa8ff9fdf1c000000

def z629 : W := mkw 0x00010801100c08c0 0x2000210022018118 0x0000000010181980 0x0000000002030330

def z630 : W := mkw 0x04b05ae269ba27a1 0x20960b5c4d3744f4 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x680006180000607a 0x0d0000c300000c0f

def z632 : W := mkw 0x05b047c02bf2f72b 0x40b608f8057e5ee5 0xdff007e01ffffffe 0xfbfe00fc03ffffff

def z633 : W := mkw 0x16dfa8001c9d0004 0x02dbf5000393a000 0x87fff8001e180001 0xf0ffff0003c30000

def z634 : W := mkw 0x0100050002005002 0x002000a000400a00 0xff0c07181e07f87f 0x7fe180e303c0ff0f

def z635 : W := mkw 0x00011823500c08c0 0x200023046a018118 0x881339e711181f86 0xd102673ce22303f0

def z636 : W := mkw 0x0a0b001514050850 0x81416002a280a10a 0xb70f001f1e07807d 0x76e1e003e3c0f00f

def z637 : W := mkw 0x059005400a905103 0x00b200a801520a20 0x8f1001e01f181f86 0xd1e2003c03e303f0

def z638 : W := mkw 0x05b007c000000000 0x00b600f800000000 0x47e0060000000000 0x28fc00c000000000

def z639 : W := mkw 0x1f9b2d151e9d5856 0x83f365a2a3d3ab0a 0xff1f3f1f1e1ff87f 0x7fe3e7e3e3c3ff0f

def z640 : W := mkw 0x25f4b7eacab07503 0x04be96fd59560ea0 0xdff0ffe0fff87f86 0xfbfe1ffc1fff0ff0

def z641 : W := mkw 0x27fffffff16eaee8 0x64fffffffe2dd5dd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z642 : W := mkw 0x0100050000000000 0x002000a000000000 0xc700070000000002 0x78e000e000000000

def z643 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2803f9e7e0061fe3 0x05007f3cfc00c3fc

def z644 : W := mkw 0x100148003dffa62c 0x4200290007bff4c5 0x180000001fffe67c 0x0300000003fffccf

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c000000078005 0x320180000000f000

def z646 : W := mkw 0x27fefffee10a02a0 0x24ffdfffdc214054 0xe7ffffffe1180783 0xfcfffffffc2300f0

def z647 : W := mkw 0x0044c008a1428228 0x4008980114285045 0xb0ecc018e1e7807d 0xb61d98031c3cf00f

def z648 : W := mkw 0x1a4fe815154f8854 0x8349fd02a2a9f10a 0x200ff81f00078079 0x0401ff03e000f00f

def z649 : W := mkw 0x0900153762005af2 0xa12002a6ec400b5e 0x680007ffe0007ffa 0x0d0000fffc000fff

def z650 : W := mkw 0x2ffff7fff767fe7a 0xc5fffefffeecffcf 0xffffffffffe7fe7f 0xfffffffffffcffcf

def z651 : W := mkw 0x1b4fed15174fd856 0x8369fda2a2e9fb0a 0xff0fff1f1e07f87f 0x7fe1ffe3e3c0ff0f

def z652 : W := mkw 0x17dfed401fdfd107 0x02fbfda803fbfa20 0x97fff9601fff9985 0xf2ffff2c03fff330

def z653 : W := mkw 0x0044c00001428000 0x0008980000285000 0x00e0c00001e00000 0x801c1800003c0000

def z654 : W := mkw 0x01015d23730e5ae2 0x20202ba46e61cb5c 0xff13ffe7ff1e7fe7 0xffe27ffcffe3cffc

def z655 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2013f8e7e11e07e1 0x84027f1cfc23c0fc

def z656 : W := mkw 0x232a17fec0000000 0x046542ffd8000000 0xe70f07ffe0000003 0x7ce1e0fffc000000

def z657 : W := mkw 0x0064828880000000 0x000c905110000000 0x40ec061800000000 0x281d80c300000000

def z658 : W := mkw 0x27ffb7ffd0040840 0x04fff6fffa008108 0xeffffffff0061867 0xfdfffffffe00c30c

def z659 : W := mkw 0x0801000116055852 0x8100200022c0ab0a 0x000000001e001800 0x0000000003c00300

def z660 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2803f807f11e1fe5 0x05007f00fe23c3fc

def z661 : W := mkw 0x169a20000c910004 0x02d3440001922000 0x070000000e000000 0x00e0000001c00000

def z662 : W := mkw 0x000000000a905103 0x0000000001520a20 0x000000001e181980 0x0000000003c30330

def z663 : W := mkw 0x00015823510e08c0 0x20002b046a21c118 0x8013f967111e1985 0xd0027f2ce223c330

def z664 : W := mkw 0x0044c008a1428228 0x4008980114285045 0xa80cc098e107867f 0x950198131c20f0cf

def z665 : W := mkw 0x05b007c00a905103 0x00b600f801520a20 0xc7f007e01e181982 0xf8fe00fc03c30330

def z666 : W := mkw 0x0a4fc01db5478a78 0xc149f803b6a8f14f 0x200fc01fe0078079 0x0401f803fc00f00f

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800008001000606 0x91000010002000c0

def z668 : W := mkw 0x0a0b001514050850 0x81416002a280a10a 0xf80f061f0007e07f 0x3f01e0c3e000fc0f

def z669 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x280001e7f11e1fe6 0x0500003cfe23c3fc

def z670 : W := mkw 0x37ffbffedc9d0004 0x06fff7ffdb93a000 0xe7fffffffe180003 0xfcffffffffc30000

def z671 : W := mkw 0x000040002162a628 0x40000800042c54c5 0xb800c080e1e7e67f 0x970018101c3cfccf

def z672 : W := mkw 0x17dfed001fdfd006 0x02fbfda003fbfa00 0xdfffff001ffff807 0xfbffffe003ffff00

def z673 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x970f01071e079805 0x72e1e020e3c0f300

def z674 : W := mkw 0x27fef7fee162a628 0x44ffdeffdc2c54c5 0xe7ffffffe1e00603 0xfcfffffffc3c00c0

def z675 : W := mkw 0x05f487c88ab07503 0x00be90f911560ea0 0xfffcc7f8fff87f87 0xffff98ff1fff0ff0

def z676 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x6f03071f1e00787a 0x4de060e3e3c00f0f

def z677 : W := mkw 0x1b0b4d151fdfd856 0x836169a2a3fbfb0a 0xff0f071f1ffff87f 0x7fe1e0e3e3ffff0f

def z678 : W := mkw 0x0801000116055852 0x8100200022c0ab0a 0xb80301071e07f87f 0x57006020e3c0ff0f

def z679 : W := mkw 0x0b0b45153767fe7a 0xc16168a2a6ecffcf 0xff0f071f1fe7fe7f 0x7fe1e0e3e3fcffcf

def z680 : W := mkw 0x0f9b05151e955852 0x81f360a2a3d2ab0a 0xffff071f1ffff87f 0xffffe0e3e3ffff0f

def z681 : W := mkw 0x0000000002207503 0x0000000000440ea0 0x0800000000007f80 0x0100000000000ff0

def z682 : W := mkw 0x00015822710e02a0 0x20002b044e21c054 0x8013f8e0f11e0785 0xd0027f1c1e23c0f0

def z683 : W := mkw 0x020b000014050000 0x004160000280a000 0x070300001e000000 0x40e0600003c00000

def z684 : W := mkw 0x0000400001428000 0x0000080000285000 0x1000000001e78004 0x02000000003cf000

def z685 : W := mkw 0x0000400001020000 0x0000080000204000 0x8000c00001060005 0x900018000020c000

def z686 : W := mkw 0x000158237bbe7fe3 0x20002b046f77cffc 0xb813f9e7fffe7fe7 0xd7027f3cffffcffc

def z687 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x50ecc698e1e1e618 0xaa1d98d31c3c3cc3

def z688 : W := mkw 0x020b000114050840 0x004160002280a108 0xbf0f01071e079867 0x77e1e020e3c0f30c

def z689 : W := mkw 0x012007c002207503 0x002400f800440ea0 0xc81007e011187f86 0xd90200fc02230ff0

def z690 : W := mkw 0x26feb2eac0000000 0x04dfd65d58000000 0x87fff8e0e0000001 0xf0ffff1c1c000000

def z691 : W := mkw 0x0065daabf16eaee8 0x600cbb557e2dd5dd 0xf8effe9fe1e7e67f 0xbf1dffd3fc3cfccf

def z692 : W := mkw 0x0045d823714e8ae0 0x2008bb046e29d15c 0xb8fff9e7f1ff9fe7 0xf71fff3cfe3ff3fc

def z693 : W := mkw 0x27ffb7fed4050000 0x04fff6ffda80a000 0xf7fffffffe078007 0xfeffffffffc0f000

def z694 : W := mkw 0x0964c79da362fe7a 0xc12c98f3b46c5fcf 0xf8ecc79fe1e7fe7f 0xbf1d98f3fc3cffcf

def z695 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x00fff80001ff8001 0x801fff00003ff000

def z696 : W := mkw 0x092007d502207d53 0x812400faa0440faa 0x680007ff00007ffa 0x0d0000ffe0000fff

def z697 : W := mkw 0x0044800000408000 0x0008900000081000 0x10ec000000e18000 0x221d8000001c3000

def z698 : W := mkw 0x0490000008900000 0x0092000001120000 0x00f0000001f80000 0x801e0000003f0000

def z699 : W := mkw 0x1000480009da8004 0x02000900013b5000 0x0000000001f80000 0x00000000003f0000

def z700 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x18e0c080e1e7e67c 0x831c18101c3cfccf

def z701 : W := mkw 0x0fbb07d51eb57d53 0x81f760faa3d6afaa 0xffef071f1ee7f87f 0x7ffde0e3e3dcff0f

def z702 : W := mkw 0x212007dc80000000 0x042400fb90000000 0x4000061800000000 0x080000c300000000

def z703 : W := mkw 0x0b0b1d37560d58d2 0xa16163a6eac1ab1a 0xff1f3f7f1e1ff9ff 0x7fe3e7efe3c3ff3f

def z704 : W := mkw 0x020b4800150f0000 0x0041690002a1e000 0x971ff8001f1f8005 0xf2e3ff0003e3f000

def z705 : W := mkw 0x16dfe8001ffff507 0x02dbfd0003fffea0 0x9ffff8001fffff85 0xf3ffff0003fffff0

def z706 : W := mkw 0x036ec79ca162a628 0x406dd8f3942c54c5 0xffefc79fe1e7e67f 0xfffdf8f3fc3cfccf

def z707 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xefffffffe0060067 0xfdfffffffc00c00c

def z708 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdff3ffe01ff87f87 0xfbfe7ffc03ff0ff0

def z709 : W := mkw 0x1edfe8011ddf8854 0x83dbfd0023bbf10a 0x97fff8001fff807d 0xf2ffff0003fff00f

def z710 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xefffffffe0001f83 0xfdfffffffc0003f0

def z711 : W := mkw 0x16dfe8013ddf8ae4 0x22dbfd0027bbf15c 0x97fff8001fff8065 0xf2ffff0003fff00c

def z712 : W := mkw 0x006492aac0000000 0x000c925558000000 0xe0effe9fe0000003 0xbc1dffd3fc000000

def z713 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xc7f3ffe7e0000002 0xf8fe7ffcfc000000

def z714 : W := mkw 0x10014801354f8ae4 0x2200290026a9f15c 0x0000000000078060 0x000000000000f00c

def z715 : W := mkw 0x16deb0236cd18ae4 0x22dbd6046d9a315c 0x3fec01e7eee19fe2 0x27fd803cfddc33fc

def z716 : W := mkw 0x16dfe8011ddf8844 0x02dbfd0023bbf108 0x9ffff8001fff9865 0xf3ffff0003fff30c

def z717 : W := mkw 0x279a75766162a628 0x44f34eaecc2c54c5 0x1f13396701e7e67c 0x43e2672ce03cfccf

def z718 : W := mkw 0x226eb2bec0000000 0x044dd657d8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z719 : W := mkw 0x0000102240000000 0x0000020448000000 0x2003f9e7e0000003 0x04007f3cfc000000

def z720 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x00000000011e07e0 0x000000000023c0fc

def z721 : W := mkw 0x27feb7fec2005002 0x04ffd6ffd8400a00 0xfffffffffe07f87f 0xffffffffffc0ff0f

def z722 : W := mkw 0x16dfe8089ddf8004 0x02dbfd0113bbf000 0xb7fff818ffff8005 0xf6ffff031ffff000

def z723 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdffc07e01fffff87 0xfbff80fc03fffff0

def z724 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x97f001e01ff81f84 0xf2fe003c03ff03f0

def z725 : W := mkw 0x27feb7fec2207503 0x04ffd6ffd8440ea0 0xeffffffff1187f87 0xfdfffffffe230ff0

def z726 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x78ec0698e1e7e67e 0x2f1d80d31c3cfccf

def z727 : W := mkw 0x2490306240000000 0x0492060c48000000 0xa013f9e7e0000003 0xd4027f3cfc000000

def z728 : W := mkw 0x0ebb02d51cb52d51 0x81d7605aa396a5aa 0x20ff00ff01ff87f9 0x841fe01fe03ff0ff

def z729 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x7f0f071f0e07f87b 0x2fe1e0e3e1c0ff0f

def z730 : W := mkw 0x27deb57ec0000000 0x04fbd6afd8000000 0x270ff81fe0000001 0x04e1ff03fc000000

def z731 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x9ffff8001fff9f85 0xf3ffff0003fff3f0

def z732 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xfffc07f81ff87f87 0xffff80ff03ff0ff0

def z733 : W := mkw 0x07feb7e240000000 0x00ffd6fc48000000 0xe7ffffe7e0000003 0xfcfffffcfc000000

def z734 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013f80011180005 0xd0027f0002230000

def z735 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2813f9e7e11e1fe3 0x85027f3cfc23c3fc

def z736 : W := mkw 0x27feb7fec8b02501 0x04ffd6ffd91604a0 0xffffffffe1f86787 0xfffffffffc3f0cf0

def z737 : W := mkw 0x00005822610a02a0 0x20000b044c214054 0xa813f9e7f1181f87 0xd5027f3cfe2303f0

def z738 : W := mkw 0x07deb53640000000 0x00fbd6a6c8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z739 : W := mkw 0x0db14fc13fbf7ff3 0xa1b629f827f7effe 0xdff007e01ffffffe 0xfbfe00fc03ffffff

def z740 : W := mkw 0x234eb53ec0000000 0x0469d6a7d8000000 0xe71fffffe0000003 0xfce3fffffc000000

def z741 : W := mkw 0x0000102240000000 0x0000020448000000 0xa813f9e7e0001f83 0xd5027f3cfc0003f0

def z742 : W := mkw 0x27deb57640000000 0x04fbd6aec8000000 0xa7fff9e7e0000003 0xf4ffff3cfc000000

def z743 : W := mkw 0x180148013ffffe7e 0xc300290027ffffcf 0x180000001ffffe7c 0x0300000003ffffcf

def z744 : W := mkw 0x36dfe81c9ddf8004 0x06dbfd0393bbf000 0x97fff8181fff8005 0xf2ffff0303fff000

def z745 : W := mkw 0x05b14fc1310e0ae0 0x20b629f82621c15c 0xcff007e0111e1fe6 0xf9fe00fc0223c3fc

def z746 : W := mkw 0x0001102350040840 0x000022046a008108 0xa813f9e7f11e1fe7 0xd5027f3cfe23c3fc

def z747 : W := mkw 0x080148013fbf7ff3 0xa100290027f7effe 0x180000001ffffffc 0x0300000003ffffff

def z748 : W := mkw 0x05b007c008900000 0x00b600f801120000 0xdff007e01ff81f86 0xfbfe00fc03ff03f0

def z749 : W := mkw 0x27fea7dc8af0f50b 0x44ffd4fb915e1ea1 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z750 : W := mkw 0x16dfa8001c9d0004 0x02dbf5000393a000 0x97fff8001ff80005 0xf2ffff0003ff0000

def z751 : W := mkw 0x234eb53ec0000000 0x0469d6a7d8000000 0x600fff1fe0000003 0x0c01ffe3fc000000

def z752 : W := mkw 0x27feb7fec8900101 0x04ffd6ffd9120020 0xe7ffffffe0180183 0xfcfffffffc030030

def z753 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x47ffffffe0000000 0xe8fffffffc000000

def z754 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17fcf8001fff8004 0xa2ff9f0003fff000

def z755 : W := mkw 0x27feb7feca905103 0x04ffd6ffd9520a20 0xf7fffffffff81987 0xfeffffffffff0330

def z756 : W := mkw 0x05d4c548abd2d32b 0x40ba98a9157a5a65 0x271cc178fe1f99f9 0x44e3982f1fc3f33f

def z757 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xd7fffe181fffe01d 0xfaffffc303fffc03

def z758 : W := mkw 0x136fefc0176ff507 0x026dfdf802edfea0 0x480fffe00007ff83 0x0901fffc0000fff0

def z759 : W := mkw 0x16dfe8013ddf8ae4 0x22dbfd0027bbf15c 0xbffff9071fff9fe7 0xf7ffff20e3fff3fc

def z760 : W := mkw 0x212017fec0000000 0x042402ffd8000000 0x6003ffffe0000003 0x0c007ffffc000000

def z761 : W := mkw 0x27feb7feca905002 0x04ffd6ffd9520a00 0xfffffffffff87807 0xffffffffffff0f00

def z762 : W := mkw 0x26deb07ec0000000 0x04dbd60fd8000000 0x201ff87fe0000001 0x0403ff0ffc000000

def z763 : W := mkw 0x226eb2bec0000000 0x044dd657d8000000 0x60effe1fe0000001 0x2c1dffc3fc000000

def z764 : W := mkw 0x0b0a153646015012 0x816142a6c8c02a02 0xf71fffffee01e01b 0xfee3fffffdc03c03

def z765 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xeffffffffe187f83 0xfdffffffffc30ff0

def z766 : W := mkw 0x24f4f2eae9f2a729 0x449e9e5d5d3e54e5 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z767 : W := mkw 0x0120078002207402 0x002400f000440e80 0xdff007e01ff87f86 0xfbfe00fc03ff0ff0

def z768 : W := mkw 0x0064c28881428000 0x000c985110285000 0xf8ecc698e1e7e07f 0xbf1d98d31c3cfc0f

def z769 : W := mkw 0x006492aac0202400 0x000c925558040480 0xf8fffffff1f87f87 0xff1ffffffe3f0ff0

def z770 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0x77effe1feee06001 0x2efdffc3fddc0c00

def z771 : W := mkw 0x05b007c88ab0750b 0x40b600f911560ea1 0xdff007f81ff87f9e 0xfbfe00ff03ff0ff3

def z772 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97fff8e01fff8785 0xf2ffff1c03fff0f0

def z773 : W := mkw 0x05b15fe37bbe7fe3 0x20b62bfc6f77cffc 0x77e3fe07eee66061 0x2efc7fc0fddccc0c

def z774 : W := mkw 0x31215ffedddf8004 0x06242bffdbbbf000 0x700007ffffff8006 0x0e0000fffffff000

def z775 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x97fff8001ff98005 0xf2ffff0003ff3000

def z776 : W := mkw 0x06dfe00015478000 0x00dbfc0002a8f000 0x97fff8001fe78005 0xf2ffff0003fcf000

def z777 : W := mkw 0x16dee80009da8004 0x02dbdd00013b5000 0x97fff8001ff80005 0xf2ffff0003ff0000

def z778 : W := mkw 0x012017ebe2207feb 0x602402fd7c440ffd 0x680007ffe0007ffa 0x0d0000fffc000fff

def z779 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8efc79fe1e7e67f 0xff1df8f3fc3cfccf

def z780 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x78ecc618e1e7e67d 0x2f1d98c31c3cfccf

def z781 : W := mkw 0x212017fee220772b 0x442402ffdc440ee5 0x680007ffe0007ffa 0x0d0000fffc000fff

def z782 : W := mkw 0x234eb53ec0000000 0x0469d6a7d8000000 0x670ffe1fe0000001 0x2ce1ffc3fc000000

def z783 : W := mkw 0x25f4b7fec0000000 0x04be96ffd8000000 0xe0f3ffffe0000003 0xdc1e7ffffc000000

def z784 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xf813ffe7f11e7fe7 0xff027ffcfe23cffc

def z785 : W := mkw 0x224eb03ecab07503 0x0449d607d9560ea0 0x380ff81ffff87f85 0x0701ff03ffff0ff0

def z786 : W := mkw 0x05914d413b9e5be3 0x20b229a82773cb7c 0x0f1001601f1e1fe4 0x41e2002c03e3c3fc

def z787 : W := mkw 0x0000102360000ae0 0x200002046c00015c 0xa813f9e7f1181fe7 0xd5027f3cfe2303fc

def z788 : W := mkw 0x236eb7bec0000000 0x046dd6f7d8000000 0xe7efff9fe0000003 0xfcfdfff3fc000000

def z789 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x7f0f061f1e07f87d 0x2fe1e0c3e3c0ff0f

def z790 : W := mkw 0x16dfe8003ddf8224 0x02dbfd0007bbf044 0x9ffff8001fff8665 0xf3ffff0003fff0cc

def z791 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x8813f9e7f1181f86 0xd1027f3cfe2303f0

def z792 : W := mkw 0x00011823700c0ae0 0x200023046e01815c 0xa813f9e7f0181fe3 0xd5027f3cfe0303fc

def z793 : W := mkw 0x08014801376ffefa 0xe100290026edffdf 0x180000001ffffffc 0x0300000003ffffff

def z794 : W := mkw 0x169b68001d9f0004 0x02d36d0003b3e000 0x97f3f8001ffe0005 0xf2fe7f0003ffc000

def z795 : W := mkw 0x07fea79c80000000 0x00ffd4f390000000 0xe7ffff9fe0000003 0xfcfffff3fc000000

def z796 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8ecc7f8e1e7ffff 0xbf1d98ff1c3cffff

def z797 : W := mkw 0x2ffeb7feceb17513 0x85ffd6ffd9d62ea2 0xfffffffffff9ff9f 0xffffffffffff3ff3

def z798 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x87fff8001ff80001 0xf0ffff0003ff0000

def z799 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17f3f8001fff8004 0xc2fe7f0003fff000

def z800 : W := mkw 0x16dfe808bddf822c 0x42dbfd0117bbf045 0x97fff800ffff8005 0xf2ffff001ffff000

def z801 : W := mkw 0x26feb2fec0000000 0x04dfd65fd8000000 0x20eff81fe0000001 0x041dff03fc000000

def z802 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x88000080111e1fe6 0x910000100223c3fc

def z803 : W := mkw 0x16dfe8011ddf8844 0x02dbfd0023bbf108 0xffffff1f1ffff87f 0xffffffe3e3ffff0f

def z804 : W := mkw 0x16dee0000dd38004 0x02dbdc0001ba7000 0x97fff8000fe78005 0xf2ffff0001fcf000

def z805 : W := mkw 0x212017ffe2207fe3 0x242402fffc440ffc 0x680007ffe0007fe2 0x0d0000fffc000ffc

def z806 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x770f071f1e07f879 0x6ee1e0e3e3c0ff0f

def z807 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff0f071f1f1fffff 0x7fe1e0e3e3e3ffff

def z808 : W := mkw 0x0100152242005002 0x002002a448400a00 0xff13ffe7fe007807 0xffe27ffcffc00f00

def z809 : W := mkw 0x012017e240000000 0x002402fc48000000 0xe013ffe7e0000003 0xdc027ffcfc000000

def z810 : W := mkw 0x020b000114050840 0x004160002280a108 0xff0f071f1e07f87f 0x7fe1e0e3e3c0ff0f

def z811 : W := mkw 0x0064828880202400 0x000c905110040480 0xf8ecc698e1e7e67f 0xbf1d98d31c3cfccf

def z812 : W := mkw 0x00659aabd06cacc8 0x600cb3557a0d9599 0x50ff3f7f10f9f998 0x6a1fe7efe21f3f33

def z813 : W := mkw 0x169b28001c9d0004 0x02d365000393a000 0x17f338001ef80000 0x62fe670003df0000

def z814 : W := mkw 0x0000102240000000 0x0000020448000000 0x0013396710181980 0x4002672ce2030330

def z815 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8ecc618e0e7e07f 0x3f1d98c31c1cfc0f

def z816 : W := mkw 0x16dfe8011ddf8844 0x02dbfd0023bbf108 0xbffff9e71fff9fe7 0xf7ffff3ce3fff3fc

def z817 : W := mkw 0x16dee8000ddb8004 0x02dbdd0001bb7000 0x97fff8000ff98001 0xf2ffff0001ff3000

def z818 : W := mkw 0x2cf5b2ebd6055852 0x859eb65d7ac0ab0a 0x18f0f8e0fe07f87c 0x831e1f1c1fc0ff0f

def z819 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x081000e0111e1fe4 0x8102001c0223c3fc

def z820 : W := mkw 0x00014801399e0ae0 0x200029002733c15c 0x180000001ffe1fe4 0x0300000003ffc3fc

def z821 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xf7fffffffef87983 0xfeffffffffdf0f30

def z822 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7fffffff1180007 0xfcfffffffe230000

def z823 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xf7ffffffeff86783 0xfefffffffdff0cf0

def z824 : W := mkw 0x234eb53ec2005002 0x0469d6a7d8400a00 0xff0fff1ffe007807 0x7fe1ffe3ffc00f00

def z825 : W := mkw 0x16dee8000ddb8004 0x02dbdd0001bb7000 0x97fcf8000fff8005 0xb2ff9f0001fff000

def z826 : W := mkw 0x27feb7fec4010000 0x04ffd6ffd8802000 0xf7ffffffee018003 0xfefffffffdc03000

def z827 : W := mkw 0x0490102248900000 0x0092020449120000 0xb7f3f9e7fff80007 0xf6fe7f3cffff0000

def z828 : W := mkw 0x27ffefddb10e0ae0 0x24fffdfbb621c15c 0x4fec0618111e1fe4 0x29fd80c30223c3fc

def z829 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17fff8001eff8001 0x62ffff0003dff000

def z830 : W := mkw 0x16dfe8003ddf8224 0x02dbfd0007bbf044 0xbffff9e0ffff9fe7 0xf7ffff3c1ffff3fc

def z831 : W := mkw 0x34f4faeae9faa62c 0x469e9f5d5d3f54c5 0x00f0f8e0e1f80600 0x801e1f1c1c3f00c0

def z832 : W := mkw 0x236eb7fec0000000 0x046dd6ffd8000000 0xe70fffffe0000003 0x7ce1fffffc000000

def z833 : W := mkw 0x24f4b2eac0000000 0x049e965d58000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z834 : W := mkw 0x27feb7fec8b02501 0x04ffd6ffd91604a0 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z835 : W := mkw 0x25b017fecab07503 0x04b602ffd9560ea0 0xfff3fffffff87f87 0xfffe7fffffff0ff0

def z836 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x1ff001e01ff87f84 0xc3fe003c03ff0ff0

def z837 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0x200ff81fe0078079 0x0401ff03fc00f00f

def z838 : W := mkw 0x2ffea7dc8eb17513 0x85ffd4fb91d62ea2 0x57ec06180ee1e018 0x2afd80c301dc3c03

def z839 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xefffffffe1f87f83 0xfdfffffffc3f0ff0

def z840 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x5fe007e01ff87f86 0x2bfc00fc03ff0ff0

def z841 : W := mkw 0x006492aac0000000 0x000c925558000000 0xa0f3f9e7e0000003 0xd41e7f3cfc000000

def z842 : W := mkw 0x27feb7fec8b02501 0x04ffd6ffd91604a0 0xf7fffffffff80787 0xfeffffffffff00f0

def z843 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8ecc698f1ffffff 0xbf1d98d31e3fffff

def z844 : W := mkw 0x16dfe808bddf822c 0x42dbfd0117bbf045 0xbffff898ffff867f 0xf7ffff131ffff0cf

def z845 : W := mkw 0x1dd4ed150bdad856 0x83ba9da2a17b5b0a 0x68f0ff1f01f8787a 0x8d1e1fe3e03f0f0f

def z846 : W := mkw 0x27feb7fec8b02400 0x04ffd6ffd9160480 0xfffffffffff86607 0xffffffffffff0cc0

def z847 : W := mkw 0x279a357640000000 0x04f346aec8000000 0x2713f967e0000001 0x44e27f2cfc000000

def z848 : W := mkw 0x324eb03ec4418004 0x0649d607d8883000 0x200ff81fe0018001 0x0401ff03fc003000

def z849 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa01ff81fe0000001 0xd403ff03fc000000

def z850 : W := mkw 0x27deb57ec0000000 0x04fbd6afd8000000 0xa7fff97fe0000001 0xf4ffff2ffc000000

def z851 : W := mkw 0x27deb57ec0000000 0x04fbd6afd8000000 0x0713f967e0000000 0x40e27f2cfc000000

def z852 : W := mkw 0x3f9b3d775e9d5856 0x87f367aeebd3ab0a 0x071339671e181800 0x40e2672ce3c30300

def z853 : W := mkw 0x05b007d40ab07503 0x00b600fa81560ea0 0xfff007ff1ff87f86 0xfffe00ffe3ff0ff0

def z854 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xfff307e71ff87f87 0xfffe60fce3ff0ff0

def z855 : W := mkw 0x16dfe8013ddf8ae4 0x22dbfd0027bbf15c 0x1fec00001fff9fe4 0x23fd800003fff3fc

def z856 : W := mkw 0x27feb7fec8b02501 0x04ffd6ffd91604a0 0xeffffffff1f81f87 0xfdfffffffe3f03f0

def z857 : W := mkw 0x04b14ac139be2fe1 0x209629582737c5fc 0x08f000e011fe1fe4 0x811e001c023fc3fc

def z858 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x50ec061800e7e078 0x2a1d80c3001cfc0f

def z859 : W := mkw 0x26feb2fec0000000 0x04dfd65fd8000000 0x00f3f8e7e0000000 0x801e7f1cfc000000

def z860 : W := mkw 0x27feb7fec8900000 0x04ffd6ffd9120000 0xe7fffffffe180003 0xfcffffffffc30000

def z861 : W := mkw 0x16bb2a88bcbd262c 0x42d765511797a4c5 0x6f133e98fe18667a 0x4de267d31fc30ccf

def z862 : W := mkw 0x00005823610a0ae0 0x20000b046c21415c 0xa813f9e7e1181fe3 0xd5027f3cfc2303fc

def z863 : W := mkw 0x000148013bfeffeb 0x60002900277fdffd 0x180000001ffffffc 0x0300000003ffffff

def z864 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8fcc7f8e1e7e67f 0xff1f98ff1c3cfccf

def z865 : W := mkw 0x0000102240000000 0x0000020448000000 0xa003f887e0000003 0x94007f10fc000000

def z866 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff0f07ff1e07ffff 0x7fe1e0ffe3c0ffff

def z867 : W := mkw 0x0000502261020220 0x00000a044c204044 0xa813f9e7f11e1fe7 0xd5027f3cfe23c3fc

def z868 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x00000000101e19e0 0x000000000203c33c

def z869 : W := mkw 0x04f4daeae9faa7a9 0x609e9b5d5d3f54f5 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z870 : W := mkw 0x024eb02240000000 0x0049d60448000000 0xa01ff9e7e0000003 0xd403ff3cfc000000

def z871 : W := mkw 0x04b002c00ab07503 0x0096005801560ea0 0x9ff000e01ff87f84 0xf3fe001c03ff0ff0

def z872 : W := mkw 0x06feb2aac0000000 0x00dfd65558000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z873 : W := mkw 0x012017e242207503 0x002402fc48440ea0 0x680007e7e0007f82 0x0d0000fcfc000ff0

def z874 : W := mkw 0x069a302240000000 0x00d3460448000000 0xa713f9e7e0000003 0xd4e27f3cfc000000

def z875 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf0ecc618e1e7e07d 0xbe1d98c31c3cfc0f

def z876 : W := mkw 0x100148013ddf8ae4 0x2200290027bbf15c 0x100000001fff8064 0x0200000003fff00c

def z877 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xb7fff9071fff8007 0xf6ffff20e3fff000

def z878 : W := mkw 0x25f4b7eacab07503 0x04be96fd59560ea0 0xfff3ffe7fff87f87 0xfffe7ffcffff0ff0

def z879 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0x201ff8ffe0000001 0x8403ff1ffc000000

def z880 : W := mkw 0x212017fec2207503 0x042402ffd8440ea0 0xe813fffff1187f87 0xdd027ffffe230ff0

def z881 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2813f9e7f1181fe2 0xc5027f3cfe2303fc

def z882 : W := mkw 0x0000102240000000 0x0000020448000000 0x2013f8e7e0000001 0x84027f1cfc000000

def z883 : W := mkw 0x00014801314e8ae8 0x600029002629d15d 0x08000000111f9ffc 0x010000000223f3ff

def z884 : W := mkw 0x27feb7fec0202400 0x04ffd6ffd8040480 0xffffffffe1e7e67f 0xfffffffffc3cfccf

def z885 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x5f0f071f1e07f87c 0x6be1e0e3e3c0ff0f

def z886 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff0fc79ffe07f87f 0xffe1f8f3ffc0ff0f

def z887 : W := mkw 0x05b007c88ab07503 0x00b600f911560ea0 0xfff007f8fff87f86 0xfffe00ff1fff0ff0

def z888 : W := mkw 0x10015823754f8ae4 0x22002b046ea9f15c 0xa813f9e7f11f9fe7 0xd5027f3cfe23f3fc

def z889 : W := mkw 0x232a17fec0000000 0x046542ffd8000000 0xe71fffffe0000003 0xfce3fffffc000000

def z890 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x671fffffe0000003 0x4ce3fffffc000000

def z891 : W := mkw 0x27feb7fecaf0f50b 0x44ffd6ffd95e1ea1 0xf7ffffffeee1e01b 0xfefffffffddc3c03

def z892 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x17fcf8000ee18000 0xa2ff9f0001dc3000

def z893 : W := mkw 0x0020428021222620 0x00040850042444c4 0xf8ecc698e1e7e67f 0xbf1d98d31c3cfccf

def z894 : W := mkw 0x36deb03eccd18004 0x06dbd607d99a3000 0x37eff81feee18001 0x26fdff03fddc3000

def z895 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x0800000010061864 0x010000000200c30c

def z896 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x68ecc698e1e7e67b 0x8d1d98d31c3cfccf

def z897 : W := mkw 0x0000102240000000 0x0000020448000000 0x0010f8e0e1180780 0x80021f1c1c2300f0

def z898 : W := mkw 0x2100157640000000 0x042002aec8000000 0xa013f9e7e0000003 0xd4027f3cfc000000

def z899 : W := mkw 0x16dfe8013ddf8ae4 0x22dbfd0027bbf15c 0x9ffff9e01fff9fe7 0xf3ffff3c03fff3fc

def z900 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7ffffffe007807b 0xfcfffffffc00f00f

def z901 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0xa8000000111e1fe7 0x150000000223c3fc

def z902 : W := mkw 0x1064ea88a16aa62c 0x420c9d51142d54c5 0xf8ecfe98e1e7e67f 0xbf1d9fd31c3cfccf

def z903 : W := mkw 0x049000000ab07503 0x0092000001560ea0 0x9ff001e01ff87f86 0xf3fe003c03ff0ff0

def z904 : W := mkw 0x0000102240000000 0x0000020448000000 0x0013f9e7e0000000 0xc0027f3cfc000000

def z905 : W := mkw 0x030a153640000000 0x006142a6c8000000 0xa713f9e7e0000003 0xd4e27f3cfc000000

def z906 : W := mkw 0x04d4a00008900000 0x009a940001120000 0x97f0f8001ff80004 0xf2fe1f0003ff0000

def z907 : W := mkw 0x09014d01370f5af2 0xa12029a026e1eb5e 0xdf1007e01f1ffffe 0xfbe200fc03e3ffff

def z908 : W := mkw 0x226eb2bec0202400 0x044dd657d8040480 0xf8effe9fe1e06607 0xbf1dffd3fc3c0cc0

def z909 : W := mkw 0x212017fec2207503 0x042402ffd8440ea0 0x600007ffe0006002 0x0c0000fffc000c00

def z910 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff1fff1f1e07f87f 0xffe3ffe3e3c0ff0f

def z911 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xe7fffffffff81f83 0xfcffffffffff03f0

def z912 : W := mkw 0x37feb7fec4418004 0x06ffd6ffd8883000 0xe7ffffffe0018003 0xfcfffffffc003000

def z913 : W := mkw 0x08014801370f5af2 0xa100290026e1eb5e 0x080000001f1e1fe4 0x0100000003e3c3fc

def z914 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff0f079f1f07fe7f 0xffe1e0f3e3e0ffcf

def z915 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x7f0c071f1e07f87e 0x2fe180e3e3c0ff0f

def z916 : W := mkw 0x234eb53ec0000000 0x0469d6a7d8000000 0x270ff91fe0000001 0x44e1ff23fc000000

def z917 : W := mkw 0x06dfe800199e0000 0x00dbfd000333c000 0x97fff8001ffe0005 0xf2ffff0003ffc000

def z918 : W := mkw 0x14f4faaae9faa6ac 0x629e9f555d3f54d5 0x00f0f8e0e1f80780 0x801e1f1c1c3f00f0

def z919 : W := mkw 0x16dfe8011ddf8844 0x02dbfd0023bbf108 0x97fff9071fff9805 0xf2ffff20e3fff300

def z920 : W := mkw 0x01214fc1332e7fe3 0x202429f82665cffc 0x480007e0111e7fe6 0x090000fc0223cffc

def z921 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xffffffffe0006007 0xfffffffffc000c00

def z922 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x17ff38000ee18000 0x62ffe70001dc3000

def z923 : W := mkw 0x226eb2bec0000000 0x044dd657d8000000 0x20eff89fe0000001 0x841dff13fc000000

def z924 : W := mkw 0x04d5c80019de8000 0x009ab900033bd000 0x97fff8001fff8005 0xf2ffff0003fff000

def z925 : W := mkw 0x0490102240000000 0x0092020448000000 0xa7f3f9e7e0000003 0xf4fe7f3cfc000000

def z926 : W := mkw 0x27feb7fec060a408 0x44ffd6ffd80c1481 0xffffffffe0e7e07f 0xfffffffffc1cfc0f

def z927 : W := mkw 0x030a153640000000 0x006142a6c8000000 0xe70fff1fe0000003 0x7ce1ffe3fc000000

def z928 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97fff9e01fff8007 0xf2ffff3c03fff000

def z929 : W := mkw 0x0b0a5d36670b52b2 0xa1614ba6cce16a56 0x571cfef8ef19e798 0xaae39fdf1de33cf3

def z930 : W := mkw 0x0000102240000000 0x0000020448000000 0xa813f9e7e1000607 0xd5027f3cfc2000c0

def z931 : W := mkw 0x000148013b9e5be3 0x200029002773cb7c 0x080000001f1e1fe4 0x0100000003e3c3fc

def z932 : W := mkw 0x0b6fc79db767fe7a 0xc16df8f3b6ecffcf 0x07e3c187ffe01e00 0xc0fc7830fffc03c0

def z933 : W := mkw 0x27feb7fec8900000 0x04ffd6ffd9120000 0xe7ffffffe1f80003 0xfcfffffffc3f0000

def z934 : W := mkw 0x1edfe81dbddf8a7c 0xc3dbfd03b7bbf14f 0xb7fff81fffff807d 0xf6ffff03fffff00f

def z935 : W := mkw 0x0044c008a1428228 0x4008980114285045 0xf8ecc618e1e7e07f 0xbf1d98c31c3cfc0f

def z936 : W := mkw 0x16dea0000cd18004 0x02dbd400019a3000 0x17eff8000ee18001 0x22fdff0001dc3000

def z937 : W := mkw 0x06dea00008900000 0x00dbd40001120000 0x97fff8000ee00001 0xf2ffff0001dc0000

def z938 : W := mkw 0x08014801330e5af2 0xa10029002661cb5e 0x08000000111e7ffc 0x010000000223cfff

def z939 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0x201ff97fe0000001 0x4403ff2ffc000000

def z940 : W := mkw 0x16dea8000cd98004 0x02dbd500019b3000 0x17fc38000ef98000 0x22ff870001df3000

def z941 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7fffe1fe0000001 0xfcffffc3fc000000

def z942 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xb7fff8181fff807d 0xf6ffff0303fff00f

def z943 : W := mkw 0x00014801316eaee8 0x60002900262dd5dd 0x0800000011fe1fe4 0x01000000023fc3fc

def z944 : W := mkw 0x16dee8000ddb8004 0x02dbdd0001bb7000 0x17ecf8000ee18000 0x22fd9f0001dc3000

def z945 : W := mkw 0x0490102368900ae0 0x209202046d12015c 0xbff001e7fff81fe6 0xf7fe003cffff03fc

def z946 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x67ffff7fe0000001 0x6cffffeffc000000

def z947 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x57f007e01ff87f80 0xeafe00fc03ff0ff0

def z948 : W := mkw 0x012017e342207dc3 0x202402fc68440fb8 0x480007e700007f82 0x090000fce0000ff0

def z949 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z950 : W := mkw 0x00015823714e8ae8 0x60002b046e29d15d 0xa813f9e7f11f9fff 0xd5027f3cfe23f3ff

def z951 : W := mkw 0x036e97bec0000000 0x006dd2f7d8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z952 : W := mkw 0x2ffeb7fec6015012 0x85ffd6ffd8c02a02 0xe7ffffffee000003 0xfcfffffffdc00000

def z953 : W := mkw 0x05b017e24ab07503 0x00b602fc49560ea0 0xf7f3ffe7eee06003 0xfefe7ffcfddc0c00

def z954 : W := mkw 0x002012aac0000000 0x0004025558000000 0xe013ffffe0000003 0xdc027ffffc000000

def z955 : W := mkw 0x25b007dc8ab07503 0x04b600fb91560ea0 0xdff007f81ff87f86 0xfbfe00ff03ff0ff0

def z956 : W := mkw 0x16dfe8141ddf8004 0x02dbfd0283bbf000 0xb7fff81f1fff8005 0xf6ffff03e3fff000

def z957 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17eff8001fff8005 0x22fdff0003fff000

def z958 : W := mkw 0x08015823750f0af0 0xa1002b046ea1e15e 0xa813f9e7f11f9fff 0xd5027f3cfe23f3ff

def z959 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x78ecc698e0e7e67b 0x2f1d98d31c1cfccf

def z960 : W := mkw 0x0000102240000000 0x0000020448000000 0xf81fffffe007e07f 0xff03fffffc00fc0f

def z961 : W := mkw 0x226eb2fec0000000 0x044dd65fd8000000 0x200ff8ffe0000001 0x0401ff1ffc000000

def z962 : W := mkw 0x16dfe8013ddf8ae4 0x22dbfd0027bbf15c 0xbffff880ffff9fe7 0xf7ffff101ffff3fc

def z963 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xfff0c7e0fff87f87 0xfffe18fc1fff0ff0

def z964 : W := mkw 0x226eb2bec060a408 0x444dd657d80c1481 0x70effe1fe0e1e019 0x2e1dffc3fc1c3c03

def z965 : W := mkw 0x0001480139be2fe1 0x200029002737c5fc 0x0800000011fe1fe4 0x01000000023fc3fc

def z966 : W := mkw 0x2ffeb7fec6015012 0x85ffd6ffd8c02a02 0xfffffffffe01f81f 0xffffffffffc03f03

def z967 : W := mkw 0x08014801350f0af0 0xa100290026a1e15e 0x0000000000078078 0x000000000000f00f

def z968 : W := mkw 0x0000102240000000 0x0000020448000000 0xa003f907e0000003 0x54007f20fc000000

def z969 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x67fffeffe0000001 0xacffffdffc000000

def z970 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x5ff007601ff87f84 0x6bfe00ec03ff0ff0

def z971 : W := mkw 0x00200288a0202628 0x40040051140404c5 0xf8ec0698e1e7e67f 0xbf1d80d31c3cfccf

def z972 : W := mkw 0x2f9b35775e955953 0x85f366aeebd2ab2a 0x071339671e181980 0x40e2672ce3c30330

def z973 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17fff8000fff8001 0xa2ffff0001fff000

def z974 : W := mkw 0x27deb57eca905103 0x04fbd6afd9520a20 0x271ff97ffe181981 0x44e3ff2fffc30330

def z975 : W := mkw 0x236eb7fec0000000 0x046dd6ffd8000000 0xe0efffffe0000003 0xbc1dfffffc000000

def z976 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x0000000011181f80 0x00000000022303f0

def z977 : W := mkw 0x0000102240000000 0x0000020448000000 0x2013f967e0000001 0x44027f2cfc000000

def z978 : W := mkw 0x16dfa8001cdd8004 0x02dbf500039bb000 0x97ff38001eff8005 0x72ffe70003dff000

def z979 : W := mkw 0x2a4eb03ec4010010 0x8549d607d8802002 0x200ff81fe0018019 0x0401ff03fc003003

def z980 : W := mkw 0x1b0b2d15160d5856 0x836165a2a2c1ab0a 0xff0f3f1f1e07f87f 0x7fe1e7e3e3c0ff0f

def z981 : W := mkw 0x00014801350f0ae0 0x2000290026a1e15c 0x180000001f1f9fe4 0x0300000003e3f3fc

def z982 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xb7fff880ffff8007 0xf6ffff101ffff000

def z983 : W := mkw 0x0000102240000000 0x0000020448000000 0xa013f9e7e1180783 0xd4027f3cfc2300f0

def z984 : W := mkw 0x27feb7fecaf0f50b 0x44ffd6ffd95e1ea1 0xfffffffffff9ff9f 0xffffffffffff3ff3

def z985 : W := mkw 0x16deb0224cd18004 0x02dbd604499a3000 0xb7fff9e7eee18003 0xf6ffff3cfddc3000

def z986 : W := mkw 0x37feb7fecc910004 0x06ffd6ffd9922000 0xe7ffffffee000003 0xfcfffffffdc00000

def z987 : W := mkw 0x216497fec0000000 0x042c92ffd8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z988 : W := mkw 0x16dee8000ddb8004 0x02dbdd0001bb7000 0x07f0f8000ff80000 0x80fe1f0001ff0000

def z989 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x9ffff9001fff9807 0xf3ffff2003fff300

def z990 : W := mkw 0x27feb7fec2005002 0x04ffd6ffd8400a00 0xf7ffffffee006003 0xfefffffffdc00c00

def z991 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xe00ffe1fe0000003 0x3c01ffc3fc000000

def z992 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x88000100111e1fe6 0x510000200223c3fc

def z993 : W := mkw 0x00014801312e2ee8 0x600029002625c5dd 0x08000000111e7ffc 0x010000000223cfff

def z994 : W := mkw 0x020a103640000000 0x00414206c8000000 0x200ff81fe0000001 0x0401ff03fc000000

def z995 : W := mkw 0x0490000008900000 0x0092000001120000 0x97f3f8001ff80005 0xf2fe7f0003ff0000

def z996 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97fff8000ee78001 0xf2ffff0001dcf000

def z997 : W := mkw 0x27feb7fec2005103 0x04ffd6ffd8400a20 0xe7ffffffe0001983 0xfcfffffffc000330

def z998 : W := mkw 0x27feb7fec2207503 0x04ffd6ffd8440ea0 0xfffffffffe007f87 0xffffffffffc00ff0

def z999 : W := mkw 0x27feb7fec2005002 0x04ffd6ffd8400a00 0xefffffffe0007803 0xfdfffffffc000f00

def z1000 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xfff007e01ffe7fe7 0xfffe00fc03ffcffc

def z1001 : W := mkw 0x01214fc0132e7503 0x002429f80265cea0 0xc813ffe0111e7f87 0xd9027ffc0223cff0

def z1002 : W := mkw 0x0044902ac0000000 0x0008920558000000 0x200ff81fe0000001 0x0401ff03fc000000

def z1003 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x70ecc698e1e7e679 0xae1d98d31c3cfccf

def z1004 : W := mkw 0x16dfe8003ddf822c 0x42dbfd0007bbf045 0x97fff8001fff807d 0xf2ffff0003fff00f

def z1005 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xbf13f9e7ff1e1fe7 0xf7e27f3cffe3c3fc

def z1006 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800c080e1000607 0x950018101c2000c0

def z1007 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x08100160111e1fe4 0x4102002c0223c3fc

def z1008 : W := mkw 0x00648288a060a628 0x400c9051140c14c5 0xf8ec0698e0e7e67f 0x3f1d80d31c1cfccf

def z1009 : W := mkw 0x26deb03ec0000000 0x04dbd607d8000000 0xa7fff9ffe0000003 0xf4ffff3ffc000000

def z1010 : W := mkw 0x212017eac2207503 0x042402fd58440ea0 0x480007e0e0007f82 0x090000fc1c000ff0

def z1011 : W := mkw 0x0000102240000000 0x0000020448000000 0xe01fffffe0000003 0xfc03fffffc000000

def z1012 : W := mkw 0x030a051402005002 0x006140a280400a00 0xff0f071f1e07f87f 0x7fe1e0e3e3c0ff0f

def z1013 : W := mkw 0x279a357640000000 0x04f346aec8000000 0xe71fffffe0000003 0xfce3fffffc000000

def z1014 : W := mkw 0x169b68001ddf8004 0x02d36d0003bbf000 0x97f338001fff8004 0xf2fe670003fff000

def z1015 : W := mkw 0x0064ca88a16aa628 0x400c9951142d54c5 0xf8fcfe98e1ffe67f 0xbf1f9fd31c3ffccf

def z1016 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x8013f9e7f11e1f85 0xd0027f3cfe23c3f0

def z1017 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xefffffffe1000607 0xfdfffffffc2000c0

def z1018 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xeffffffff0001807 0xfdfffffffe000300

def z1019 : W := mkw 0x16dfa0001cd58004 0x02dbf400039ab000 0x97fff8001ee78005 0xf2ffff0003dcf000

def z1020 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xffffffffeee07f83 0xfffffffffddc0ff0

def z1021 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xf7fffe181fff8007 0xfeffffc303fff000

def z1022 : W := mkw 0x26feb2bec0000000 0x04dfd657d8000000 0xe7fffe9fe0000003 0xfcffffd3fc000000

def z1023 : W := mkw 0x00014801314e8ae8 0x600029002629d15d 0x0000000000078078 0x000000000000f00f

def z1024 : W := mkw 0x180148013fdfdaf6 0xa300290027fbfb5e 0x180000001ffffffc 0x0300000003ffffff

def z1025 : W := mkw 0x059005400a905103 0x00b200a801520a20 0x9ff001e01ff81f86 0xf3fe003c03ff03f0

def z1026 : W := mkw 0x0064d2aae162a628 0x400c9a555c2c54c5 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z1027 : W := mkw 0x0000000000000000 0x0000000000000000 0xa803010710001807 0x55006020e2000300

def z1028 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0x58ecc698e1e7e67c 0xab1d98d31c3cfccf

def z1029 : W := mkw 0x16dfa8001cdd8004 0x02dbf500039bb000 0x97fff8001ef98001 0xf2ffff0003df3000

def z1030 : W := mkw 0x059005000a905002 0x00b200a001520a00 0xdff007e01ff87f86 0xfbfe00fc03ff0ff0

def z1031 : W := mkw 0x06dee00009d28000 0x00dbdc00013a5000 0x97fff8001fff8005 0xf2ffff0003fff000

def z1032 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8fcc698f1ffe67f 0xff1f98d31e3ffccf

def z1033 : W := mkw 0x16dfe8401ddf8105 0x02dbfd0803bbf020 0x97fff8601fff8185 0xf2ffff0c03fff030

def z1034 : W := mkw 0x0044c00021428220 0x0008980004285044 0xf8ecc698e1e7e67f 0xbf1d98d31c3cfccf

def z1035 : W := mkw 0x00011823500c08c0 0x200023046a018118 0xa813f9e7f1181f87 0xd5027f3cfe2303f0

def z1036 : W := mkw 0x0065ca89b16eaee8 0x600cb951362dd5dd 0x58ec061811fffffc 0x2b1d80c3023fffff

def z1037 : W := mkw 0x006492aac060a408 0x400c9255580c1481 0xf0ffffffe0e1e01b 0xfe1ffffffc1c3c03

def z1038 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x87f3f8001ffe0005 0xd0fe7f0003ffc000

def z1039 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x00000000111e0064 0x000000000223c00c

def z1040 : W := mkw 0x2ffeb7fec4010010 0x85ffd6ffd8802002 0xe7ffffffe001801b 0xfcfffffffc003003

def z1041 : W := mkw 0x27ba37f64ab07503 0x04f746fec9560ea0 0xfff3ffe7fff87f87 0xfffe7ffcffff0ff0

def z1042 : W := mkw 0x05b14fc13bfeffeb 0x60b629f8277fdffd 0xdff007e01ffffffe 0xfbfe00fc03ffffff

def z1043 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xdff3ffe7fff87f86 0xfbfe7ffcffff0ff0

def z1044 : W := mkw 0x030b051414050000 0x006160a28280a000 0xff0f071f1e07e07f 0x7fe1e0e3e3c0fc0f

def z1045 : W := mkw 0x26feb2fec8b02501 0x04dfd65fd91604a0 0x20fff8ffe1f80781 0x841fff1ffc3f00f0

def z1046 : W := mkw 0x06dfa0001c950000 0x00dbf4000392a000 0x97fff8001fff8005 0xf2ffff0003fff000

def z1047 : W := mkw 0x3ffeb7feced1d016 0x87ffd6ffd9da3a02 0xf7ffffffeee1e01b 0xfefffffffddc3c03

def z1048 : W := mkw 0x04910800189c0000 0x0092210003138000 0x97f338001ff80004 0xf2fe670003ff0000

def z1049 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x9ffff8001fffe07d 0xf3ffff0003fffc0f

def z1050 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf0ecc698e0e7e07b 0xbe1d98d31c1cfc0f

def z1051 : W := mkw 0x26deb03ec0000000 0x04dbd607d8000000 0x27eff81fe0000001 0x24fdff03fc000000

def z1052 : W := mkw 0x0064c2c8a162a729 0x400c9859142c54e5 0xf8ecc6f8e1e7e7ff 0xbf1d98df1c3cfcff

def z1053 : W := mkw 0x002012a240000000 0x0004025448000000 0xe0f3ffe7e0000003 0xfc1e7ffcfc000000

def z1054 : W := mkw 0x00015823750f0ae0 0x20002b046ea1e15c 0xb813f9e7ff1f9fe7 0xd7027f3cffe3f3fc

def z1055 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xa7f3f9e7e0000003 0xd4fe7f3cfc000000

def z1056 : W := mkw 0x169b28001c9d0004 0x02d365000393a000 0x97ff38001fff8005 0xf2ffe70003fff000

def z1057 : W := mkw 0x00014801314e8ae0 0x200029002629d15c 0x1800000011ff9fe4 0x03000000023ff3fc

def z1058 : W := mkw 0x0000102240000000 0x0000020448000000 0xa813f9e7f0001807 0xd5027f3cfe000300

def z1059 : W := mkw 0x07ba17f64ab07503 0x00f742fec9560ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z1060 : W := mkw 0x05f497eacab07503 0x00be92fd59560ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z1061 : W := mkw 0x1edfe8141ddf8014 0x83dbfd0283bbf002 0x97fff8181fff801d 0xf2ffff0303fff003

def z1062 : W := mkw 0x10014801354f8ae4 0x2200290026a9f15c 0x08000000111f9fe4 0x010000000223f3fc

def z1063 : W := mkw 0x0b0b0d15160d58d2 0xa16161a2a2c1ab1a 0xff0f071f1e1ff9ff 0x7fe1e0e3e3c3ff3f

def z1064 : W := mkw 0x2000103ec0000000 0x04000207d8000000 0xa013f9ffe0000003 0xd4027f3ffc000000

def z1065 : W := mkw 0x27feb7fec2207503 0x04ffd6ffd8440ea0 0xffffffffe1e07f87 0xfffffffffc3c0ff0

def z1066 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97eff8001ee78005 0x72fdff0003dcf000

def z1067 : W := mkw 0x124ff82bf54f8aec 0x6249ff057ea9f15d 0x200ff81fe0078079 0x0401ff03fc00f00f

def z1068 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xf7ffffffe1e00007 0xfefffffffc3c0000

def z1069 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdffc07f81ff9ff9e 0xfbff80ff03ff3ff3

def z1070 : W := mkw 0x27feb7fec0202501 0x04ffd6ffd80404a0 0xe7ffffffe0000783 0xfcfffffffc0000f0

def z1071 : W := mkw 0x27feb7fec0202400 0x04ffd6ffd8040480 0xefffffffe0006603 0xfdfffffffc000cc0

def z1072 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xf7ffffffe001e01b 0xfefffffffc003c03

def z1073 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa81ff9fff11f9fff 0xd503ff3ffe23f3ff

def z1074 : W := mkw 0x0000102240000000 0x0000020448000000 0x280001e7e0001f82 0x0500003cfc0003f0

def z1075 : W := mkw 0x092017bfe2207efa 0xe12402f7fc440fdf 0x680007ffe0007ffa 0x0d0000fffc000fff

def z1076 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x27fff9ffe0000001 0xc4ffff3ffc000000

def z1077 : W := mkw 0x04b012e240000000 0x0096025c48000000 0xa0f3f9e7e0000003 0xd41e7f3cfc000000

def z1078 : W := mkw 0x234eb57ec0000000 0x0469d6afd8000000 0x200ff97fe0000001 0x0401ff2ffc000000

def z1079 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xffecc698ffe7e67f 0xfffd98d31ffcfccf

def z1080 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xf7fffffffe000007 0xfeffffffffc00000

def z1081 : W := mkw 0x04904800099a0000 0x0092090001334000 0x97f0f8001ff80004 0xf2fe1f0003ff0000

def z1082 : W := mkw 0x0064ca88a16aa6a8 0x600c9951142d54d5 0xf8ecc698e1ffe7ff 0xbf1d98d31c3ffcff

def z1083 : W := mkw 0x14d4e80009da8004 0x029a9d00013b5000 0x17f0f8000ff80000 0xa2fe1f0001ff0000

def z1084 : W := mkw 0x27feb7fec2005002 0x04ffd6ffd8400a00 0xffffffffff187f87 0xffffffffffe30ff0

def z1085 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa81ff9fff1181f87 0xd503ff3ffe2303f0

def z1086 : W := mkw 0x16dfe8003ddf8224 0x02dbfd0007bbf044 0xfffffe98ffffe67f 0xffffffd31ffffccf

def z1087 : W := mkw 0x27feb7fec2005002 0x04ffd6ffd8400a00 0xe7fffffffe001803 0xfcffffffffc00300

def z1088 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2013f9e7f11e1fe1 0xc4027f3cfe23c3fc

def z1089 : W := mkw 0x16dff8225ddf8004 0x02dbff044bbbf000 0xbffff9e7ffff9f87 0xf7ffff3cfffff3f0

def z1090 : W := mkw 0x27feb7fec0408000 0x04ffd6ffd8081000 0xf7ffffffe0e18003 0xfefffffffc1c3000

def z1091 : W := mkw 0x2000103ec0000000 0x04000207d8000000 0x2003f81fe0000001 0x04007f03fc000000

def z1092 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97f3f8001ff80004 0xf2fe7f0003ff0000

def z1093 : W := mkw 0x059005400ab07503 0x00b200a801560ea0 0x9ff001601ff87f84 0xf3fe002c03ff0ff0

def z1094 : W := mkw 0x27feb7fec8900000 0x04ffd6ffd9120000 0xf7ffffffeee00003 0xfefffffffddc0000

def z1095 : W := mkw 0x2044b02ac0000000 0x0408960558000000 0xa013f9e7e0000003 0xd4027f3cfc000000

def z1096 : W := mkw 0x0000102240000000 0x0000020448000000 0xa013f807e0000001 0xd4027f00fc000000

def z1097 : W := mkw 0x1edfe8151ddf8854 0x83dbfd02a3bbf10a 0xbffff91f1fff987f 0xf7ffff23e3fff30f

def z1098 : W := mkw 0x1f9b3d375e9d58d6 0xa3f367a6ebd3ab1a 0x071339671e181980 0x40e2672ce3c30330

def z1099 : W := mkw 0x00015822510e0000 0x00002b044a21c000 0xa813f9e7f11e1f87 0xd5027f3cfe23c3f0

def z1100 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x8ff001e01ff81f86 0xd1fe003c03ff03f0

def z1101 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x18000000111ffffc 0x030000000223ffff

def z1102 : W := mkw 0x0000102240000000 0x0000020448000000 0xa013f9e7f0181983 0xd4027f3cfe030330

def z1103 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xffffffffffffffff 0xffffffffffffffff

def z1104 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xf7fffffffff86007 0xfeffffffffff0c00

def z1105 : W := mkw 0x24f4b2eac0000000 0x049e965d58000000 0x00f3f9e7e0000000 0xc01e7f3cfc000000

def z1106 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x5ff006e01ff87f84 0xabfe00dc03ff0ff0

def z1107 : W := mkw 0x00015823714e8ae0 0x20002b046e29d15c 0xb813f9e7f1ff9fe7 0xd7027f3cfe3ff3fc

def z1108 : W := mkw 0x04b012e248b02501 0x0096025c491604a0 0xa0f3f9e7e1f80783 0xd41e7f3cfc3f00f0

def z1109 : W := mkw 0x08014801350f0af0 0xa100290026a1e15e 0x08000000111f9ffc 0x010000000223f3ff

def z1110 : W := mkw 0x16dfe8011ddf88c4 0x22dbfd0023bbf118 0x97fff8001fff9985 0xf2ffff0003fff330

def z1111 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97eff8000fe78005 0xb2fdff0001fcf000

def z1112 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xdffffe001fffe007 0xfbffffc003fffc00

def z1113 : W := mkw 0x059015624a905103 0x00b202ac49520a20 0xa713f9e7fe181983 0xd4e27f3cffc30330

def z1114 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8fffe98e1e7e67f 0xff1fffd31c3cfccf

def z1115 : W := mkw 0x00014801330e5ae2 0x200029002661cb5c 0x180000001f1e7fe4 0x0300000003e3cffc

def z1116 : W := mkw 0x169b28001c9d0004 0x02d365000393a000 0x07f338001ff80000 0xc0fe670003ff0000

def z1117 : W := mkw 0x27feb7fec0202400 0x04ffd6ffd8040480 0xf7ffffffe0e06003 0xfefffffffc1c0c00

def z1118 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x0800000000061fe0 0x010000000000c3fc

def z1119 : W := mkw 0x06deb02240000000 0x00dbd60448000000 0xa7fff807e0000001 0xf4ffff00fc000000

def z1120 : W := mkw 0x15b14fc13fffffe7 0x22b629f827fffffc 0xdff007e01fffffe6 0xfbfe00fc03fffffc

def z1121 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x88100000111e1fe4 0xd10200000223c3fc

def z1122 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x97fff9601fff9985 0xf2ffff2c03fff330

def z1123 : W := mkw 0x2044b02ac0000000 0x0408960558000000 0x2003f807e0000001 0x04007f00fc000000

def z1124 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xf7ffffffe0078007 0xfefffffffc00f000

def z1125 : W := mkw 0x14d5e80019de8004 0x029abd00033bd000 0x97f3f8001ffe0005 0xf2fe7f0003ffc000

def z1126 : W := mkw 0x2ffeb7fec661f41a 0xc5ffd6ffd8cc3e83 0xf7ffffffeee1e01b 0xfefffffffddc3c03

def z1127 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa00ff91fe0000003 0x5401ff23fc000000

def z1128 : W := mkw 0x16dfa8001cdd8004 0x02dbf500039bb000 0x07f338001ef80000 0x40fe670003df0000

def z1129 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x07fff8001fff8001 0xc0ffff0003fff000

def z1130 : W := mkw 0x1001480139de8ae4 0x22002900273bd15c 0x0800000011fe1fe4 0x01000000023fc3fc

def z1131 : W := mkw 0x16dee8000ddb8004 0x02dbdd0001bb7000 0x97fcf8001ff98004 0xf2ff9f0003ff3000

def z1132 : W := mkw 0x236eb7fec0000000 0x046dd6ffd8000000 0xe01fffffe0000003 0xdc03fffffc000000

def z1133 : W := mkw 0x16dfe8089ddf800c 0x42dbfd0113bbf001 0x97fff8181fff801d 0xf2ffff0303fff003

def z1134 : W := mkw 0x024eb02240000000 0x0049d60448000000 0x200ff807e0000001 0x0401ff00fc000000

def z1135 : W := mkw 0x16dfa8001cdd8004 0x02dbf500039bb000 0x17ef38000ee18000 0x22fde70001dc3000

def z1136 : W := mkw 0x0590156240000000 0x00b202ac48000000 0xa713f9e7e0000003 0xd4e27f3cfc000000

def z1137 : W := mkw 0x27deb53ec0000000 0x04fbd6a7d8000000 0xe7ffff1fe0000003 0xfcffffe3fc000000

def z1138 : W := mkw 0x100148013d9f0ae4 0x2200290027b3e15c 0x080000001f1e1fe4 0x0100000003e3c3fc

def z1139 : W := mkw 0x25b017fec0000000 0x04b602ffd8000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z1140 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff1f077f1e1ff9ff 0x7fe3e0efe3c3ff3f

def z1141 : W := mkw 0x27feb7fec2207402 0x04ffd6ffd8440e80 0xffffffffffe07e07 0xfffffffffffc0fc0

def z1142 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xb81ff9e7f11f9fe7 0xf703ff3cfe23f3fc

def z1143 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7fffffff0181983 0xfcfffffffe030330

def z1144 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7ffffffe1180783 0xfcfffffffc2300f0

def z1145 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa70ff81fe0000001 0x74e1ff03fc000000

def z1146 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa00ff89fe0000003 0x9401ff13fc000000

def z1147 : W := mkw 0x04914801399e0ae0 0x209229002733c15c 0x9ff000001ffe1fe4 0xf3fe000003ffc3fc

def z1148 : W := mkw 0x224eb03ec0408008 0x4449d607d8081001 0x200ff81fe0018019 0x0401ff03fc003003

def z1149 : W := mkw 0x0044902ac0000000 0x0008920558000000 0xa01ff9ffe0000003 0xd403ff3ffc000000

def z1150 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xffef071f1fe7f87f 0xfffde0e3e3fcff0f

def z1151 : W := mkw 0x04d4b02240000000 0x009a960448000000 0xa0f3f9e7e0000003 0xd41e7f3cfc000000

def z1152 : W := mkw 0x00014801312e2ee0 0x200029002625c5dc 0x1800000011fe7fe4 0x03000000023fcffc

def z1153 : W := mkw 0x1490280008980004 0x0292050001130000 0x97f038001ff80004 0xf2fe070003ff0000

def z1154 : W := mkw 0x37feb7fec8d08004 0x06ffd6ffd91a1000 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z1155 : W := mkw 0x236eb7fec0000000 0x046dd6ffd8000000 0x600ffe1fe0000001 0x0c01ffc3fc000000

def z1156 : W := mkw 0x37feb7feccf1a40c 0x46ffd6ffd99e3481 0xf7ffffffeee1e01b 0xfefffffffddc3c03

def z1157 : W := mkw 0x26deb03ec8900000 0x04dbd607d9120000 0xb7fff81ffff80005 0xf6ffff03ffff0000

def z1158 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xb813f9e7f11fffff 0xd7027f3cfe23ffff

def z1159 : W := mkw 0x024fc800154f8000 0x0049f90002a9f000 0x97fff8001fff8005 0xf2ffff0003fff000

def z1160 : W := mkw 0x26feb2eac0000000 0x04dfd65d58000000 0xa7fff9e7e0000003 0xf4ffff3cfc000000

def z1161 : W := mkw 0x14d4e80009da8004 0x029a9d00013b5000 0x97fcf8001fff8005 0xf2ff9f0003fff000

def z1162 : W := mkw 0x220a303640000000 0x04414606c8000000 0xa013f9e7e0000003 0xd4027f3cfc000000

def z1163 : W := mkw 0x00014801332e7fe3 0x200029002665cffc 0x08000000111e7fe4 0x010000000223cffc

def z1164 : W := mkw 0x012017e242207503 0x002402fc48440ea0 0xe813ffe7e0007f83 0xdd027ffcfc000ff0

def z1165 : W := mkw 0x37feb7fecef1f507 0x06ffd6ffd9de3ea0 0xf7ffffffeee1e003 0xfefffffffddc3c00

def z1166 : W := mkw 0x16dfe8003ddf8224 0x02dbfd0007bbf044 0x97fff880ffff8605 0xf2ffff101ffff0c0

def z1167 : W := mkw 0x1a4ff837754f8af4 0xa349ff06eea9f15e 0x200ff81fe0078079 0x0401ff03fc00f00f

def z1168 : W := mkw 0x25f4b7eac0000000 0x04be96fd58000000 0xe7f3ffe7e0000003 0xfcfe7ffcfc000000

def z1169 : W := mkw 0x006482888060a408 0x400c9051100c1481 0xf8ecc698e0e7e07f 0xbf1d98d31c1cfc0f

def z1170 : W := mkw 0x05b14fc13bbe7fe3 0x20b629f82777cffc 0x5fe006001ffe7fe4 0x2bfc00c003ffcffc

def z1171 : W := mkw 0x2ffeb7fec2005012 0x85ffd6ffd8400a02 0xe7ffffffe000601b 0xfcfffffffc000c03

def z1172 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xf70f071f0e07e07b 0x7ee1e0e3e1c0fc0f

def z1173 : W := mkw 0x212017f642207503 0x042402fec8440ea0 0x480007e700007f82 0x090000fce0000ff0

def z1174 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17fff8001ff98000 0xe2ffff0003ff3000

def z1175 : W := mkw 0x26feb2fec0000000 0x04dfd65fd8000000 0xe0fffeffe0000003 0xbc1fffdffc000000

def z1176 : W := mkw 0x27feb7fec8900000 0x04ffd6ffd9120000 0xfffffffffff81f87 0xffffffffffff03f0

def z1177 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x87fff9e7e0000001 0xf0ffff3cfc000000

def z1178 : W := mkw 0x069a200008900000 0x00d3440001120000 0x97f338001ff80004 0xf2fe670003ff0000

def z1179 : W := mkw 0x24f4b2eac8b02501 0x049e965d591604a0 0xa8f3f9e7f1f81f87 0xd51e7f3cfe3f03f0

def z1180 : W := mkw 0x14d5e8001ddf8004 0x029abd0003bbf000 0x97f0f8001fff8004 0xf2fe1f0003fff000

def z1181 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x570c06180e07e078 0x2ae180c301c0fc0f

def z1182 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0x07f3f9e7fff81f80 0xc0fe7f3cffff03f0

def z1183 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8ecc798f1e7fe7f 0xff1d98f31e3cffcf

def z1184 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff1f07ff1e07f87f 0xffe3e0ffe3c0ff0f

def z1185 : W := mkw 0x26deb03ec0000000 0x04dbd607d8000000 0x271ff81fe0000001 0x44e3ff03fc000000

def z1186 : W := mkw 0x16dfe8011ddf8844 0x02dbfd0023bbf108 0xb7fff8071fff8065 0xf6ffff00e3fff00c

def z1187 : W := mkw 0x292017ffe2207e7a 0xc52402fffc440fcf 0x680007ffe0007e7a 0x0d0000fffc000fcf

def z1188 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0x0003f807e0000000 0x00007f00fc000000

def z1189 : W := mkw 0x2ffeb7fec6015012 0x85ffd6ffd8c02a02 0xffffffffee07e07f 0xfffffffffdc0fc0f

def z1190 : W := mkw 0x00214a81312e2ee0 0x200429502625c5dc 0xd8e0068011fe7fe6 0xbb1c00d0023fcffc

def z1191 : W := mkw 0x27feb7fec0408008 0x44ffd6ffd8081001 0xe7ffffffe001801b 0xfcfffffffc003003

def z1192 : W := mkw 0x01014d01330e5ae2 0x202029a02661cb5c 0xdf0007001f1e7fe6 0x7be000e003e3cffc

def z1193 : W := mkw 0x16dfe8003ddf8224 0x02dbfd0007bbf044 0xb7fff800ffff8065 0xf6ffff001ffff00c

def z1194 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0xf80c0618111fffff 0x3f0180c30223ffff

def z1195 : W := mkw 0x030a153642005002 0x006142a6c8400a00 0xff1fffffff187f87 0xffe3ffffffe30ff0

def z1196 : W := mkw 0x27feb7fec0202400 0x04ffd6ffd8040480 0xfffffffff1f87f87 0xfffffffffe3f0ff0

def z1197 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7efff1fe0000003 0x7cfdffe3fc000000

def z1198 : W := mkw 0x012017e2622077a3 0x202402fc4c440ef4 0x480007e0e0007f82 0x090000fc1c000ff0

def z1199 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xb8f3f9e7f1fe1fe7 0xf71e7f3cfe3fc3fc

def z1200 : W := mkw 0x27feb7fec0202400 0x04ffd6ffd8040480 0xe7ffffffe1e00603 0xfcfffffffc3c00c0

def z1201 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17ff38001fff8004 0x62ffe70003fff000

def z1202 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xa013f9e7f1181f83 0xd4027f3cfe2303f0

def z1203 : W := mkw 0x16dfe8013ddf8a64 0x02dbfd0027bbf14c 0xbffff987ffff9e67 0xf7ffff30fffff3cc

def z1204 : W := mkw 0x27feb7feca905103 0x04ffd6ffd9520a20 0xfffffffffe187987 0xffffffffffc30f30

def z1205 : W := mkw 0x236eb7fec2207503 0x046dd6ffd8440ea0 0x680fffffe0007f83 0x0d01fffffc000ff0

def z1206 : W := mkw 0x202012eac0000000 0x0404025d58000000 0xa013f9e7e0000003 0xd4027f3cfc000000

def z1207 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z1208 : W := mkw 0x020a102240000000 0x0041420448000000 0xa71ff9e7e0000003 0xf4e3ff3cfc000000

def z1209 : W := mkw 0x00014801316eaee8 0x60002900262dd5dd 0x1800000001e7e67c 0x03000000003cfccf

def z1210 : W := mkw 0x1edfe8151ddf8854 0x83dbfd02a3bbf10a 0xfffffe1f1fffe07f 0xffffffc3e3fffc0f

def z1211 : W := mkw 0x279a35764a905103 0x04f346aec9520a20 0xaf13f9e7ff181f87 0xd5e27f3cffe303f0

def z1212 : W := mkw 0x000010224ab07503 0x0000020449560ea0 0xb813f9e7fff87f87 0xd7027f3cffff0ff0

def z1213 : W := mkw 0x0000102240000000 0x0000020448000000 0xa813f9e7e0060067 0xd5027f3cfc00c00c

def z1214 : W := mkw 0x07feb7e24ab07503 0x00ffd6fc49560ea0 0xffffffe7fff87f87 0xfffffffcffff0ff0

def z1215 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0x200ff9ffe0000003 0x0401ff3ffc000000

def z1216 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xe7effe9fe0000003 0xbcfdffd3fc000000

def z1217 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xf70f061f1e07e07d 0x7ee1e0c3e3c0fc0f

def z1218 : W := mkw 0x04b0028008b02400 0x0096005001160480 0xdff007e01ff87f86 0xfbfe00fc03ff0ff0

def z1219 : W := mkw 0x07ba17f640000000 0x00f742fec8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1220 : W := mkw 0x14d4e80009da8004 0x029a9d00013b5000 0x07f0f8001ff80000 0xc0fe1f0003ff0000

def z1221 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x17ec00000ee78000 0x22fd800001dcf000

def z1222 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0x9ffff8801fff8607 0xf3ffff1003fff0c0

def z1223 : W := mkw 0x05f497eac0000000 0x00be92fd58000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1224 : W := mkw 0x226eb2bec0000000 0x044dd657d8000000 0x600ffe9fe0000003 0x0c01ffd3fc000000

def z1225 : W := mkw 0x00214a81316eaee8 0x60042950262dd5dd 0xd8f007e011fffffe 0xfb1e00fc023fffff

def z1226 : W := mkw 0x324ff83ff54f8ae4 0x2649ff07fea9f15c 0x200ff81fe0078061 0x0401ff03fc00f00c

def z1227 : W := mkw 0x37fea7dc8ef1f507 0x06ffd4fb91de3ea0 0x57ec06180ee1e000 0x2afd80c301dc3c00

def z1228 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff0f061f0e07e07f 0x3fe1e0c3e1c0fc0f

def z1229 : W := mkw 0x0b0b0d15160d5852 0x816161a2a2c1ab0a 0xff1f3f1f1e1ff87f 0x7fe3e7e3e3c3ff0f

def z1230 : W := mkw 0x0f9b1d775e9d59d3 0xa1f363aeebd3ab3a 0x071339671e181980 0x40e2672ce3c30330

def z1231 : W := mkw 0x0044902240000000 0x0008920448000000 0xa0fff9e7e0000003 0xf41fff3cfc000000

def z1232 : W := mkw 0x0100152240000000 0x002002a448000000 0xe713ffe7e0000003 0xfce27ffcfc000000

def z1233 : W := mkw 0x27feb7fec060a408 0x44ffd6ffd80c1481 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z1234 : W := mkw 0x27deb57ec0000000 0x04fbd6afd8000000 0xe71fff7fe0000003 0x7ce3ffeffc000000

def z1235 : W := mkw 0x26deb03ec0000000 0x04dbd607d8000000 0x20fff81fe0000001 0x841fff03fc000000

def z1236 : W := mkw 0x292017ffc2207d53 0x852402fff8440faa 0x680007ffe0007ffa 0x0d0000fffc000fff

def z1237 : W := mkw 0x27ba37f640000000 0x04f746fec8000000 0xe7f3ffe7e0000003 0xfcfe7ffcfc000000

def z1238 : W := mkw 0x0b0b4d15370f5af2 0xa16169a2a6e1eb5e 0x5f0c06181f1ffffc 0x2be180c303e3ffff

def z1239 : W := mkw 0x2b4eb53ec6015012 0x8569d6a7d8c02a02 0x770ffe1fee01e019 0x2ee1ffc3fdc03c03

def z1240 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0xff1f071f1f1ff87f 0xffe3e0e3e3e3ff0f

def z1241 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x0813f9e7f11e1fe4 0xc1027f3cfe23c3fc

def z1242 : W := mkw 0x0000102240000000 0x0000020448000000 0xa013f9e7f1180007 0xd4027f3cfe230000

def z1243 : W := mkw 0x020a103640000000 0x00414206c8000000 0xa01ff9ffe0000003 0xd403ff3ffc000000

def z1244 : W := mkw 0x092017f762207ff3 0xa12402feec440ffe 0x680007ffe0007ffa 0x0d0000fffc000fff

def z1245 : W := mkw 0x27feb7fec060a408 0x44ffd6ffd80c1481 0xffffffffe1e1e61f 0xfffffffffc3c3cc3

def z1246 : W := mkw 0x37feb7fecef1f507 0x06ffd6ffd9de3ea0 0xfffffffffff9ff87 0xffffffffffff3ff0

def z1247 : W := mkw 0x124fe800154f8004 0x0249fd0002a9f000 0x97eff8001fe78005 0xf2fdff0003fcf000

def z1248 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xf80ffe1fe007e07f 0x3f01ffc3fc00fc0f

def z1249 : W := mkw 0x16dfe8001ddf8004 0x02dbfd0003bbf000 0xbffff8001fff8067 0xf7ffff0003fff00c

def z1250 : W := mkw 0x37feb7feccd18004 0x06ffd6ffd99a3000 0xf7fffffffff98007 0xfeffffffffff3000

def z1251 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0xefffffffe000607b 0xfdfffffffc000c0f

def z1252 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xc7f007e01ff81f82 0xf8fe00fc03ff03f0

def z1253 : W := mkw 0x149148001ddf8004 0x0292290003bbf000 0x97f3f8001fff8005 0xf2fe7f0003fff000

def z1254 : W := mkw 0x279a357640000000 0x04f346aec8000000 0x0713f9e7e0000000 0xc0e27f3cfc000000

def z1255 : W := mkw 0x100148013fffffe7 0x2200290027fffffc 0x180000001fffffe4 0x0300000003fffffc

def z1256 : W := mkw 0x0db007d40ab07513 0x81b600fa81560ea2 0xdff007f81ff87f9e 0xfbfe00ff03ff0ff3

def z1257 : W := mkw 0x100148013dffaeec 0x6200290027bff5dd 0x180000001ffffffc 0x0300000003ffffff

def z1258 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0x2813f9e7f01e1fe3 0x45027f3cfe03c3fc

def z1259 : W := mkw 0x0b0b055516055953 0x816160aaa2c0ab2a 0xff0f077f1e07f9ff 0x7fe1e0efe3c0ff3f

def z1260 : W := mkw 0x220a303640000000 0x04414606c8000000 0x2003f807e0000001 0x04007f00fc000000

def z1261 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x0800000001060664 0x010000000020c0cc

def z1262 : W := mkw 0x224eb03ec0000000 0x0449d607d8000000 0xa0eff81fe0000001 0xb41dff03fc000000

def z1263 : W := mkw 0x0900051502005852 0x812000a2a0400b0a 0xff0c071f1e07f87f 0x7fe180e3e3c0ff0f

def z1264 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xffffffffefe06607 0xfffffffffdfc0cc0

def z1265 : W := mkw 0x0b0a051506015852 0x816140a2a0c02b0a 0xff0c071f0e07f87f 0x3fe180e3e1c0ff0f

def z1266 : W := mkw 0x27feb7fecab07503 0x04ffd6ffd9560ea0 0xfffffffffee07807 0xffffffffffdc0f00

def z1267 : W := mkw 0x27ba37fec0000000 0x04f746ffd8000000 0xe713ffffe0000003 0xdce27ffffc000000

def z1268 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0x4ff007e01ff87f82 0xc9fe00fc03ff0ff0

def z1269 : W := mkw 0x00014801310e0ae0 0x200029002621c15c 0x080001e0111e1fe6 0x0100003c0223c3fc

def z1270 : W := mkw 0x0b0b153756055852 0x816162a6eac0ab0a 0xff1fffffff1fffff 0xffe3ffffffe3ffff

def z1271 : W := mkw 0x16dfe8003ddf82a4 0x22dbfd0007bbf054 0x97fff8001fff8785 0xf2ffff0003fff0f0

def z1272 : W := mkw 0x08014801370f5af2 0xa100290026e1eb5e 0x180000001e07f87c 0x0300000003c0ff0f

def z1273 : W := mkw 0x24f4b2eac0000000 0x049e965d58000000 0x20f3f8e7e0000001 0x841e7f1cfc000000

def z1274 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xe81ffffff11e1fe7 0xfd03fffffe23c3fc

def z1275 : W := mkw 0x0100153640000000 0x002002a6c8000000 0xe013ffffe0000003 0xdc027ffffc000000

def z1276 : W := mkw 0x26feb2fec0000000 0x04dfd65fd8000000 0xa0fff9ffe0000003 0xd41fff3ffc000000

def z1277 : W := mkw 0x27feb7feca905103 0x04ffd6ffd9520a20 0xe7ffffffee000003 0xfcfffffffdc00000

def z1278 : W := mkw 0x0b0a051406015012 0x816140a280c02a02 0xff0f071f0e07e07f 0x7fe1e0e3e1c0fc0f

def z1279 : W := mkw 0x0101050112045842 0x002020a022408b08 0xff0f071f1e07f87f 0x7fe1e0e3e3c0ff0f

def z1280 : W := mkw 0x149148013ddf8ae4 0x2292290027bbf15c 0x9ff001e01fff9fe6 0xf3fe003c03fff3fc

def z1281 : W := mkw 0x2ffeb7feceb17513 0x85ffd6ffd9d62ea2 0xf7ffffffeee1e01b 0xfefffffffddc3c03

def z1282 : W := mkw 0x0064c288a162a628 0x400c9851142c54c5 0xf8fcc6f8e1ffe7ff 0xbf1f98df1c3ffcff

def z1283 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xdff007e01ffffffe 0xfbfe00fc03ffffff

def z1284 : W := mkw 0x27deb57ec0000000 0x04fbd6afd8000000 0xa71ff9ffe0000003 0xd4e3ff3ffc000000

def z1285 : W := mkw 0x00015823710e0ae0 0x20002b046e21c15c 0xe813fffff11e7fff 0xdd027ffffe23cfff

def z1286 : W := mkw 0x16dfe808bddf822c 0x42dbfd0117bbf045 0xfffffe18ffffe07f 0xffffffc31ffffc0f

def z1287 : W := mkw 0x27feb7fec0202408 0x44ffd6ffd8040481 0xe7ffffffe000601b 0xfcfffffffc000c03

def z1288 : W := mkw 0x04b002c008b02501 0x00960058011604a0 0x9ff001e01ff81f86 0xf3fe003c03ff03f0

def z1289 : W := mkw 0x05b007c00ab07503 0x00b600f801560ea0 0xfff007f81ff87ffe 0xfffe00ff03ff0fff

def z1290 : W := mkw 0x27feb7feca905103 0x04ffd6ffd9520a20 0xefffffffff181f87 0xfdffffffffe303f0

def z1291 : W := mkw 0x0a0b001514050850 0x81416002a280a10a 0xff0f061f1e07e07f 0x7fe1e0c3e3c0fc0f

def z1292 : W := mkw 0x27feb7fec0000000 0x04ffd6ffd8000000 0x67efffffe0000003 0x2cfdfffffc000000

def z1293 : W := mkw 0x1edfe8151ddf8854 0x83dbfd02a3bbf10a 0x97fff8071fff8005 0xf2ffff00e3fff000

def z1294 : W := mkw 0x26feb2fec0000000 0x04dfd65fd8000000 0xa7fff8ffe0000001 0xf4ffff1ffc000000

def z1295 : W := mkw 0x0a4fd83ff54f8af8 0xe149fb07fea9f15f 0x200ff81fe0078079 0x0401ff03fc00f00f

def z1296 : W := mkw 0x002012a240202400 0x0004025448040480 0xf8f3ffe7e1e06607 0xff1e7ffcfc3c0cc0

def z1297 : W := mkw 0x27feb7fec2207503 0x04ffd6ffd8440ea0 0xe7ffffffe0006003 0xfcfffffffc000c00

def z1298 : W := mkw 0x069b48001d9f0000 0x00d3690003b3e000 0x97fff8001fff8005 0xf2ffff0003fff000

def z1299 : W := mkw 0x06deb02248900000 0x00dbd60449120000 0xbffff9e7fff81f87 0xf7ffff3cffff03f0

def z1300 : W := mkw 0x0b0b051516055852 0x816160a2a2c0ab0a 0x6f0f071f1e07f87b 0x4de1e0e3e3c0ff0f

def z1301 : W := mkw 0x16dfa8001cdd8004 0x02dbf500039bb000 0x97ff38001ff98004 0xf2ffe70003ff3000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z8]),(0,[z0,z1,z3,z9,z4,z5,z8]),(0,[z0,z1,z3,z4,z10,z5,z8])],[(0,[z0,z11,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z12,z4,z5,z8]),(1,[z13,z1,z3,z14,z5,z8]),(0,[z0,z1,z15,z3,z4,z5,z8]),(0,[z0,z1,z16,z3,z4,z5,z8]),(0,[z0,z1,z3,z17,z4,z5,z18])],[(0,[z0,z1,z3,z4,z5,z19,z8]),(1,[z20,z0,z1,z3,z4,z5]),(0,[z21,z0,z1,z3,z4,z22,z8]),(0,[z0,z1,z3,z23,z4,z5,z24]),(0,[z0,z1,z3,z4,z25,z5,z8]),(1,[z0,z26,z3,z4,z27,z8]),(0,[z0,z1,z28,z3,z29,z5,z8]),(1,[z0,z1,z3,z4,z5,z30]),(0,[z31,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z32,z8])],[(0,[z0,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z33,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z34]),(0,[z0,z1,z35,z3,z4,z5,z8]),(0,[z0,z1,z36,z4,z5,z8,z24]),(0,[z0,z1,z3,z37,z4,z5,z8])],[(0,[z0,z1,z3,z4,z27,z38,z8]),(0,[z0,z1,z3,z4,z5,z39,z8]),(0,[z0,z1,z3,z17,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z8,z40]),(0,[z0,z1,z3,z4,z5,z41,z24]),(0,[z0,z1,z3,z4,z42,z5,z8]),(0,[z0,z1,z3,z4,z5,z43,z8])],[(0,[z44,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z45,z5,z8]),(1,[z46,z0,z1,z3,z4,z5]),(0,[z20,z0,z1,z47,z3,z4,z5]),(0,[z0,z1,z48,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z49,z8]),(0,[z0,z1,z3,z4,z5,z50,z8])],[(0,[z0,z1,z3,z51,z4,z5,z8]),(0,[z0,z52,z1,z3,z4,z5,z8]),(0,[z53,z46,z0,z1,z3,z4,z5]),(0,[z46,z0,z54,z1,z3,z4,z5]),(0,[z21,z0,z1,z3,z23,z5,z8]),(0,[z0,z1,z3,z23,z4,z5,z8]),(0,[z0,z1,z3,z55,z4,z5,z56])]],
   [[(0,[z0,z1,z3,z4,z57,z5,z8]),(0,[z58,z59,z1,z3,z4,z5,z8]),(0,[z60,z0,z1,z61,z4,z5,z8]),(0,[z62,z0,z1,z3,z4,z5,z8]),(0,[z20,z0,z1,z3,z4,z5,z63]),(0,[z0,z1,z3,z4,z5,z24,z24])],[(0,[z0,z1,z3,z64,z4,z5,z8]),(0,[z0,z1,z65,z3,z4,z5,z8]),(0,[z31,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z66,z3,z4,z5,z8]),(0,[z0,z67,z1,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z14,z5,z8]),(0,[z0,z1,z3,z4,z68,z5,z8]),(0,[z69,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z70,z5,z8]),(0,[z0,z71,z1,z3,z4,z5,z72]),(0,[z0,z1,z3,z4,z5,z41,z8])],[(0,[z73,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z74,z4,z5,z8]),(0,[z0,z1,z3,z4,z75,z76,z8])],[(0,[z20,z77,z0,z1,z3,z4,z5]),(0,[z0,z54,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z78,z24])],[(0,[z59,z0,z1,z3,z4,z5,z24]),(0,[z20,z79,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z24,z80]),(0,[z46,z0,z81,z1,z3,z4,z5]),(0,[z31,z46,z0,z1,z3,z4,z5]),(0,[z21,z0,z1,z82,z4,z5,z8]),(0,[z0,z1,z3,z4,z83,z5,z8])],[(0,[z0,z84,z1,z3,z4,z85,z8]),(0,[z0,z1,z3,z4,z86,z5,z8]),(0,[z87,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z88,z5,z24]),(0,[z0,z1,z89,z3,z4,z5,z8])],[(0,[z0,z1,z3,z90,z4,z5,z8]),(0,[z0,z1,z3,z91,z4,z5,z6]),(0,[z20,z1,z61,z3,z4,z5,z8]),(0,[z62,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z92,z8]),(0,[z0,z1,z93,z3,z4,z5,z8]),(0,[z0,z94,z1,z3,z4,z5,z8])]],
   [[(0,[z95,z0,z1,z2,z3,z4,z5]),(0,[z96,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z97,z4,z5,z98]),(0,[z0,z1,z3,z4,z5,z6,z63]),(0,[z0,z1,z3,z4,z99,z5,z8]),(0,[z0,z1,z3,z4,z5,z100,z8]),(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z101,z5,z76,z8]),(0,[z0,z1,z3,z4,z5,z102,z8])],[(0,[z0,z1,z3,z4,z5,z8,z103]),(0,[z46,z0,z1,z28,z3,z4,z5]),(0,[z0,z54,z1,z3,z4,z5,z8]),(0,[z104,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z105,z3,z4,z5,z8])],[(0,[z59,z0,z1,z3,z4,z5,z8]),(0,[z106,z0,z1,z3,z4,z5,z8]),(0,[z107,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z55,z4,z108,z8]),(0,[z0,z1,z3,z109,z4,z5,z8]),(0,[z0,z1,z110,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z111,z5,z8]),(0,[z0,z112,z1,z3,z4,z5,z6])],[(0,[z46,z0,z1,z3,z4,z5,z76]),(0,[z0,z113,z1,z3,z4,z5,z8]),(0,[z0,z114,z1,z3,z4,z5,z8]),(0,[z0,z1,z28,z29,z4,z5,z8]),(0,[z0,z1,z3,z4,z88,z5,z8]),(0,[z0,z1,z115,z3,z4,z5,z8])],[(0,[z116,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z117,z4,z5]),(0,[z0,z1,z3,z4,z118,z5,z8]),(0,[z0,z119,z1,z3,z4,z5,z8])],[(0,[z0,z120,z1,z3,z4,z5,z8]),(0,[z0,z1,z121,z3,z4,z5,z8]),(0,[z0,z122,z1,z3,z4,z5,z8])],[(0,[z123,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z98]),(0,[z0,z1,z124,z3,z4,z5,z8])],[(0,[z125,z0,z1,z3,z4,z5,z8]),(0,[z1,z61,z3,z4,z5,z126,z8]),(0,[z0,z1,z3,z127,z4,z5,z8]),(1,[z128,z1,z3,z4,z38,z8]),(0,[z0,z1,z3,z4,z129,z5,z8]),(0,[z0,z84,z1,z3,z4,z5,z8]),(0,[z31,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z101,z27,z8]),(0,[z0,z1,z3,z4,z5,z130,z24]),(0,[z0,z1,z3,z131,z4,z5,z8])],[(0,[z20,z0,z1,z3,z4,z5,z72]),(0,[z0,z1,z132,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z133,z5,z8]),(0,[z0,z134,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z135,z5,z8])],[(0,[z0,z1,z4,z5,z6,z8,z24]),(1,[z136,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z137,z5,z6]),(0,[z0,z1,z138,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z139,z8]),(1,[z0,z1,z3,z4,z5,z140]),(0,[z0,z1,z3,z141,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z142,z8]),(1,[z59,z143,z3,z4,z5,z8]),(0,[z0,z1,z144,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z108,z76,z8]),(1,[z20,z1,z3,z4,z5,z80]),(0,[z0,z1,z3,z4,z145,z5,z8]),(0,[z0,z1,z3,z4,z101,z75,z8])],[(0,[z0,z1,z3,z146,z4,z5,z8]),(0,[z46,z0,z143,z1,z3,z4,z5]),(0,[z147,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z101,z5,z6])],[(0,[z77,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z148,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z149,z8]),(0,[z0,z1,z3,z4,z5,z150,z8]),(0,[z125,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z151,z3,z4,z5,z8]),(1,[z152,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z140]),(0,[z0,z1,z3,z4,z5,z153,z8])],[(0,[z0,z1,z3,z4,z154,z38,z8]),(0,[z116,z46,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z137,z5]),(0,[z0,z1,z3,z4,z5,z155,z6]),(0,[z0,z1,z3,z156,z4,z5,z8]),(0,[z0,z1,z3,z4,z157,z5,z8])]],
   [[(0,[z0,z1,z3,z4,z5,z8,z158]),(0,[z0,z159,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z160,z4,z14,z5]),(0,[z0,z1,z3,z4,z5,z38,z24]),(0,[z0,z1,z3,z161,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z76,z6])],[(0,[z162,z0,z163,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z164,z5,z8]),(0,[z0,z1,z165,z3,z4,z5,z8]),(0,[z0,z81,z3,z166,z4,z5,z8]),(0,[z0,z1,z167,z3,z4,z5,z8]),(0,[z0,z26,z1,z3,z4,z75,z8]),(0,[z0,z1,z3,z4,z5,z6,z72])],[(0,[z147,z0,z1,z3,z4,z5,z8]),(0,[z168,z0,z1,z3,z4,z5,z8]),(0,[z162,z1,z3,z4,z5,z126,z8]),(0,[z0,z1,z3,z4,z169,z5,z8]),(0,[z0,z1,z3,z4,z170,z5,z24]),(0,[z0,z1,z171,z3,z4,z5,z8]),(0,[z0,z71,z3,z4,z5,z8,z63]),(0,[z0,z1,z3,z172,z4,z5,z8])],[(0,[z162,z0,z1,z3,z173,z5,z8]),(0,[z20,z0,z81,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z174,z8]),(1,[z0,z1,z3,z160,z4,z5])],[(1,[z20,z1,z61,z3,z4,z5]),(0,[z128,z0,z1,z3,z4,z38,z8]),(0,[z0,z1,z3,z4,z5,z38,z8]),(0,[z0,z175,z1,z3,z4,z5,z24]),(0,[z176,z0,z1,z3,z4,z5,z72]),(0,[z177,z0,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z178,z5,z8]),(0,[z0,z1,z3,z179,z4,z5,z8]),(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z180,z4,z5,z8])],[(0,[z20,z0,z1,z28,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z181,z8]),(0,[z0,z1,z3,z4,z170,z5,z8]),(0,[z0,z1,z3,z4,z5,z182,z8]),(1,[z183,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z6,z184])]],
   [[(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z8]),(0,[z0,z1,z186,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z187,z8]),(0,[z0,z1,z3,z4,z188,z5,z8])],[(0,[z77,z0,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z24]),(0,[z147,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z189]),(0,[z190,z0,z1,z3,z4,z5,z8])],[(0,[z143,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z38,z41,z8]),(0,[z0,z1,z191,z3,z4,z5,z8]),(0,[z192,z0,z1,z3,z4,z5,z8]),(0,[z177,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z55,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z193,z8]),(0,[z0,z84,z1,z166,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z194,z24])],[(0,[z0,z1,z3,z4,z195,z5,z8]),(0,[z20,z0,z1,z196,z3,z4,z5]),(0,[z46,z0,z71,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z197,z5,z8])],[(0,[z0,z1,z3,z4,z198,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z199]),(0,[z0,z1,z3,z4,z5,z8,z200]),(0,[z20,z0,z1,z48,z3,z4,z5]),(0,[z147,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z201])],[(0,[z0,z202,z1,z3,z4,z5,z8]),(0,[z203,z0,z1,z3,z4,z5,z8]),(0,[z204,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z205,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z206]),(0,[z0,z207,z1,z3,z4,z5,z8]),(0,[z0,z1,z208,z3,z4,z5,z8]),(0,[z0,z1,z3,z209,z4,z5,z8])],[(0,[z210,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z63,z211]),(0,[z0,z212,z1,z3,z4,z5,z8])]],
   [[(1,[z0,z213,z3,z4,z5,z8]),(1,[z0,z1,z3,z179,z4,z5]),(0,[z0,z1,z28,z166,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z214,z8])],[(0,[z0,z1,z3,z4,z5,z8,z215]),(0,[z21,z0,z1,z3,z4,z5,z140]),(1,[z21,z0,z3,z170,z5,z8]),(0,[z0,z1,z3,z4,z5,z216,z8]),(0,[z0,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z36,z3,z4,z5,z6]),(0,[z217,z0,z1,z3,z4,z5,z6])],[(0,[z162,z0,z1,z3,z4,z218,z8]),(0,[z0,z1,z3,z4,z5,z8,z219]),(1,[z0,z1,z3,z4,z5,z220]),(0,[z0,z1,z3,z4,z85,z5,z8]),(0,[z0,z1,z28,z3,z221,z5,z8]),(0,[z0,z1,z3,z4,z222,z5,z8]),(0,[z0,z1,z3,z4,z5,z223,z8]),(0,[z0,z1,z224,z3,z4,z5,z8]),(0,[z0,z1,z3,z5,z18,z8,z211])],[(0,[z20,z0,z143,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z72,z24]),(0,[z0,z1,z3,z225,z4,z5,z8])],[(0,[z58,z46,z0,z1,z3,z4,z5]),(0,[z20,z0,z226,z1,z3,z4,z5]),(0,[z21,z152,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z227,z4,z5,z8]),(0,[z0,z175,z1,z3,z170,z5,z8]),(0,[z0,z1,z228,z3,z4,z5,z8]),(0,[z0,z1,z3,z141,z4,z101,z8])],[(0,[z0,z1,z3,z229,z4,z5,z8]),(0,[z0,z230,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z231]),(0,[z0,z1,z3,z4,z137,z232,z8])],[(0,[z162,z0,z1,z4,z154,z5,z8]),(0,[z0,z1,z3,z233,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z234])]],
   [[(0,[z162,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z91,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z235,z8]),(0,[z0,z1,z3,z4,z236,z5,z8]),(0,[z0,z1,z237,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z72,z8]),(0,[z0,z1,z3,z4,z238,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z239])],[(1,[z240,z0,z1,z3,z4,z5]),(0,[z20,z0,z1,z3,z4,z5,z232]),(0,[z241,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z4,z154,z5,z41,z8]),(1,[z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z242,z3,z4,z5,z8]),(0,[z243,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z244,z4,z5,z8]),(0,[z13,z1,z3,z4,z14,z5,z8]),(0,[z245,z0,z1,z3,z4,z5,z8]),(0,[z246,z0,z1,z3,z4,z5,z8]),(0,[z247,z0,z1,z3,z4,z5,z8]),(0,[z248,z0,z1,z3,z4,z5,z8]),(0,[z21,z0,z1,z3,z4,z5,z249]),(2,[z183,z1,z3,z4,z5])],[(0,[z0,z1,z3,z250,z4,z5,z8]),(0,[z79,z0,z1,z3,z4,z108,z8]),(0,[z0,z81,z84,z3,z4,z5,z8]),(0,[z21,z0,z1,z251,z4,z5,z8]),(0,[z0,z1,z3,z4,z252,z5,z8])],[(0,[z162,z46,z0,z1,z3,z4,z5]),(0,[z0,z253,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z91,z4,z5,z8]),(0,[z0,z1,z254,z3,z4,z5,z8]),(0,[z0,z1,z255,z3,z4,z5,z8]),(1,[z176,z0,z3,z4,z5,z72])],[(1,[z0,z1,z3,z4,z5,z8]),(0,[z77,z1,z2,z3,z4,z5,z8]),(0,[z58,z0,z1,z3,z4,z5,z6]),(0,[z0,z256,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z257])],[(0,[z258,z0,z1,z3,z4,z5,z8]),(0,[z58,z0,z1,z3,z97,z5,z8])]],
   [[(0,[z95,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z259,z3,z4,z5,z8]),(0,[z31,z0,z1,z3,z4,z5,z24]),(0,[z0,z112,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z260,z5,z8])],[(0,[z0,z1,z3,z4,z14,z5,z8]),(0,[z246,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z8]),(0,[z0,z1,z3,z4,z5,z8,z80]),(1,[z0,z1,z261,z221,z5,z8])],[(0,[z20,z0,z71,z1,z3,z4,z5]),(0,[z0,z1,z262,z3,z4,z5,z8]),(0,[z0,z1,z196,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z108,z75,z8]),(0,[z0,z1,z3,z4,z5,z18,z72]),(0,[z0,z1,z3,z4,z5,z24,z211]),(0,[z0,z1,z3,z4,z137,z5,z24]),(0,[z0,z1,z3,z4,z5,z6,z263])],[(0,[z60,z1,z61,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z1,z264,z3,z4,z5,z8]),(0,[z0,z1,z3,z141,z4,z5,z24])],[(0,[z0,z2,z3,z166,z4,z5,z8]),(0,[z0,z1,z265,z3,z4,z5,z8]),(0,[z60,z0,z1,z266,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z267,z8]),(0,[z0,z268,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z269])],[(0,[z162,z0,z1,z3,z4,z5,z6]),(0,[z0,z270,z1,z3,z4,z5,z8]),(0,[z258,z20,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z5,z72]),(0,[z0,z1,z3,z4,z271,z5,z8]),(0,[z272,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z101,z5,z24]),(0,[z0,z273,z1,z3,z4,z5,z8])],[(1,[z0,z1,z3,z4,z274,z8]),(0,[z0,z163,z1,z3,z4,z5,z8]),(0,[z0,z1,z275,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z75,z6]),(0,[z0,z1,z266,z3,z4,z101,z8])]],
   [[(0,[z0,z1,z3,z4,z101,z108,z8]),(0,[z0,z1,z3,z276,z4,z5,z8]),(0,[z0,z277,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z269]),(0,[z21,z0,z175,z3,z4,z5,z8]),(0,[z278,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z266,z3,z4,z76,z8]),(0,[z0,z1,z3,z4,z137,z5,z8])],[(0,[z79,z46,z0,z1,z3,z4,z5]),(0,[z0,z279,z1,z3,z4,z5,z8]),(0,[z0,z1,z47,z3,z4,z75,z8]),(0,[z0,z280,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z141,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z281,z8]),(0,[z0,z1,z3,z4,z5,z8,z282])],[(0,[z283,z0,z1,z3,z4,z5,z8]),(0,[z0,z81,z1,z3,z4,z5,z8])],[(0,[z284,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z285,z4,z5,z8]),(0,[z0,z1,z3,z4,z101,z5,z8])],[(0,[z20,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z286,z8]),(0,[z0,z1,z61,z3,z4,z5,z287]),(0,[z128,z0,z1,z47,z3,z4,z8]),(0,[z0,z288,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z289]),(1,[z0,z1,z3,z4,z137,z232])],[(0,[z0,z1,z213,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z290]),(0,[z0,z1,z3,z4,z5,z155,z8]),(0,[z20,z58,z0,z1,z3,z4,z5]),(0,[z20,z0,z1,z3,z4,z5,z41])],[(0,[z0,z1,z3,z4,z5,z291,z8]),(0,[z0,z1,z3,z4,z5,z292,z8]),(0,[z0,z1,z3,z4,z5,z76,z8])],[(1,[z0,z1,z3,z4,z293,z8]),(0,[z0,z1,z3,z4,z5,z294,z8]),(1,[z295,z1,z3,z4,z5,z8]),(0,[z0,z296,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z297,z4,z5,z8]),(0,[z0,z1,z3,z4,z298,z5,z8])]],
   [[(0,[z59,z1,z3,z4,z14,z5,z8]),(0,[z0,z143,z1,z3,z4,z5,z158]),(0,[z0,z1,z3,z97,z4,z5,z6]),(0,[z176,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z299,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z293,z5,z8]),(0,[z77,z0,z1,z3,z4,z5,z24]),(0,[z0,z300,z1,z3,z4,z5,z8]),(0,[z0,z1,z301,z3,z4,z5,z8]),(0,[z0,z1,z3,z97,z221,z5,z8]),(0,[z0,z1,z3,z4,z5,z302,z8]),(0,[z0,z303,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z304,z8]),(0,[z0,z1,z3,z4,z5,z22,z8]),(0,[z305,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z17,z5,z18])],[(0,[z0,z1,z306,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z307,z5,z8]),(0,[z79,z0,z1,z3,z4,z5,z6]),(0,[z20,z176,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z3,z23,z4,z5]),(0,[z46,z0,z1,z3,z4,z291,z8]),(1,[z46,z1,z3,z4,z5,z126]),(0,[z0,z1,z3,z4,z5,z308,z8]),(0,[z0,z1,z3,z55,z4,z5,z24]),(0,[z0,z1,z3,z309,z4,z5,z6]),(0,[z0,z310,z1,z3,z4,z5,z8])],[(0,[z58,z1,z2,z3,z4,z5,z8]),(0,[z59,z0,z143,z3,z4,z5,z8]),(0,[z0,z1,z3,z311,z4,z5,z8]),(0,[z21,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z312,z5,z8])],[(0,[z0,z84,z1,z3,z4,z5,z24]),(0,[z0,z1,z47,z3,z4,z154,z8])],[(0,[z77,z0,z1,z3,z4,z5,z8]),(0,[z60,z0,z1,z91,z4,z5,z8]),(0,[z0,z1,z3,z4,z14,z5,z6]),(0,[z313,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z24,z63]),(0,[z314,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z315,z8])],[(0,[z46,z1,z3,z4,z5,z126,z8]),(0,[z0,z295,z1,z3,z4,z5,z8]),(0,[z0,z1,z196,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z316,z5,z8]),(0,[z0,z1,z317,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z5,z56]),(0,[z0,z1,z318,z3,z4,z5,z8]),(0,[z0,z1,z3,z319,z4,z5,z8]),(0,[z0,z1,z320,z3,z4,z5,z8]),(0,[z0,z1,z321,z3,z4,z5,z8]),(0,[z0,z322,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z55,z4,z5,z8])],[(0,[z0,z84,z143,z3,z4,z5,z8]),(0,[z46,z0,z1,z196,z3,z4,z5]),(0,[z0,z1,z196,z3,z17,z5,z8])],[(0,[z0,z323,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z193]),(0,[z176,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z28,z3,z4,z5,z24]),(0,[z31,z0,z1,z36,z4,z5,z8])],[(0,[z21,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z324,z4,z5,z8])],[(0,[z0,z1,z3,z4,z325,z5,z8]),(0,[z0,z1,z3,z14,z221,z5,z8]),(0,[z0,z1,z3,z4,z5,z326,z8]),(0,[z46,z0,z1,z132,z3,z4,z5]),(0,[z0,z1,z3,z327,z4,z5,z8])],[(1,[z0,z1,z3,z4,z5,z302]),(0,[z0,z1,z3,z4,z328,z5,z8]),(0,[z0,z1,z3,z4,z5,z329,z8]),(0,[z330,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z24,z331])],[(0,[z0,z1,z3,z4,z332,z5,z8]),(1,[z0,z1,z3,z4,z333,z5]),(0,[z0,z81,z1,z166,z4,z5,z8])],[(0,[z77,z0,z1,z3,z4,z274,z8]),(0,[z217,z0,z1,z3,z4,z5,z8]),(0,[z334,z0,z1,z3,z4,z5,z8]),(0,[z79,z0,z1,z266,z3,z4,z8]),(0,[z21,z46,z0,z1,z3,z4,z5]),(0,[z0,z81,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z335,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z336,z8]),(0,[z0,z1,z28,z3,z4,z5,z8]),(0,[z0,z1,z261,z3,z4,z5,z337]),(0,[z0,z338,z1,z3,z4,z5,z8]),(0,[z0,z1,z36,z3,z4,z5,z8]),(0,[z0,z1,z339,z3,z4,z5,z8])]],
   [[(0,[z0,z1,z3,z4,z108,z232,z8]),(0,[z340,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z341,z4,z5,z8]),(0,[z0,z26,z1,z3,z4,z27,z8]),(0,[z0,z342,z1,z3,z4,z5,z24]),(0,[z343,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z29,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z218,z8]),(0,[z0,z1,z3,z29,z97,z5,z8]),(0,[z20,z0,z0,z1,z3,z4,z5]),(0,[z344,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z266,z3,z4,z5,z30])],[(0,[z0,z1,z345,z3,z4,z5,z8]),(0,[z21,z0,z3,z4,z170,z5,z8]),(1,[z1,z3,z4,z5,z346,z24]),(0,[z0,z347,z1,z3,z4,z5,z8])],[(0,[z217,z60,z0,z1,z3,z4,z5]),(0,[z13,z0,z1,z3,z14,z5,z8]),(0,[z348,z0,z1,z3,z4,z5,z8]),(0,[z0,z230,z1,z3,z4,z5,z8]),(0,[z0,z1,z47,z3,z4,z101,z8])],[(0,[z0,z1,z3,z4,z349,z5,z8]),(0,[z0,z350,z1,z3,z4,z5,z8]),(0,[z21,z295,z1,z3,z4,z5,z8]),(0,[z0,z26,z1,z3,z4,z5,z6]),(0,[z176,z0,z3,z4,z5,z72,z8]),(0,[z0,z1,z47,z3,z4,z76,z8]),(0,[z0,z342,z1,z3,z4,z5,z8])],[(0,[z0,z351,z1,z3,z4,z5,z8]),(0,[z0,z143,z1,z3,z4,z5,z352]),(0,[z162,z0,z213,z3,z4,z5,z8]),(0,[z1,z3,z4,z108,z5,z38,z8]),(0,[z217,z20,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z5,z232]),(1,[z0,z84,z353,z4,z5,z8]),(0,[z0,z1,z354,z3,z4,z5,z8])],[(0,[z77,z0,z1,z3,z4,z293,z8]),(0,[z0,z1,z3,z4,z5,z355,z8]),(0,[z58,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z117,z4,z5,z8]),(0,[z0,z1,z356,z3,z4,z5,z8]),(0,[z0,z1,z3,z357,z4,z8,z24]),(0,[z0,z1,z3,z4,z5,z358,z6])]],
   [[(0,[z359,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z61,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z216]),(1,[z1,z3,z4,z5,z346,z8]),(0,[z0,z1,z3,z4,z5,z308,z6])],[(0,[z0,z1,z3,z360,z4,z5,z8]),(0,[z20,z0,z1,z3,z23,z4,z5]),(0,[z0,z1,z3,z4,z5,z361,z8])],[(0,[z0,z1,z362,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z363]),(0,[z46,z0,z1,z3,z4,z221,z5]),(0,[z0,z1,z3,z4,z5,z364,z8])],[(0,[z365,z0,z1,z3,z4,z5,z8]),(0,[z162,z1,z3,z91,z4,z5,z8]),(0,[z348,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z366,z8]),(0,[z0,z1,z266,z3,z4,z27,z8]),(0,[z0,z1,z3,z4,z5,z346,z24])],[(1,[z0,z367,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z368,z8]),(0,[z58,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z369,z8]),(0,[z0,z1,z3,z370,z4,z5,z8]),(0,[z0,z1,z3,z371,z4,z5,z8]),(0,[z0,z1,z3,z4,z372,z5,z8])],[(0,[z0,z1,z3,z4,z108,z5,z24]),(0,[z0,z71,z1,z3,z4,z5,z8]),(0,[z0,z1,z261,z28,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z373,z8]),(0,[z20,z0,z1,z3,z4,z27,z5]),(0,[z20,z0,z1,z3,z4,z5,z56]),(0,[z0,z54,z3,z4,z5,z75,z8]),(0,[z0,z1,z3,z4,z5,z72,z211]),(0,[z0,z1,z3,z4,z5,z8,z374])],[(0,[z162,z0,z1,z3,z4,z5,z24]),(0,[z46,z0,z1,z61,z3,z4,z5]),(0,[z0,z1,z3,z4,z375,z5,z8]),(0,[z0,z1,z266,z3,z4,z75,z8]),(1,[z0,z1,z3,z357,z4,z8]),(0,[z0,z1,z3,z4,z376,z5,z8]),(0,[z0,z1,z377,z3,z5,z76,z8]),(0,[z0,z1,z378,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z379,z8])]],
   [[(0,[z380,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z381,z5,z8]),(0,[z0,z1,z3,z4,z382,z5,z8]),(0,[z0,z1,z3,z4,z5,z75,z24]),(0,[z0,z1,z3,z4,z27,z76,z8]),(0,[z0,z1,z3,z383,z4,z5,z8]),(0,[z0,z1,z3,z384,z4,z5,z8]),(0,[z0,z1,z266,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z346,z8]),(0,[z385,z0,z1,z3,z4,z5,z8])],[(1,[z60,z1,z61,z4,z5,z8]),(0,[z0,z1,z386,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z387]),(0,[z46,z46,z0,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z388]),(0,[z0,z1,z3,z4,z5,z389,z8])],[(0,[z0,z1,z3,z4,z108,z5,z8]),(0,[z0,z1,z3,z390,z4,z5,z8]),(0,[z0,z1,z3,z391,z4,z5,z8])],[(0,[z392,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z393,z5,z8]),(0,[z0,z1,z3,z394,z4,z5,z8])],[(0,[z162,z0,z1,z3,z4,z5,z8]),(0,[z395,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z396,z4,z5,z8])],[(0,[z0,z1,z3,z4,z397,z5,z8]),(0,[z0,z1,z3,z4,z5,z75,z8]),(1,[z0,z1,z3,z4,z5,z398]),(0,[z0,z1,z47,z3,z4,z5,z257]),(0,[z0,z1,z3,z233,z4,z5,z24]),(0,[z0,z399,z1,z3,z4,z5,z8])],[(0,[z0,z400,z1,z3,z4,z5,z8]),(0,[z0,z401,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z24,z402]),(0,[z0,z1,z3,z4,z5,z6,z56])],[(0,[z0,z1,z403,z3,z4,z5,z8]),(0,[z0,z1,z3,z117,z4,z5,z38]),(0,[z46,z0,z1,z3,z4,z101,z5]),(0,[z404,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z211])]],
   [[(0,[z46,z0,z1,z3,z4,z170,z5]),(0,[z0,z1,z3,z4,z5,z8,z220]),(0,[z0,z1,z3,z4,z5,z8,z405]),(0,[z0,z1,z406,z3,z4,z5,z8]),(0,[z0,z1,z196,z3,z4,z5,z211]),(0,[z0,z1,z3,z4,z5,z8,z407])],[(0,[z46,z0,z1,z2,z3,z4,z5]),(0,[z0,z408,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z97,z4,z5,z24]),(0,[z0,z1,z3,z409,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z289,z8]),(0,[z410,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z411,z5,z8]),(0,[z46,z0,z1,z3,z412,z4,z5]),(0,[z46,z0,z1,z3,z4,z5,z41]),(0,[z0,z1,z166,z4,z221,z5,z8]),(0,[z0,z3,z23,z4,z170,z5,z8]),(0,[z0,z1,z3,z4,z5,z24,z413])],[(0,[z46,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z261,z3,z4,z5,z40]),(0,[z0,z1,z266,z3,z4,z154,z8])],[(0,[z414,z0,z1,z3,z4,z5,z8]),(0,[z79,z0,z1,z3,z4,z5,z24]),(0,[z20,z0,z1,z3,z4,z5,z80]),(0,[z0,z26,z54,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z415,z5,z8]),(0,[z0,z1,z416,z3,z4,z5,z8]),(0,[z0,z1,z417,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z418])],[(1,[z0,z1,z3,z4,z328,z8]),(0,[z0,z419,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z420]),(0,[z0,z421,z1,z3,z4,z5,z8])],[(0,[z422,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z423,z3,z4,z5,z8]),(0,[z0,z1,z3,z97,z4,z5,z8]),(0,[z20,z0,z1,z3,z4,z154,z5]),(0,[z0,z1,z3,z424,z4,z5,z8]),(0,[z0,z1,z3,z4,z221,z5,z6]),(0,[z0,z1,z47,z4,z154,z5,z8]),(0,[z0,z1,z3,z425,z4,z5,z8])],[(0,[z0,z1,z3,z426,z4,z5,z8]),(0,[z0,z1,z3,z4,z14,z5,z24]),(0,[z0,z1,z3,z4,z5,z427,z8]),(0,[z240,z46,z0,z1,z3,z4,z5]),(0,[z428,z0,z1,z3,z4,z5,z8]),(0,[z0,z353,z3,z166,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z429,z8]),(1,[z0,z1,z3,z4,z5,z430]),(0,[z0,z1,z3,z4,z5,z8,z24]),(0,[z0,z1,z3,z431,z4,z5,z8]),(0,[z0,z1,z432,z3,z4,z5,z8])]],
   [[(0,[z59,z143,z1,z3,z4,z5,z8]),(0,[z0,z1,z433,z3,z4,z5,z8]),(0,[z20,z0,z1,z3,z4,z221,z5]),(0,[z434,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z435]),(0,[z0,z1,z196,z3,z4,z5,z24])],[(0,[z436,z0,z1,z3,z4,z5,z8]),(0,[z79,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z437,z3,z4,z5,z8]),(0,[z0,z438,z1,z3,z4,z5,z8]),(0,[z0,z81,z1,z3,z4,z5,z220]),(0,[z0,z1,z3,z309,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z439])],[(0,[z0,z1,z61,z3,z4,z5,z200]),(0,[z46,z0,z1,z3,z166,z4,z5]),(0,[z440,z0,z1,z3,z4,z5,z8]),(0,[z0,z71,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z194,z24]),(0,[z0,z1,z196,z3,z4,z5,z18]),(0,[z0,z441,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z442,z8])],[(0,[z162,z0,z1,z3,z4,z5,z290]),(0,[z20,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z443,z3,z4,z5,z8]),(0,[z176,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z444,z4,z5,z8])],[(0,[z0,z445,z1,z3,z4,z5,z8]),(0,[z446,z0,z1,z3,z4,z5,z8]),(1,[z162,z1,z91,z4,z5,z8]),(0,[z20,z0,z1,z317,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z80]),(0,[z46,z0,z1,z3,z4,z381,z5]),(1,[z0,z81,z166,z4,z5,z8]),(0,[z0,z1,z3,z4,z447,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z448])],[(0,[z0,z449,z1,z3,z4,z5,z8]),(0,[z20,z0,z1,z61,z3,z4,z5]),(0,[z0,z1,z3,z4,z450,z5,z8])],[(0,[z0,z143,z1,z3,z4,z5,z6]),(0,[z0,z451,z1,z3,z4,z5,z8]),(0,[z20,z0,z1,z36,z3,z4,z5])],[(0,[z452,z0,z1,z3,z4,z5,z8]),(0,[z20,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z453,z8]),(1,[z0,z1,z3,z4,z194,z8])]],
   [[(0,[z162,z0,z1,z61,z4,z5,z8]),(0,[z0,z1,z3,z4,z173,z5,z8]),(0,[z0,z1,z454,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z108,z5]),(0,[z0,z81,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z8,z455]),(0,[z0,z1,z47,z3,z4,z27,z8]),(0,[z176,z0,z1,z3,z4,z5,z8])],[(0,[z456,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z101,z38,z8]),(0,[z0,z1,z3,z4,z457,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z458]),(0,[z0,z1,z3,z4,z5,z8,z459])],[(0,[z0,z1,z3,z4,z5,z460,z8]),(0,[z46,z0,z1,z3,z141,z4,z5]),(0,[z0,z1,z266,z4,z5,z41,z8])],[(0,[z0,z143,z3,z166,z4,z5,z8]),(0,[z461,z0,z1,z3,z4,z5,z8]),(0,[z46,z0,z1,z261,z3,z4,z5]),(0,[z0,z1,z3,z462,z4,z5,z8]),(0,[z0,z1,z3,z4,z463,z5,z8])],[(0,[z20,z0,z1,z3,z4,z5,z38]),(0,[z0,z1,z3,z4,z5,z464,z8]),(0,[z0,z1,z266,z3,z4,z232,z8]),(0,[z0,z1,z465,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z76,z24])],[(0,[z20,z0,z1,z3,z4,z101,z5]),(0,[z0,z1,z3,z466,z4,z5,z8]),(0,[z0,z1,z47,z3,z4,z5,z6])],[(0,[z452,z20,z0,z1,z3,z4,z5]),(0,[z20,z0,z1,z3,z4,z170,z5]),(0,[z0,z26,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z420,z8]),(1,[z0,z1,z3,z141,z101,z8]),(0,[z0,z1,z3,z17,z5,z18,z8])],[(0,[z0,z1,z3,z250,z91,z4,z5]),(0,[z46,z0,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z29,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z30,z8]),(0,[z467,z0,z1,z3,z4,z5,z8])]],
   [[(0,[z0,z367,z1,z2,z3,z4,z5]),(0,[z162,z0,z1,z3,z4,z5,z193]),(0,[z0,z1,z3,z468,z4,z5,z8]),(0,[z0,z226,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z469,z5,z8]),(0,[z0,z1,z3,z4,z470,z5,z8])],[(0,[z0,z1,z61,z3,z4,z5,z24]),(0,[z13,z0,z1,z3,z4,z471,z8]),(0,[z20,z0,z1,z3,z4,z5,z6]),(0,[z0,z84,z1,z353,z4,z5,z8]),(1,[z0,z1,z36,z4,z5,z24])],[(0,[z0,z1,z3,z4,z472,z5,z8]),(0,[z0,z1,z3,z473,z4,z5,z8]),(0,[z21,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z474,z5,z8])],[(0,[z162,z60,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z290]),(0,[z0,z1,z3,z4,z5,z475,z8]),(0,[z21,z0,z1,z3,z4,z328,z8]),(0,[z0,z26,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z476,z5,z8])],[(0,[z0,z1,z3,z4,z5,z8,z477]),(0,[z0,z1,z3,z82,z4,z5,z8]),(0,[z0,z1,z478,z3,z4,z5,z8]),(0,[z0,z1,z3,z479,z4,z5,z8])],[(0,[z162,z20,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z108,z41,z8]),(0,[z0,z480,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z358,z8]),(0,[z0,z1,z481,z3,z4,z5,z8]),(0,[z0,z3,z4,z5,z72,z8,z63]),(0,[z0,z1,z3,z482,z4,z5,z8]),(0,[z1,z3,z4,z5,z346,z8,z24])],[(0,[z0,z1,z61,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z198,z8]),(0,[z0,z1,z3,z55,z4,z38,z8]),(0,[z0,z1,z3,z4,z5,z8,z483]),(0,[z0,z1,z28,z353,z4,z5,z8]),(0,[z0,z1,z3,z4,z484,z5,z8])],[(0,[z0,z1,z485,z3,z4,z5,z8]),(0,[z486,z0,z1,z3,z4,z5,z8]),(0,[z487,z46,z0,z1,z3,z4,z5]),(1,[z0,z1,z28,z29,z5,z8]),(0,[z0,z1,z488,z3,z4,z5,z8])]],
   [[(0,[z77,z0,z143,z3,z4,z5,z8]),(0,[z489,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z490,z3,z4,z5,z8]),(0,[z20,z0,z1,z3,z166,z4,z5]),(0,[z0,z1,z3,z4,z27,z5,z6]),(0,[z0,z1,z3,z4,z491,z5,z8])],[(0,[z20,z0,z1,z3,z4,z5,z75]),(0,[z0,z1,z266,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z194,z8,z24]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z4,z5,z263,z8]),(0,[z492,z0,z1,z3,z4,z5,z8])],[(0,[z493,z0,z1,z3,z4,z5,z8]),(1,[z20,z46,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z181]),(0,[z0,z175,z1,z3,z23,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z494]),(0,[z0,z1,z266,z3,z55,z4,z8]),(0,[z0,z1,z495,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z154,z108,z8]),(0,[z46,z0,z1,z3,z4,z27,z5]),(0,[z0,z1,z3,z4,z5,z496,z8]),(0,[z0,z1,z3,z4,z497,z5,z8])],[(0,[z0,z1,z3,z498,z4,z5,z8]),(0,[z0,z1,z3,z4,z471,z5,z8]),(0,[z20,z0,z1,z3,z29,z4,z5]),(0,[z499,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z500,z6])],[(0,[z501,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z502,z3,z4,z5,z8]),(0,[z0,z1,z3,z97,z4,z5,z302]),(0,[z503,z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z353,z4,z221,z5,z8]),(0,[z0,z1,z3,z504,z4,z5,z8]),(0,[z0,z1,z261,z3,z29,z5,z8]),(0,[z0,z1,z36,z3,z4,z5,z24]),(0,[z0,z1,z339,z3,z4,z5,z24])],[(0,[z0,z1,z505,z3,z4,z5,z8]),(0,[z20,z0,z1,z3,z4,z108,z5]),(0,[z46,z0,z1,z3,z4,z5,z291]),(0,[z0,z1,z353,z3,z4,z5,z6]),(0,[z506,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z39,z8]),(0,[z0,z1,z266,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z154,z5,z8])],[(0,[z0,z1,z3,z507,z4,z5,z8]),(1,[z0,z1,z345,z4,z5,z8]),(0,[z20,z0,z84,z1,z3,z4,z5]),(0,[z508,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z509,z8]),(1,[z0,z1,z3,z4,z238,z8])]],
   [[(0,[z0,z510,z1,z3,z4,z5,z8]),(0,[z20,z0,z1,z3,z141,z4,z5]),(0,[z0,z1,z3,z4,z511,z5,z8]),(0,[z0,z1,z3,z4,z5,z512,z8])],[(0,[z20,z0,z1,z261,z3,z4,z5]),(0,[z20,z46,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z513,z8]),(0,[z0,z1,z3,z4,z5,z18,z24]),(0,[z0,z1,z377,z3,z141,z5,z8])],[(0,[z0,z1,z3,z4,z514,z5,z8]),(0,[z46,z0,z1,z3,z4,z381,z8]),(0,[z21,z0,z1,z3,z170,z5,z8]),(1,[z0,z175,z3,z23,z5,z8]),(0,[z0,z1,z515,z3,z4,z5,z8]),(0,[z0,z1,z3,z516,z4,z5,z8])],[(0,[z0,z517,z1,z3,z4,z5,z8]),(0,[z1,z61,z3,z91,z4,z5,z8]),(0,[z0,z518,z1,z3,z4,z5,z8]),(1,[z79,z1,z3,z4,z108,z8]),(0,[z79,z0,z1,z47,z3,z4,z8]),(1,[z0,z1,z3,z4,z5,z337]),(0,[z0,z1,z377,z3,z4,z101,z8])],[(0,[z0,z1,z3,z519,z4,z5,z8]),(0,[z58,z1,z3,z97,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z5,z8]),(0,[z46,z0,z1,z3,z4,z5,z24]),(0,[z520,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z377,z3,z4,z76,z8]),(0,[z0,z1,z3,z55,z4,z8,z56])],[(1,[z0,z1,z4,z450,z5,z8]),(0,[z20,z0,z1,z3,z4,z521,z5])],[(0,[z0,z1,z3,z522,z4,z5,z8]),(0,[z0,z1,z523,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z521,z5,z8]),(0,[z0,z1,z3,z4,z5,z18,z8])],[(0,[z0,z1,z3,z4,z5,z524,z8]),(0,[z525,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z232,z6]),(1,[z0,z1,z196,z3,z5,z211])]],
   [[(0,[z20,z0,z1,z353,z3,z4,z5])],[(0,[z46,z0,z1,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z5,z80]),(1,[z0,z1,z3,z4,z22,z8]),(0,[z526,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z47,z3,z4,z232,z8]),(0,[z0,z1,z527,z3,z4,z5,z8]),(0,[z0,z1,z3,z55,z4,z137,z8]),(0,[z0,z1,z3,z4,z528,z5,z8])],[(0,[z0,z1,z3,z4,z5,z529,z8]),(0,[z530,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z352,z8]),(0,[z46,z0,z1,z3,z4,z154,z5]),(0,[z0,z1,z3,z4,z531,z5,z8]),(0,[z0,z71,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z5,z532,z8]),(0,[z0,z1,z3,z4,z533,z5,z8]),(0,[z46,z0,z1,z266,z3,z4,z5]),(0,[z0,z1,z534,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z221,z5,z8]),(0,[z183,z0,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z5,z274,z8]),(1,[z0,z1,z3,z4,z5,z352]),(0,[z0,z1,z3,z160,z4,z5,z8]),(0,[z0,z1,z345,z4,z5,z38,z8]),(0,[z0,z1,z3,z4,z5,z535,z8]),(0,[z79,z1,z3,z4,z108,z5,z8]),(0,[z0,z536,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z357,z4,z24]),(0,[z0,z1,z3,z3,z4,z5,z6])],[(0,[z46,z60,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z537,z8]),(0,[z538,z0,z1,z3,z4,z5,z8])],[(0,[z77,z59,z1,z3,z4,z5,z8]),(0,[z0,z143,z1,z3,z4,z5,z24]),(0,[z128,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z539,z3,z4,z5,z8]),(0,[z0,z1,z540,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z541]),(0,[z0,z1,z3,z4,z5,z542,z8]),(0,[z0,z1,z3,z543,z4,z5,z8])]],
   [[(1,[z0,z1,z47,z4,z154,z8]),(0,[z0,z1,z3,z4,z5,z544,z8])],[(0,[z0,z1,z3,z545,z4,z5,z8]),(0,[z0,z1,z546,z3,z91,z4,z8]),(0,[z0,z1,z3,z4,z38,z76,z8]),(0,[z20,z0,z1,z3,z179,z4,z5]),(0,[z0,z1,z3,z4,z5,z126,z8]),(0,[z0,z1,z3,z4,z547,z5,z8]),(0,[z0,z1,z3,z4,z5,z548,z8]),(0,[z183,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z549,z3,z4,z5,z8]),(1,[z0,z1,z386,z3,z4,z5]),(0,[z20,z0,z1,z3,z4,z5,z211]),(1,[z0,z1,z266,z4,z41,z8]),(0,[z240,z0,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z550,z4,z5,z8]),(0,[z0,z1,z551,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z333,z5,z8]),(0,[z46,z0,z1,z36,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z552]),(0,[z0,z1,z3,z4,z154,z5,z6])],[(0,[z0,z143,z1,z3,z4,z5,z8]),(1,[z0,z1,z82,z4,z5,z8]),(0,[z0,z1,z3,z4,z553,z5,z8]),(0,[z0,z1,z554,z3,z4,z5,z8]),(0,[z555,z0,z1,z3,z4,z5,z8]),(0,[z0,z556,z1,z3,z4,z5,z8])],[(0,[z557,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z558,z8]),(0,[z152,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z559,z3,z4,z5,z6])],[(0,[z46,z0,z1,z3,z97,z4,z5]),(0,[z0,z1,z3,z4,z5,z560,z8]),(0,[z0,z1,z47,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z561,z5,z8])],[(1,[z0,z1,z3,z519,z5,z8]),(0,[z240,z0,z1,z3,z4,z5,z8]),(0,[z60,z0,z1,z4,z154,z5,z8]),(0,[z0,z1,z3,z4,z5,z562,z8]),(0,[z0,z1,z3,z4,z5,z563,z8]),(0,[z0,z1,z3,z564,z4,z5,z8]),(0,[z0,z1,z3,z565,z4,z5,z8]),(0,[z0,z1,z47,z3,z55,z4,z8])]],
   [[],[(0,[z566,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z218,z8]),(0,[z128,z0,z1,z3,z4,z5,z6]),(0,[z46,z0,z1,z3,z4,z5,z38]),(0,[z567,z46,z0,z1,z3,z4,z5]),(0,[z0,z175,z1,z3,z4,z5,z6])],[(0,[z46,z0,z1,z3,z91,z4,z5]),(0,[z20,z1,z3,z4,z5,z8,z80]),(0,[z20,z0,z1,z3,z4,z5,z24]),(0,[z568,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z569,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z211])],[(1,[z77,z2,z3,z4,z5,z8]),(0,[z0,z1,z3,z570,z4,z5,z8]),(0,[z0,z1,z571,z3,z4,z5,z8]),(0,[z0,z572,z1,z3,z4,z5,z8]),(0,[z0,z1,z29,z4,z221,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z398]),(0,[z0,z1,z47,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z573,z5,z8]),(0,[z0,z1,z3,z141,z101,z5,z8])],[(0,[z240,z60,z0,z1,z3,z4,z5]),(0,[z20,z0,z1,z3,z4,z5,z235]),(0,[z20,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z24,z56])],[(0,[z20,z13,z0,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z34]),(0,[z574,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z575,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z576,z5,z8])],[(0,[z0,z1,z577,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z578,z8]),(0,[z0,z1,z579,z3,z4,z5,z8]),(0,[z0,z1,z527,z3,z4,z5,z6]),(0,[z580,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z581,z4,z5,z8]),(0,[z0,z1,z582,z3,z4,z5,z8])],[(0,[z79,z0,z1,z3,z4,z38,z8]),(0,[z20,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z40]),(0,[z0,z1,z3,z4,z5,z8,z583])]],
   [[(0,[z0,z367,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z584]),(0,[z557,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z585,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z586,z8]),(0,[z0,z1,z3,z587,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z588,z8]),(0,[z1,z3,z4,z5,z126,z8,z80]),(0,[z0,z1,z3,z166,z4,z5,z6]),(0,[z0,z1,z3,z4,z27,z5,z24]),(0,[z0,z1,z266,z3,z4,z41,z8]),(0,[z589,z0,z1,z3,z4,z5,z8])],[(0,[z20,z0,z1,z266,z3,z4,z5]),(0,[z0,z84,z1,z3,z4,z294,z8]),(0,[z0,z1,z3,z4,z5,z6,z24]),(0,[z0,z1,z3,z4,z137,z5,z232])],[(0,[z0,z1,z590,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z333,z5,z38]),(0,[z0,z1,z3,z4,z27,z108,z8]),(0,[z591,z0,z1,z3,z4,z5,z8])],[(0,[z20,z60,z0,z1,z3,z4,z5]),(0,[z13,z46,z0,z1,z3,z4,z5]),(0,[z0,z81,z1,z353,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z18])],[(0,[z592,z0,z1,z3,z4,z5,z8]),(0,[z162,z0,z1,z266,z4,z5,z8]),(0,[z0,z1,z546,z3,z4,z5,z8]),(0,[z128,z0,z1,z266,z3,z4,z8]),(0,[z0,z1,z3,z593,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z430]),(1,[z31,z0,z1,z4,z5,z6])],[(0,[z60,z0,z1,z3,z4,z5,z6]),(0,[z128,z1,z3,z4,z5,z38,z8]),(0,[z46,z0,z1,z3,z4,z5,z75]),(0,[z0,z1,z3,z4,z27,z5,z8]),(0,[z136,z0,z1,z3,z4,z5,z8]),(0,[z594,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z595,z8]),(0,[z58,z13,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z149,z8]),(0,[z0,z1,z353,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z596,z8]),(0,[z0,z1,z3,z4,z597,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z8]),(0,[z0,z1,z3,z4,z5,z598,z8])]],
   [[(0,[z0,z1,z3,z4,z5,z8,z599])],[(0,[z600,z0,z1,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z29,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z601]),(0,[z0,z1,z47,z266,z4,z5,z8]),(0,[z0,z1,z47,z3,z4,z5,z289])],[(0,[z46,z0,z1,z3,z55,z4,z5]),(0,[z0,z1,z3,z4,z5,z602,z8]),(0,[z0,z1,z3,z4,z5,z500,z8]),(0,[z0,z1,z3,z357,z4,z5,z24])],[(0,[z0,z1,z603,z3,z4,z5,z8]),(0,[z0,z1,z3,z604,z4,z5,z8]),(0,[z0,z84,z353,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z605,z8]),(0,[z0,z1,z261,z4,z221,z5,z8])],[(0,[z162,z0,z1,z3,z4,z198,z8]),(0,[z0,z1,z502,z3,z91,z4,z8]),(0,[z20,z0,z1,z3,z97,z4,z5]),(1,[z0,z1,z3,z412,z4,z5]),(0,[z46,z0,z84,z1,z3,z4,z5]),(0,[z0,z1,z353,z3,z4,z5,z8]),(0,[z0,z1,z261,z3,z4,z5,z6]),(0,[z0,z1,z28,z3,z4,z5,z216]),(0,[z0,z1,z377,z3,z4,z5,z6])],[(0,[z20,z0,z1,z3,z17,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z63]),(0,[z0,z1,z261,z3,z221,z5,z8]),(0,[z0,z1,z3,z29,z4,z5,z24])],[(0,[z0,z1,z3,z4,z5,z606,z8]),(0,[z13,z0,z1,z3,z4,z5,z6]),(0,[z607,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z78,z8])],[(0,[z13,z0,z1,z3,z97,z5,z8]),(0,[z487,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z608,z5,z8]),(0,[z46,z0,z175,z1,z3,z4,z5]),(0,[z0,z1,z3,z609,z4,z5,z8]),(0,[z0,z1,z610,z3,z4,z5,z8]),(1,[z183,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z357,z4,z5,z8])]],
   [[(0,[z20,z0,z1,z3,z91,z4,z5]),(1,[z0,z1,z3,z4,z5,z98]),(0,[z0,z1,z3,z4,z611,z5,z8]),(0,[z612,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z232,z24])],[(0,[z0,z1,z3,z4,z5,z363,z8]),(0,[z46,z0,z1,z377,z3,z4,z5]),(0,[z176,z0,z1,z3,z4,z5,z63])],[(0,[z46,z0,z26,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z613]),(0,[z0,z1,z614,z3,z4,z5,z8]),(0,[z0,z1,z3,z55,z4,z5,z232])],[(1,[z0,z1,z3,z4,z471,z8]),(0,[z0,z1,z3,z4,z5,z8,z615]),(0,[z0,z1,z616,z3,z4,z5,z8]),(0,[z0,z1,z353,z3,z4,z5,z269]),(0,[z0,z1,z3,z4,z617,z5,z8])],[(0,[z58,z0,z1,z3,z14,z5,z8]),(0,[z0,z618,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z331]),(0,[z0,z1,z619,z3,z4,z5,z8]),(0,[z0,z1,z620,z3,z4,z5,z8])],[(1,[z95,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z353,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z621]),(0,[z622,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z232,z8])],[(0,[z162,z0,z1,z91,z4,z5,z8]),(0,[z20,z0,z1,z3,z623,z4,z5]),(1,[z46,z0,z1,z3,z4,z291]),(1,[z46,z0,z1,z3,z4,z381]),(0,[z0,z1,z3,z624,z4,z5,z8]),(0,[z0,z175,z3,z23,z4,z5,z8]),(0,[z0,z1,z3,z625,z4,z5,z8]),(0,[z0,z1,z3,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z626,z5,z8]),(1,[z0,z1,z377,z3,z76,z8])],[(1,[z0,z1,z3,z250,z4,z5]),(0,[z0,z1,z3,z4,z5,z337,z8])]],
   [[(0,[z0,z1,z3,z4,z38,z75,z8]),(0,[z0,z1,z3,z4,z627,z5,z8]),(0,[z0,z1,z3,z4,z5,z249,z8]),(1,[z0,z71,z3,z4,z5,z63])],[(0,[z0,z1,z3,z4,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z628,z8]),(0,[z46,z0,z1,z3,z4,z14,z5]),(0,[z503,z0,z1,z3,z4,z5,z8]),(0,[z79,z128,z1,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z370,z4,z5]),(0,[z0,z1,z3,z23,z4,z5,z6]),(0,[z176,z0,z71,z3,z4,z5,z8]),(0,[z0,z1,z28,z3,z4,z5,z398])],[(0,[z629,z0,z1,z3,z4,z5,z8]),(0,[z59,z46,z0,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z158]),(0,[z0,z1,z630,z3,z4,z5,z8]),(0,[z20,z0,z54,z1,z3,z4,z5]),(0,[z46,z0,z253,z1,z3,z4,z5]),(0,[z631,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z632,z4,z5,z8]),(0,[z0,z1,z3,z4,z633,z5,z8]),(0,[z0,z1,z3,z4,z5,z130,z8])],[(0,[z0,z1,z3,z3,z4,z5,z8]),(0,[z0,z1,z634,z3,z4,z5,z8]),(0,[z635,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z636,z4,z5,z8]),(0,[z136,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z637,z3,z4,z5,z8]),(0,[z0,z1,z638,z3,z4,z5,z8]),(0,[z13,z0,z1,z3,z4,z149,z8]),(0,[z46,z0,z1,z3,z4,z5,z126]),(0,[z0,z1,z3,z4,z5,z639,z8]),(0,[z0,z1,z3,z4,z5,z41,z6]),(0,[z0,z1,z3,z4,z154,z5,z24]),(0,[z0,z1,z3,z4,z5,z640,z8])],[(0,[z0,z1,z3,z4,z5,z8,z641]),(0,[z0,z1,z3,z4,z5,z287,z8]),(0,[z0,z1,z642,z3,z4,z5,z8]),(0,[z643,z0,z1,z3,z4,z5,z8])],[(0,[z1,z3,z97,z4,z14,z5,z8]),(0,[z20,z0,z1,z3,z4,z533,z5]),(0,[z123,z46,z0,z1,z3,z4,z5]),(0,[z0,z54,z1,z3,z4,z27,z8]),(0,[z0,z1,z3,z4,z644,z5,z8]),(0,[z0,z1,z47,z3,z4,z41,z8])],[(1,[z162,z20,z1,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z5,z211]),(0,[z645,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z266,z3,z4,z5,z430])]],
   [[(1,[z0,z1,z502,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z8,z646]),(0,[z20,z0,z1,z3,z55,z4,z5]),(0,[z0,z647,z1,z3,z4,z5,z8]),(0,[z0,z1,z196,z3,z5,z8,z211])],[(0,[z0,z1,z3,z4,z108,z5,z363]),(0,[z0,z1,z3,z4,z5,z388,z8]),(1,[z0,z1,z3,z4,z5,z249]),(0,[z0,z1,z3,z4,z5,z648,z8])],[(0,[z128,z0,z1,z3,z4,z5,z24]),(1,[z0,z1,z251,z4,z5,z8]),(0,[z0,z54,z1,z3,z4,z75,z8]),(1,[z0,z1,z4,z5,z6,z24])],[(0,[z0,z1,z3,z649,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z650]),(0,[z0,z54,z1,z3,z4,z5,z6]),(0,[z0,z1,z559,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z651,z8])],[(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z386,z3,z4,z14,z5]),(0,[z128,z0,z1,z3,z4,z108,z8]),(0,[z0,z1,z3,z4,z5,z652,z8]),(0,[z0,z653,z1,z3,z4,z5,z8]),(0,[z0,z1,z654,z3,z4,z5,z8]),(0,[z655,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z184]),(0,[z0,z1,z3,z4,z5,z656,z8])],[(0,[z59,z0,z2,z3,z4,z5,z8]),(0,[z0,z657,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z658]),(0,[z20,z0,z175,z1,z3,z4,z5]),(0,[z629,z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z659,z4,z5,z8])],[(0,[z20,z0,z1,z3,z4,z5,z76]),(0,[z660,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z232,z8,z56])],[(0,[z0,z1,z3,z4,z661,z5,z8]),(1,[z0,z1,z3,z4,z5,z200]),(0,[z128,z0,z1,z3,z4,z5,z8]),(0,[z20,z0,z1,z377,z3,z4,z5]),(0,[z662,z0,z1,z3,z4,z5,z8]),(0,[z0,z175,z1,z3,z4,z5,z8]),(0,[z663,z0,z1,z3,z4,z5,z8])]],
   [[(0,[z0,z664,z1,z3,z4,z5,z8]),(0,[z20,z0,z26,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z291,z8])],[(0,[z46,z0,z1,z3,z4,z5,z18]),(0,[z0,z81,z1,z3,z4,z5,z181]),(1,[z0,z1,z3,z4,z294,z8]),(0,[z0,z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z665,z3,z4,z5,z8]),(1,[z183,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z55,z4,z56])],[(0,[z0,z84,z2,z3,z4,z5,z8]),(0,[z0,z1,z3,z166,z4,z5,z24]),(0,[z0,z1,z3,z666,z4,z5,z8]),(0,[z0,z1,z3,z4,z221,z5,z24]),(0,[z183,z1,z3,z4,z5,z8,z24])],[(0,[z667,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z8]),(1,[z0,z163,z3,z4,z5,z8]),(0,[z486,z0,z1,z3,z91,z4,z5]),(0,[z0,z1,z3,z623,z4,z5,z8]),(0,[z0,z1,z3,z668,z4,z5,z8]),(0,[z0,z1,z3,z4,z626,z5,z6]),(0,[z669,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z8,z670])],[(1,[z0,z1,z3,z173,z5,z8]),(0,[z162,z0,z1,z3,z519,z5,z8]),(0,[z671,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z402]),(0,[z0,z1,z3,z4,z5,z194,z8])],[(1,[z217,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z672,z8]),(0,[z31,z0,z1,z4,z5,z6,z8])],[(0,[z60,z0,z1,z3,z4,z5,z24]),(0,[z20,z0,z1,z3,z4,z14,z5]),(0,[z0,z1,z3,z4,z5,z126,z24]),(0,[z0,z1,z3,z166,z4,z5,z8]),(0,[z0,z1,z3,z673,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z18,z63]),(0,[z0,z1,z3,z29,z4,z39,z8])]],
   [[(0,[z46,z0,z1,z47,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z8,z674]),(0,[z0,z1,z3,z675,z4,z5,z8]),(0,[z0,z1,z3,z29,z4,z238,z8]),(0,[z0,z1,z3,z4,z5,z8,z56])],[(0,[z567,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z108,z5,z34]),(0,[z0,z1,z3,z676,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z413]),(0,[z0,z1,z3,z4,z5,z677,z8])],[(0,[z0,z1,z4,z450,z5,z38,z8]),(0,[z20,z0,z1,z3,z4,z5,z126]),(0,[z20,z0,z1,z3,z4,z137,z5]),(0,[z0,z1,z3,z412,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z5,z63]),(0,[z0,z1,z3,z678,z4,z5,z8]),(1,[z0,z1,z3,z4,z85,z8]),(0,[z0,z1,z3,z4,z679,z5,z8]),(0,[z0,z1,z3,z4,z680,z5,z8])],[(0,[z0,z1,z251,z3,z4,z5,z8]),(0,[z0,z1,z3,z141,z4,z76,z8])],[(0,[z60,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z287]),(0,[z46,z0,z1,z3,z4,z547,z5]),(1,[z0,z1,z3,z4,z381,z8]),(0,[z681,z0,z1,z3,z4,z5,z8]),(0,[z147,z0,z1,z3,z4,z5,z6]),(0,[z682,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z38,z232,z8]),(0,[z0,z1,z683,z3,z4,z5,z8]),(0,[z0,z3,z4,z27,z5,z75,z8]),(0,[z0,z1,z261,z3,z4,z5,z24]),(0,[z0,z1,z377,z3,z4,z5,z24])],[(0,[z684,z0,z1,z3,z4,z5,z8])],[(0,[z685,z0,z1,z3,z4,z5,z8]),(0,[z13,z0,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z29,z14,z5,z8]),(0,[z0,z1,z3,z4,z5,z38,z6]),(0,[z0,z686,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z17,z4,z5,z211]),(0,[z0,z1,z3,z4,z137,z5,z56])]],
   [[(0,[z0,z687,z1,z3,z4,z5,z8]),(0,[z0,z1,z688,z3,z4,z5,z8]),(0,[z0,z1,z689,z3,z4,z5,z8]),(1,[z0,z54,z3,z4,z75,z8]),(1,[z0,z1,z3,z4,z5,z257]),(0,[z0,z1,z3,z4,z5,z690,z8])],[(0,[z0,z1,z691,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z170,z5,z6]),(0,[z0,z692,z1,z3,z4,z5,z8]),(0,[z0,z71,z1,z3,z4,z5,z63]),(0,[z0,z1,z3,z4,z5,z24,z199]),(0,[z0,z1,z3,z4,z5,z8,z693]),(0,[z0,z1,z3,z694,z4,z5,z8])],[(1,[z486,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z259,z3,z4,z5]),(0,[z46,z0,z1,z3,z17,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z126]),(0,[z0,z1,z261,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z695,z5,z8]),(0,[z0,z1,z3,z696,z4,z5,z8]),(0,[z0,z1,z377,z3,z4,z5,z8])],[],[(0,[z0,z697,z1,z3,z4,z5,z8]),(0,[z13,z0,z1,z3,z4,z5,z8]),(1,[z58,z1,z3,z97,z5,z8]),(0,[z53,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z698,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z699,z5,z8]),(0,[z0,z700,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z701,z5,z8]),(0,[z20,z128,z0,z1,z3,z4,z5])],[(0,[z20,z59,z0,z1,z3,z4,z5]),(1,[z0,z1,z546,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z702,z8]),(0,[z0,z26,z3,z4,z27,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z448])],[(0,[z0,z1,z3,z4,z703,z5,z8]),(0,[z0,z1,z704,z3,z4,z5,z8]),(0,[z0,z1,z353,z3,z4,z5,z388]),(0,[z0,z1,z3,z17,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z705,z8]),(0,[z0,z1,z706,z3,z4,z5,z8])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z59,z143,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z707]),(0,[z0,z1,z708,z4,z5,z8]),(0,[z344,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z709,z8])],[],[(0,[z152,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z710]),(0,[z0,z1,z502,z3,z4,z24]),(0,[z0,z1,z3,z4,z711,z8]),(0,[z183,z1,z3,z4,z27,z5])],[(0,[z0,z712,z1,z3,z4,z5])],[(0,[z0,z1,z251,z4,z5,z24])],[(0,[z295,z1,z3,z4,z5,z6])],[(0,[z0,z213,z3,z173,z5,z8]),(0,[z0,z1,z3,z4,z5,z713])],[(0,[z46,z0,z1,z502,z3,z4]),(0,[z0,z1,z3,z4,z714,z5]),(0,[z0,z81,z166,z4,z5,z181]),(0,[z0,z1,z4,z5,z6,z153])],[(0,[z58,z1,z3,z545,z5,z8]),(0,[z13,z1,z3,z14,z149,z8]),(0,[z79,z1,z3,z4,z715,z8]),(0,[z46,z0,z1,z3,z4,z716]),(0,[z0,z1,z3,z4,z5,z249]),(0,[z0,z1,z3,z4,z5,z717])],[(0,[z0,z1,z3,z4,z5,z718]),(0,[z719,z0,z1,z3,z4,z5]),(0,[z720,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z721]),(0,[z0,z1,z3,z4,z722,z8]),(0,[z0,z1,z723,z4,z5,z8]),(0,[z0,z1,z675,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z24])],[(0,[z0,z1,z3,z4,z291,z24]),(0,[z0,z1,z724,z4,z5,z8])],[(0,[z162,z0,z1,z412,z4,z5]),(0,[z0,z1,z3,z4,z5,z725]),(0,[z20,z0,z726,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z727]),(0,[z0,z1,z261,z728,z5,z8])],[(0,[z0,z1,z3,z729,z5,z8]),(0,[z46,z1,z3,z4,z5,z282])],[(0,[z0,z1,z3,z4,z5,z730]),(0,[z240,z0,z1,z3,z4,z711]),(0,[z0,z1,z28,z179,z4,z5]),(0,[z46,z0,z1,z3,z4,z731]),(0,[z0,z1,z732,z4,z5,z8]),(0,[z0,z1,z3,z357,z4,z194]),(0,[z183,z1,z3,z4,z5,z18])],[(0,[z0,z1,z3,z4,z5,z200]),(0,[z1,z36,z4,z5,z346,z24])],[]],
   [[(0,[z183,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z733,z4,z5]),(0,[z589,z1,z3,z4,z38,z8]),(0,[z734,z183,z1,z3,z4,z5]),(0,[z0,z1,z3,z357,z4,z232]),(0,[z0,z1,z3,z55,z4,z56])],[(0,[z46,z0,z1,z3,z4,z85]),(0,[z46,z0,z1,z28,z29,z5]),(0,[z735,z1,z3,z4,z5,z8])],[(0,[z0,z163,z3,z4,z5,z8])],[(0,[z0,z1,z3,z55,z4,z291]),(0,[z0,z1,z3,z4,z5,z736]),(0,[z737,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z738,z4,z5]),(0,[z0,z1,z3,z4,z739,z5]),(0,[z0,z1,z3,z4,z85,z24]),(0,[z183,z176,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z740]),(0,[z741,z0,z1,z3,z4,z5]),(0,[z0,z230,z3,z4,z5,z263])],[],[(0,[z162,z1,z91,z173,z5,z8])],[(0,[z0,z1,z3,z4,z5,z742]),(0,[z21,z183,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z743])],[],[(0,[z0,z1,z3,z4,z8,z744]),(0,[z62,z0,z1,z3,z533,z5]),(0,[z0,z1,z3,z745,z4,z5]),(0,[z295,z1,z251,z4,z5,z8]),(0,[z0,z54,z3,z4,z75,z24]),(1,[z0,z1,z728,z5,z8]),(0,[z746,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z381,z8]),(0,[z0,z1,z3,z55,z4,z257])],[(0,[z0,z1,z3,z747,z4,z5]),(0,[z0,z1,z748,z4,z5,z8]),(0,[z20,z589,z1,z3,z4,z5]),(0,[z557,z0,z1,z3,z370,z5]),(0,[z0,z84,z353,z4,z5,z6]),(0,[z0,z1,z632,z4,z5,z24]),(0,[z1,z3,z4,z5,z749,z24]),(0,[z0,z1,z3,z4,z750,z24])],[(0,[z0,z1,z3,z4,z5,z24])],[(0,[z58,z1,z3,z97,z5,z24]),(0,[z183,z1,z3,z17,z4,z5]),(0,[z0,z1,z3,z4,z5,z751])],[(0,[z183,z1,z3,z4,z5,z290]),(0,[z0,z1,z3,z4,z5,z752])]],
   [[(0,[z0,z1,z3,z4,z5,z753]),(0,[z0,z1,z546,z3,z4,z24]),(0,[z20,z0,z1,z3,z4,z754]),(0,[z0,z1,z3,z4,z5,z755])],[(0,[z0,z163,z3,z4,z5,z290]),(0,[z183,z1,z3,z91,z4,z5]),(0,[z60,z1,z4,z573,z5,z8]),(0,[z20,z0,z1,z3,z141,z101]),(0,[z0,z353,z756,z4,z5,z8])],[(0,[z0,z1,z3,z4,z757,z8]),(0,[z0,z1,z3,z4,z758,z8]),(0,[z0,z1,z3,z4,z759,z8])],[(0,[z0,z1,z3,z4,z5,z760]),(0,[z0,z1,z47,z4,z102,z8]),(0,[z0,z1,z4,z194,z6,z24]),(0,[z0,z1,z3,z4,z5,z761])],[(0,[z46,z1,z3,z4,z291,z126]),(0,[z0,z1,z3,z4,z5,z762])],[(0,[z0,z1,z3,z4,z5,z763]),(0,[z0,z1,z3,z764,z4,z5]),(0,[z0,z1,z261,z221,z5,z8]),(0,[z0,z1,z3,z4,z194,z257])],[(0,[z0,z1,z3,z4,z5,z765])],[(0,[z0,z1,z3,z5,z766,z24])],[(0,[z46,z190,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z72,z717]),(0,[z176,z0,z3,z4,z5,z78]),(0,[z0,z1,z4,z154,z758,z8])],[(0,[z20,z0,z1,z3,z4,z5]),(0,[z0,z1,z767,z4,z5,z8]),(0,[z0,z213,z3,z4,z5,z6]),(0,[z0,z1,z3,z173,z198,z8]),(0,[z0,z1,z3,z4,z5,z269]),(0,[z0,z768,z3,z4,z5,z8])],[(0,[z0,z769,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z770])],[(0,[z0,z1,z3,z4,z274,z8]),(0,[z0,z1,z771,z4,z5,z8]),(0,[z0,z1,z3,z4,z772,z8]),(0,[z1,z61,z773,z4,z5,z8]),(0,[z0,z1,z47,z409,z4,z8]),(0,[z20,z1,z3,z4,z573,z5]),(0,[z0,z1,z28,z29,z5,z216]),(0,[z0,z1,z3,z4,z8,z774])],[(0,[z46,z0,z1,z3,z4,z775]),(0,[z0,z1,z3,z776,z4,z8])],[(0,[z0,z1,z3,z4,z777,z24])],[(0,[z0,z1,z778,z3,z4,z8]),(0,[z0,z163,z3,z4,z5,z193]),(0,[z0,z779,z3,z4,z5,z8]),(0,[z0,z1,z179,z4,z221,z5])],[(0,[z0,z780,z3,z4,z5,z8]),(0,[z20,z0,z84,z353,z4,z5]),(0,[z0,z1,z3,z4,z781,z8])]],
   [[(0,[z217,z136,z1,z3,z4,z5]),(0,[z0,z3,z756,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z289]),(0,[z0,z1,z3,z309,z5,z18])],[(0,[z0,z1,z266,z4,z218,z8]),(0,[z0,z1,z3,z4,z5,z782]),(0,[z20,z0,z1,z3,z4,z22])],[(0,[z0,z1,z3,z4,z218,z290]),(0,[z0,z1,z3,z4,z5,z783]),(0,[z1,z3,z4,z715,z38,z8]),(0,[z784,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z785])],[(0,[z295,z1,z3,z4,z5,z8]),(0,[z0,z1,z786,z3,z4,z5])],[(0,[z787,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z5,z788]),(0,[z21,z0,z3,z170,z5,z140])],[(0,[z0,z1,z3,z519,z198,z8]),(0,[z183,z175,z1,z3,z4,z5])],[],[(0,[z20,z0,z780,z3,z4,z5]),(0,[z183,z1,z377,z3,z4,z5])],[(0,[z0,z1,z3,z789,z5,z8]),(0,[z183,z26,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z790,z8]),(0,[z162,z1,z91,z4,z5,z6]),(0,[z20,z0,z1,z3,z4,z328]),(0,[z791,z1,z3,z4,z5,z8]),(0,[z792,z1,z3,z4,z5,z8]),(0,[z0,z1,z266,z4,z157,z8])],[(0,[z0,z1,z3,z793,z4,z5]),(0,[z162,z1,z3,z179,z4,z5])],[(0,[z0,z1,z3,z4,z794,z8]),(0,[z240,z0,z1,z412,z4,z5]),(0,[z0,z1,z3,z795,z4,z5])],[(0,[z0,z796,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z797]),(0,[z0,z1,z3,z4,z194,z6])],[(0,[z0,z1,z3,z4,z328,z140]),(0,[z21,z0,z3,z170,z5,z249])],[(0,[z0,z1,z3,z623,z5,z18])]],
   [[(0,[z162,z217,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z149,z24]),(0,[z46,z0,z81,z166,z4,z5])],[(0,[z46,z0,z1,z3,z173,z5]),(0,[z0,z1,z345,z4,z218,z8]),(0,[z0,z1,z3,z4,z5,z302]),(0,[z0,z84,z353,z4,z85,z8]),(0,[z152,z1,z3,z4,z328,z8]),(0,[z0,z1,z3,z4,z798,z8])],[(0,[z0,z1,z3,z4,z799,z8]),(0,[z0,z1,z124,z4,z5,z6])],[(0,[z20,z1,z3,z4,z5,z80]),(0,[z0,z1,z3,z4,z800,z8])],[(0,[z0,z1,z3,z4,z5,z801]),(0,[z20,z0,z26,z3,z4,z27]),(0,[z802,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z803,z8]),(0,[z0,z1,z3,z4,z804,z8]),(0,[z0,z1,z3,z357,z4,z56])],[(0,[z0,z1,z179,z166,z4,z5]),(0,[z0,z1,z3,z4,z805,z24])],[(0,[z0,z1,z3,z806,z5,z8]),(0,[z20,z0,z1,z3,z4,z274]),(0,[z0,z1,z3,z807,z5,z8]),(0,[z0,z1,z3,z4,z328,z249])],[(0,[z20,z499,z1,z3,z4,z5]),(0,[z0,z1,z808,z3,z4,z5]),(0,[z0,z1,z809,z3,z4,z5])],[],[(0,[z162,z1,z502,z91,z4,z8]),(0,[z0,z1,z317,z4,z5,z6]),(0,[z123,z0,z1,z3,z547,z5]),(0,[z0,z84,z353,z4,z5,z8]),(0,[z183,z1,z339,z3,z4,z5])],[(0,[z0,z1,z810,z3,z5,z8]),(0,[z486,z0,z1,z546,z3,z4]),(0,[z183,z46,z1,z3,z4,z5]),(0,[z0,z811,z3,z4,z5,z8])],[(0,[z1,z812,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z346,z8]),(0,[z20,z0,z1,z3,z357,z4])],[(0,[z0,z1,z3,z4,z813,z8]),(0,[z814,z183,z1,z3,z4,z5])],[(0,[z0,z815,z3,z4,z5,z8]),(0,[z1,z61,z3,z250,z4,z5]),(0,[z60,z1,z61,z4,z5,z287]),(0,[z0,z1,z3,z370,z5,z211]),(0,[z0,z1,z3,z4,z816,z8]),(0,[z0,z1,z47,z4,z154,z257])],[(0,[z0,z1,z3,z4,z817,z8]),(0,[z46,z152,z1,z3,z4,z5]),(1,[z0,z1,z3,z5,z818])]],
   [[(0,[z819,z0,z1,z3,z4,z5]),(0,[z820,z0,z1,z3,z4,z5])],[(0,[z0,z1,z90,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z821]),(0,[z0,z1,z3,z4,z5,z822]),(0,[z0,z1,z3,z4,z5,z823]),(0,[z20,z0,z1,z82,z4,z5])],[],[(0,[z77,z95,z2,z3,z4,z5]),(0,[z21,z0,z3,z170,z5,z24]),(0,[z0,z1,z3,z4,z5,z824])],[(0,[z0,z1,z3,z4,z825,z8]),(0,[z0,z1,z3,z4,z5,z826]),(0,[z183,z1,z3,z4,z194,z24])],[(0,[z0,z1,z827,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z828]),(0,[z0,z1,z3,z4,z5,z818])],[(0,[z0,z1,z3,z4,z829,z8]),(0,[z20,z0,z213,z3,z4,z5])],[(0,[z0,z213,z3,z4,z5,z8]),(0,[z46,z0,z1,z546,z3,z4]),(0,[z0,z1,z3,z179,z4,z5]),(0,[z20,z295,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z830,z8]),(0,[z0,z1,z3,z5,z8,z831]),(0,[z0,z1,z3,z4,z5,z832])],[(0,[z162,z0,z1,z502,z4,z8]),(0,[z0,z1,z339,z3,z5,z211])],[(0,[z0,z1,z3,z4,z5,z833]),(0,[z0,z1,z3,z4,z5,z834]),(0,[z13,z1,z3,z160,z14,z5]),(0,[z0,z71,z3,z4,z5,z717]),(0,[z183,z1,z3,z4,z5,z63])],[(0,[z0,z1,z3,z4,z5,z835]),(0,[z284,z46,z1,z3,z4,z5]),(0,[z629,z0,z253,z3,z4,z5]),(0,[z0,z1,z836,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z837])],[],[(0,[z162,z20,z1,z3,z4,z218]),(0,[z1,z3,z4,z5,z8,z838]),(0,[z0,z1,z3,z4,z5,z839])],[(0,[z0,z1,z840,z4,z5,z8]),(0,[z0,z1,z3,z4,z715,z8]),(0,[z0,z841,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z6,z744]),(0,[z0,z1,z3,z4,z5,z842])],[(0,[z0,z1,z3,z4,z775,z8]),(0,[z0,z1,z3,z55,z4,z235]),(0,[z46,z0,z843,z3,z4,z5])],[(0,[z240,z0,z1,z3,z4,z775]),(0,[z0,z1,z3,z4,z844,z8]),(0,[z0,z1,z3,z141,z845,z8])]],
   [[(0,[z20,z0,z1,z3,z4,z149]),(0,[z0,z1,z345,z4,z154,z8]),(0,[z0,z1,z3,z4,z5,z846])],[(0,[z0,z1,z3,z4,z5,z847]),(0,[z0,z1,z3,z4,z5,z848]),(0,[z20,z0,z1,z840,z4,z5])],[(0,[z0,z1,z3,z4,z5,z849]),(0,[z20,z0,z1,z377,z3,z76]),(0,[z20,z1,z3,z4,z5,z346]),(0,[z0,z1,z3,z4,z5,z850]),(0,[z0,z1,z3,z4,z5,z851]),(0,[z0,z3,z4,z5,z8,z852]),(0,[z0,z1,z853,z4,z5,z8])],[(0,[z20,z0,z1,z854,z4,z5]),(0,[z0,z81,z166,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z430]),(0,[z183,z1,z36,z4,z5,z24])],[],[(0,[z162,z20,z1,z91,z4,z5]),(0,[z0,z1,z3,z4,z5,z855])],[(0,[z0,z213,z3,z4,z5,z290]),(0,[z20,z58,z1,z3,z97,z5]),(0,[z0,z1,z47,z4,z154,z6]),(0,[z1,z3,z4,z194,z346,z8])],[],[(0,[z162,z1,z91,z4,z5,z8]),(0,[z162,z1,z546,z91,z4,z8]),(0,[z0,z1,z3,z4,z5,z856]),(0,[z46,z0,z1,z3,z4,z294]),(0,[z0,z1,z857,z3,z4,z5]),(0,[z183,z858,z1,z3,z4,z5]),(0,[z0,z1,z3,z357,z4,z6])],[(0,[z162,z20,z1,z3,z4,z198]),(0,[z79,z46,z1,z3,z4,z108])],[(0,[z60,z1,z61,z4,z5,z6]),(0,[z183,z1,z3,z4,z5,z72])],[(0,[z0,z1,z3,z4,z5,z859]),(0,[z0,z1,z3,z4,z194,z8])],[(0,[z136,z1,z3,z91,z4,z5]),(0,[z0,z1,z3,z4,z5,z860]),(0,[z0,z1,z3,z17,z5,z818])],[],[(0,[z0,z3,z4,z27,z861,z8]),(0,[z862,z1,z3,z4,z5,z8])],[(0,[z863,z0,z1,z3,z4,z5]),(0,[z0,z864,z3,z4,z5,z8]),(0,[z0,z1,z345,z4,z101,z8]),(0,[z865,z0,z1,z3,z4,z5]),(0,[z20,z1,z3,z4,z5,z442]),(1,[z0,z756,z4,z5,z8])]],
   [[(0,[z0,z1,z3,z866,z5,z8]),(0,[z1,z3,z773,z4,z5,z8]),(0,[z0,z1,z689,z4,z154,z8]),(0,[z867,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z293,z24]),(0,[z0,z1,z478,z4,z5,z24])],[(0,[z58,z1,z3,z97,z5,z98]),(0,[z20,z1,z105,z3,z4,z5]),(0,[z305,z46,z1,z3,z4,z5]),(0,[z295,z1,z3,z4,z328,z8]),(0,[z0,z1,z3,z141,z101,z8])],[(0,[z0,z213,z3,z4,z5,z193]),(0,[z868,z0,z1,z3,z4,z5]),(0,[z0,z1,z266,z4,z758,z8])],[(0,[z0,z1,z869,z3,z5,z8]),(0,[z20,z692,z1,z3,z4,z5]),(0,[z0,z1,z165,z4,z5,z24]),(0,[z183,z81,z1,z3,z4,z5]),(0,[z0,z1,z870,z3,z4,z5]),(0,[z0,z1,z871,z4,z5,z8])],[(0,[z20,z0,z54,z3,z4,z75]),(0,[z0,z338,z353,z4,z5,z8])],[(0,[z0,z1,z3,z872,z4,z5]),(0,[z20,z0,z1,z873,z3,z4]),(0,[z0,z1,z115,z4,z5,z6])],[(0,[z0,z1,z3,z874,z4,z5]),(0,[z1,z3,z357,z4,z346,z8])],[(0,[z0,z875,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z876,z5]),(0,[z0,z1,z3,z4,z877,z8]),(0,[z183,z1,z28,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z878]),(0,[z0,z1,z3,z4,z88,z194])],[(0,[z0,z1,z3,z4,z198,z8]),(0,[z0,z1,z3,z4,z5,z879]),(0,[z0,z1,z3,z4,z5,z880]),(0,[z46,z1,z3,z4,z5,z126]),(0,[z46,z1,z3,z4,z5,z828]),(0,[z881,z1,z3,z4,z5,z8]),(0,[z183,z1,z3,z4,z5,z76])],[(0,[z20,z0,z1,z345,z4,z5]),(0,[z20,z635,z1,z3,z4,z5]),(0,[z882,z0,z1,z3,z4,z5]),(0,[z883,z0,z1,z3,z4,z5])],[(0,[z162,z1,z773,z4,z5,z8]),(0,[z0,z1,z4,z333,z450,z5]),(0,[z0,z1,z3,z4,z5,z884]),(0,[z0,z1,z3,z4,z232,z774])],[(0,[z20,z0,z1,z3,z885,z5]),(0,[z183,z1,z3,z4,z5,z413])],[(0,[z0,z1,z3,z886,z5,z8]),(0,[z183,z58,z1,z3,z4,z5]),(0,[z128,z1,z3,z117,z4,z38]),(0,[z0,z1,z887,z4,z5,z8])],[(0,[z46,z0,z1,z3,z4,z194]),(0,[z183,z1,z3,z357,z4,z24])]],
   [[(0,[z1,z3,z4,z888,z5,z24])],[(0,[z0,z1,z3,z4,z5,z889]),(0,[z1,z3,z4,z5,z828,z80]),(0,[z0,z1,z3,z4,z5,z890])],[(0,[z0,z1,z3,z4,z5,z891])],[(0,[z46,z0,z1,z3,z4,z218]),(0,[z0,z1,z3,z4,z892,z8])],[(0,[z183,z143,z1,z3,z4,z5]),(0,[z162,z1,z91,z4,z5,z193]),(0,[z0,z893,z3,z4,z5,z8]),(0,[z0,z1,z505,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z894]),(0,[z895,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z17,z547,z5]),(0,[z0,z896,z3,z4,z5,z8]),(0,[z897,z183,z1,z3,z4,z5]),(1,[z183,z1,z3,z4,z194])],[(0,[z0,z1,z3,z885,z5,z8]),(0,[z162,z183,z1,z3,z4,z5]),(0,[z183,z342,z1,z3,z4,z5])],[(0,[z0,z175,z3,z23,z5,z8]),(0,[z183,z1,z3,z4,z137,z5])],[(0,[z0,z1,z3,z4,z5,z898]),(0,[z136,z0,z1,z3,z4,z899]),(0,[z0,z1,z3,z141,z101,z6])],[(0,[z46,z0,z1,z3,z4,z39]),(0,[z0,z1,z3,z4,z5,z900]),(0,[z901,z0,z1,z3,z4,z5]),(0,[z0,z3,z4,z902,z5,z8])],[(0,[z46,z0,z1,z3,z4,z293]),(0,[z183,z240,z1,z3,z4,z5]),(0,[z0,z1,z903,z4,z5,z8]),(0,[z0,z1,z82,z4,z22,z8])],[(0,[z0,z1,z261,z221,z5,z337])],[(0,[z904,z0,z1,z3,z4,z5]),(0,[z0,z1,z905,z3,z4,z5]),(0,[z0,z1,z906,z3,z4,z8])],[(0,[z0,z1,z3,z907,z4,z5]),(0,[z0,z1,z3,z4,z5,z908]),(0,[z0,z401,z166,z4,z5,z8]),(0,[z0,z1,z377,z3,z76,z6])],[(1,[z162,z1,z179,z4,z5]),(0,[z0,z1,z3,z4,z909,z200]),(0,[z272,z1,z3,z4,z38,z8]),(0,[z20,z0,z1,z3,z910,z5]),(0,[z0,z1,z251,z4,z5,z911])],[(0,[z0,z1,z3,z4,z5,z774])],[(0,[z0,z1,z3,z4,z198,z6]),(0,[z0,z1,z3,z4,z5,z912]),(0,[z0,z1,z3,z913,z4,z5]),(0,[z0,z1,z3,z4,z5,z216]),(0,[z0,z1,z29,z728,z5,z8])]],
   [[(0,[z46,z0,z1,z3,z4,z198]),(0,[z0,z1,z28,z29,z5,z6])],[(0,[z0,z1,z3,z914,z5,z8]),(0,[z20,z46,z1,z3,z4,z291]),(0,[z20,z46,z1,z3,z4,z381]),(0,[z20,z0,z1,z3,z915,z5]),(0,[z0,z1,z3,z4,z5,z916]),(0,[z0,z1,z28,z728,z5,z8])],[(0,[z0,z1,z3,z4,z899,z6])],[],[(0,[z0,z1,z47,z4,z154,z8]),(0,[z0,z1,z3,z4,z232,z430]),(0,[z0,z1,z4,z5,z24,z439])],[(0,[z20,z1,z3,z4,z5,z290]),(0,[z0,z1,z3,z917,z4,z8])],[(0,[z0,z1,z3,z4,z198,z193]),(0,[z0,z1,z3,z357,z4,z8])],[(0,[z0,z1,z3,z918,z5,z8]),(0,[z0,z1,z3,z4,z919,z8]),(0,[z0,z1,z920,z3,z4,z5]),(0,[z0,z1,z4,z5,z785,z8]),(0,[z0,z1,z425,z4,z5,z6])],[(0,[z77,z367,z2,z3,z4,z5]),(0,[z60,z1,z61,z4,z5,z8]),(0,[z0,z1,z773,z4,z5,z8]),(0,[z46,z120,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z388])],[(0,[z0,z1,z490,z221,z5,z8]),(0,[z20,z1,z3,z4,z5,z50]),(0,[z46,z0,z1,z3,z807,z5]),(0,[z0,z1,z3,z4,z5,z921]),(0,[z0,z1,z3,z4,z922,z8])],[(0,[z77,z2,z3,z4,z5,z24]),(0,[z217,z60,z1,z61,z4,z5]),(0,[z0,z1,z3,z4,z5,z923])],[(0,[z0,z1,z924,z3,z4,z8]),(0,[z59,z618,z3,z4,z5,z8]),(0,[z0,z1,z3,z519,z5,z8]),(0,[z0,z175,z3,z23,z5,z6]),(0,[z0,z1,z925,z3,z4,z5])],[(0,[z59,z143,z3,z4,z5,z158]),(0,[z0,z1,z3,z4,z5,z926]),(0,[z313,z1,z3,z4,z108,z8]),(0,[z0,z1,z3,z4,z5,z398])],[(0,[z0,z323,z166,z4,z5,z8]),(0,[z162,z486,z1,z91,z4,z5]),(0,[z0,z1,z927,z3,z4,z5]),(0,[z240,z0,z1,z132,z4,z5]),(0,[z0,z1,z266,z4,z41,z30]),(1,[z0,z1,z3,z4,z774])],[(0,[z0,z1,z4,z450,z5,z6]),(0,[z0,z1,z3,z4,z291,z6])],[(0,[z20,z0,z1,z3,z4,z928]),(0,[z21,z20,z0,z3,z170,z5]),(0,[z0,z1,z3,z4,z328,z24])]],
   [[(0,[z0,z1,z3,z929,z5,z8]),(0,[z930,z0,z1,z3,z4,z5]),(0,[z931,z0,z1,z3,z4,z5])],[(0,[z0,z1,z603,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z34]),(0,[z183,z128,z1,z3,z4,z5]),(0,[z0,z3,z4,z932,z5,z8])],[(0,[z46,z0,z1,z3,z4,z790]),(0,[z0,z1,z3,z4,z22,z6]),(0,[z0,z1,z3,z4,z5,z933])],[(0,[z0,z1,z3,z173,z5,z6]),(1,[z1,z3,z4,z5,z828]),(0,[z0,z1,z3,z4,z934,z8]),(0,[z0,z935,z3,z4,z5,z8]),(0,[z136,z0,z1,z3,z4,z936])],[(0,[z0,z1,z3,z937,z4,z8]),(0,[z0,z350,z3,z4,z27,z8]),(0,[z46,z686,z1,z3,z4,z5]),(0,[z0,z1,z577,z3,z76,z8]),(0,[z0,z1,z3,z938,z4,z5])],[(0,[z128,z1,z4,z450,z38,z8])],[(0,[z0,z1,z3,z4,z5,z911]),(0,[z0,z1,z620,z4,z5,z24])],[(0,[z46,z0,z1,z3,z4,z817])],[(0,[z77,z2,z3,z4,z274,z8]),(0,[z0,z1,z3,z4,z5,z939]),(0,[z0,z1,z4,z154,z355,z8]),(0,[z31,z0,z1,z412,z4,z5]),(0,[z0,z1,z3,z4,z940,z8])],[(0,[z0,z296,z3,z4,z27,z8])],[(0,[z60,z0,z1,z179,z4,z5]),(0,[z46,z0,z1,z47,z4,z154])],[(1,[z1,z3,z4,z715,z8]),(0,[z20,z0,z1,z266,z4,z41])],[(0,[z0,z1,z3,z4,z5,z941]),(0,[z0,z1,z3,z4,z942,z8]),(0,[z943,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z944,z8])],[(0,[z20,z0,z163,z3,z4,z5]),(0,[z0,z1,z82,z4,z5,z6])],[(0,[z0,z1,z945,z3,z4,z8]),(0,[z46,z0,z1,z3,z4,z238]),(0,[z217,z183,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z946]),(0,[z499,z2,z3,z4,z5,z8])]],
   [[(0,[z0,z1,z947,z4,z5,z8]),(0,[z245,z2,z3,z4,z5,z8]),(0,[z0,z1,z3,z519,z5,z6]),(0,[z0,z1,z3,z17,z5,z130])],[(0,[z20,z77,z2,z3,z4,z5]),(0,[z0,z1,z948,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z949])],[(0,[z46,z60,z1,z61,z4,z5]),(0,[z58,z1,z3,z97,z5,z6]),(0,[z240,z0,z1,z3,z4,z194])],[(0,[z950,z1,z3,z4,z5,z8])],[(0,[z0,z1,z951,z3,z4,z5]),(0,[z162,z20,z1,z3,z519,z5]),(0,[z0,z1,z3,z4,z5,z98]),(0,[z183,z1,z4,z5,z6,z24])],[(0,[z0,z1,z3,z4,z5,z952]),(0,[z20,z1,z3,z953,z4,z5]),(0,[z0,z954,z1,z3,z4,z5])],[],[(0,[z0,z1,z3,z519,z5,z193]),(0,[z0,z1,z4,z5,z955,z8]),(0,[z0,z1,z196,z3,z533,z5]),(0,[z0,z1,z251,z4,z22,z8])],[(0,[z13,z1,z3,z929,z5,z8])],[(0,[z183,z1,z3,z4,z5,z199]),(0,[z0,z1,z3,z4,z956,z6])],[(0,[z162,z1,z91,z4,z5,z290]),(0,[z162,z1,z250,z91,z4,z5]),(0,[z46,z0,z1,z4,z450,z5]),(0,[z46,z0,z1,z3,z4,z291]),(0,[z183,z1,z3,z23,z4,z5]),(0,[z0,z1,z377,z3,z76,z8])],[(0,[z20,z0,z1,z3,z4,z957]),(0,[z1,z3,z958,z4,z5,z8])],[(0,[z0,z959,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z126,z200]),(0,[z960,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z961])],[(0,[z0,z1,z3,z910,z5,z8]),(0,[z21,z152,z3,z170,z5,z8]),(0,[z0,z1,z3,z4,z962,z8])],[(0,[z0,z1,z28,z29,z5,z8]),(0,[z0,z1,z36,z4,z194,z24])],[(0,[z20,z0,z1,z963,z4,z5]),(0,[z0,z1,z4,z5,z6,z102])]],
   [[(0,[z0,z1,z3,z4,z861,z8]),(0,[z0,z1,z3,z4,z39,z24]),(0,[z0,z1,z3,z4,z899,z8])],[(0,[z0,z1,z3,z4,z5,z964]),(0,[z0,z1,z345,z4,z5,z24]),(0,[z20,z46,z1,z3,z4,z5]),(0,[z20,z0,z1,z251,z4,z5]),(0,[z0,z1,z3,z4,z238,z24])],[(0,[z0,z1,z345,z55,z4,z8]),(0,[z965,z0,z1,z3,z4,z5]),(0,[z183,z1,z3,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z346])],[(0,[z162,z20,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z966]),(0,[z0,z1,z3,z967,z4,z5]),(0,[z968,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z412,z4,z291]),(0,[z0,z1,z3,z412,z4,z381])],[(0,[z0,z1,z3,z4,z5,z969]),(0,[z0,z1,z502,z3,z4,z8])],[(0,[z79,z1,z3,z4,z108,z24])],[(0,[z20,z0,z1,z970,z4,z5]),(0,[z0,z971,z3,z4,z5,z8])],[(0,[z0,z843,z3,z4,z5,z8]),(0,[z0,z3,z4,z5,z24,z972])],[(0,[z0,z1,z3,z4,z973,z8]),(0,[z128,z1,z3,z4,z333,z38]),(0,[z20,z79,z1,z3,z4,z108]),(0,[z0,z1,z3,z4,z5,z974]),(0,[z0,z1,z3,z4,z294,z24])],[(0,[z162,z1,z540,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z975])],[],[(0,[z0,z1,z3,z4,z198,z290]),(0,[z0,z1,z4,z450,z5,z8]),(0,[z0,z1,z3,z4,z471,z6]),(0,[z0,z1,z3,z4,z291,z8]),(0,[z1,z3,z4,z108,z715,z8])],[(0,[z128,z1,z3,z4,z38,z6]),(0,[z976,z152,z1,z3,z4,z5])],[(0,[z20,z669,z1,z3,z4,z5]),(0,[z0,z1,z266,z425,z4,z8])],[(0,[z977,z0,z1,z3,z4,z5]),(0,[z0,z3,z23,z932,z5,z8]),(0,[z183,z1,z3,z4,z154,z5])]],
   [[(0,[z0,z1,z3,z4,z978,z8]),(0,[z0,z163,z3,z4,z218,z8]),(0,[z162,z20,z1,z61,z4,z5]),(0,[z128,z0,z1,z345,z4,z8]),(0,[z0,z1,z3,z4,z22,z8])],[(0,[z0,z1,z3,z173,z5,z8]),(0,[z0,z1,z3,z4,z5,z979]),(0,[z0,z1,z3,z5,z980,z8]),(0,[z183,z1,z3,z4,z221,z5]),(0,[z981,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z232,z34]),(0,[z20,z0,z1,z3,z4,z982]),(0,[z983,z0,z1,z3,z4,z5])],[(0,[z59,z812,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z352]),(0,[z0,z1,z3,z4,z5,z984]),(0,[z0,z1,z3,z4,z985,z5]),(0,[z0,z175,z3,z932,z5,z8]),(0,[z0,z1,z266,z4,z41,z24])],[(0,[z0,z1,z3,z4,z5,z986]),(0,[z0,z1,z3,z4,z5,z987])],[(0,[z0,z1,z3,z4,z988,z8]),(0,[z183,z1,z61,z3,z4,z5])],[(0,[z0,z1,z3,z4,z989,z8]),(0,[z0,z1,z3,z4,z5,z990])],[(0,[z0,z1,z3,z4,z5,z287])],[(0,[z0,z1,z502,z3,z4,z6]),(0,[z0,z1,z251,z4,z5,z991]),(0,[z0,z1,z4,z728,z5,z8])],[(0,[z0,z1,z3,z4,z333,z232])],[(0,[z46,z0,z1,z3,z519,z5]),(0,[z0,z1,z3,z4,z218,z24]),(0,[z0,z1,z82,z4,z5,z8]),(0,[z0,z1,z251,z4,z5,z6]),(0,[z992,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z728,z5,z8])],[(0,[z162,z20,z1,z266,z4,z5]),(0,[z993,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z257])],[(0,[z0,z1,z994,z3,z4,z5]),(0,[z20,z0,z1,z261,z221,z5])],[(0,[z486,z0,z1,z3,z4,z5]),(0,[z0,z1,z995,z3,z4,z8]),(0,[z183,z1,z3,z4,z101,z5])],[(0,[z0,z1,z3,z4,z996,z8]),(0,[z0,z1,z3,z4,z5,z997]),(0,[z152,z1,z3,z4,z5,z140]),(0,[z183,z1,z3,z4,z170,z5]),(0,[z183,z177,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z137,z774])]],
   [[(0,[z183,z77,z1,z3,z4,z5]),(0,[z183,z1,z2,z3,z4,z5]),(0,[z58,z1,z3,z97,z5,z8]),(0,[z0,z1,z3,z4,z5,z998])],[(0,[z77,z812,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z471]),(0,[z0,z1,z507,z4,z5,z24]),(0,[z183,z1,z3,z4,z5,z41]),(0,[z0,z112,z3,z4,z5,z358])],[(0,[z162,z1,z3,z250,z4,z5]),(0,[z0,z1,z546,z3,z4,z8]),(0,[z0,z81,z756,z4,z5,z8]),(1,[z0,z3,z932,z5,z8]),(0,[z0,z1,z3,z4,z5,z999])],[(0,[z0,z1,z1000,z4,z5,z8]),(0,[z162,z46,z1,z91,z4,z5]),(0,[z128,z46,z1,z3,z4,z38]),(0,[z0,z1,z3,z4,z521,z232]),(0,[z0,z122,z3,z4,z75,z8])],[(0,[z0,z1,z1001,z3,z4,z8])],[(0,[z240,z60,z1,z61,z4,z5]),(0,[z217,z1,z3,z4,z5,z420])],[(0,[z0,z1002,z1,z3,z4,z5]),(0,[z0,z1003,z3,z4,z5,z8]),(1,[z1,z773,z4,z5,z8]),(0,[z594,z1,z3,z4,z108,z8]),(0,[z0,z1,z3,z4,z1004,z8]),(0,[z0,z1,z3,z4,z5,z40]),(0,[z1005,z1,z3,z4,z5,z8]),(0,[z1006,z183,z1,z3,z4,z5])],[(0,[z1007,z0,z1,z3,z4,z5]),(0,[z0,z647,z3,z4,z75,z8]),(0,[z0,z1,z3,z4,z956,z8])],[(0,[z77,z46,z2,z3,z4,z5]),(0,[z0,z1,z403,z4,z5,z24]),(0,[z0,z1008,z3,z4,z5,z8]),(0,[z125,z0,z226,z3,z4,z5]),(0,[z20,z0,z175,z3,z23,z5]),(0,[z152,z1,z3,z4,z5,z249])],[(0,[z0,z1,z3,z4,z5,z1009]),(0,[z183,z1,z3,z166,z4,z5]),(0,[z0,z1,z36,z357,z4,z24]),(0,[z0,z1,z3,z4,z1010,z8])],[(0,[z1011,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z137,z194])],[(0,[z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z1012,z3,z5,z24])],[(0,[z0,z1,z3,z4,z5,z1013]),(0,[z0,z1,z47,z179,z4,z5]),(0,[z348,z0,z1,z3,z4,z521]),(0,[z0,z54,z3,z4,z861,z8]),(0,[z31,z0,z1,z4,z5,z6]),(0,[z0,z1,z354,z4,z5,z24]),(0,[z0,z1,z3,z4,z1014,z6])],[(0,[z0,z1,z3,z173,z5,z193]),(0,[z0,z1,z3,z519,z5,z290]),(0,[z0,z1015,z3,z4,z5,z8]),(0,[z1016,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1017]),(0,[z0,z1,z3,z4,z5,z1018]),(1,[z1,z3,z929,z5,z8]),(0,[z0,z1,z3,z4,z1019,z8]),(0,[z0,z1,z3,z4,z5,z1020]),(0,[z0,z1,z3,z4,z1021,z8])],[(1,[z183,z1,z3,z4,z5]),(0,[z183,z1,z3,z4,z108,z5])]],
   [[(0,[z20,z343,z1,z3,z4,z5]),(0,[z46,z0,z84,z353,z4,z5]),(0,[z183,z84,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1022]),(0,[z0,z1,z3,z4,z626,z500])],[(0,[z1023,z0,z1,z3,z4,z5]),(0,[z13,z46,z1,z3,z14,z5]),(0,[z0,z1,z3,z4,z5,z1024]),(0,[z0,z54,z3,z4,z75,z6]),(0,[z0,z342,z3,z4,z5,z63]),(0,[z183,z1,z3,z141,z4,z5])],[(0,[z0,z1,z1025,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z804]),(0,[z0,z1,z3,z4,z5,z991]),(0,[z183,z1,z1026,z3,z4,z5]),(0,[z1027,z183,z1,z3,z4,z5])],[(0,[z0,z1,z3,z412,z4,z5])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z243,z1,z3,z4,z38,z8]),(0,[z246,z0,z1,z3,z4,z235]),(0,[z0,z1,z47,z4,z648,z8])],[(0,[z0,z1028,z3,z4,z5,z8]),(0,[z46,z0,z1,z3,z4,z1029]),(0,[z0,z84,z353,z4,z294,z8]),(0,[z0,z1,z527,z3,z4,z448])],[(0,[z501,z1,z3,z14,z5,z8]),(0,[z0,z1,z1030,z4,z5,z8]),(0,[z787,z1,z3,z4,z5,z8])],[(0,[z0,z1,z546,z3,z4,z6]),(0,[z116,z0,z1,z412,z4,z5])],[(0,[z0,z1,z3,z4,z1029,z8]),(0,[z0,z1,z3,z1031,z4,z8]),(0,[z0,z1,z196,z3,z5,z184])],[(0,[z0,z1032,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z1033,z8])],[(0,[z0,z1,z3,z4,z471,z8]),(0,[z0,z3,z4,z5,z717,z8]),(0,[z0,z1,z47,z4,z758,z8])],[(0,[z0,z1034,z3,z4,z5,z8]),(0,[z128,z1,z3,z4,z38,z8]),(0,[z0,z3,z4,z5,z8,z972]),(0,[z1035,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z709,z24])],[(0,[z812,z2,z3,z4,z5,z8]),(0,[z95,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z396,z101,z8])],[(0,[z0,z1,z1036,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z381]),(0,[z0,z1,z3,z4,z711,z24])],[(0,[z0,z1037,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1038,z8]),(0,[z0,z1,z3,z250,z4,z5]),(0,[z1039,z0,z1,z3,z4,z5]),(0,[z183,z1,z3,z233,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1040]),(0,[z0,z1,z4,z576,z5,z24])]],
   [[(0,[z0,z1,z3,z4,z5,z1041]),(0,[z0,z1,z3,z4,z957,z8])],[(0,[z0,z1,z3,z1042,z4,z5]),(0,[z0,z1,z3,z4,z5,z1043]),(0,[z0,z1,z1044,z3,z5,z8]),(0,[z0,z1,z3,z4,z5,z1045]),(0,[z0,z1,z3,z1046,z4,z8]),(0,[z0,z1,z3,z4,z5,z1047])],[(0,[z20,z128,z1,z3,z4,z38]),(0,[z0,z226,z3,z4,z5,z72])],[(0,[z20,z0,z1,z502,z3,z4]),(0,[z1,z3,z4,z5,z126,z828]),(0,[z183,z1,z3,z4,z5,z211])],[(0,[z0,z1,z1048,z3,z4,z8]),(0,[z20,z0,z1,z995,z3,z4]),(0,[z0,z1,z3,z4,z1049,z8])],[(0,[z0,z1050,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1051])],[(0,[z20,z13,z1,z3,z14,z5]),(0,[z21,z0,z3,z170,z22,z8]),(0,[z0,z1052,z3,z4,z5,z8])],[],[(0,[z0,z1,z3,z160,z4,z5])],[(0,[z20,z1,z61,z3,z4,z5]),(0,[z0,z1,z995,z3,z179,z4]),(0,[z0,z1053,z1,z3,z4,z5]),(0,[z0,z1,z251,z4,z5,z8]),(0,[z1054,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1055]),(0,[z1,z3,z929,z4,z5,z8]),(0,[z0,z1,z3,z4,z1056,z8]),(0,[z1057,z0,z1,z3,z4,z5]),(1,[z0,z3,z4,z5,z717]),(0,[z1058,z0,z1,z3,z4,z5])],[(0,[z183,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z1059,z4,z5])],[(0,[z0,z1,z3,z1060,z4,z5]),(0,[z0,z163,z3,z4,z5,z24]),(0,[z128,z1,z540,z3,z4,z8]),(0,[z20,z0,z1,z3,z4,z85]),(0,[z20,z0,z1,z28,z29,z5]),(0,[z46,z0,z1,z3,z357,z4]),(0,[z0,z1,z3,z4,z232,z257])],[],[(0,[z0,z1,z4,z758,z5,z8])]],
   [[(0,[z20,z1,z495,z3,z4,z5]),(0,[z295,z1,z3,z4,z5,z140])],[(0,[z21,z0,z82,z170,z5,z8])],[(0,[z0,z1,z3,z4,z333,z291]),(0,[z452,z0,z48,z3,z4,z5]),(1,[z183,z1,z3,z357,z4])],[(0,[z0,z1,z3,z4,z982,z8]),(0,[z162,z20,z1,z4,z154,z5]),(0,[z183,z1,z266,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1061,z8]),(0,[z0,z1,z3,z4,z1062,z5])],[(0,[z217,z0,z1,z3,z4,z5]),(0,[z0,z213,z3,z4,z218,z8]),(0,[z46,z0,z1,z3,z1063,z5]),(0,[z0,z1,z3,z4,z5,z1064]),(0,[z746,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z928,z8]),(0,[z0,z1,z3,z4,z381,z24]),(0,[z46,z1,z3,z4,z5,z182]),(0,[z0,z1,z3,z4,z5,z220]),(0,[z0,z1,z3,z4,z5,z1065])],[(0,[z0,z1,z3,z4,z1066,z8]),(0,[z0,z1,z3,z4,z149,z6])],[(0,[z0,z1,z4,z1067,z5,z8]),(0,[z176,z0,z259,z3,z4,z5]),(0,[z737,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z85,z8]),(0,[z0,z1,z3,z4,z5,z1068]),(0,[z295,z1,z3,z4,z5,z249])],[(0,[z0,z1,z1069,z4,z5,z8]),(0,[z0,z1,z3,z4,z1014,z8]),(0,[z0,z1,z82,z4,z328,z8]),(0,[z0,z1,z266,z4,z41,z430])],[],[(0,[z0,z1,z3,z4,z5,z1070])],[(0,[z183,z1,z3,z97,z4,z5]),(0,[z21,z46,z0,z3,z170,z5])],[(0,[z0,z1,z132,z4,z5,z24]),(0,[z0,z1,z28,z29,z39,z8]),(0,[z0,z1,z3,z55,z4,z448])],[(0,[z0,z518,z3,z4,z75,z8]),(0,[z20,z612,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1071]),(0,[z0,z54,z3,z4,z75,z8]),(0,[z0,z1,z28,z29,z238,z8]),(0,[z0,z1,z16,z4,z5,z24])]],
   [[(0,[z1,z773,z91,z4,z5,z8]),(0,[z0,z1,z4,z5,z6,z475])],[(0,[z0,z1,z3,z4,z5,z1072]),(0,[z46,z0,z1,z3,z4,z149]),(0,[z1,z3,z4,z5,z749,z8]),(0,[z0,z1,z3,z4,z750,z8]),(0,[z176,z0,z3,z4,z5,z72]),(0,[z0,z1,z3,z466,z101,z8])],[(0,[z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z5,z18,z818])],[(0,[z0,z1,z3,z173,z5,z290]),(0,[z0,z1,z502,z3,z250,z4]),(0,[z13,z1,z3,z14,z5,z24]),(0,[z79,z0,z1,z345,z4,z8]),(0,[z46,z0,z1,z377,z3,z76]),(0,[z46,z1,z3,z516,z4,z5]),(0,[z1073,z1,z3,z4,z5,z8]),(0,[z1074,z183,z1,z3,z4,z5])],[(0,[z0,z1,z3,z1075,z4,z8]),(0,[z0,z71,z48,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1076]),(0,[z0,z26,z3,z4,z27,z24])],[(0,[z20,z0,z864,z3,z4,z5]),(0,[z46,z0,z1,z3,z141,z101]),(0,[z0,z1,z1077,z3,z4,z5])],[(0,[z0,z1,z3,z4,z274,z24]),(0,[z162,z1,z91,z4,z218,z8]),(0,[z0,z1,z3,z4,z5,z1078]),(0,[z0,z1079,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1080])],[(0,[z1,z61,z3,z953,z4,z5]),(0,[z0,z1,z1081,z3,z4,z8]),(0,[z46,z0,z1082,z3,z4,z5])],[(0,[z46,z104,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1083,z8]),(0,[z0,z1,z3,z4,z5,z1084])],[(0,[z0,z1,z3,z4,z5,z1085]),(0,[z13,z1,z386,z3,z14,z5]),(0,[z21,z0,z3,z170,z5,z6]),(0,[z0,z1,z3,z4,z781,z24])],[(0,[z0,z1,z3,z4,z1086,z8]),(0,[z183,z54,z1,z3,z4,z5])],[(0,[z0,z1,z3,z5,z766,z8]),(0,[z0,z1,z3,z4,z5,z1087])],[(0,[z46,z0,z1,z3,z4,z5]),(0,[z0,z1,z345,z4,z76,z8]),(0,[z79,z1,z264,z3,z4,z8]),(0,[z1088,z1,z3,z4,z5,z8])],[(0,[z0,z421,z3,z4,z27,z8])],[(0,[z20,z1,z3,z4,z5,z200])]],
   [[(0,[z0,z1,z117,z4,z450,z5]),(0,[z240,z0,z1,z3,z4,z291]),(0,[z240,z0,z1,z3,z4,z381]),(0,[z0,z113,z1,z4,z5,z6]),(0,[z183,z1,z3,z4,z5,z1089]),(0,[z177,z0,z3,z4,z5,z78]),(0,[z0,z1,z3,z4,z137,z232])],[(0,[z0,z1,z3,z4,z5,z1090]),(0,[z0,z1,z3,z4,z5,z1091]),(0,[z0,z1,z3,z4,z1092,z8]),(0,[z183,z1,z3,z55,z4,z5])],[(0,[z867,z1,z3,z4,z5,z8]),(0,[z0,z71,z3,z4,z5,z263]),(0,[z0,z1,z3,z4,z777,z8]),(0,[z0,z1,z4,z758,z41,z8])],[(0,[z0,z1,z3,z4,z293,z8]),(0,[z162,z20,z213,z3,z4,z5]),(0,[z53,z0,z1,z3,z4,z381]),(0,[z0,z1,z1093,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1094]),(0,[z183,z79,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1095]),(0,[z612,z0,z1,z266,z4,z8])],[(0,[z1096,z0,z1,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z22])],[(0,[z0,z1,z3,z17,z5,z18])],[(0,[z0,z812,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z1097,z8]),(0,[z0,z3,z4,z5,z1098,z8]),(0,[z1099,z1,z3,z4,z5,z24])],[(0,[z183,z59,z1,z3,z4,z5]),(0,[z0,z1,z1100,z4,z5,z8]),(0,[z1,z3,z4,z5,z346,z200])],[],[(0,[z0,z81,z166,z4,z5,z6]),(0,[z1101,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z117,z4,z5]),(0,[z20,z87,z1,z3,z4,z5])],[(0,[z20,z0,z81,z166,z4,z5]),(0,[z1102,z0,z1,z3,z4,z5]),(0,[z0,z1,z82,z4,z5,z1103])],[(0,[z20,z0,z1,z3,z173,z5]),(0,[z0,z1,z3,z4,z5,z1104])],[(0,[z0,z1,z3,z4,z5,z193]),(0,[z20,z0,z1028,z3,z4,z5]),(0,[z46,z0,z1,z3,z4,z328])],[(0,[z0,z1,z3,z4,z5,z1105]),(0,[z0,z1,z179,z4,z5,z6]),(0,[z21,z0,z251,z170,z5,z8]),(0,[z0,z1,z47,z4,z484,z8])]],
   [[(0,[z183,z1,z3,z4,z14,z5]),(0,[z20,z0,z1,z1106,z4,z5]),(0,[z46,z0,z1,z3,z4,z1019]),(0,[z152,z1,z3,z4,z5,z24])],[(0,[z0,z1,z546,z3,z250,z4]),(0,[z60,z1,z61,z4,z5,z200]),(0,[z183,z1,z3,z357,z4,z8])],[(0,[z0,z1,z3,z4,z333,z5]),(0,[z20,z0,z1,z3,z4,z877]),(0,[z1107,z1,z3,z4,z5,z8]),(0,[z1,z3,z4,z888,z5,z8]),(0,[z0,z1,z4,z10,z5,z24])],[(0,[z0,z1,z12,z4,z5,z24]),(0,[z0,z1,z1108,z3,z4,z5]),(0,[z183,z1,z3,z4,z5,z126]),(0,[z0,z3,z4,z5,z717,z63]),(0,[z0,z1,z3,z1109,z4,z5]),(0,[z0,z1,z432,z4,z5,z6])],[(0,[z20,z136,z1,z3,z4,z5]),(0,[z136,z1,z3,z4,z5,z155])],[(0,[z0,z1,z3,z4,z149,z8]),(0,[z183,z1,z3,z179,z4,z5]),(0,[z46,z0,z1,z3,z4,z1110])],[(0,[z0,z1,z3,z4,z1111,z8]),(0,[z162,z20,z1,z179,z4,z5]),(0,[z60,z0,z1,z412,z4,z5]),(0,[z0,z1,z3,z4,z1112,z8]),(0,[z0,z811,z3,z4,z5,z24])],[(0,[z162,z20,z163,z3,z4,z5]),(0,[z0,z1,z1113,z3,z4,z5]),(0,[z0,z1,z36,z4,z5,z785]),(0,[z1,z3,z4,z5,z346,z24])],[(0,[z0,z1,z3,z4,z293,z6]),(0,[z58,z1,z3,z929,z5,z8]),(0,[z46,z0,z26,z3,z4,z27]),(0,[z0,z1,z251,z4,z328,z8]),(0,[z183,z0,z1,z3,z4,z194]),(0,[z0,z1,z3,z5,z818,z211])],[(0,[z0,z1114,z3,z4,z5,z8]),(0,[z79,z1,z3,z4,z108,z34]),(0,[z20,z256,z1,z3,z4,z5]),(0,[z567,z0,z259,z3,z4,z5]),(0,[z1115,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1116,z8])],[(0,[z0,z1,z3,z4,z5,z1117])],[(0,[z46,z0,z1,z3,z4,z274]),(0,[z0,z1,z3,z4,z805,z8]),(0,[z20,z152,z1,z3,z4,z5])],[(0,[z20,z1,z165,z3,z4,z5]),(0,[z1118,z0,z1,z3,z4,z5]),(0,[z0,z1,z225,z4,z5,z6])],[(0,[z0,z1,z3,z1119,z4,z5]),(0,[z0,z1,z3,z937,z4,z200]),(0,[z0,z1,z3,z4,z1120,z5]),(0,[z1121,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1122,z8])],[]],
   [[(0,[z162,z20,z1,z317,z4,z5]),(0,[z0,z1,z3,z4,z5,z1123]),(0,[z0,z1,z345,z4,z27,z8]),(0,[z0,z1,z3,z4,z5,z1124])],[(0,[z162,z1,z179,z4,z5,z8]),(0,[z0,z1,z3,z4,z1125,z8]),(0,[z0,z84,z353,z4,z5,z269]),(0,[z0,z1,z3,z4,z5,z1126])],[(0,[z0,z213,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z1127]),(0,[z0,z1,z3,z4,z1128,z8]),(0,[z20,z1,z3,z565,z4,z5]),(0,[z20,z1,z255,z3,z4,z5]),(0,[z0,z1,z3,z4,z1129,z8])],[(0,[z20,z0,z1,z546,z3,z4]),(0,[z0,z1,z3,z4,z1130,z5])],[(0,[z0,z1,z3,z4,z1131,z8]),(0,[z0,z1,z3,z4,z5,z1132]),(0,[z0,z1,z345,z4,z75,z8]),(0,[z503,z0,z1,z3,z623,z5]),(0,[z0,z1,z3,z4,z39,z6])],[(0,[z0,z1,z345,z4,z5,z6]),(0,[z46,z0,z1,z82,z4,z5]),(0,[z0,z1,z3,z4,z238,z6])],[(0,[z0,z1,z3,z4,z1133,z8])],[(0,[z0,z1,z1134,z4,z450,z5]),(0,[z0,z1,z3,z4,z1135,z8]),(0,[z183,z1,z47,z3,z4,z5])],[(0,[z162,z163,z91,z4,z5,z8]),(0,[z20,z607,z1,z3,z4,z5]),(0,[z0,z1,z1136,z3,z4,z5]),(0,[z21,z0,z3,z170,z5,z8])],[(0,[z0,z1,z3,z519,z218,z8]),(0,[z0,z1,z3,z4,z775,z24]),(0,[z183,z1,z3,z4,z194,z8])],[(0,[z46,z0,z213,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1137]),(0,[z0,z1,z3,z845,z76,z8])],[(0,[z46,z295,z1,z3,z4,z5]),(0,[z1011,z295,z1,z3,z4,z5])],[(0,[z128,z1,z345,z4,z38,z8]),(0,[z0,z1,z3,z636,z76,z8])],[],[(0,[z0,z84,z756,z4,z5,z8]),(0,[z0,z3,z4,z861,z75,z8]),(0,[z0,z1,z3,z4,z1138,z5])],[(0,[z0,z1,z3,z4,z5,z1139]),(0,[z46,z0,z1050,z3,z4,z5])]],
   [[(0,[z240,z0,z1,z3,z4,z5]),(0,[z183,z1,z3,z4,z5,z331])],[(0,[z0,z1,z3,z4,z328,z8])],[(0,[z0,z1,z3,z1140,z5,z8]),(0,[z20,z1,z3,z4,z5,z32])],[(0,[z162,z1,z91,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z1141]),(0,[z0,z1,z261,z221,z5,z24])],[(0,[z20,z0,z1,z3,z4,z294]),(0,[z1142,z1,z3,z4,z5,z8]),(0,[z0,z1,z665,z4,z5,z24])],[(0,[z0,z1,z3,z4,z5,z1143]),(0,[z0,z1,z3,z4,z5,z1144]),(0,[z31,z183,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1145])],[(0,[z46,z1,z3,z4,z5,z346]),(0,[z183,z1,z3,z357,z4,z5]),(0,[z0,z1,z3,z4,z194,z24])],[(0,[z0,z1,z3,z4,z5,z1146]),(0,[z0,z1,z1147,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1148]),(0,[z976,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z137,z291]),(0,[z0,z81,z166,z4,z5,z8])],[(0,[z0,z1149,z1,z3,z4,z5])],[(0,[z0,z163,z3,z4,z198,z8]),(0,[z0,z253,z3,z4,z5,z63]),(0,[z0,z1,z3,z1150,z5,z8]),(0,[z0,z1,z579,z4,z5,z6]),(0,[z176,z0,z3,z4,z5,z717]),(0,[z0,z1,z1151,z3,z4,z5])],[(0,[z20,z204,z1,z3,z4,z5]),(0,[z1152,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1153,z8])],[(0,[z20,z506,z1,z3,z4,z5])],[(0,[z1,z61,z4,z5,z475,z8]),(0,[z0,z1,z756,z4,z5,z8])],[(0,[z46,z0,z163,z3,z4,z5]),(0,[z183,z60,z1,z3,z4,z5])],[(0,[z162,z0,z1,z179,z4,z5]),(0,[z0,z1,z3,z4,z5,z1154]),(0,[z20,z0,z779,z3,z4,z5]),(1,[z0,z1,z3,z845,z8])]],
   [[(0,[z0,z1,z3,z4,z5,z1155])],[(0,[z77,z2,z3,z4,z5,z6]),(0,[z0,z1,z1106,z4,z5,z8]),(0,[z295,z1,z3,z4,z5,z24]),(0,[z0,z1,z3,z4,z5,z1156]),(0,[z0,z1,z3,z4,z5,z1157]),(1,[z0,z1,z4,z5,z785]),(0,[z183,z1,z3,z4,z5,z78])],[(0,[z1158,z1,z3,z4,z5,z8]),(0,[z1,z3,z357,z4,z346,z24])],[(0,[z46,z1,z3,z4,z381,z126])],[(0,[z0,z1,z970,z4,z5,z8]),(0,[z0,z1,z1159,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z290]),(0,[z0,z1,z3,z4,z5,z1160]),(0,[z0,z1,z3,z4,z1161,z8])],[(0,[z0,z756,z166,z4,z5,z8]),(0,[z0,z1,z36,z4,z5,z24])],[(0,[z0,z1,z4,z714,z450,z5]),(0,[z20,z1,z3,z4,z5,z828]),(0,[z0,z1,z3,z4,z328,z6])],[(0,[z0,z1,z412,z4,z5,z24]),(0,[z0,z1,z416,z4,z5,z6])],[(0,[z20,z0,z1,z3,z789,z5]),(0,[z0,z1,z3,z4,z5,z1162]),(0,[z1163,z0,z1,z3,z4,z5])],[(0,[z0,z1,z1164,z3,z4,z5]),(0,[z46,z0,z54,z3,z4,z75]),(0,[z0,z1,z728,z221,z5,z8]),(0,[z183,z1,z3,z4,z5,z402])],[],[(0,[z20,z0,z1,z3,z4,z194]),(0,[z0,z1,z3,z4,z5,z1165]),(0,[z0,z1,z559,z3,z5,z184])],[],[(0,[z0,z1,z3,z4,z1166,z8]),(0,[z0,z1,z4,z5,z1167,z8]),(0,[z183,z1,z196,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1168]),(0,[z46,z0,z1169,z3,z4,z5])],[(0,[z46,z0,z1,z345,z4,z5]),(0,[z0,z1,z3,z564,z5,z18])]],
   [[(0,[z0,z1,z3,z1170,z4,z5]),(0,[z538,z0,z3,z4,z5,z72])],[],[(0,[z0,z1,z3,z4,z5,z1171]),(0,[z0,z1,z3,z4,z39,z8]),(0,[z0,z1,z4,z260,z5,z24])],[(0,[z0,z1,z345,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1103]),(0,[z0,z1,z3,z4,z238,z8]),(0,[z240,z0,z1,z3,z357,z4]),(0,[z0,z1,z3,z5,z845,z8])],[(0,[z0,z1,z3,z1172,z5,z8]),(0,[z489,z0,z1,z266,z4,z8]),(0,[z20,z0,z1,z3,z4,z39]),(0,[z0,z1,z3,z4,z1173,z8])],[(0,[z0,z1,z3,z4,z1174,z8]),(0,[z20,z0,z1,z3,z4,z293]),(0,[z0,z1,z3,z4,z5,z1175])],[(0,[z0,z1,z3,z4,z5,z1176]),(0,[z0,z1,z3,z4,z5,z1177]),(0,[z0,z1,z3,z1178,z4,z8])],[(0,[z0,z1,z3,z4,z5,z1179]),(0,[z0,z1,z1134,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z337]),(0,[z183,z1,z3,z4,z5,z130]),(0,[z183,z1,z3,z4,z5,z194])],[(0,[z525,z1,z3,z4,z108,z8]),(0,[z0,z84,z353,z4,z5,z24]),(0,[z0,z1,z3,z4,z1180,z6])],[(0,[z183,z1,z3,z1181,z4,z5])],[(0,[z183,z1,z3,z4,z5,z232]),(0,[z0,z1,z3,z55,z4,z774])],[(0,[z0,z163,z3,z519,z5,z8]),(0,[z0,z1,z196,z3,z5,z211])],[(0,[z20,z0,z1,z3,z4,z198]),(0,[z46,z0,z1,z3,z1172,z5]),(0,[z0,z1,z3,z4,z5,z1182])],[(0,[z0,z1183,z3,z4,z5,z8]),(0,[z0,z3,z4,z861,z5,z8]),(0,[z0,z1,z266,z4,z578,z8])],[(0,[z20,z0,z1,z3,z1184,z5]),(0,[z136,z1,z3,z4,z5,z126])],[(0,[z0,z1,z3,z173,z218,z8]),(0,[z0,z1,z3,z4,z5,z1185]),(0,[z183,z183,z1,z3,z4,z5]),(0,[z0,z1,z339,z3,z5,z413])]],
   [[(0,[z0,z1,z3,z4,z1186,z8]),(0,[z0,z1,z3,z4,z8,z1187]),(0,[z0,z1,z3,z233,z5,z130])],[(0,[z0,z1,z3,z4,z5,z363]),(0,[z0,z1,z82,z4,z5,z1188]),(0,[z0,z1,z3,z357,z4,z24])],[(0,[z0,z1,z3,z4,z5,z1189]),(0,[z0,z1190,z1,z3,z4,z5])],[(0,[z0,z367,z1,z3,z4,z5]),(0,[z60,z1,z61,z4,z5,z24]),(0,[z1,z3,z4,z5,z8,z828]),(0,[z183,z71,z1,z3,z4,z5]),(0,[z0,z1,z582,z4,z5,z24])],[(0,[z0,z1,z3,z953,z4,z5]),(0,[z669,z1,z3,z4,z108,z8])],[],[(0,[z0,z1,z3,z4,z5,z1191]),(0,[z0,z1,z386,z3,z4,z5]),(0,[z0,z1,z1192,z3,z4,z5]),(0,[z0,z1,z266,z4,z41,z8])],[(0,[z21,z0,z3,z170,z328,z8])],[(0,[z217,z0,z1,z179,z4,z5]),(0,[z0,z1,z4,z5,z24,z599])],[(0,[z0,z1,z3,z4,z1193,z8]),(0,[z0,z1,z873,z3,z179,z4]),(0,[z1194,z0,z1,z3,z4,z5]),(0,[z240,z1,z3,z4,z5,z346])],[(0,[z183,z13,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z381,z34]),(0,[z0,z1,z319,z4,z5,z24])],[(0,[z0,z1,z1195,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1196]),(0,[z0,z1,z3,z4,z5,z1197]),(0,[z0,z1,z1198,z3,z4,z8]),(0,[z0,z1,z345,z117,z4,z5]),(0,[z79,z1,z3,z4,z108,z6])],[(0,[z162,z213,z91,z4,z5,z8]),(0,[z1199,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z309,z5,z308])],[(0,[z46,z0,z1,z261,z221,z5])],[(0,[z77,z2,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1200]),(0,[z0,z81,z166,z4,z5,z220]),(0,[z0,z1,z3,z4,z294,z6])]],
   [[(0,[z0,z1,z3,z4,z1201,z8]),(0,[z1202,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z1203,z8]),(0,[z0,z1,z3,z4,z5,z1204]),(0,[z0,z1,z3,z4,z5,z1205]),(0,[z0,z1,z3,z4,z5,z1206])],[(0,[z0,z1,z3,z4,z909,z8]),(0,[z0,z1,z4,z5,z6,z640])],[(0,[z0,z1,z854,z4,z5,z8]),(0,[z258,z0,z1,z179,z4,z5]),(0,[z217,z0,z1,z317,z4,z5]),(0,[z20,z0,z1,z708,z4,z5]),(0,[z0,z1,z3,z55,z4,z430]),(0,[z0,z1,z47,z4,z154,z289])],[(0,[z0,z1,z4,z154,z218,z8]),(0,[z0,z1,z345,z4,z333,z5])],[(0,[z0,z1,z3,z4,z5,z1207]),(1,[z0,z1,z4,z758,z8]),(0,[z1,z3,z4,z194,z346,z24])],[(0,[z20,z1,z3,z4,z611,z5]),(0,[z487,z0,z1,z3,z4,z291]),(0,[z0,z1,z1208,z3,z4,z5])],[(0,[z1209,z0,z1,z3,z4,z5]),(0,[z20,z660,z1,z3,z4,z5]),(0,[z20,z0,z1,z47,z4,z154]),(0,[z0,z1,z3,z4,z1210,z8]),(0,[z0,z1,z377,z3,z845,z8])],[(0,[z0,z1,z3,z4,z5,z1211]),(0,[z1212,z0,z1,z3,z4,z5])],[(0,[z0,z441,z3,z4,z5,z63])],[],[(0,[z20,z0,z1,z3,z4,z238]),(0,[z0,z1,z205,z3,z5,z211])],[(0,[z1101,z295,z1,z3,z4,z5]),(0,[z1213,z0,z1,z3,z4,z5]),(0,[z0,z1,z266,z4,z41,z6])],[(0,[z0,z1,z3,z1184,z5,z8]),(0,[z0,z1,z3,z1214,z4,z5]),(0,[z385,z46,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1215]),(0,[z0,z1,z4,z5,z366,z24]),(0,[z0,z1,z3,z4,z22,z140])],[(0,[z20,z60,z1,z61,z4,z5]),(0,[z20,z0,z1114,z3,z4,z5]),(0,[z20,z526,z1,z3,z4,z5]),(0,[z0,z112,z3,z4,z5,z72]),(0,[z950,z1,z3,z4,z5,z24])],[(0,[z0,z213,z3,z4,z198,z8]),(0,[z116,z20,z1,z3,z4,z5]),(0,[z20,z580,z1,z3,z4,z5]),(0,[z0,z1,z36,z179,z4,z5]),(0,[z46,z0,z1,z266,z4,z41])]],
   [[(0,[z77,z2,z3,z4,z293,z8]),(0,[z152,z1,z3,z4,z22,z8]),(0,[z0,z1,z3,z141,z101,z24])],[(0,[z0,z1,z3,z4,z5,z1216]),(0,[z0,z1,z3,z1217,z5,z8]),(0,[z1,z3,z4,z715,z5,z8]),(0,[z0,z1,z873,z3,z4,z8])],[(0,[z59,z143,z3,z4,z5,z352]),(0,[z0,z1,z3,z4,z218,z6]),(0,[z607,z1,z3,z97,z5,z8]),(0,[z20,z1,z3,z4,z5,z509])],[(0,[z0,z1,z1218,z4,z5,z8]),(0,[z183,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z1219,z4,z5]),(0,[z0,z1,z3,z4,z1220,z8]),(0,[z183,z1,z3,z4,z1221,z5])],[(0,[z0,z1,z3,z4,z1222,z8]),(0,[z0,z1,z3,z1223,z4,z5]),(0,[z0,z1,z3,z4,z1110,z8]),(0,[z0,z1,z345,z4,z232,z8]),(0,[z0,z1,z3,z4,z5,z1224]),(0,[z116,z183,z1,z3,z4,z5])],[(0,[z1,z3,z929,z14,z5,z8])],[(0,[z0,z1,z3,z4,z22,z249]),(0,[z0,z1,z3,z4,z1180,z8]),(0,[z1,z3,z958,z4,z5,z24]),(0,[z0,z1,z3,z4,z936,z8])],[(0,[z60,z1,z773,z4,z5,z8]),(0,[z13,z1,z3,z14,z5,z6]),(0,[z0,z26,z3,z4,z861,z8])],[(0,[z0,z1225,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z198,z24]),(0,[z0,z1,z4,z5,z8,z1226]),(0,[z0,z1,z82,z4,z5,z140]),(0,[z1,z3,z4,z5,z24,z1227]),(0,[z0,z1,z3,z4,z845,z8])],[(0,[z0,z1,z3,z1228,z5,z8]),(0,[z0,z1,z3,z1229,z5,z8]),(0,[z136,z60,z1,z3,z4,z5]),(0,[z0,z1,z28,z29,z5,z24])],[],[(0,[z20,z59,z143,z3,z4,z5]),(0,[z0,z1,z266,z507,z4,z8]),(0,[z46,z0,z1,z3,z4,z996]),(0,[z152,z1,z82,z4,z5,z8])],[(0,[z0,z1082,z3,z4,z5,z8]),(0,[z0,z71,z3,z4,z5,z63])],[(0,[z0,z3,z4,z1230,z5,z8]),(0,[z13,z1,z3,z14,z471,z8]),(0,[z0,z1,z3,z468,z101,z8]),(0,[z20,z0,z1,z3,z4,z1201]),(0,[z1035,z1,z3,z4,z5,z8]),(0,[z0,z1231,z1,z3,z4,z5]),(0,[z0,z1,z3,z5,z8,z818])],[(0,[z0,z1,z3,z4,z5,z158]),(0,[z20,z1,z3,z479,z4,z5]),(0,[z0,z1,z1232,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1233]),(0,[z0,z1,z3,z915,z5,z8]),(0,[z0,z1,z3,z4,z5,z1234]),(0,[z183,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z1235])]],
   [[(0,[z162,z1,z91,z4,z198,z8]),(0,[z0,z84,z353,z4,z5,z388]),(0,[z0,z1,z3,z4,z24,z1236])],[(0,[z0,z163,z3,z173,z5,z8]),(0,[z0,z1,z3,z4,z5,z181]),(0,[z0,z1,z82,z4,z5,z249])],[(0,[z0,z1,z3,z4,z5,z1237]),(0,[z20,z0,z1,z3,z4,z218]),(0,[z20,z183,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1238,z5]),(1,[z0,z3,z4,z861,z8])],[(0,[z0,z1,z3,z4,z5,z1239])],[(0,[z404,z46,z1,z3,z4,z5]),(0,[z0,z175,z3,z23,z5,z24])],[(0,[z46,z0,z1,z251,z4,z5])],[(0,[z0,z84,z637,z4,z5,z8]),(0,[z0,z1,z3,z1240,z5,z8]),(0,[z20,z1,z3,z609,z4,z5])],[(0,[z0,z1,z4,z450,z5,z24]),(0,[z1241,z1,z3,z4,z5,z8]),(0,[z1242,z0,z1,z3,z4,z5])],[(1,[z812,z3,z4,z5,z8]),(0,[z21,z0,z3,z932,z5,z8])],[(0,[z21,z295,z3,z170,z5,z8])],[(0,[z79,z1,z3,z4,z108,z8]),(0,[z0,z1,z3,z4,z381,z56]),(0,[z0,z1,z1243,z3,z4,z5])],[(0,[z0,z1,z3,z1244,z4,z8]),(0,[z0,z1,z3,z4,z22,z24]),(0,[z0,z1,z3,z4,z936,z6]),(0,[z0,z1,z196,z3,z5,z818])],[(0,[z0,z1,z3,z173,z5,z24])],[(0,[z0,z1,z3,z4,z5,z1245]),(0,[z0,z1,z3,z4,z754,z8]),(0,[z0,z1,z3,z4,z5,z1246]),(0,[z183,z1,z3,z4,z5,z80]),(0,[z0,z1,z3,z4,z381,z291]),(0,[z0,z1,z3,z4,z294,z8])],[(0,[z0,z1,z688,z3,z76,z8]),(0,[z0,z1,z3,z4,z1247,z8]),(0,[z0,z1,z4,z5,z464,z24])],[(0,[z0,z1,z3,z4,z5,z1248])]],
   [[(0,[z0,z1,z3,z4,z1249,z8]),(0,[z0,z213,z3,z519,z5,z8]),(0,[z0,z1,z3,z4,z5,z1250]),(0,[z0,z1,z3,z55,z4,z333])],[(0,[z0,z1,z3,z1063,z5,z8]),(0,[z635,z143,z3,z4,z5,z8]),(0,[z0,z1,z345,z4,z5,z1155]),(0,[z0,z1,z353,z179,z4,z5]),(0,[z0,z1,z3,z4,z5,z1251]),(0,[z0,z1,z1252,z4,z5,z8]),(0,[z0,z1,z3,z4,z1253,z6])],[(0,[z0,z1,z3,z4,z5,z1254]),(0,[z0,z1169,z3,z4,z5,z8]),(0,[z0,z1,z47,z4,z154,z24]),(0,[z183,z1,z3,z4,z88,z5])],[(0,[z0,z1,z3,z4,z1255,z5]),(0,[z0,z1,z4,z1256,z5,z8]),(0,[z0,z1,z3,z917,z4,z24])],[(0,[z0,z1,z3,z4,z1257,z5]),(0,[z1258,z1,z3,z4,z5,z8]),(0,[z152,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1259,z5,z8]),(0,[z0,z1,z4,z5,z785,z24])],[(0,[z60,z0,z1,z502,z4,z8]),(0,[z96,z20,z1,z3,z4,z5]),(0,[z492,z46,z1,z3,z4,z5]),(0,[z0,z1,z82,z4,z5,z24]),(0,[z183,z0,z1,z3,z357,z4])],[(0,[z0,z1,z3,z4,z5,z1260]),(0,[z162,z20,z1,z3,z173,z5]),(0,[z20,z0,z1,z3,z519,z5]),(0,[z1261,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z357,z4,z430]),(0,[z183,z1,z36,z3,z4,z5])],[(0,[z1,z3,z97,z929,z5,z8]),(0,[z0,z1,z3,z4,z381,z232]),(0,[z0,z1,z3,z4,z5,z1188]),(0,[z0,z1,z3,z4,z5,z1262]),(0,[z0,z1,z3,z55,z4,z194])],[(0,[z0,z1,z3,z519,z5,z24]),(0,[z0,z1,z3,z1263,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1264]),(0,[z0,z1,z3,z1265,z5,z8]),(0,[z0,z1,z3,z4,z5,z1266]),(0,[z46,z0,z1,z3,z4,z711])],[(0,[z612,z1,z3,z4,z38,z8]),(0,[z0,z1,z4,z5,z6,z785]),(0,[z0,z1,z3,z4,z722,z6])],[],[(0,[z20,z0,z1,z3,z4,z471]),(0,[z183,z1,z3,z4,z5,z38])],[(0,[z0,z1,z3,z4,z5,z1267]),(0,[z0,z1,z634,z221,z5,z8]),(0,[z0,z1,z1268,z4,z5,z8]),(0,[z1269,z0,z1,z3,z4,z5]),(0,[z183,z1,z3,z4,z1270,z5])],[(0,[z1,z3,z4,z5,z126,z290]),(0,[z46,z0,z1,z3,z4,z1271])]],
   [[(0,[z0,z1,z3,z4,z218,z8]),(0,[z0,z1,z3,z55,z4,z34]),(0,[z0,z1,z3,z932,z5,z8])],[(0,[z162,z1,z91,z519,z5,z8]),(0,[z295,z1,z3,z4,z22,z8]),(0,[z0,z1,z3,z4,z1004,z24])],[(0,[z183,z1,z3,z4,z5,z6]),(0,[z1,z4,z5,z6,z346,z24]),(0,[z0,z1,z3,z4,z626,z232])],[(0,[z0,z1,z3,z1272,z4,z5]),(0,[z0,z1,z3,z4,z5,z1273]),(0,[z0,z1,z28,z668,z5,z8]),(0,[z1274,z1,z3,z4,z5,z8]),(0,[z0,z1,z1275,z3,z4,z5])],[(0,[z0,z163,z3,z4,z5,z6]),(0,[z0,z3,z932,z170,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1276]),(0,[z13,z1,z3,z14,z5,z8]),(0,[z1,z3,z4,z5,z24,z838])],[(0,[z0,z1,z3,z4,z5,z1277]),(0,[z0,z1,z3,z1278,z5,z8]),(0,[z0,z1,z251,z4,z5,z140]),(0,[z0,z26,z3,z4,z27,z8]),(0,[z0,z1,z3,z4,z5,z30])],[(0,[z0,z1,z345,z4,z5,z1176]),(0,[z20,z525,z1,z3,z4,z5]),(0,[z147,z183,z1,z3,z4,z5]),(0,[z31,z0,z1,z4,z5,z785]),(0,[z0,z1,z3,z101,z845,z8])],[(0,[z0,z1,z1279,z3,z5,z8]),(0,[z143,z812,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z1280,z5])],[(0,[z0,z1,z345,z4,z41,z8]),(0,[z46,z0,z1,z3,z1278,z5]),(0,[z152,z1,z251,z4,z5,z8]),(0,[z0,z1,z261,z221,z5,z40])],[(0,[z0,z1,z963,z4,z5,z8]),(0,[z1,z61,z3,z179,z4,z5]),(0,[z183,z1,z3,z4,z5,z75])],[(0,[z0,z1,z3,z4,z5,z1281])],[(0,[z0,z1282,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z731,z8]),(0,[z46,z0,z175,z3,z23,z5]),(0,[z295,z1,z82,z4,z5,z8]),(0,[z1,z3,z4,z5,z8,z1227]),(0,[z183,z1,z3,z4,z5,z346])],[(0,[z0,z1,z3,z4,z381,z6]),(0,[z183,z1,z3,z29,z4,z5])],[(0,[z0,z726,z3,z4,z5,z8]),(0,[z0,z1,z110,z4,z5,z24])],[(0,[z0,z1,z3,z4,z716,z8]),(0,[z0,z1,z251,z4,z5,z249])]],
   [[(0,[z20,z0,z1,z3,z886,z5]),(0,[z0,z1,z1012,z3,z5,z8]),(0,[z904,z152,z1,z3,z4,z5]),(0,[z0,z1,z1283,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1284]),(0,[z1285,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z1286,z8]),(0,[z0,z1,z357,z4,z6,z24])],[(0,[z0,z1,z3,z4,z5,z1287]),(0,[z0,z1,z1288,z4,z5,z8]),(0,[z183,z1,z261,z3,z4,z5])],[(0,[z0,z1,z590,z29,z5,z8]),(0,[z0,z1,z3,z1031,z4,z24])],[(0,[z526,z1,z3,z14,z5,z8]),(0,[z0,z1,z1289,z4,z5,z8]),(0,[z0,z1,z3,z4,z8,z1236])],[(0,[z0,z1,z3,z4,z5,z1290]),(0,[z217,z1,z61,z3,z4,z5]),(0,[z0,z1,z3,z4,z471,z24]),(0,[z0,z1,z28,z29,z5,z398])],[(0,[z128,z1,z3,z4,z38,z24]),(0,[z79,z1,z3,z4,z108,z363]),(0,[z20,z1,z132,z3,z4,z5]),(0,[z0,z1,z3,z1291,z5,z8])],[(0,[z0,z1,z3,z4,z5,z1292]),(0,[z46,z1,z3,z4,z528,z5]),(0,[z0,z1,z261,z221,z5,z6])],[(0,[z128,z1,z3,z4,z715,z8]),(0,[z0,z1,z3,z4,z1293,z8]),(0,[z0,z1,z3,z4,z5,z1294]),(0,[z0,z342,z3,z4,z5,z331]),(0,[z0,z1,z377,z3,z76,z24])],[(0,[z20,z0,z1,z4,z450,z5]),(0,[z20,z0,z1,z3,z4,z291]),(0,[z20,z0,z1,z3,z4,z381]),(0,[z20,z1,z3,z4,z5,z420]),(0,[z46,z1,z3,z4,z5,z231]),(0,[z183,z1,z353,z3,z4,z5]),(0,[z1099,z1,z3,z4,z5,z8])],[(0,[z0,z1,z1295,z4,z5,z8]),(0,[z20,z467,z1,z3,z4,z5])],[(0,[z486,z0,z1,z502,z3,z4]),(0,[z0,z1,z179,z4,z5,z41]),(0,[z0,z1296,z1,z3,z4,z5]),(0,[z20,z1,z3,z587,z4,z5]),(0,[z0,z26,z3,z4,z27,z6])],[(0,[z0,z1,z3,z4,z218,z193]),(0,[z0,z1,z3,z4,z5,z1297]),(0,[z0,z1,z3,z1046,z4,z24]),(0,[z0,z1,z3,z4,z774,z56])],[(0,[z0,z1,z3,z4,z274,z6]),(0,[z0,z1,z3,z1298,z4,z8]),(0,[z58,z46,z1,z3,z97,z5])],[(0,[z136,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z1299,z4,z5]),(0,[z0,z1,z3,z1300,z5,z8])],[(0,[z0,z1,z3,z4,z1301,z8]),(0,[z0,z1,z3,z4,z1253,z8]),(0,[z0,z1,z3,z4,z1271,z8]),(0,[z58,z1,z3,z97,z5,z302]),(0,[z0,z1,z3,z4,z5,z140]),(0,[z0,z1,z3,z357,z4,z402]),(0,[z0,z1,z417,z4,z5,z24])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 505).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1011).take 356) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1367)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [505, 506, 356] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 133).take 125).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 258).take 154).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 412).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [133, 125, 154, 100] = true :=
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

end PEqualNP.Outside.L_meta_38731

theorem PEqualNP.Outside.L_meta_38731 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4274055872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4274055872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38731.solve