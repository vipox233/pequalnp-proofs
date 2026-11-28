import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36332

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00200000140088ab#64 ++ 0x801000000a004455#64 ++ 0xffd0a4047c099fff#64 ++ 0xffe852023e04cfff#64 : BitVec 256),
   (0x10400a19b212a599#64 ++ 0x0820050cd90952cc#64 ++ 0x77b95a3bb236e599#64 ++ 0xbbdcad1dd91b72cc#64 : BitVec 256),
   (0x028262c2c2c70614#64 ++ 0x014131616163830a#64 ++ 0xed7e63c3c3c7061f#64 ++ 0x76bf31e1e1e3830f#64 : BitVec 256),
   (0xab05836c03780740#64 ++ 0x5582c1b601bc03a0#64 ++ 0xdcf783fc03f807e0#64 ++ 0xee7bc1fe01fc03f0#64 : BitVec 256),
   (0xcc07f40001ad5000#64 ++ 0x6603fa0000d6a800#64 ++ 0xc3fffc0003fff801#64 ++ 0xe1fffe0001fffc00#64 : BitVec 256),
   (0xf007fdb768000000#64 ++ 0x7803fedbb4000000#64 ++ 0x3ff7fffffc000000#64 ++ 0x1ffbfffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00200000140088ab 0x801000000a004455 0xffd0a4047c099fff 0xffe852023e04cfff

def z1 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7e63c3c3c7061f 0x76bf31e1e1e3830f

def z2 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff97a3bf237e79f 0xfffcbd1df91bf3cf

def z3 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcf783fc03f807e0 0xee7bc1fe01fc03f0

def z4 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc3fffc0003fff801 0xe1fffe0001fffc00

def z5 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc000000 0x1ffbfffffe000000

def z6 : W := mkw 0x0002608240000000 0x0001304120000000 0x3ff6e7c7fc000000 0x1ffb73e3fe000000

def z7 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b95a3bb236e599 0xbbdcad1dd91b72cc

def z8 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff9fe3ffe3fffff 0xfffcff1fff1fffff

def z9 : W := mkw 0xa905812c01380140 0x5482c096009c00a0 0x1081803c003801e0 0x8840c01e001c00f0

def z10 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xdffffc0403ffffe1 0xeffffe0201fffff0

def z11 : W := mkw 0x0000020082020410 0x0000010041010208 0x6538420382060419 0x329c2101c103020c

def z12 : W := mkw 0xab05836c837a0750 0x5582c1b641bd03a8 0xfdffc3ff83fe07f9 0xfeffe1ffc1ff03fc

def z13 : W := mkw 0x10426a9bf212a599 0x0821354df90952cc 0x7fff7bfbf236e599 0xbfffbdfdf91b72cc

def z14 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x00295a3b82366000 0x0014ad1dc11b3000

def z15 : W := mkw 0x0b00024803780740 0x0580012401bc03a0 0xdcd0800403f807e0 0xee68400201fc03f0

def z16 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x3400023bb0000598 0x1a00011dd80002cc

def z17 : W := mkw 0x00200000140088ab 0x801000000a004455 0x128084043c0899e0 0x894042021e044cf0

def z18 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x23295a3bb236e019 0x1194ad1dd91b700c

def z19 : W := mkw 0x0000020882120510 0x0000010441090288 0x75b9423b82360599 0xbadca11dc11b02cc

def z20 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0x1c0003fc000007e0 0x0e0001fe000003f0

def z21 : W := mkw 0xab05816401680240 0x5582c0b200b40120 0x884681c401c80260 0x442340e200e40130

def z22 : W := mkw 0xfb07ffff6b780740 0x7d83ffffb5bc03a0 0xfff7fffffff807e0 0xfffbfffffffc03f0

def z23 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xfffffffffffff801 0xfffffffffffffc00

def z24 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7f9fe3bb23ffd99 0xfbfcff1dd91ffecc

def z25 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x37b95a3bb2366000 0x1bdcad1dd91b3000

def z26 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3381fc3ffc000000 0x19c0fe1ffe000000

def z27 : W := mkw 0x0280024082c70614 0x014001204163830a 0xc008000003c7061f 0x6004000001e3830f

def z28 : W := mkw 0x0020000004000822 0x8010000002000411 0x8840a4044c091a66 0x4420520226048d33

def z29 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3c0003fffc000000 0x1e0001fffe000000

def z30 : W := mkw 0xa925812c153889eb 0xd492c0960a9c44f5 0xffd1a43c7c399fff 0xffe8d21e3e1ccfff

def z31 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xd081803c03f807e0 0xe840c01e01fc03f0

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x43b958000236e001 0xa1dcac00011b7000

def z33 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdfffdbfc03fee7e1 0xefffedfe01ff73f0

def z34 : W := mkw 0xdc47fe19b3bff599 0x6e23ff0cd9dffacc 0xf7fffe3bb3fffd99 0xfbffff1dd9fffecc

def z35 : W := mkw 0x10200811340088ab 0x881004089a004455 0xfff1fe3ffc099fff 0xfff8ff1ffe04cfff

def z36 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x03f7fc0000000000 0x01fbfe0000000000

def z37 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x002e43c383c60000 0x001721e1c1e30000

def z38 : W := mkw 0x0000000010008089 0x0000000008004044 0x7790000030008599 0xbbc80000180042cc

def z39 : W := mkw 0x1000081120000000 0x0800040890000000 0x00215a3b80000000 0x0010ad1dc0000000

def z40 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x40295a3b8236e599 0xa014ad1dc11b72cc

def z41 : W := mkw 0x00826082c0870014 0x004130416043800a 0x21086003c007001f 0x10843001e003800f

def z42 : W := mkw 0x0b80024883ff0754 0x05c0012441ff83aa 0xc008000003ff07ff 0xe004000001ff83ff

def z43 : W := mkw 0xcc07f40001285000 0x6603fa0000942800 0x03f7fc000038f800 0x81fbfe00001c7c00

def z44 : W := mkw 0xa0258124140088ab 0xd012c0920a004455 0xfff7a7fc7c099fff 0xfffbd3fe3e04cfff

def z45 : W := mkw 0x50427c93f802a099 0x28213e49fc01504c 0x23087c03fc06e019 0x11843e01fe03700c

def z46 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc008000003fff801 0xe004000001fffc00

def z47 : W := mkw 0x02a262c2d6c78ebf 0x815131616b63c75f 0xfffee7c7ffcf9fff 0xffff73e3ffe7cfff

def z48 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x37b75bfbb0000000 0x1bdbadfdd8000000

def z49 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3c0000047c0007fe 0x1e0000023e0003ff

def z50 : W := mkw 0xcc27f40015add8ab 0xe613fa000ad6ec55 0xfffffc047fffffff 0xfffffe023fffffff

def z51 : W := mkw 0xce87f6c2c3ef5614 0x6743fb6161f7ab0a 0xefffffc3c3fffe1f 0xf7ffffe1e1ffff0f

def z52 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x00275bfb80000000 0x0013adfdc0000000

def z53 : W := mkw 0xf287fff7eac70614 0x7943fffbf563830a 0xffffffffffc7061f 0x7fffffffffe3830f

def z54 : W := mkw 0x0002600000850000 0x0001300000428000 0xc17e600003c70001 0x60bf300001e38000

def z55 : W := mkw 0xf0259d353c0088ab 0xf812ce9a9e004455 0x12819c3c3c0899e0 0x8940ce1e1e044cf0

def z56 : W := mkw 0xf007ffb7ea020410 0x7803ffdbf5010208 0x7ffffffffe060419 0x3fffffffff03020c

def z57 : W := mkw 0x028260c240c50204 0x0141306120628102 0x884621c041c10206 0x442310e020e08103

def z58 : W := mkw 0x028002c2c2420614 0x014001616121030a 0x2c0003c3c000061e 0x160001e1e000030f

def z59 : W := mkw 0x00200000140088ab 0x801000000a004455 0xbc40a4047c091ffe 0x5e2052023e048fff

def z60 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x9c4683fc01c807e0 0x4e2341fe00e403f0

def z61 : W := mkw 0xce87f6c2c3ef5614 0x6743fb6161f7ab0a 0xed7ee7c3c3cf1e1f 0x76bf73e1e1e78f0f

def z62 : W := mkw 0x4402740000855000 0x22013a000042a800 0x03087c000007f801 0x01843e000003fc00

def z63 : W := mkw 0xeb07f7ee4b780740 0x7583fbf725bc03a0 0xdcf7a7fc4ff807e0 0xee7bd3fe27fc03f0

def z64 : W := mkw 0xf307ffff6a500740 0x7983ffffb52803a0 0x3ff7fffffc0007e0 0x1ffbfffffe0003f0

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0x2d50200040000000 0x16a8100020000000

def z66 : W := mkw 0xab25836c17788feb 0xd592c1b60bbc47f5 0xfff7a7fc7ff99fff 0xfffbd3fe3ffccfff

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x3fd0a4047c000000 0x1fe852023e000000

def z68 : W := mkw 0xf027fdb77c0088ab 0xf813fedbbe004455 0xfff7fffffc099fff 0xfffbfffffe04cfff

def z69 : W := mkw 0x12c26adbf2d7a79d 0x0961356df96bd3ce 0xffff7bfbf3f7e79f 0xffffbdfdf9fbf3cf

def z70 : W := mkw 0xcc05940001ad5000 0x6602ca0000d6a800 0xc2899c0003fff801 0xe144ce0001fffc00

def z71 : W := mkw 0x02a0024096c78ebf 0x815001204b63c75f 0xffd8a4047fcf9fff 0xffec52023fe7cfff

def z72 : W := mkw 0x0202624002c50600 0x0101312001628300 0xcd7e63c003c70601 0x66bf31e001e38300

def z73 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x002f580003f66000 0x0017ac0001fb3000

def z74 : W := mkw 0xf407fdb768855000 0x7a03fedbb442a800 0x3ffffffffc07f801 0x1ffffffffe03fc00

def z75 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0x02819c000038f800 0x8140ce00001c7c00

def z76 : W := mkw 0xfb07fdf769680240 0x7d83fefbb4b40120 0xbff7fffffdc80260 0x5ffbfffffee40130

def z77 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37085a3bb006e599 0x1b842d1dd80372cc

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0xed5020004001061f 0x76a810002000830f

def z79 : W := mkw 0x0002600000850000 0x0001300000428000 0x002e400003c60000 0x0017200001e30000

def z80 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x653e43c383c60419 0x329f21e1c1e3020c

def z81 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdff7a7fc03f99fe1 0xeffbd3fe01fccff0

def z82 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x74b1023bb2300598 0xba58811dd91802cc

def z83 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x63085803b236e599 0xb1842c01d91b72cc

def z84 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x002703f803f00000 0x001381fc01f80000

def z85 : W := mkw 0x028262c242c50604 0x0141316121628302 0xcc7623c043c10606 0x663b11e021e08303

def z86 : W := mkw 0x10400811b002a099 0x08200408d801504c 0x23085803b006e019 0x11842c01d803700c

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z88 : W := mkw 0xcc27f40005ad5822 0xe613fa0002d6ac11 0xcbfffc044ffffa67 0xe5fffe0227fffd33

def z89 : W := mkw 0xa005812400000000 0x5002c09200000000 0x002703f800000000 0x001381fc00000000

def z90 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0xc2f79c0003f8f800 0xe17bce0001fc7c00

def z91 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfd5020047c0107ff 0x7ea810023e0083ff

def z92 : W := mkw 0x0c00000001285000 0x0600000000942800 0x000000000038f800 0x80000000001c7c00

def z93 : W := mkw 0x00200000140088ab 0x801000000a004455 0xab40a4047c099a7f 0x55a052023e04cd3f

def z94 : W := mkw 0x2b00036c03780740 0x158001b601bc03a0 0xdc0003fc03f807e0 0xee0001fe01fc03f0

def z95 : W := mkw 0xab05816401680240 0x5582c0b200b40120 0x000601c001c00000 0x000300e000e00000

def z96 : W := mkw 0x0000008240000000 0x0000004120000000 0x2c0003c3c0000000 0x160001e1e0000000

def z97 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x3ffffffffff66000 0x1ffffffffffb3000

def z98 : W := mkw 0xf0059d3528000000 0x7802ce9a94000000 0x12819c3c3c000000 0x0940ce1e1e000000

def z99 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x43bf580003f6e001 0xa1dfac0001fb7000

def z100 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3fd0a7fffc000000 0x1fe853fffe000000

def z101 : W := mkw 0xbbc7ebfff3ffa7dd 0x5de3f5fff9ffd3ee 0xfffffbfff3ffe7ff 0xfffffdfff9fff3ff

def z102 : W := mkw 0x0200024002400600 0x0100012001200300 0xed7623c043c1061f 0x76bb11e021e0830f

def z103 : W := mkw 0x0200024002400600 0x0100012001200300 0xcc7603c003c00600 0x663b01e001e00300

def z104 : W := mkw 0xb005893520000000 0x5802c49a90000000 0x3ff7dbffb0000000 0x1ffbedffd8000000

def z105 : W := mkw 0xbb458b7da37a2750 0x5da2c5bed1bd13a8 0xdcffdbff83fe67e0 0xee7fedffc1ff33f0

def z106 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9da3fb23ee7f9 0xfffced1fd91f73fc

def z107 : W := mkw 0x02a260c254c58aaf 0x815130612a62c557 0xffd6a5c47dc99fff 0xffeb52e23ee4cfff

def z108 : W := mkw 0xa905812401280040 0x5482c09200940020 0x0000800400080060 0x0000400200040030

def z109 : W := mkw 0x104008193010a189 0x0820040c980850c4 0x128118383030e180 0x89408c1c181870c0

def z110 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x12a7dfffbc000000 0x0953efffde000000

def z111 : W := mkw 0xe007f5a648000000 0x7003fad324000000 0x1cf7a7fc4c000000 0x0e7bd3fe26000000

def z112 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc0ffd80003fe6000 0xe07fec0001ff3000

def z113 : W := mkw 0xcf07f64803fd5740 0x6783fb2401feaba0 0xc3fffc0003ffffe1 0xe1fffe0001fffff0

def z114 : W := mkw 0x0280024082420614 0x014001204121030a 0x000000000000061e 0x000000000000030f

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x128084043c000000 0x094042021e000000

def z116 : W := mkw 0x0000020082020410 0x0000010041010208 0xed786203c207061f 0x76bc3101e103830f

def z117 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1c8183fc003807e0 0x8e40c1fe001c03f0

def z118 : W := mkw 0x8805800001280000 0x4402c00000940000 0x8046800001c80000 0x4023400000e40000

def z119 : W := mkw 0xe287f7e6cac70614 0x7143fbf36563830a 0xed7ee7c7cfc7061f 0x76bf73e3e7e3830f

def z120 : W := mkw 0xf067ffbffe12adbb 0xf833ffdfff0956dd 0xfffffffffe3fffff 0xffffffffff1fffff

def z121 : W := mkw 0x0000020802100500 0x0000010401080280 0xdcf1823c023807e0 0xee78c11e011c03f0

def z122 : W := mkw 0xf0259d353c0088ab 0xf812ce9a9e004455 0xffd1bc3c7c099fff 0xffe8de1e3e04cfff

def z123 : W := mkw 0x0b00024803780740 0x0580012401bc03a0 0xd4b1023803f807e0 0xea58811c01fc03f0

def z124 : W := mkw 0xe007f5a648000000 0x7003fad324000000 0x0846a5c44c000000 0x042352e226000000

def z125 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0xcbfffdc44ffff801 0xe5fffee227fffc00

def z126 : W := mkw 0xab05816c01780340 0x5582c0b600bc01a0 0x98c781fc01f803e0 0xcc63c0fe00fc01f0

def z127 : W := mkw 0x10600811b402a8bb 0x88300408da01545d 0xffd8fc07fc0fffff 0xffec7e03fe07ffff

def z128 : W := mkw 0x0000000010008089 0x0000000008004044 0x7fd0a4047c008599 0xbfe852023e0042cc

def z129 : W := mkw 0xfb07ffff6b780740 0x7d83ffffb5bc03a0 0x00275bfb83f00000 0x0013adfdc1f80000

def z130 : W := mkw 0x004002089212a599 0x00200104490952cc 0x54b902380236e599 0xaa5c811c011b72cc

def z131 : W := mkw 0x50027c9368000000 0x28013e49b4000000 0x23007c03fc000000 0x11803e01fe000000

def z132 : W := mkw 0x1000081120000000 0x0800040890000000 0x77b95a3bb236e001 0xbbdcad1dd91b7000

def z133 : W := mkw 0xce87f6c2c3ef5614 0x6743fb6161f7ab0a 0xed7f7bc3c3f7661f 0x76bfbde1e1fbb30f

def z134 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x032f7c0003f7f801 0x0197be0001fbfc00

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3d0a40000099801 0xe1e852000004cc00

def z136 : W := mkw 0x00200000140088ab 0x801000000a004455 0xc000000000099fff 0xe00000000004cfff

def z137 : W := mkw 0x00200000140088ab 0x801000000a004455 0x779084043c089df9 0xbbc842021e044efc

def z138 : W := mkw 0xf287fff7ea420614 0x7943fffbf521030a 0x3ff7fffffc00061e 0x1ffbfffffe00030f

def z139 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0x000003f800000000 0x000001fc00000000

def z140 : W := mkw 0x0300024802500740 0x01800124012803a0 0x00000000000007e0 0x00000000000003f0

def z141 : W := mkw 0x104008193010a189 0x0820040c980850c4 0x779118383030e599 0xbbc88c1c181872cc

def z142 : W := mkw 0x0020000004000822 0x8010000002000411 0x8000000000091a66 0x4000000000048d33

def z143 : W := mkw 0x02a262c2d6c78ebf 0x815131616b63c75f 0xef7e67c3ffc79e1f 0x77bf33e1ffe3cf0f

def z144 : W := mkw 0x10426a19b297a599 0x0821350cd94bd2cc 0xf7ff7a3bb3f7e599 0xfbffbd1dd9fbf2cc

def z145 : W := mkw 0x0e80024083ef5614 0x0740012041f7ab0a 0xc008000003fffe1f 0xe004000001ffff0f

def z146 : W := mkw 0xef05976c03785740 0x7782cbb601bc2ba0 0xdef79ffc03f8ffe0 0xef7bcffe01fc7ff0

def z147 : W := mkw 0xab25836c07780f62 0xd592c1b603bc07b1 0xdcf7a7fc4ff91fe6 0xee7bd3fe27fc8ff3

def z148 : W := mkw 0x0200024802500700 0x0100012401280380 0xdcf703f803f00780 0xee7b81fc01f803c0

def z149 : W := mkw 0x300269b768000000 0x180134dbb4000000 0x3d7663fffc000000 0x1ebb31fffe000000

def z150 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x7ffffffffe36e001 0xbfffffffff1b7000

def z151 : W := mkw 0x02a0024096c78ebf 0x815001204b63c75f 0xc008000003cf9fff 0xe004000001e7cfff

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3f9fc00023ff801 0xe1fcfe00011ffc00

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0xc076000003c00000 0x603b000001e00000

def z154 : W := mkw 0xed07f52c01bd5140 0x7683fa9600dea8a0 0xd3fffc3c03fff9e1 0xe9fffe1e01fffcf0

def z155 : W := mkw 0x0b00024803780740 0x0580012401bc03a0 0xc000000003f807e0 0xe000000001fc03f0

def z156 : W := mkw 0xfb27ffff7f788feb 0xfd93ffffbfbc47f5 0xfff7fffffff99fff 0xfffbfffffffccfff

def z157 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfff7a7fc7ff807e0 0xfffbd3fe3ffc03f0

def z158 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3e8084047c089ffe 0x9f4042023e044fff

def z159 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7408023bb236e599 0xba04011dd91b72cc

def z160 : W := mkw 0x028002c2c2420614 0x014001616121030a 0xed5023c3c001061f 0x76a811e1e000830f

def z161 : W := mkw 0xfc27fdb77dadd8ab 0xfe13fedbbed6ec55 0xffffffffffffffff 0xffffffffffffffff

def z162 : W := mkw 0xdc47fe19a3bf7510 0x6e23ff0cd1dfba88 0xc3fffe3b83fff801 0xe1ffff1dc1fffc00

def z163 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xf7b95a3bb23fffff 0xfbdcad1dd91fffff

def z164 : W := mkw 0x0b00004001680240 0x0580002000b40120 0x8000000001c80260 0x4000000000e40130

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0xdcd08004000807e0 0xee684002000403f0

def z166 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b97e3bfe37fd9f 0xbbdcbf1dff1bfecf

def z167 : W := mkw 0xef07f76c03fd5740 0x7783fbb601feaba0 0xdcffdbfc03fe67e0 0xee7fedfe01ff33f0

def z168 : W := mkw 0xef07f76c03fd5740 0x7783fbb601feaba0 0xdffffffc03ffffe1 0xeffffffe01fffff0

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x028118000030e000 0x81408c0000187000

def z170 : W := mkw 0x00200000140088ab 0x801000000a004455 0x779024007c019d9f 0xbbc812003e00cecf

def z171 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3c46a7fffc000000 0x1e2353fffe000000

def z172 : W := mkw 0xa305836c02500740 0x5182c1b6012803a0 0x1cf783fc000007e0 0x0e7bc1fe000003f0

def z173 : W := mkw 0x1000081120000000 0x0800040890000000 0x3400023bb0000000 0x1a00011dd8000000

def z174 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x23277ffbfc000000 0x1193bffdfe000000

def z175 : W := mkw 0xb945893d3138a1c9 0x5ca2c49e989c50e4 0x1281983c3038e1e0 0x8940cc1e181c70f0

def z176 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x3f007ffffc000000 0x1f803ffffe000000

def z177 : W := mkw 0x468276c2c2c75614 0x23413b616163ab0a 0xef7e7fc3c3c7fe1f 0x77bf3fe1e1e3ff0f

def z178 : W := mkw 0x54427e19b297f599 0x2a213f0cd94bfacc 0x77b97e3bb237fd99 0xbbdcbf1dd91bfecc

def z179 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0x0008000003f66000 0x0004000001fb3000

def z180 : W := mkw 0xd007fc9368000000 0x6803fe49b4000000 0x23f7fc03fc000000 0x11fbfe01fe000000

def z181 : W := mkw 0x8805800001280000 0x4402c00000940000 0xdcf7800403f807e0 0xee7bc00201fc03f0

def z182 : W := mkw 0x004002089212a599 0x00200104490952cc 0x400800000236e599 0xa0040000011b72cc

def z183 : W := mkw 0x1000081120000000 0x0800040890000000 0x37b15a3bb0000000 0x1bd8ad1dd8000000

def z184 : W := mkw 0x0020000004000822 0x8010000002000411 0x080000044c000266 0x0400000226000133

def z185 : W := mkw 0xab87e3eec3ff0754 0x55c3f1f761ff83aa 0xfdffe3ffc3ff07ff 0xfefff1ffe1ff83ff

def z186 : W := mkw 0xf047ffbffa12a599 0x7823ffdffd0952cc 0x7ffffffffe36e599 0xbfffffffff1b72cc

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x0280840000089800 0x8140420000044c00

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x5490000000000580 0xaa480000000002c0

def z189 : W := mkw 0x1000081120000000 0x0800040890000000 0x3ff1fe3ffc000000 0x1ff8ff1ffe000000

def z190 : W := mkw 0x00200000140088ab 0x801000000a004455 0x230024007c01981f 0x118012003e00cc0f

def z191 : W := mkw 0x200001a648000000 0x100000d324000000 0x080001c44c000000 0x040000e226000000

def z192 : W := mkw 0x028260c240c50204 0x0141306120628102 0x000601c001c00000 0x000300e000e00000

def z193 : W := mkw 0x238263eec2d70754 0x11c131f7616b83aa 0xfd7e63ffc3c707ff 0x7ebf31ffe1e383ff

def z194 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc01061f 0x7ffbfffffe00830f

def z195 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc3d6a40001c99801 0xe1eb520000e4cc00

def z196 : W := mkw 0xf047ffbfea122510 0x7823ffdff5091288 0x3ffffffffe366000 0x1fffffffff1b3000

def z197 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc0807e0 0xfffbfffffe0403f0

def z198 : W := mkw 0x0002600000000000 0x0001300000000000 0x0176600000000000 0x00bb300000000000

def z199 : W := mkw 0x0000020082020410 0x0000010041010208 0x0028420382060000 0x00142101c1030000

def z200 : W := mkw 0x50027c9368000000 0x28013e49b4000000 0x0000580380000000 0x00002c01c0000000

def z201 : W := mkw 0x4402740000855000 0x22013a000042a800 0xc3d8fc00000ff801 0xe1ec7e000007fc00

def z202 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x3ff7fc047c000000 0x1ffbfe023e000000

def z203 : W := mkw 0x0002600000850000 0x0001300000428000 0x8046200001c10000 0x4023100000e08000

def z204 : W := mkw 0xa905812c01380140 0x5482c096009c00a0 0xd0f7803c03f801e0 0xe87bc01e01fc00f0

def z205 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0x5cb103fc023007e0 0xae5881fe011803f0

def z206 : W := mkw 0xab45836c937aa7d9 0x55a2c1b649bd53ec 0xdcff83fc03fee7f9 0xee7fc1fe01ff73fc

def z207 : W := mkw 0x12c00adbf252a79d 0x0960056df92953ce 0x7fb95bfbf236e79f 0xbfdcadfdf91b73cf

def z208 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x3c00023ffc0007fe 0x1e00011ffe0003ff

def z209 : W := mkw 0xa005812400000000 0x5002c09200000000 0x3ff7a7fc7c000000 0x1ffbd3fe3e000000

def z210 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x0027580000000000 0x0013ac0000000000

def z211 : W := mkw 0x00200000140088ab 0x801000000a004455 0xd28084043c099fff 0xe94042021e04cfff

def z212 : W := mkw 0xd007fc1120000000 0x6803fe0890000000 0x37f7fe3bb0000000 0x1bfbff1dd8000000

def z213 : W := mkw 0x004002089212a599 0x00200104490952cc 0x0000000000000598 0x00000000000002cc

def z214 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x0000023b80000000 0x0000011dc0000000

def z215 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xc3fffffb83fff801 0xe1fffffdc1fffc00

def z216 : W := mkw 0xe007f5a648000000 0x7003fad324000000 0x2d76e7c7cc000000 0x16bb73e3e6000000

def z217 : W := mkw 0x0082608240850004 0x0041304120428002 0x0000200040010006 0x0000100020008003

def z218 : W := mkw 0x10400819b012a199 0x0820040cd80950cc 0x3389583bb036e199 0x99c4ac1dd81b70cc

def z219 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2d0863c3c007061f 0x168431e1e003830f

def z220 : W := mkw 0x3000093528000000 0x1800049a94000000 0x1000003c3c000000 0x0800001e1e000000

def z221 : W := mkw 0x028262c2c2420614 0x014131616121030a 0x2d7663c3c000061e 0x16bb31e1e000030f

def z222 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc0f7800003f80000 0xe07bc00001fc0000

def z223 : W := mkw 0xc007f48240000000 0x6003fa4120000000 0x2ff7ffc3c0000000 0x17fbffe1e0000000

def z224 : W := mkw 0xbb458b7db37aa7d9 0x5da2c5bed9bd53ec 0xffffdbffb3fee7f9 0xffffedffd9ff73fc

def z225 : W := mkw 0xa005812400000000 0x5002c09200000000 0x1cf783fc00000000 0x0e7bc1fe00000000

def z226 : W := mkw 0xf0059d3528000000 0x7802ce9a94000000 0x3fd1bc3c7c000000 0x1fe8de1e3e000000

def z227 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0xc3f7fc0000099801 0xe1fbfe000004cc00

def z228 : W := mkw 0x00a26082d48788bf 0x805130416a43c45f 0xffd8e407fc0f9fff 0xffec7203fe07cfff

def z229 : W := mkw 0x104008193010a189 0x0820040c980850c4 0x53b958383236e181 0xa9dcac1c191b70c0

def z230 : W := mkw 0x0000000010008089 0x0000000008004044 0xffd08004300887f9 0xffe84002180443fc

def z231 : W := mkw 0xab25816415688aeb 0xd592c0b20ab44575 0xffd6a5c47dc99fff 0xffeb52e23ee4cfff

def z232 : W := mkw 0xbb458b7db37aa7d9 0x5da2c5bed9bd53ec 0xfcf783ffb3f807f8 0xfe7bc1ffd9fc03fc

def z233 : W := mkw 0x00a26082d48788bf 0x805130416a43c45f 0x23086403fc07981f 0x11843201fe03cc0f

def z234 : W := mkw 0x0000020802100500 0x0000010401080280 0x0021023802300000 0x0010811c01180000

def z235 : W := mkw 0x0002600000850000 0x0001300000428000 0xed7e600043c7061f 0x76bf300021e3830f

def z236 : W := mkw 0xab05836403680640 0x5582c1b201b40320 0xcc7683c403c80660 0x663b41e201e40330

def z237 : W := mkw 0x8005800000000000 0x4002c00000000000 0x00f7800000000000 0x007bc00000000000

def z238 : W := mkw 0x004002089212a599 0x00200104490952cc 0x43b958000236e599 0xa1dcac00011b72cc

def z239 : W := mkw 0x12e26adbf6d7afbf 0x8971356dfb6bd7df 0xffffffffffffffff 0xffffffffffffffff

def z240 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x54b95a3b82366580 0xaa5cad1dc11b32c0

def z241 : W := mkw 0x028262cac2d70714 0x01413165616b838a 0xfdff63fbc3f7079f 0xfeffb1fde1fb83cf

def z242 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff9fc047e3fffff 0xfffcfe023f1fffff

def z243 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0x0001180000306000 0x00008c0000183000

def z244 : W := mkw 0x0002608240000000 0x0001304120000000 0x2d7663c3c0000000 0x16bb31e1e0000000

def z245 : W := mkw 0x0200024002400600 0x0100012001200300 0x002603c003c00000 0x001301e001e00000

def z246 : W := mkw 0xce87f6c2c3ef5614 0x6743fb6161f7ab0a 0xc3ffffc383fff801 0xe1ffffe1c1fffc00

def z247 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xc02703f803f807e0 0xe01381fc01fc03f0

def z248 : W := mkw 0xcc2594001528d8ab 0xe612ca000a946c55 0xffd1bc047c39ffff 0xffe8de023e1cffff

def z249 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfdf7a3fc43f907ff 0xfefbd1fe21fc83ff

def z250 : W := mkw 0x006002089612adbb 0x803001044b0956dd 0xc0080000023fffff 0xe0040000011fffff

def z251 : W := mkw 0x12c26adbe2d72714 0x0961356df16b938a 0xed7f7bfbc3f7661f 0x76bfbdfde1fbb30f

def z252 : W := mkw 0x02c0024892d7a79d 0x01600124496bd3ce 0xc008000003f7e79f 0xe004000001fbf3cf

def z253 : W := mkw 0x32800bf7ea420614 0x194005fbf521030a 0x3c0003fffc00061e 0x1e0001fffe00030f

def z254 : W := mkw 0x004000009002a099 0x002000004801504c 0x000800000006e019 0x000400000003700c

def z255 : W := mkw 0xec07f52401ad5000 0x7603fa9200d6a800 0xdffffffc03fff801 0xeffffffe01fffc00

def z256 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x34295a3bb2366598 0x1a14ad1dd91b32cc

def z257 : W := mkw 0xef07f56401ed5240 0x7783fab200f6a920 0x8846a5c401c91a60 0x442352e200e48d30

def z258 : W := mkw 0xcc27f40015add8ab 0xe613fa000ad6ec55 0xe3fffc007ffff81f 0xf1fffe003ffffc0f

def z259 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0xffffffffffc70001 0x7fffffffffe38000

def z260 : W := mkw 0xbb458b7da37a2750 0x5da2c5bed1bd13a8 0x002f5bfb83f66000 0x0017adfdc1fb3000

def z261 : W := mkw 0xab05816401680240 0x5582c0b200b40120 0x9cf783fc01c80260 0x4e7bc1fe00e40130

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00000000001061f 0x600000000000830f

def z263 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0xc3d1bc000039f801 0xe1e8de00001cfc00

def z264 : W := mkw 0x0c20000015add8ab 0x861000000ad6ec55 0xc008000003ffffff 0xe004000001ffffff

def z265 : W := mkw 0x0000000010008089 0x0000000008004044 0xffd020007001879f 0xffe810003800c3cf

def z266 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3fb15bfffc000000 0x1fd8adfffe000000

def z267 : W := mkw 0x8c05800001ad5000 0x4602c00000d6a800 0xc0ff800003fff801 0xe07fc00001fffc00

def z268 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x212e63c3c3c7001f 0x109731e1e1e3800f

def z269 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xac4623c3c1c1061e 0x562311e1e0e0830f

def z270 : W := mkw 0x0200004000400200 0x0100002000200100 0x884601c001c00200 0x442300e000e00100

def z271 : W := mkw 0xbb658b7db77aaffb 0xddb2c5bedbbd57fd 0xffffffffffffffff 0xffffffffffffffff

def z272 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xefff7bc3c3f7e61f 0xf7ffbde1e1fbf30f

def z273 : W := mkw 0x10400811a0022010 0x08200408d0011008 0x0008580380066000 0x00042c01c0033000

def z274 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x43b95a3b8236e001 0xa1dcad1dc11b7000

def z275 : W := mkw 0xcc87f482c1af5014 0x6643fa4160d7a80a 0xe3fffc03c3fff81f 0xf1fffe01e1fffc0f

def z276 : W := mkw 0x44827482c0875014 0x22413a416043a80a 0x23087c03c007f81f 0x11843e01e003fc0f

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd0a4047c01061f 0x7fe852023e00830f

def z278 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc3b9580003fff801 0xe1dcac0001fffc00

def z279 : W := mkw 0xf2c7fffffad7a79d 0x7963fffffd6bd3ce 0xfffffffffff7e79f 0xfffffffffffbf3cf

def z280 : W := mkw 0xab85836c83ff0754 0x55c2c1b641ff83aa 0xdcff83fc03ff07ff 0xee7fc1fe01ff83ff

def z281 : W := mkw 0xab25836c17788feb 0xd592c1b60bbc47f5 0xfcf783fc7ff807fe 0xfe7bc1fe3ffc03ff

def z282 : W := mkw 0xce87f4c241ed5204 0x6743fa6120f6a902 0xcbfffdc043fffa07 0xe5fffee021fffd03

def z283 : W := mkw 0xcc07f48241ad5000 0x6603fa4120d6a800 0xefffffc3c3fff801 0xf7ffffe1e1fffc00

def z284 : W := mkw 0xa905812c01380140 0x5482c096009c00a0 0x1cf783fc003801e0 0x8e7bc1fe001c00f0

def z285 : W := mkw 0x12400a59b252a799 0x0920052cd92953cc 0xffff5bfbb3f6e799 0xffffadfdd9fb73cc

def z286 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x02afdc0003fef800 0x8157ee0001ff7c00

def z287 : W := mkw 0xfc07fdb769285000 0x7e03fedbb4942800 0x3ff7fffffc38f800 0x9ffbfffffe1c7c00

def z288 : W := mkw 0x104008193010a189 0x0820040c980850c4 0x37b15a3bb030e180 0x9bd8ad1dd81870c0

def z289 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x8046a40001c91800 0x4023520000e48c00

def z290 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x886783fc03f80260 0x4433c1fe01fc0130

def z291 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1c2703fc03f007e0 0x0e1381fe01f803f0

def z292 : W := mkw 0xcc2594001528d8ab 0xe612ca000a946c55 0x12819c043c38f9e0 0x8940ce021e1c7cf0

def z293 : W := mkw 0x0b8262cac3ff0754 0x05c1316561ff83aa 0xed7e63c3c3ff07ff 0xf6bf31e1e1ff83ff

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd0a4047c099801 0xffe852023e04cc00

def z295 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xeffffc0043fffe1f 0xf7fffe0021ffff0f

def z296 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b9de3fbe3efdf9 0xbbdcef1fdf1f7efc

def z297 : W := mkw 0x028002c2c2420614 0x014001616121030a 0x000003c380000000 0x000001e1c0000000

def z298 : W := mkw 0xab05816401680240 0x5582c0b200b40120 0xdcd681c401c807e0 0xee6b40e200e403f0

def z299 : W := mkw 0xf0059d3528000000 0x7802ce9a94000000 0x1ef79ffc3c000000 0x0f7bcffe1e000000

def z300 : W := mkw 0xf0459f3dba12a599 0x7822cf9edd0952cc 0x77b9de3fbe36e599 0xbbdcef1fdf1b72cc

def z301 : W := mkw 0x4002740000000000 0x20013a0000000000 0x03007c0000000000 0x01803e0000000000

def z302 : W := mkw 0x020262c242400600 0x0101316121200300 0xed7663c3c3c00600 0x76bb31e1e1e00300

def z303 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc17f780003f76001 0x60bfbc0001fbb000

def z304 : W := mkw 0x00200000140088ab 0x801000000a004455 0x00000000000007fe 0x00000000000003ff

def z305 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7790023bb0008599 0xbbc8011dd80042cc

def z306 : W := mkw 0x1000089368000000 0x08000449b4000000 0x20000003fc000000 0x10000001fe000000

def z307 : W := mkw 0x30400bbffa12a599 0x182005dffd0952cc 0x7fb95bfffe36e599 0xbfdcadffff1b72cc

def z308 : W := mkw 0x10600811b402a8bb 0x88300408da01545d 0x23087c03fc07f81f 0x11843e01fe03fc0f

def z309 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc02f580003fff801 0xe017ac0001fffc00

def z310 : W := mkw 0x0002608240000000 0x0001304120000000 0x084621c040000000 0x042310e020000000

def z311 : W := mkw 0xb00589b768000000 0x5802c4dbb4000000 0x3cf783fffc000000 0x1e7bc1fffe000000

def z312 : W := mkw 0x442274001485d8ab 0xa2113a000a42ec55 0xffd8fc047c0fffff 0xffec7e023e07ffff

def z313 : W := mkw 0x8a05824003680600 0x4502c12001b40300 0xccf783c003f80600 0xe67bc1e001fc0300

def z314 : W := mkw 0xcc07f60083af5410 0x6603fb0041d7aa08 0xe7fffe0383fffc19 0xf3ffff01c1fffe0c

def z315 : W := mkw 0x12c00a59b2d7a79d 0x0960052cd96bd3ce 0xf7b95a3bb3f7e79f 0xfbdcad1dd9fbf3cf

def z316 : W := mkw 0xce87f64083ef5614 0x6743fb2041f7ab0a 0xc3fffc0003fffe1f 0xe1fffe0001ffff0f

def z317 : W := mkw 0x54427c11b087f099 0x2a213e08d843f84c 0x23087c03b007f819 0x11843e01d803fc0c

def z318 : W := mkw 0x0020000004000822 0x8010000002000411 0xcbd0a4044c099a67 0xe5e852022604cd33

def z319 : W := mkw 0xdc47fe19a3bf7510 0x6e23ff0cd1dfba88 0x002f5a3b83f66000 0x0017ad1dc1fb3000

def z320 : W := mkw 0x4c02740001ad5000 0x26013a0000d6a800 0xc3087c0003fff801 0xe1843e0001fffc00

def z321 : W := mkw 0xce07f64003ed5600 0x6703fb2001f6ab00 0xcfffffc003fffe01 0xe7ffffe001ffff00

def z322 : W := mkw 0x2320036c16508feb 0x919001b60b2847f5 0xffd0a7fc7c099fff 0xffe853fe3e04cfff

def z323 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0xfff7fffffff80000 0xfffbfffffffc0000

def z324 : W := mkw 0x0000000010008089 0x0000000008004044 0x1280000030008180 0x89400000180040c0

def z325 : W := mkw 0x0000000010008089 0x0000000008004044 0x2300000030008019 0x118000001800400c

def z326 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x54b703f803f00580 0xaa5b81fc01f802c0

def z327 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xc0f783f803f80000 0xe07bc1fc01fc0000

def z328 : W := mkw 0x0000020802100500 0x0000010401080280 0x54b1023802300580 0xaa58811c011802c0

def z329 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc0f7a40003f91800 0xe07bd20001fc8c00

def z330 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7ff9fe3ffe36e599 0xbffcff1fff1b72cc

def z331 : W := mkw 0xf287fdf768c50204 0x7943fefbb4628102 0xbff7fffffdc10206 0x5ffbfffffee08103

def z332 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xc84681c403f807e0 0xe42340e201fc03f0

def z333 : W := mkw 0xe007f5a648000000 0x7003fad324000000 0x000601c000000000 0x000300e000000000

def z334 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1cf783fc03f00000 0x0e7bc1fe01f80000

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0xefd0a40040099e1f 0xf7e852002004cf0f

def z336 : W := mkw 0x10400811b002a099 0x08200408d801504c 0x20000003b0000018 0x10000001d800000c

def z337 : W := mkw 0x33000bff6a500740 0x198005ffb52803a0 0x3c0003fffc0007e0 0x1e0001fffe0003f0

def z338 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x886e63c3c3c70206 0x443731e1e1e38103

def z339 : W := mkw 0xcc27f40005ad5822 0xe613fa0002d6ac11 0x8846a4044dc91a66 0x4423520226e48d33

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x030858000006e001 0x01842c0000037000

def z341 : W := mkw 0x2300016400400240 0x118000b200200120 0x080001c400000260 0x040000e200000130

def z342 : W := mkw 0xaf05836c03fd5740 0x5782c1b601feaba0 0xdcff83fc03ffffe1 0xee7fc1fe01fffff0

def z343 : W := mkw 0x02a262c2c6c70e36 0x815131616363871b 0xed7ee7c7cfcf1e7f 0x76bf73e3e7e78f3f

def z344 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3380a4047c0999ff 0x99c052023e04ccff

def z345 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7538423bb2060599 0x3a9c211dd90302cc

def z346 : W := mkw 0x4402740000855000 0x22013a000042a800 0x0008580000066000 0x00042c0000033000

def z347 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3c275bfffc000000 0x1e13adfffe000000

def z348 : W := mkw 0xe027f5a64c000822 0xf013fad326000411 0x8846a5c44c091a66 0x442352e226048d33

def z349 : W := mkw 0x0f00024803fd5740 0x0780012401feaba0 0xc008000003ffffe1 0xe004000001fffff0

def z350 : W := mkw 0xf0059d3528000000 0x7802ce9a94000000 0x0001183800000000 0x00008c1c00000000

def z351 : W := mkw 0x0200024002400600 0x0100012001200300 0xc000000003c00600 0x6000000001e00300

def z352 : W := mkw 0x02a260c244c50a26 0x8151306122628513 0x8846a5c44dc91a66 0x442352e226e48d33

def z353 : W := mkw 0x8805800001280000 0x4402c00000940000 0x0027000003f00000 0x0013800001f80000

def z354 : W := mkw 0x104008193010a189 0x0820040c980850c4 0x1000003830000180 0x0800001c180000c0

def z355 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x002f5bfb83f66000 0x0017adfdc1fb3000

def z356 : W := mkw 0x0000000010008089 0x0000000008004044 0x77b958003236e599 0xbbdcac00191b72cc

def z357 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc3d8a40003fff801 0xe1ec520001fffc00

def z358 : W := mkw 0x0000020802100500 0x0000010401080280 0x57b95a380236e581 0xabdcad1c011b72c0

def z359 : W := mkw 0x028002c2c2420614 0x014001616121030a 0xec7603c3c3c0061e 0x763b01e1e1e0030f

def z360 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xc02e43c383c7061f 0x601721e1c1e3830f

def z361 : W := mkw 0x0220024016408eab 0x811001200b204755 0xfff6a7c47fc99fff 0xfffb53e23fe4cfff

def z362 : W := mkw 0x4402740000855000 0x22013a000042a800 0xc37e7c0003c7f801 0x61bf3e0001e3fc00

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x10808004000801e0 0x88404002000400f0

def z364 : W := mkw 0x0000020002000400 0x0000010001000200 0x4430020002000400 0x2218010001000200

def z365 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xbff7fffffdc91800 0x5ffbfffffee48c00

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000000000807e0 0xe0000000000403f0

def z367 : W := mkw 0xfc47ffbffbbff599 0x7e23ffdffddffacc 0xfffffffffffffd99 0xfffffffffffffecc

def z368 : W := mkw 0x12c26adbf2d7a79d 0x0961356df96bd3ce 0x77bf5bfbb3f6e599 0xbbdfadfdd9fb72cc

def z369 : W := mkw 0xe287f5e648c50204 0x7143faf324628102 0x8846a5c44dc10206 0x442352e226e08103

def z370 : W := mkw 0xcc47f60893bff599 0x6623fb0449dffacc 0xc3fffc0003fffd99 0xe1fffe0001fffecc

def z371 : W := mkw 0x8a87e2c2c3ef0614 0x4543f16161f7830a 0xedffe3c3c3ff061f 0xf6fff1e1e1ff830f

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040a40000091800 0x4020520000048c00

def z373 : W := mkw 0x0000020082020410 0x0000010041010208 0x67b95a038236e419 0xb3dcad01c11b720c

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x400800000236e001 0xa0040000011b7000

def z375 : W := mkw 0x0020000004000822 0x8010000002000411 0xbfd0a4047c091a66 0x5fe852023e048d33

def z376 : W := mkw 0x50227c937c0088ab 0xa8113e49be004455 0xffd0fc07fc099fff 0xffe87e03fe04cfff

def z377 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x65395a3b82366419 0x329cad1dc11b320c

def z378 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0x0000840000081800 0x0000420000040c00

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0xffd0a4047c0807e0 0xffe852023e0403f0

def z380 : W := mkw 0xaba7e3eed7ff8fff 0xd5d3f1f76bffc7ff 0xffffe7ffffff9fff 0xfffff3ffffffcfff

def z381 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xc84e21c043c7061f 0x642710e021e3830f

def z382 : W := mkw 0x028260c240c50204 0x0141306120628102 0xad7663c3c1c10206 0x56bb31e1e0e08103

def z383 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfcd080047c0807fe 0xfe6840023e0403ff

def z384 : W := mkw 0x0002608240850000 0x0001304120428000 0xed7e63c3c3c70001 0x76bf31e1e1e38000

def z385 : W := mkw 0x1040081920102100 0x0820040c90081080 0x0001183800306000 0x00008c1c00183000

def z386 : W := mkw 0x02a262c2d6c78ebf 0x815131616b63c75f 0xed7e63c3c3cf9fff 0xf6bf31e1e1e7cfff

def z387 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x0006000001c00000 0x0003000000e00000

def z388 : W := mkw 0xab25836c17788feb 0xd592c1b60bbc47f5 0xdcf783fc03f99fff 0xee7bc1fe01fccfff

def z389 : W := mkw 0xdc459c193138f189 0x6e22ce0c989c78c4 0x12819c383038f980 0x8940ce1c181c7cc0

def z390 : W := mkw 0x0c20000015add8ab 0x861000000ad6ec55 0xffd8a4047fffffff 0xffec52023fffffff

def z391 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xfffffc047ffff801 0xfffffe023ffffc00

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c7603c000000000 0x063b01e000000000

def z393 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfc0000047c099fff 0xfe0000023e04cfff

def z394 : W := mkw 0x32826bf7eac70614 0x194135fbf563830a 0xfd7e63ffffc7061f 0x7ebf31ffffe3830f

def z395 : W := mkw 0xcc27f40015add8ab 0xe613fa000ad6ec55 0xc3fffc0003ffffff 0xe1fffe0001ffffff

def z396 : W := mkw 0xf047ffbffa12a599 0x7823ffdffd0952cc 0x77bf5bfbb236e599 0xbbdfadfdd91b72cc

def z397 : W := mkw 0xce87f6c2c3ef5614 0x6743fb6161f7ab0a 0x002f5bc383f66000 0x0017ade1c1fb3000

def z398 : W := mkw 0x10000a11a2020410 0x08000508d1010208 0x77b95a3bb2060419 0x3bdcad1dd903020c

def z399 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0x8000000001c91800 0x4000000000e48c00

def z400 : W := mkw 0xbb058bff6b780740 0x5d82c5ffb5bc03a0 0xfcf783fffff807e0 0xfe7bc1fffffc03f0

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x2530420380000000 0x12982101c0000000

def z402 : W := mkw 0xf0059d3528000000 0x7802ce9a94000000 0x37b1de3fbc000000 0x1bd8ef1fde000000

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x6510000000000419 0x328800000000020c

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0xdfd0a40400099fe1 0xefe852020004cff0

def z405 : W := mkw 0x0280024082c70614 0x014001204163830a 0xcc7e03c003c7061f 0x663f01e001e3830f

def z406 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x82c7bc0001f9f800 0xc163de0000fcfc00

def z407 : W := mkw 0x1000081120000000 0x0800040890000000 0x1281183830000000 0x09408c1c18000000

def z408 : W := mkw 0x8805800001280000 0x4402c00000940000 0x0081800000380000 0x8040c000001c0000

def z409 : W := mkw 0x54027c9368855000 0x2a013e49b442a800 0x23087c03fc07f801 0x11843e01fe03fc00

def z410 : W := mkw 0x00200000140088ab 0x801000000a004455 0xdcd0800400099fff 0xee6840020004cfff

def z411 : W := mkw 0x4002748248000000 0x20013a4124000000 0x000024004c000000 0x0000120026000000

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0d0800000080000 0xe068400000040000

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x03b1580000000000 0x01d8ac0000000000

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c0000004000061e 0x160000002000030f

def z415 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc3f7a40003f99801 0xe1fbd20001fccc00

def z416 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc099801 0xfffbfffffe04cc00

def z417 : W := mkw 0xf287fff7eac70614 0x7943fffbf563830a 0x002f5bfb83c60000 0x0017adfdc1e30000

def z418 : W := mkw 0xe007f5a648000000 0x7003fad324000000 0x3fd6a5c47c000000 0x1feb52e23e000000

def z419 : W := mkw 0x02a262c2d6c78ebf 0x815131616b63c75f 0xfd7e63c7ffc707ff 0x7ebf31e3ffe383ff

def z420 : W := mkw 0x4402740000855000 0x22013a000042a800 0x43b97c000237f801 0xa1dcbe00011bfc00

def z421 : W := mkw 0x028260c240c50204 0x0141306120628102 0xed5621c041c1061f 0x76ab10e020e0830f

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000099801 0xe00000000004cc00

def z423 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x36811a3bb030e598 0x9b408d1dd81872cc

def z424 : W := mkw 0xeb07f5e649680240 0x7583faf324b40120 0x8846a5c44dc80260 0x442352e226e40130

def z425 : W := mkw 0xfc059d3529285000 0x7e02ce9a94942800 0x12819c3c3c38f800 0x8940ce1e1e1c7c00

def z426 : W := mkw 0x0280004000c50204 0x0140002000628102 0x8000000001c10206 0x4000000000e08103

def z427 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc17ee40003cf1801 0x60bf720001e78c00

def z428 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x1cf7dbff80000000 0x0e7bedffc0000000

def z429 : W := mkw 0xab07e3ee43780740 0x5583f1f721bc03a0 0xfdf7e3ffc3f807e0 0xfefbf1ffe1fc03f0

def z430 : W := mkw 0xf2a7fff7fec78ebf 0xf953fffbff63c75f 0xffffffffffcf9fff 0xffffffffffe7cfff

def z431 : W := mkw 0xab87e3ee43fd0744 0x55c3f1f721fe83a2 0xdcf7a3fc43f907e6 0xee7bd1fe21fc83f3

def z432 : W := mkw 0x10400a193210a589 0x0820050c990852c4 0x56b11a383230e580 0xab588d1c191872c0

def z433 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x7fb95a3ffe36e7ff 0xbfdcad1fff1b73ff

def z434 : W := mkw 0xf007fdb778008089 0x7803fedbbc004044 0x7ff7fffffc008599 0xbffbfffffe0042cc

def z435 : W := mkw 0xa925812c153889eb 0xd492c0960a9c44f5 0x1281843c3c3899e0 0x8940c21e1e1c4cf0

def z436 : W := mkw 0x028000c240400204 0x0140006120200102 0x080001c040000206 0x040000e020000103

def z437 : W := mkw 0xf087fdb7e8870014 0x7843fedbf443800a 0x3ffffffffc07001f 0x1ffffffffe03800f

def z438 : W := mkw 0x33400b7db252a7d9 0x19a005bed92953ec 0x7fb95bffb236e7f9 0xbfdcadffd91b73fc

def z439 : W := mkw 0xfb07ffff6b780740 0x7d83ffffb5bc03a0 0xdcf7dbff83f807e0 0xee7bedffc1fc03f0

def z440 : W := mkw 0xdec7fedbf3fff79d 0x6f63ff6df9fffbce 0xfffffffbf3ffff9f 0xfffffffdf9ffffcf

def z441 : W := mkw 0x12c00adbf252a79d 0x0960056df92953ce 0x3c0003fbf000079e 0x1e0001fdf80003cf

def z442 : W := mkw 0x0000000000000000 0x0000000000000000 0x40b1000002300000 0xa058800001180000

def z443 : W := mkw 0x0040020882122510 0x0020010441091288 0x0008000002366000 0x00040000011b3000

def z444 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfffee7c7ffc7061f 0x7fff73e3ffe3830f

def z445 : W := mkw 0x98458a19b33aa599 0x4c22c50cd99d52cc 0xf7ffda3bb3fee599 0xfbffed1dd9ff72cc

def z446 : W := mkw 0xfb07ffff6b780740 0x7d83ffffb5bc03a0 0x3ff7fffffff00000 0x1ffbfffffff80000

def z447 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xeffee7c3c3cf9e1f 0xf7ff73e1e1e7cf0f

def z448 : W := mkw 0x0280024082c70614 0x014001204163830a 0xed58200043c7061f 0x76ac100021e3830f

def z449 : W := mkw 0x302009b77c0088ab 0x981004dbbe004455 0xffd0a7fffc099fff 0xffe853fffe04cfff

def z450 : W := mkw 0xab87e3eec3ff0754 0x55c3f1f761ff83aa 0xdcffc3ff83fe07e0 0xee7fe1ffc1ff03f0

def z451 : W := mkw 0x2320036c16508feb 0x919001b60b2847f5 0x3c0003fc7c0007fe 0x1e0001fe3e0003ff

def z452 : W := mkw 0xcc07f60803bd5500 0x6603fb0401deaa80 0xd7fffe3803fffd81 0xebffff1c01fffec0

def z453 : W := mkw 0xdc47fe19b3bff599 0x6e23ff0cd9dffacc 0x77bf5a3bb3f6e599 0xbbdfad1dd9fb72cc

def z454 : W := mkw 0xf007fd3528000000 0x7803fe9a94000000 0x13f7fc3c3c000000 0x09fbfe1e1e000000

def z455 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3f0024047c019fff 0x1f8012023e00cfff

def z456 : W := mkw 0x00826082c0870014 0x004130416043800a 0x2d7e63c3c007001f 0x16bf31e1e003800f

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x230024007c000000 0x118012003e000000

def z458 : W := mkw 0x00226082540088ab 0x801130412a004455 0xfff6e7c7fc099fff 0xfffb73e3fe04cfff

def z459 : W := mkw 0xf047ffbfea122510 0x7823ffdff5091288 0x002f5bfb82366000 0x0017adfdc11b3000

def z460 : W := mkw 0x00200000140088ab 0x801000000a004455 0xf790000030099fff 0xfbc800001804cfff

def z461 : W := mkw 0x50027c9368000000 0x28013e49b4000000 0x37b17e3bfc000000 0x1bd8bf1dfe000000

def z462 : W := mkw 0xdc67fe19b7bffdbb 0xee33ff0cdbdffedd 0xfffffe3fffffffff 0xffffff1fffffffff

def z463 : W := mkw 0x00200000140088ab 0x801000000a004455 0x200000007c00001e 0x100000003e00000f

def z464 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x03fffc0003f66000 0x01fffe0001fb3000

def z465 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0xdc7603fc03c007e0 0x6e3b01fe01e003f0

def z466 : W := mkw 0x028260c2c0c70214 0x014130616063810a 0xa94e61c3c1c7021f 0x54a730e1e0e3810f

def z467 : W := mkw 0xf287fff7eac70614 0x7943fffbf563830a 0xed7f7bfbc3c7061f 0x76bfbdfde1e3830f

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c000004000007e0 0x0e000002000003f0

def z469 : W := mkw 0xab87e3e6c3ef0654 0x55c3f1f361f7832a 0xed7ee3c7c3cf067f 0x76bf71e3e1e7833f

def z470 : W := mkw 0xcc27f40015add8ab 0xe613fa000ad6ec55 0xffd6a4047dc99fff 0xffeb52023ee4cfff

def z471 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x2d777bfbc0000000 0x16bbbdfde0000000

def z472 : W := mkw 0x00200000140088ab 0x801000000a004455 0xc840a4044c099fff 0xe42052022604cfff

def z473 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2c2e43c3c3c6061e 0x161721e1e1e3030f

def z474 : W := mkw 0x00200000140088ab 0x801000000a004455 0xded084043c089fe0 0xef6842021e044ff0

def z475 : W := mkw 0x028262c2d2c7869d 0x014131616963c34e 0xfffe63c3f3c7879f 0xffff31e1f9e3c3cf

def z476 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x000003fb80000000 0x000001fdc0000000

def z477 : W := mkw 0xdc47fc11b1aff099 0x6e23fe08d8d7f84c 0xe3fffc03b3fff819 0xf1fffe01d9fffc0c

def z478 : W := mkw 0xf0459d3d3810a189 0x7822ce9e9c0850c4 0x12819c3c3c30e180 0x8940ce1e1e1870c0

def z479 : W := mkw 0xe027f5a65c0088ab 0xf013fad32e004455 0xffd6a5c47c099fff 0xffeb52e23e04cfff

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300240000019801 0x018012000000cc00

def z481 : W := mkw 0x028260c240c50204 0x0141306120628102 0xc97e61c043c70207 0x64bf30e021e38103

def z482 : W := mkw 0x0400000000855000 0x020000000042a800 0x000800000007f801 0x000400000003fc00

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0xfdd0a004400907ff 0xfee85002200483ff

def z484 : W := mkw 0x0000020802100500 0x0000010401080280 0x4000000002300580 0xa0000000011802c0

def z485 : W := mkw 0x00026282c2020410 0x0001314161010208 0x6d7e63c3c2060419 0x36bf31e1e103020c

def z486 : W := mkw 0x00200000140088ab 0x801000000a004455 0x000000000001981f 0x000000000000cc0f

def z487 : W := mkw 0x2000012400000000 0x1000009200000000 0x1c0003fc00000000 0x0e0001fe00000000

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0029580002366000 0x0014ac00011b3000

def z489 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x834efc0001cff801 0x41a77e0000e7fc00

def z490 : W := mkw 0xb9458b3db33aa5d9 0x5ca2c59ed99d52ec 0x77b9da3fb23ee5f9 0xbbdced1fd91f72fc

def z491 : W := mkw 0xce87f4c241ed5204 0x6743fa6120f6a902 0x8846a5c041c91a06 0x442352e020e48d03

def z492 : W := mkw 0xab05816401680240 0x5582c0b200b40120 0xc8f781c403f80260 0xe47bc0e201fc0130

def z493 : W := mkw 0xa905812c01380140 0x5482c096009c00a0 0xdcd1803c003807e0 0xee68c01e001c03f0

def z494 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c0000047c000000 0x1e0000023e000000

def z495 : W := mkw 0xf027fdb77c0088ab 0xf813fedbbe004455 0x3ff7fffffc0007fe 0x1ffbfffffe0003ff

def z496 : W := mkw 0x004002089212a599 0x00200104490952cc 0x779800003236e599 0xbbcc0000191b72cc

def z497 : W := mkw 0x0002608240000000 0x0001304120000000 0x21006003c0000000 0x10803001e0000000

def z498 : W := mkw 0x50427e9bfa12a599 0x28213f4dfd0952cc 0x77b97e3bfe36e599 0xbbdcbf1dff1b72cc

def z499 : W := mkw 0xff07ffff6bfd5740 0x7f83ffffb5feaba0 0xffffffffffffffe1 0xfffffffffffffff0

def z500 : W := mkw 0x0000020092028499 0x000001004901424c 0x77b84203b2068599 0xbbdc2101d90342cc

def z501 : W := mkw 0x50027c9368000000 0x28013e49b4000000 0x3fd0fc07fc000000 0x1fe87e03fe000000

def z502 : W := mkw 0xa005812400000000 0x5002c09200000000 0xdcf783fc000807e0 0xee7bc1fe000403f0

def z503 : W := mkw 0x0080000080870014 0x004000004043800a 0x000800000007001f 0x000400000003800f

def z504 : W := mkw 0x88258000152888ab 0xc412c0000a944455 0xfff7a4047ff99fff 0xfffbd2023ffccfff

def z505 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cd0800400000000 0x0e68400200000000

def z506 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2d7e63c3c3c60000 0x16bf31e1e1e30000

def z507 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0x43b9dc00023ef801 0xa1dcee00011f7c00

def z508 : W := mkw 0xa805812401280000 0x5402c09200940000 0xdcf783fc03f80000 0xee7bc1fe01fc0000

def z509 : W := mkw 0x0282624082c70614 0x014131204163830a 0xc17e600003c7061f 0x60bf300001e3830f

def z510 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfdfee3c7c3cf07ff 0xfeff71e3e1e783ff

def z511 : W := mkw 0x50227c937c0088ab 0xa8113e49be004455 0x23007c03fc01981f 0x11803e01fe00cc0f

def z512 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xffd0a63ffc099fff 0xffe8531ffe04cfff

def z513 : W := mkw 0x30400bbffa12a599 0x182005dffd0952cc 0x3c0003fffc000598 0x1e0001fffe0002cc

def z514 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x0867ffffcc000000 0x0433ffffe6000000

def z515 : W := mkw 0x8807e00001ad0000 0x4403f00000d68000 0xc1ffe00003ff0001 0xe0fff00001ff8000

def z516 : W := mkw 0x0b400248937aa7d9 0x05a0012449bd53ec 0xc008000003fee7f9 0xe004000001ff73fc

def z517 : W := mkw 0x0000020812108589 0x00000104090842c4 0x77b1023832308599 0xbbd8811c191842cc

def z518 : W := mkw 0xfc07fd3529ad5000 0x7e03fe9a94d6a800 0xd3fffc3c3ffff801 0xe9fffe1e1ffffc00

def z519 : W := mkw 0x0020000004000822 0x8010000002000411 0xdcd0a4044c091fe6 0xee68520226048ff3

def z520 : W := mkw 0x00826282c2870414 0x004131416143820a 0x65386203c207041f 0x329c3101e103820f

def z521 : W := mkw 0x00200000140088ab 0x801000000a004455 0xe30024007c099fff 0xf18012003e04cfff

def z522 : W := mkw 0xcea7f6c2d7efdebf 0xe753fb616bf7ef5f 0xffffffc7ffffffff 0xffffffe3ffffffff

def z523 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xc17e63c383c70001 0x60bf31e1c1e38000

def z524 : W := mkw 0xb0458b3db212a599 0x5822c59ed90952cc 0x7fffdbffb236e599 0xbfffedffd91b72cc

def z525 : W := mkw 0xf007ffbf6a100500 0x7803ffdfb5080280 0x7ff7fffffe300580 0xbffbffffff1802c0

def z526 : W := mkw 0x006002089612adbb 0x803001044b0956dd 0xffd8a4047e3fffff 0xffec52023f1fffff

def z527 : W := mkw 0x106008193410a9ab 0x8830040c9a0854d5 0x12819c3c3c38f9e0 0x8940ce1e1e1c7cf0

def z528 : W := mkw 0x0000020802100500 0x0000010401080280 0x1400023800000580 0x0a00011c000002c0

def z529 : W := mkw 0x0b20024817788feb 0x859001240bbc47f5 0xffd0a4047ff99fff 0xffe852023ffccfff

def z530 : W := mkw 0x0b00024803780740 0x0580012401bc03a0 0x0000000003f00000 0x0000000001f80000

def z531 : W := mkw 0x00200000140088ab 0x801000000a004455 0xc3d0a40000099fff 0xe1e852000004cfff

def z532 : W := mkw 0x00826082c0870014 0x004130416043800a 0xed586003c007061f 0x76ac3001e003830f

def z533 : W := mkw 0xf047fdbf7810a189 0x7823fedfbc0850c4 0x3ff7fffffc30e180 0x9ffbfffffe1870c0

def z534 : W := mkw 0x028002c2c2420614 0x014001616121030a 0x6d3843c3c206061f 0x369c21e1e103030f

def z535 : W := mkw 0x02a002c2d6428ebf 0x815001616b21475f 0x3c0003c7fc0007fe 0x1e0001e3fe0003ff

def z536 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x528918383236e599 0xa9448c1c191b72cc

def z537 : W := mkw 0xa205836402400600 0x5102c1b201200300 0xdcf783fc03c00600 0x6e7bc1fe01e00300

def z538 : W := mkw 0xef07f76c03fd5740 0x7783fbb601feaba0 0x002f5bf803f66000 0x0017adfc01fb3000

def z539 : W := mkw 0x00200000140088ab 0x801000000a004455 0x020004003c009800 0x010002001e004c00

def z540 : W := mkw 0x0280024082c70614 0x014001204163830a 0x0008000003c60000 0x0004000001e30000

def z541 : W := mkw 0xc005940000000000 0x6002ca0000000000 0x02819c0000000000 0x0140ce0000000000

def z542 : W := mkw 0xfe87fff7ebef5614 0x7f43fffbf5f7ab0a 0xfffffffffffffe1f 0xffffffffffffff0f

def z543 : W := mkw 0x0e8262c2c3ef5614 0x0741316161f7ab0a 0xed7e63c3c3fffe1f 0xf6bf31e1e1ffff0f

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x210020004001001f 0x108010002000800f

def z545 : W := mkw 0xab87e3eec3ff0754 0x55c3f1f761ff83aa 0x002f43fb83f60000 0x0017a1fdc1fb0000

def z546 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x3e819ffffc000000 0x1f40cffffe000000

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x3790000030000000 0x1bc8000018000000

def z548 : W := mkw 0x302009b77c0088ab 0x981004dbbe004455 0x3c0003fffc0007fe 0x1e0001fffe0003ff

def z549 : W := mkw 0x0200024082420610 0x0100012041210308 0xed7e43c383c60619 0x76bf21e1c1e3030c

def z550 : W := mkw 0xa005832c02100500 0x5002c19601080280 0x5cf783fc02300580 0xae7bc1fe011802c0

def z551 : W := mkw 0x00200000140088ab 0x801000000a004455 0xe3d0a4007c09981f 0xf1e852003e04cc0f

def z552 : W := mkw 0xfb87ffffebff0754 0x7dc3fffff5ff83aa 0xffffffffffff07ff 0xffffffffffff83ff

def z553 : W := mkw 0x0002620082870410 0x0001310041438208 0xe57e620383c70419 0x72bf3101c1e3820c

def z554 : W := mkw 0x00200000140088ab 0x801000000a004455 0x00000000000899e0 0x8000000000044cf0

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0x4138400002060001 0x209c200001030000

def z556 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37b15a3bb0000598 0x1bd8ad1dd80002cc

def z557 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x10a783fc03f801e0 0x8853c1fe01fc00f0

def z558 : W := mkw 0x028002c2c2c70614 0x014001616163830a 0xec0803c3c3c7061f 0x760401e1e1e3830f

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0x0840a4044c000000 0x0420520226000000

def z560 : W := mkw 0xd047fe19b212a599 0x6823ff0cd90952cc 0x77fffe3bb236e599 0xbbffff1dd91b72cc

def z561 : W := mkw 0x0020000004000822 0x8010000002000411 0x000084040c081860 0x0000420206040c30

def z562 : W := mkw 0x0002608240000000 0x0001304120000000 0x002643c380000000 0x001321e1c0000000

def z563 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0x8846a5c44dc91800 0x442352e226e48c00

def z564 : W := mkw 0x1000081130008089 0x0800040898004044 0x77b15a3bb0008599 0xbbd8ad1dd80042cc

def z565 : W := mkw 0x004000081010a189 0x00200004080850c4 0x000000000030e180 0x80000000001870c0

def z566 : W := mkw 0x8b05824803780740 0x4582c12401bc03a0 0xc0f7800003f807e0 0xe07bc00001fc03f0

def z567 : W := mkw 0x1002689360000000 0x08013449b0000000 0x3ff77bfbf0000000 0x1ffbbdfdf8000000

def z568 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x0389fc00003ff801 0x81c4fe00001ffc00

def z569 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x2b46fdc7fc000000 0x15a37ee3fe000000

def z570 : W := mkw 0x12c26adbe2d72714 0x0961356df16b938a 0x002f5bfb83f66000 0x0017adfdc1fb3000

def z571 : W := mkw 0xa287e3e6c2c70614 0x5143f1f36163830a 0xfdffe3ffc3c7061f 0x7efff1ffe1e3830f

def z572 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x12a95a3bb236e180 0x8954ad1dd91b70c0

def z573 : W := mkw 0xef07f76c03fd5740 0x7783fbb601feaba0 0xc3fffff803fff801 0xe1fffffc01fffc00

def z574 : W := mkw 0x238003eec2520754 0x11c001f7612903aa 0x3c0003ffc00007fe 0x1e0001ffe00003ff

def z575 : W := mkw 0x1b400a59b37aa7d9 0x0da0052cd9bd53ec 0xf7b95a3bb3fee7f9 0xfbdcad1dd9ff73fc

def z576 : W := mkw 0x0b20024817788feb 0x859001240bbc47f5 0xc000000003f99fff 0xe000000001fccfff

def z577 : W := mkw 0xdc47fc1931bdf189 0x6e23fe0c98def8c4 0xd3fffc3833fff981 0xe9fffe1c19fffcc0

def z578 : W := mkw 0xc007f40000850000 0x6003fa0000428000 0xc3fffc0003c70001 0x61fffe0001e38000

def z579 : W := mkw 0x0020000004000822 0x8010000002000411 0x000024004c011806 0x0000120026008c03

def z580 : W := mkw 0xbb458b7d3378a7c9 0x5da2c5be99bc53e4 0xdef79bfc33f8e7e0 0xef7bcdfe19fc73f0

def z581 : W := mkw 0xab87e3eec3ff0754 0x55c3f1f761ff83aa 0xed7f63fbc3f7061f 0x76bfb1fde1fb830f

def z582 : W := mkw 0x0000000800100100 0x0000000400080080 0x1081003800300180 0x8840801c001800c0

def z583 : W := mkw 0x0002600000850000 0x0001300000428000 0x0108600000070001 0x0084300000038000

def z584 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x0046a40000000000 0x0023520000000000

def z585 : W := mkw 0x4402740000855000 0x22013a000042a800 0x0000240000011800 0x0000120000008c00

def z586 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x806ffc0003ff7800 0x4037fe0001ffbc00

def z587 : W := mkw 0xab25816405680a62 0xd592c0b202b40531 0x8846a5c44dc91a66 0x442352e226e48d33

def z588 : W := mkw 0xe005952408000000 0x7002ca9204000000 0x000084040c000000 0x0000420206000000

def z589 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3fd0a4047c0007fe 0x1fe852023e0003ff

def z590 : W := mkw 0x10400a11b202a499 0x08200508d901524c 0x67385a03b206e419 0x339c2d01d903720c

def z591 : W := mkw 0xf047fdb7f802a099 0x7823fedbfc01504c 0x3ffffffffc06e019 0x1ffffffffe03700c

def z592 : W := mkw 0xa005812400000000 0x5002c09200000000 0x1081803c00000000 0x0840c01e00000000

def z593 : W := mkw 0x00200000140088ab 0x801000000a004455 0xd3d0a4043c0999e1 0xe9e852021e04ccf0

def z594 : W := mkw 0x52827ed3eac70614 0x29413f69f563830a 0xef7e7fc3ffc7061f 0x77bf3fe1ffe3830f

def z595 : W := mkw 0x0800000001280000 0x0400000000940000 0xc000000003f80000 0xe000000001fc0000

def z596 : W := mkw 0x104008113000a089 0x0820040898005044 0x020018003000e000 0x01000c0018007000

def z597 : W := mkw 0x442274001485d8ab 0xa2113a000a42ec55 0x23087c007c07f81f 0x11843e003e03fc0f

def z598 : W := mkw 0xc807f40001280000 0x6403fa0000940000 0xc3f7fc0003f80000 0xe1fbfe0001fc0000

def z599 : W := mkw 0xa905812c01380140 0x5482c096009c00a0 0x0001003800300000 0x0000801c00180000

def z600 : W := mkw 0x33400b7db252a7d9 0x19a005bed92953ec 0x3c0003ffb00007f8 0x1e0001ffd80003fc

def z601 : W := mkw 0x02c262cad2d7a79d 0x01613165696bd3ce 0xed7e63c3c3f7e79f 0xf6bf31e1e1fbf3cf

def z602 : W := mkw 0x10000a1922100500 0x0800050c91080280 0x77b15a3bb2300580 0xbbd8ad1dd91802c0

def z603 : W := mkw 0x00200000140088ab 0x801000000a004455 0x9ac0a4047c099be6 0xcd6052023e04cdf3

def z604 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x83f7fc0001c91800 0x41fbfe0000e48c00

def z605 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc3ffd80003fee001 0xe1ffec0001ff7000

def z606 : W := mkw 0x0000000010008089 0x0000000008004044 0xf7d0a40030099d99 0xfbe852001804cecc

def z607 : W := mkw 0x0000000000000000 0x0000000000000000 0x03d0a40000000000 0x01e8520000000000

def z608 : W := mkw 0xf907fdbf69380140 0x7c83fedfb49c00a0 0x3ff7fffffc3801e0 0x9ffbfffffe1c00f0

def z609 : W := mkw 0xef07f76c03fd5740 0x7783fbb601feaba0 0xdcf7a7fc03f91fe0 0xee7bd3fe01fc8ff0

def z610 : W := mkw 0x10c26a9bf297a59d 0x0861354df94bd2ce 0x77b97a3bf237e59f 0xbbdcbd1df91bf2cf

def z611 : W := mkw 0xed05952c01385140 0x7682ca96009c28a0 0x12819c3c0038f9e0 0x8940ce1e001c7cf0

def z612 : W := mkw 0x00826082c0870014 0x004130416043800a 0x0008400380060000 0x00042001c0030000

def z613 : W := mkw 0x0020020816108dab 0x801001040b0846d5 0xfff1a63c7e399fff 0xfff8d31e3f1ccfff

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x8840800400080260 0x4420400200040130

def z615 : W := mkw 0xab25836c17788feb 0xd592c1b60bbc47f5 0xdef787fc3ff89fe0 0xef7bc3fe1ffc4ff0

def z616 : W := mkw 0xa007e1a640000000 0x5003f0d320000000 0x3df7e3ffc0000000 0x1efbf1ffe0000000

def z617 : W := mkw 0x50001c1128000000 0x28000e0894000000 0x02001c003c000000 0x01000e001e000000

def z618 : W := mkw 0xab07e36c03fd0740 0x5583f1b601fe83a0 0xddffe3fc03ff07e1 0xeefff1fe01ff83f0

def z619 : W := mkw 0x0000000010008089 0x0000000008004044 0x4000000000008599 0xa0000000000042cc

def z620 : W := mkw 0x0020020096028cbb 0x801001004b01465d 0xfff8e607fe0f9fff 0xfffc7303ff07cfff

def z621 : W := mkw 0x1000081120000000 0x0800040890000000 0x23005803b0000000 0x11802c01d8000000

def z622 : W := mkw 0xbb058b7d23780740 0x5d82c5be91bc03a0 0xfff7dbffb3f807e0 0xfffbedffd9fc03f0

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0xc150200000010001 0x60a8100000008000

def z624 : W := mkw 0xfb059f7d2b780740 0x7d82cfbe95bc03a0 0xdef79ffc3ff807e0 0xef7bcffe1ffc03f0

def z625 : W := mkw 0xf047ffbffa12a599 0x7823ffdffd0952cc 0x3ff7fffffc000598 0x1ffbfffffe0002cc

def z626 : W := mkw 0x00200000140088ab 0x801000000a004455 0x7f9000047c0087ff 0xbfc800023e0043ff

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x14b1023800000000 0x0a58811c00000000

def z628 : W := mkw 0xeb07f76c03780740 0x7583fbb601bc03a0 0xdff7fffc03f807e0 0xeffbfffe01fc03f0

def z629 : W := mkw 0x12826ad3e2c70614 0x09413569f163830a 0xffff7bfbf3c7061f 0x7fffbdfdf9e3830f

def z630 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3fd0a4047c01981f 0x1fe852023e00cc0f

def z631 : W := mkw 0x00200000140088ab 0x801000000a004455 0xef5024007c019e1f 0x77a812003e00cf0f

def z632 : W := mkw 0xf287fff7eac70614 0x7943fffbf563830a 0x3fffffffffc60000 0x1fffffffffe30000

def z633 : W := mkw 0xc287f6c2c2c70614 0x6143fb616163830a 0xefffffc3c3c7061f 0x77ffffe1e1e3830f

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x8840200040010206 0x4420100020008103

def z635 : W := mkw 0xa005812400000000 0x5002c09200000000 0x084681c400000000 0x042340e200000000

def z636 : W := mkw 0xf027fdb77c0088ab 0xf813fedbbe004455 0x3ff7fffffc0899e0 0x9ffbfffffe044cf0

def z637 : W := mkw 0xab87e1e641ed0244 0x55c3f0f320f68122 0x8846a1c441c90266 0x442350e220e48133

def z638 : W := mkw 0x00800082c0020014 0x004000416001000a 0x20000003c000001e 0x10000001e000000f

def z639 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc04ea40003fff801 0xe027520001fffc00

def z640 : W := mkw 0x0c02600001ad5000 0x0601300000d6a800 0xc17e600003fff801 0xe0bf300001fffc00

def z641 : W := mkw 0x12c26ad3f2c7a69d 0x09613569f963d34e 0xef7e7bc3f3c7e61f 0x77bf3de1f9e3f30f

def z642 : W := mkw 0xe007f5a648000000 0x7003fad324000000 0x0bf7fdc44c000000 0x05fbfee226000000

def z643 : W := mkw 0xef27f76c17fddfeb 0xf793fbb60bfeeff5 0xfffffffc7fffffff 0xfffffffe3fffffff

def z644 : W := mkw 0xdc459e19b33af599 0x6e22cf0cd99d7acc 0x77b9de3bb23efd99 0xbbdcef1dd91f7ecc

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc50000000000600 0x6628000000000300

def z646 : W := mkw 0x50027c9368000000 0x28013e49b4000000 0x2f767fc3fc000000 0x17bb3fe1fe000000

def z647 : W := mkw 0x02a002c2d6428ebf 0x815001616b21475f 0xffd0a7c7fc099fff 0xffe853e3fe04cfff

def z648 : W := mkw 0xff47ff7db3fff7d9 0x7fa3ffbed9fffbec 0xffffffffb3fffff9 0xffffffffd9fffffc

def z649 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xe1086003c3c7061f 0x70843001e1e3830f

def z650 : W := mkw 0x1c400a19b3bff599 0x0e20050cd9dffacc 0xf7b95a3bb3fffd99 0xfbdcad1dd9fffecc

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x4390000000008001 0xa1c8000000004000

def z652 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x1ac7bdfc7c000000 0x0d63defe3e000000

def z653 : W := mkw 0x00200000140088ab 0x801000000a004455 0xed50200040099fff 0xf6a810002004cfff

def z654 : W := mkw 0xcc27f40015add8ab 0xe613fa000ad6ec55 0xd3fffc043ffff9e1 0xe9fffe021ffffcf0

def z655 : W := mkw 0xf207fff76a400600 0x7903fffbb5200300 0xfff7ffffffc00600 0x7ffbffffffe00300

def z656 : W := mkw 0x00200000140088ab 0x801000000a004455 0x100000043c0001e0 0x080000021e0000f0

def z657 : W := mkw 0x004002089212a599 0x00200104490952cc 0x653842038236e599 0xb29c2101c11b72cc

def z658 : W := mkw 0xf027fdb76c000822 0xf813fedbb6000411 0xbff7fffffc091a66 0x5ffbfffffe048d33

def z659 : W := mkw 0xef87f7eec3ff5754 0x77c3fbf761ffabaa 0xffffffffc3ffffff 0xffffffffe1ffffff

def z660 : W := mkw 0x0002608240000000 0x0001304120000000 0xed7663c3c001061f 0x76bb31e1e000830f

def z661 : W := mkw 0x0020000004000822 0x8010000002000411 0xed50a4044c091e7f 0x76a8520226048f3f

def z662 : W := mkw 0x00226000148588ab 0x801130000a42c455 0xfffee4047fcf9fff 0xffff72023fe7cfff

def z663 : W := mkw 0x50827c93e8870014 0x28413e49f443800a 0x23087c03fc07001f 0x11843e01fe03800f

def z664 : W := mkw 0x0280024082c70614 0x014001204163830a 0xe538420383c7061f 0x729c2101c1e3830f

def z665 : W := mkw 0xe007f52400000000 0x7003fa9200000000 0x1ff7fffc00000000 0x0ffbfffe00000000

def z666 : W := mkw 0xdc07fc9369ad5000 0x6e03fe49b4d6a800 0xe3fffc03fffff801 0xf1fffe01fffffc00

def z667 : W := mkw 0x0000000010008089 0x0000000008004044 0x3400000030000598 0x1a000000180002cc

def z668 : W := mkw 0x0c40020893bff599 0x0620010449dffacc 0xc008000003fffd99 0xe004000001fffecc

def z669 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0xdcd083fc000807e0 0xee6841fe000403f0

def z670 : W := mkw 0xa905832c03380540 0x5482c196019c02a0 0x54b1823c023805e0 0xaa58c11e011c02f0

def z671 : W := mkw 0x0002600000850000 0x0001300000428000 0xc3ff780003f7e001 0xe1ffbc0001fbf000

def z672 : W := mkw 0xcc07f40011add089 0x6603fa0008d6e844 0xf7fffc0033fffd99 0xfbfffe0019fffecc

def z673 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xcc7e43c383c60600 0x663f21e1c1e30300

def z674 : W := mkw 0x0000020082020410 0x0000010041010208 0x2400020380000418 0x12000101c000020c

def z675 : W := mkw 0x00826082c0870014 0x004130416043800a 0xe17e6003c3c7001f 0x70bf3001e1e3800f

def z676 : W := mkw 0xc027f400140088ab 0xe013fa000a004455 0xfff7fc047c099fff 0xfffbfe023e04cfff

def z677 : W := mkw 0x0000020082020410 0x0000010041010208 0x4008000002060419 0x200400000103020c

def z678 : W := mkw 0x10400811b002a099 0x08200408d801504c 0x37b95a3bb006e019 0x1bdcad1dd803700c

def z679 : W := mkw 0xf027fdb77c0088ab 0xf813fedbbe004455 0x3ff7fffffc01981f 0x1ffbfffffe00cc0f

def z680 : W := mkw 0xab8583eec37a0754 0x55c2c1f761bd03aa 0xfcf783ffc3f807fe 0xfe7bc1ffe1fc03ff

def z681 : W := mkw 0x8805820803380500 0x4402c104019c0280 0xd4f7823803f80580 0xea7bc11c01fc02c0

def z682 : W := mkw 0x10400811b002a099 0x08200408d801504c 0x63b95803b236e019 0xb1dcac01d91b700c

def z683 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xcc7703f803f00600 0x663b81fc01f80300

def z684 : W := mkw 0x12c26adbf2d7a79d 0x0961356df96bd3ce 0xfd7e63fbf3c7079f 0x7ebf31fdf9e383cf

def z685 : W := mkw 0xdc07fc1121ad5000 0x6e03fe0890d6a800 0xf7fffe3bb3fff801 0xfbffff1dd9fffc00

def z686 : W := mkw 0xab05836c137887c9 0x5582c1b609bc43e4 0xfff783fc33f887f9 0xfffbc1fe19fc43fc

def z687 : W := mkw 0x4400140000005000 0x22000a0000002800 0x02001c000000f800 0x01000e0000007c00

def z688 : W := mkw 0x0002600000850000 0x0001300000428000 0xc3fee40003cf9801 0xe1ff720001e7cc00

def z689 : W := mkw 0x0900000801380140 0x04800004009c00a0 0x00000000003801e0 0x80000000001c00f0

def z690 : W := mkw 0xef07f56401ed5240 0x7783fab200f6a920 0xcbfffdc403fffa61 0xe5fffee201fffd30

def z691 : W := mkw 0xc007f40000000000 0x6003fa0000000000 0x43fffc000236e001 0xa1fffe00011b7000

def z692 : W := mkw 0x2100012c00100140 0x10800096000800a0 0x1000003c000001e0 0x0800001e000000f0

def z693 : W := mkw 0x0000000000850000 0x0000000000428000 0xc008000003c70001 0x6004000001e38000

def z694 : W := mkw 0xc407f40000855000 0x6203fa000042a800 0x03fffc000007f801 0x01fffe000003fc00

def z695 : W := mkw 0x0200024002400600 0x0100012001200300 0x0c0003c000000600 0x060001e000000300

def z696 : W := mkw 0x0200024002400600 0x0100012001200300 0xdcf683c403c807e0 0xee7b41e201e403f0

def z697 : W := mkw 0xbb458b7db37aa7d9 0x5da2c5bed9bd53ec 0x77bf5bfbb3f6e599 0xbbdfadfdd9fb72cc

def z698 : W := mkw 0xf9059d3d29380140 0x7c82ce9e949c00a0 0x12819c3c3c3801e0 0x8940ce1e1e1c00f0

def z699 : W := mkw 0x0000000080020010 0x0000000040010008 0x2108400380060019 0x10842001c003000c

def z700 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3fd0a4047c0899e0 0x9fe852023e044cf0

def z701 : W := mkw 0x0b00024803780740 0x0580012401bc03a0 0xcc7603c003f807e0 0xe63b01e001fc03f0

def z702 : W := mkw 0xfb47fffffb7aa7d9 0x7da3fffffdbd53ec 0xfffffffffffee7f9 0xffffffffffff73fc

def z703 : W := mkw 0x10400811b002a099 0x08200408d801504c 0x77985803b006e599 0xbbcc2c01d80372cc

def z704 : W := mkw 0x10c26893f087a09d 0x08613449f843d04e 0x23087803f007e01f 0x11843c01f803f00f

def z705 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x03f7fffb80000000 0x01fbfffdc0000000

def z706 : W := mkw 0x106008193410a9ab 0x8830040c9a0854d5 0xffd1bc3c7c39ffff 0xffe8de1e3e1cffff

def z707 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc06ffc0003fff801 0xe037fe0001fffc00

def z708 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x3fd1bffffc000000 0x1fe8dffffe000000

def z709 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7e63c3c3cf07ff 0xf6bf31e1e1e783ff

def z710 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0xfffffffffff7e001 0xfffffffffffbf000

def z711 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x63b95a3bb236e019 0xb1dcad1dd91b700c

def z712 : W := mkw 0x10400819b012a199 0x0820040cd80950cc 0x1289583bb036e180 0x8944ac1dd81b70c0

def z713 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7fff5bfbb236e599 0xbfffadfdd91b72cc

def z714 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x3ef79ffffc000000 0x1f7bcffffe000000

def z715 : W := mkw 0x6702776c02d55740 0x33813bb6016aaba0 0x1f087ffc0007ffe1 0x0f843ffe0003fff0

def z716 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x33a7fffffc000000 0x19d3fffffe000000

def z717 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x23f7fffbfc000000 0x11fbfffdfe000000

def z718 : W := mkw 0xce8596c2c36a5614 0x6742cb6161b52b0a 0x2e819fc3c038fe1e 0x9740cfe1e01c7f0f

def z719 : W := mkw 0xdc47fe19b3bff599 0x6e23ff0cd9dffacc 0xb446a63bb1c91d98 0x5a23531dd8e48ecc

def z720 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xcc7703f803f807e0 0xe63b81fc01fc03f0

def z721 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x40295a3b82366419 0x2014ad1dc11b320c

def z722 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xfff7fffffff91800 0xfffbfffffffc8c00

def z723 : W := mkw 0x10400819b012a199 0x0820040cd80950cc 0x73b9583bb236e199 0xb9dcac1dd91b70cc

def z724 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3d5023fffc000000 0x1ea811fffe000000

def z725 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x12afdfffbffef800 0x8957efffdfff7c00

def z726 : W := mkw 0x028260c2c0c70214 0x014130616063810a 0xa84621c3c1c1021e 0x542310e1e0e0810f

def z727 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfdfee3c7c3c7061f 0x7eff71e3e1e3830f

def z728 : W := mkw 0xec07f52401ad5000 0x7603fa9200d6a800 0xd3fffc3c03fff801 0xe9fffe1e01fffc00

def z729 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xe17e63c3c3c7001f 0x70bf31e1e1e3800f

def z730 : W := mkw 0xa987e1aec1bf0154 0x54c3f0d760df80aa 0x3189e03fc03f01ff 0x98c4f01fe01f80ff

def z731 : W := mkw 0x0280024082c70614 0x014001204163830a 0xed7e43c383c7061f 0x76bf21e1c1e3830f

def z732 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7fb95a3bf236e79f 0xbfdcad1df91b73cf

def z733 : W := mkw 0x028262cac2d70714 0x01413165616b838a 0xed7f63fbc3f7061f 0x76bfb1fde1fb830f

def z734 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b97e3bfe36e599 0xbbdcbf1dff1b72cc

def z735 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x36a95a3bb236e598 0x9b54ad1dd91b72cc

def z736 : W := mkw 0x0200024802500700 0x0100012401280380 0xdcf783fc03f807e0 0xee7bc1fe01fc03f0

def z737 : W := mkw 0x0002608240850000 0x0001304120428000 0xed7e63c3c3c7061f 0x76bf31e1e1e3830f

def z738 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xbff7fffffc080260 0x5ffbfffffe040130

def z739 : W := mkw 0x3c0009b769ad5000 0x1e0004dbb4d6a800 0xfc0803fffffff801 0xfe0401fffffffc00

def z740 : W := mkw 0x8805800001280000 0x4402c00000940000 0xc3fffc0003fff801 0xe1fffe0001fffc00

def z741 : W := mkw 0xf407fdb768855000 0x7a03fedbb442a800 0xffffffffffc7f801 0x7fffffffffe3fc00

def z742 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x23297e3bfe37f81f 0x1194bf1dff1bfc0f

def z743 : W := mkw 0x1000081120000000 0x0800040890000000 0x00295a3b82366000 0x0014ad1dc11b3000

def z744 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xad4e63c3c1c7061f 0x56a731e1e0e3830f

def z745 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3cd083fffc000000 0x1e6841fffe000000

def z746 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc0801e0 0x9ffbfffffe0400f0

def z747 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc0007e0 0x1ffbfffffe0003f0

def z748 : W := mkw 0xf407fdb768855000 0x7a03fedbb442a800 0x3ffffffffc066000 0x1ffffffffe033000

def z749 : W := mkw 0xf027fdb77c0088ab 0xf813fedbbe004455 0xc0275bfb80099fff 0xe013adfdc004cfff

def z750 : W := mkw 0xb005893520000000 0x5802c49a90000000 0x3ff7fffffc000000 0x1ffbfffffe000000

def z751 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfc40a4047c099fff 0xfe2052023e04cfff

def z752 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7f9da3bb23ee599 0xfbfced1dd91f72cc

def z753 : W := mkw 0xa805812401280000 0x5402c09200940000 0xdcf783fc03f807e0 0xee7bc1fe01fc03f0

def z754 : W := mkw 0x038262cac2d70754 0x01c13165616b83aa 0xed7e63c3c3c707ff 0x76bf31e1e1e383ff

def z755 : W := mkw 0x02a262c2d6c78ebf 0x815131616b63c75f 0x12aec7c7bfce99e0 0x895763e3dfe74cf0

def z756 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3f9003fffc000000 0x1fc801fffe000000

def z757 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff8e4047e0f9fff 0xfffc72023f07cfff

def z758 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfffee7c7ffcf9e1f 0xffff73e3ffe7cf0f

def z759 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x3c0087fffc000000 0x1e0043fffe000000

def z760 : W := mkw 0xf2859f75aac70614 0x7942cfbad563830a 0xd2899c3c3fc7061f 0x6944ce1e1fe3830f

def z761 : W := mkw 0xab05836c837a0750 0x5582c1b641bd03a8 0xfcf783ff83f807f8 0xfe7bc1ffc1fc03fc

def z762 : W := mkw 0x028262cac2d70714 0x01413165616b838a 0xfdffe3ffc3ff07ff 0xfefff1ffe1ff83ff

def z763 : W := mkw 0xbb458975b16aa2d9 0x5da2c4bad8b5516c 0xab4ed9c7b1cee279 0x55a76ce3d8e7713c

def z764 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7f97a3bb237e599 0xfbfcbd1dd91bf2cc

def z765 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x54b783fc03f805e0 0xaa5bc1fe01fc02f0

def z766 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xd3ffffffbffff801 0xe9ffffffdffffc00

def z767 : W := mkw 0x028260c240c50204 0x0141306120628102 0xed7663c3c1c1061f 0x76bb31e1e0e0830f

def z768 : W := mkw 0x1000081120000000 0x0800040890000000 0x37b95a3bb2366000 0x1bdcad1dd91b3000

def z769 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xd0a783fc03f807e0 0xe853c1fe01fc03f0

def z770 : W := mkw 0x028262cac2d70714 0x01413165616b838a 0xed7e63c3c3f7079f 0xf6bf31e1e1fb83cf

def z771 : W := mkw 0x10600a19a6122d32 0x8830050cd3091699 0x8869fe3fce3f7a66 0x4434ff1fe71fbd33

def z772 : W := mkw 0xcc27f40015add8ab 0xe613fa000ad6ec55 0x3c2f58047ff667fe 0x1e17ac023ffb33ff

def z773 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7f7bc3c3f7661f 0x76bfbde1e1fbb30f

def z774 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x9c6783fc03f807e0 0x4e33c1fe01fc03f0

def z775 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xbff7fffffc091800 0x5ffbfffffe048c00

def z776 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0xdcf703fc03f007e0 0xee7b81fe01f803f0

def z777 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc308580003fff801 0xe1842c0001fffc00

def z778 : W := mkw 0x1000081120000000 0x0800040890000000 0x43b95a3b8236e001 0xa1dcad1dc11b7000

def z779 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b9de3fbe36e599 0xbbdcef1fdf1b72cc

def z780 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0xdcf9da3f823e67e0 0xee7ced1fc11f33f0

def z781 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff1a4047e399fff 0xfff8d2023f1ccfff

def z782 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xfffffffffffffe1f 0xffffffffffffff0f

def z783 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3c0603fffc000000 0x1e0301fffe000000

def z784 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x3fd0fffffc000000 0x1fe87ffffe000000

def z785 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x82effc0003fff800 0xc177fe0001fffc00

def z786 : W := mkw 0xb965893d3538a9eb 0xdcb2c49e9a9c54f5 0x12819c3c3c38f9e0 0x8940ce1e1e1c7cf0

def z787 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x3c005bfffc000000 0x1e002dfffe000000

def z788 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfff7a7fc43f99fff 0xfffbd3fe21fccfff

def z789 : W := mkw 0xcc07f48241ad5000 0x6603fa4120d6a800 0xefffffc3c3fffe1f 0xf7ffffe1e1ffff0f

def z790 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0xc3fffdc003fff801 0xe1fffee001fffc00

def z791 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x21295a3b82366019 0x1094ad1dc11b300c

def z792 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x37b77ffbfc000000 0x1bdbbffdfe000000

def z793 : W := mkw 0xe047f7aeda12a599 0x7023fbd76d0952cc 0x484ea5c44e36e599 0xa42752e2271b72cc

def z794 : W := mkw 0x10000a1922100500 0x0800050c91080280 0x77b95a3bb236e581 0xbbdcad1dd91b72c0

def z795 : W := mkw 0x5b027edb6b780740 0x2d813f6db5bc03a0 0xe3007c03fff807e0 0xf1803e01fffc03f0

def z796 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x40295a3b8236e001 0xa014ad1dc11b7000

def z797 : W := mkw 0xec07f52401ad5000 0x7603fa9200d6a800 0xdffffffc03ffffe1 0xeffffffe01fffff0

def z798 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xad7663c3c1c1061e 0x56bb31e1e0e0830f

def z799 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x232f7ffbfff7f801 0x1197bffdfffbfc00

def z800 : W := mkw 0x00200000140088ab 0x801000000a004455 0xbec0a4047c099ffe 0xdf6052023e04cfff

def z801 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3d76e7fffc000000 0x1ebb73fffe000000

def z802 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x3c0027fffc000000 0x1e0013fffe000000

def z803 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x52a95a3bb236e599 0xa954ad1dd91b72cc

def z804 : W := mkw 0x12c268db70d5a38d 0x0961346db86ad1c6 0x9ac739f871f1e386 0xcd639cfc38f8f1c3

def z805 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfff783fc33f807e0 0xfffbc1fe19fc03f0

def z806 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x23007ffbfc000000 0x11803ffdfe000000

def z807 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9fe3ffe37e79f 0xfffcff1fff1bf3cf

def z808 : W := mkw 0xef87f5e641ed5244 0x77c3faf320f6a922 0x8846a5c441c91a66 0x442352e220e48d33

def z809 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3fb75bfffc000000 0x1fdbadfffe000000

def z810 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xfffffc0443ffffff 0xfffffe0221ffffff

def z811 : W := mkw 0xee87f5e649ed5204 0x7743faf324f6a902 0x8846a5c44dc91a06 0x442352e226e48d03

def z812 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xffb95a3ffe3fffff 0xffdcad1fff1fffff

def z813 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xd7fffc0003fffd81 0xebfffe0001fffec0

def z814 : W := mkw 0x104008193010a189 0x0820040c980850c4 0x77b95a3bb236e181 0xbbdcad1dd91b70c0

def z815 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9fe3ffe3ee7f9 0xfffcff1fff1f73fc

def z816 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x43bfdc0003fef801 0xa1dfee0001ff7c00

def z817 : W := mkw 0x300009b768000000 0x180004dbb4000000 0xfcd083fffc0807e0 0xfe6841fffe0403f0

def z818 : W := mkw 0x300009b768000000 0x180004dbb4000000 0xffd0a7fffc099801 0xffe853fffe04cc00

def z819 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x02a95a3b8236e000 0x8154ad1dc11b7000

def z820 : W := mkw 0x028262cac2d70714 0x01413165616b838a 0xfd7e63fbc3c7079f 0x7ebf31fde1e383cf

def z821 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x00295a3b82366598 0x0014ad1dc11b32cc

def z822 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2d7e63c3c3c6061e 0x16bf31e1e1e3030f

def z823 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2d7e63c3c3c7001f 0x16bf31e1e1e3800f

def z824 : W := mkw 0xab05836c837a0750 0x5582c1b641bd03a8 0xffffdbff83fee7f9 0xffffedffc1ff73fc

def z825 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfcd0a4047c091ffe 0xfe6852023e048fff

def z826 : W := mkw 0xfc07fdb769285000 0x7e03fedbb4942800 0x3ff7fffffc306000 0x1ffbfffffe183000

def z827 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3cf7a7fffc000000 0x1e7bd3fffe000000

def z828 : W := mkw 0xa905812c01380140 0x5482c096009c00a0 0xdcf783fc03f801e0 0xee7bc1fe01fc00f0

def z829 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x57b95a3b8236e581 0xabdcad1dc11b72c0

def z830 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc0907ff 0xfffbfffffe0483ff

def z831 : W := mkw 0x300269b768850000 0x180134dbb4428000 0xfd7e63ffffc70001 0x7ebf31ffffe38000

def z832 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x67395a3bb236e419 0x339cad1dd91b720c

def z833 : W := mkw 0x0b600248977aaffb 0x85b001244bbd57fd 0xc008000003ffffff 0xe004000001ffffff

def z834 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b95a3bb237fd9f 0xbbdcad1dd91bfecf

def z835 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3f005bfffc000000 0x1f802dfffe000000

def z836 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0x1c2603fc03c007e0 0x0e1301fe01e003f0

def z837 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcf783fc03f99fe1 0xee7bc1fe01fccff0

def z838 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77f9fe3bb236e599 0xbbfcff1dd91b72cc

def z839 : W := mkw 0xab25836c17788feb 0xd592c1b60bbc47f5 0x232727f87ff1981f 0x119393fc3ff8cc0f

def z840 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0x0846a5c44dc00000 0x042352e226e00000

def z841 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdef79bfc03f8e7e0 0xef7bcdfe01fc73f0

def z842 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b95a3bb23efdf9 0xbbdcad1dd91f7efc

def z843 : W := mkw 0x4c02740001ad5000 0x26013a0000d6a800 0xc37e7c0003fff801 0xe1bf3e0001fffc00

def z844 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1c0603fc01c007e0 0x0e0301fe00e003f0

def z845 : W := mkw 0xf907fdb769280040 0x7c83fedbb4940020 0x3ff7fffffc080060 0x1ffbfffffe040030

def z846 : W := mkw 0x300269b768000000 0x180134dbb4000000 0x3d0063fffc000000 0x1e8031fffe000000

def z847 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x102703fc03f001e0 0x081381fe01f800f0

def z848 : W := mkw 0x068262c2c2c75614 0x034131616163ab0a 0xed7e63c3c3c7fe1f 0x76bf31e1e1e3ff0f

def z849 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9fe3ffe3ffd99 0xfffcff1fff1ffecc

def z850 : W := mkw 0x428276c2cac70614 0x21413b616563830a 0xed7e67c3cfc7061f 0x76bf33e1e7e3830f

def z851 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xf7f9fe3bfe3ffd9f 0xfbfcff1dff1ffecf

def z852 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x3ff7fffffdc00000 0x1ffbfffffee00000

def z853 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0x8046a5c001c91800 0x402352e000e48c00

def z854 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2c0603c3c1c0061e 0x160301e1e0e0030f

def z855 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc019801 0x1ffbfffffe00cc00

def z856 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3f0027fffc000000 0x1f8013fffe000000

def z857 : W := mkw 0x12400a59b252a799 0x0920052cd92953cc 0x7fb95bfbb236e799 0xbfdcadfdd91b73cc

def z858 : W := mkw 0x13400a59b252a7d9 0x09a0052cd92953ec 0x77b95a3bb236e7f9 0xbbdcad1dd91b73fc

def z859 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdc4683fc03f807e0 0xee2341fe01fc03f0

def z860 : W := mkw 0xab85836c837a0754 0x55c2c1b641bd03aa 0xdcf783fc03f807fe 0xee7bc1fe01fc03ff

def z861 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3fd6a7fffc000000 0x1feb53fffe000000

def z862 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x14b95a3b82366000 0x0a5cad1dc11b3000

def z863 : W := mkw 0x12400a59b252a799 0x0920052cd92953cc 0x77bf5bfbb3f6e599 0xbbdfadfdd9fb72cc

def z864 : W := mkw 0x10400819b012a199 0x0820040cd80950cc 0x7799583bb036e599 0xbbccac1dd81b72cc

def z865 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x2b67fffffc000000 0x15b3fffffe000000

def z866 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff1a63c7c099fff 0xfff8d31e3e04cfff

def z867 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfff7a7fc7ff99fe1 0xfffbd3fe3ffccff0

def z868 : W := mkw 0x0200024082420610 0x0100012041210308 0xed7e63c3c3c7061f 0x76bf31e1e1e3830f

def z869 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x33a95a3bb236e199 0x99d4ad1dd91b70cc

def z870 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xef7e7bc3c3c7e61f 0x77bf3de1e1e3f30f

def z871 : W := mkw 0x468276c2c2c75614 0x23413b616163ab0a 0xefff7fc3c3f7fe1f 0xf7ffbfe1e1fbff0f

def z872 : W := mkw 0x1002689360000000 0x08013449b0000000 0x3ff7fffffc000000 0x1ffbfffffe000000

def z873 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xefff7bc3c3c7061f 0x77ffbde1e1e3830f

def z874 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7fb95a3ffe36e599 0xbfdcad1fff1b72cc

def z875 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x43b95a3b8236e599 0xa1dcad1dc11b72cc

def z876 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0xc3f9fe3b823ff801 0xe1fcff1dc11ffc00

def z877 : W := mkw 0x10200811340088ab 0x881004089a004455 0xfff9fe3ffe3fffff 0xfffcff1fff1fffff

def z878 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x34295a3bb2366000 0x1a14ad1dd91b3000

def z879 : W := mkw 0x028002c2c2420614 0x014001616121030a 0xed7623c3c3c1061f 0x76bb11e1e1e0830f

def z880 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff97a3bf23fffff 0xfffcbd1df91fffff

def z881 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x200003fbfc000000 0x100001fdfe000000

def z882 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc3fffc0003fffe1f 0xe1fffe0001ffff0f

def z883 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x3f767ffffc000000 0x1fbb3ffffe000000

def z884 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xfffffffffffe6000 0xffffffffffff3000

def z885 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0xfff7fffffff807e0 0xfffbfffffffc03f0

def z886 : W := mkw 0xb80589b769280000 0x5c02c4dbb4940000 0xfcf783fffff80000 0xfe7bc1fffffc0000

def z887 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfffffffffe3ff801 0xffffffffff1ffc00

def z888 : W := mkw 0xb00589b768000000 0x5802c4dbb4000000 0x3c4683fffc000000 0x1e2341fffe000000

def z889 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x100003ffbc000000 0x080001ffde000000

def z890 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7fb95a3fb236e7f9 0xbfdcad1fd91b73fc

def z891 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x7fb9de3ffe3effff 0xbfdcef1fff1f7fff

def z892 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xcbfffc0403fffa61 0xe5fffe0201fffd30

def z893 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b95a3bb236e7ff 0xbbdcad1dd91b73ff

def z894 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0xefffffc7cffff801 0xf7ffffe3e7fffc00

def z895 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x00295a3b8236e180 0x8014ad1dc11b70c0

def z896 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc3bf580003fff801 0xe1dfac0001fffc00

def z897 : W := mkw 0x12400a59b252a799 0x0920052cd92953cc 0xffff7bfbf3f7e79f 0xffffbdfdf9fbf3cf

def z898 : W := mkw 0xed07f52401ad5040 0x7683fa9200d6a820 0xc3fffc0403fff861 0xe1fffe0201fffc30

def z899 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x10275bffbc000000 0x0813adffde000000

def z900 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfdf783fc03f807f9 0xfefbc1fe01fc03fc

def z901 : W := mkw 0xec07f52409ad5000 0x7603fa9204d6a800 0xc3fffc040ffff801 0xe1fffe0207fffc00

def z902 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdc7703fc03f007e0 0x6e3b81fe01f803f0

def z903 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x836ffc0003fff801 0x41b7fe0001fffc00

def z904 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37295a3bb236e599 0x1b94ad1dd91b72cc

def z905 : W := mkw 0x028002c2c2420614 0x014001616121030a 0xac4603c3c1c0061e 0x562301e1e0e0030f

def z906 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x002e43c383c7001f 0x001721e1c1e3800f

def z907 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcd683fc01c807e0 0xee6b41fe00e403f0

def z908 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc32f7c0003fff801 0xe197be0001fffc00

def z909 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfffe63c3f3c7061f 0x7fff31e1f9e3830f

def z910 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc00061e 0x1ffbfffffe00030f

def z911 : W := mkw 0xab05816c01780340 0x5582c0b600bc01a0 0x984681fc01c803e0 0x4c2340fe00e401f0

def z912 : W := mkw 0x50027c9368000000 0x28013e49b4000000 0x3ff77ffbfc000000 0x1ffbbffdfe000000

def z913 : W := mkw 0xcc07f48249ad5000 0x6603fa4124d6a800 0xc3fffc004ffff801 0xe1fffe0027fffc00

def z914 : W := mkw 0xec07f52401ad5000 0x7603fa9200d6a800 0xcbfffdc403fff801 0xe5fffee201fffc00

def z915 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0xffffffffffcf9801 0xffffffffffe7cc00

def z916 : W := mkw 0xb00589b768000000 0x5802c4dbb4000000 0x3c8183fffc000000 0x1e40c1fffe000000

def z917 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xbc46a7fffdc91800 0x5e2353fffee48c00

def z918 : W := mkw 0x2b00036c03780740 0x158001b601bc03a0 0xdc7603fc03f807e0 0xee3b01fe01fc03f0

def z919 : W := mkw 0x4c02740001ad5000 0x26013a0000d6a800 0xc3b97c0003fff801 0xe1dcbe0001fffc00

def z920 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xf7f9fe3fbe3ffdf9 0xfbfcff1fdf1ffefc

def z921 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xd7fffe3803fff801 0xebffff1c01fffc00

def z922 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff9da3fb23fffff 0xfffced1fd91fffff

def z923 : W := mkw 0xcc07f48241ad5000 0x6603fa4120d6a800 0xcbfffdc043fff801 0xe5fffee021fffc00

def z924 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xf7fffc0033fff801 0xfbfffe0019fffc00

def z925 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1cf783fc03f007e0 0x0e7bc1fe01f803f0

def z926 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xe53e43c383c7061f 0x729f21e1c1e3830f

def z927 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x2f777ffbfc000000 0x17bbbffdfe000000

def z928 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed5623c3c1c1061f 0x76ab11e1e0e0830f

def z929 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3f277ffffc000000 0x1f93bffffe000000

def z930 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x74b95a3bb2366598 0xba5cad1dd91b32cc

def z931 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xbff7fffffc010206 0x5ffbfffffe008103

def z932 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xc17e63c383c7061f 0x60bf31e1c1e3830f

def z933 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x00295a3b8236e019 0x0014ad1dc11b700c

def z934 : W := mkw 0xef05976c03785740 0x7782cbb601bc2ba0 0xdff7bffc03f9ffe1 0xeffbdffe01fcfff0

def z935 : W := mkw 0x12400a59a2522710 0x0920052cd1291388 0xcc7f5bfb83f66600 0x663fadfdc1fb3300

def z936 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xf7f9fe3bb23fffff 0xfbfcff1dd91fffff

def z937 : W := mkw 0xab05836c837a0750 0x5582c1b641bd03a8 0xdcff83fc03fe07f9 0xee7fc1fe01ff03fc

def z938 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xec7623c3c3c1061e 0x763b11e1e1e0830f

def z939 : W := mkw 0x12400a59b252a799 0x0920052cd92953cc 0xffffdbffb3fee7f9 0xffffedffd9ff73fc

def z940 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3e8087fffc000000 0x1f4043fffe000000

def z941 : W := mkw 0xcc07f48241ad5000 0x6603fa4120d6a800 0xe3fffc03c3fff801 0xf1fffe01e1fffc00

def z942 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xeffffc0043fff801 0xf7fffe0021fffc00

def z943 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x9cf783fc01c807e0 0x4e7bc1fe00e403f0

def z944 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x002703f803f007e0 0x001381fc01f803f0

def z945 : W := mkw 0x00200000140088ab 0x801000000a004455 0xf380a4047c099fff 0xf9c052023e04cfff

def z946 : W := mkw 0xaf05836c03785740 0x5782c1b601bc2ba0 0xdcf783fc03f8ffe0 0xee7bc1fe01fc7ff0

def z947 : W := mkw 0x70027db768000000 0x38013edbb4000000 0x3fb17ffffc000000 0x1fd8bffffe000000

def z948 : W := mkw 0xf087fdb768850004 0x7843fedbb4428002 0x3ff7fffffc010006 0x1ffbfffffe008003

def z949 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdff783fc03f887e1 0xeffbc1fe01fc43f0

def z950 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3c7603fffc000000 0x1e3b01fffe000000

def z951 : W := mkw 0x028002c2c2c70614 0x014001616163830a 0xec7e03c3c3c7061f 0x763f01e1e1e3830f

def z952 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc3f9fc0003fff801 0xe1fcfe0001fffc00

def z953 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfd50a4047c091fff 0x7ea852023e048fff

def z954 : W := mkw 0xfc059db769285000 0x7e02cedbb4942800 0x3e819ffffc38f800 0x9f40cffffe1c7c00

def z955 : W := mkw 0x12c00a59b252a79d 0x0960052cd92953ce 0x77b95a3bb236e79f 0xbbdcad1dd91b73cf

def z956 : W := mkw 0x02e0024896d7afbf 0x817001244b6bd7df 0xc008000003ffffff 0xe004000001ffffff

def z957 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfdfe63c3c3c7079f 0xfeff31e1e1e383cf

def z958 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xe3fffc007ffff801 0xf1fffe003ffffc00

def z959 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3c40a7fffc000000 0x1e2053fffe000000

def z960 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7e63c3c3cf9e1f 0xf6bf31e1e1e7cf0f

def z961 : W := mkw 0x10600819b412a9bb 0x8830040cda0954dd 0xffd9fc3ffc3fffff 0xffecfe1ffe1fffff

def z962 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x67b95a3b8236e419 0xb3dcad1dc11b720c

def z963 : W := mkw 0x1000081130008089 0x0800040898004044 0x77b95a3bb236e599 0xbbdcad1dd91b72cc

def z964 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1ca783fc03f807e0 0x8e53c1fe01fc03f0

def z965 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xfffffc047ffffe1f 0xfffffe023fffff0f

def z966 : W := mkw 0x00826082c0870014 0x004130416043800a 0xed7e63c3c3c7001f 0x76bf31e1e1e3800f

def z967 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x7ffffffffff6e001 0xbffffffffffb7000

def z968 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x3fb1dffffc000000 0x1fd8effffe000000

def z969 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x12a95a3bb2366000 0x0954ad1dd91b3000

def z970 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfdf7a3fc43f807e0 0xfefbd1fe21fc03f0

def z971 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff6a4047fc99fff 0xfffb52023fe4cfff

def z972 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xec4e23c3c3c7061f 0x762711e1e1e3830f

def z973 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x03fffc0003f7f801 0x01fffe0001fbfc00

def z974 : W := mkw 0x10000a11a2020410 0x08000508d1010208 0x77b95a3bb236e419 0xbbdcad1dd91b720c

def z975 : W := mkw 0x12e00adbf652afbf 0x8970056dfb2957df 0x3c0003fffc0007fe 0x1e0001fffe0003ff

def z976 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3c215bfffc000000 0x1e10adfffe000000

def z977 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x43bf7c0003f7f801 0xa1dfbe0001fbfc00

def z978 : W := mkw 0x0b00024803780740 0x0580012401bc03a0 0xdcf703f803f807e0 0xee7b81fc01fc03f0

def z979 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xddf7a3fc03f907e1 0xeefbd1fe01fc83f0

def z980 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x3ff9fe3ffe366000 0x1ffcff1fff1b3000

def z981 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdef787fc03f89fe0 0xef7bc3fe01fc4ff0

def z982 : W := mkw 0xb00589b768000000 0x5802c4dbb4000000 0x3ff7dbfffc000000 0x1ffbedfffe000000

def z983 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x03295a3b8236e001 0x0194ad1dc11b7000

def z984 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x002e43c383c6061e 0x001721e1c1e3030f

def z985 : W := mkw 0xab05816401680240 0x5582c0b200b40120 0xdcf783fc01c807e0 0xee7bc1fe00e403f0

def z986 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfff7a7fc7ff907ff 0xfffbd3fe3ffc83ff

def z987 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ffffffffe366000 0x1fffffffff1b3000

def z988 : W := mkw 0x10400811b002a099 0x08200408d801504c 0x77b95a3bb236e019 0xbbdcad1dd91b700c

def z989 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdffffffc03ffffe1 0xeffffffe01fffff0

def z990 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x7fb97e3ffe37ffff 0xbfdcbf1fff1bffff

def z991 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xe3fffffbfffff801 0xf1fffffdfffffc00

def z992 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0xfff7fffffff99801 0xfffbfffffffccc00

def z993 : W := mkw 0x00200000140088ab 0x801000000a004455 0x3f80a4047c099fff 0x9fc052023e04cfff

def z994 : W := mkw 0x74027db768855000 0x3a013edbb442a800 0x3f087ffffc07f801 0x1f843ffffe03fc00

def z995 : W := mkw 0xab45836c837a2750 0x55a2c1b641bd13a8 0xdcff83fc03fe67e0 0xee7fc1fe01ff33f0

def z996 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc2cfbc0003fff801 0xe167de0001fffc00

def z997 : W := mkw 0xab05836c837a0750 0x5582c1b641bd03a8 0xdcffc3ff83fe07e0 0xee7fe1ffc1ff03f0

def z998 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b97a3bf237e59f 0xbbdcbd1df91bf2cf

def z999 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0x3ff7fffffc380000 0x9ffbfffffe1c0000

def z1000 : W := mkw 0x10e26893f487a8bf 0x88713449fa43d45f 0x23087c03fc07f81f 0x11843e01fe03fc0f

def z1001 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37895a3bb036e599 0x9bc4ad1dd81b72cc

def z1002 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcf7a7fc03f91fe0 0xee7bd3fe01fc8ff0

def z1003 : W := mkw 0x02c262cac2d72714 0x01613165616b938a 0xed7e63c3c3f7661f 0x76bf31e1e1fbb30f

def z1004 : W := mkw 0x8c05800001ad5000 0x4602c00000d6a800 0xc3ffd80003fff801 0xe1ffec0001fffc00

def z1005 : W := mkw 0x10400819b012a199 0x0820040cd80950cc 0x2309583bb036e019 0x1184ac1dd81b700c

def z1006 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7b95a3bb23ffd99 0xfbdcad1dd91ffecc

def z1007 : W := mkw 0x00200000140088ab 0x801000000a004455 0xbf40a4047c099fff 0x5fa052023e04cfff

def z1008 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff1fc047c099fff 0xfff8fe023e04cfff

def z1009 : W := mkw 0xa205836402400600 0x5102c1b201200300 0xdcf783fc03c807e0 0xee7bc1fe01e403f0

def z1010 : W := mkw 0xab05816c01780340 0x5582c0b600bc01a0 0xdcd781fc01f807e0 0xee6bc0fe00fc03f0

def z1011 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xffffffffffffffe1 0xfffffffffffffff0

def z1012 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ffffffffc06e001 0x1ffffffffe037000

def z1013 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x40b95a3b82366000 0xa05cad1dc11b3000

def z1014 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0x000601c001c00000 0x000300e000e00000

def z1015 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0xed797a3bc237661f 0x76bcbd1de11bb30f

def z1016 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3cb103fffc000000 0x1e5881fffe000000

def z1017 : W := mkw 0xab05836c837a0750 0x5582c1b641bd03a8 0xfdffe3ffc3ff07ff 0xfefff1ffe1ff83ff

def z1018 : W := mkw 0x028260c2c0c70214 0x014130616063810a 0x210e61c3c1c7001f 0x108730e1e0e3800f

def z1019 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xedfee3c3c3cf061f 0xf6ff71e1e1e7830f

def z1020 : W := mkw 0xec27f5a64dad5822 0xf613fad326d6ac11 0x8846a5c44dc91a66 0x442352e226e48d33

def z1021 : W := mkw 0xfc07fdb769285000 0x7e03fedbb4942800 0x3ff7fffffc081800 0x1ffbfffffe040c00

def z1022 : W := mkw 0x00200000140088ab 0x801000000a004455 0xffd8a4047e3fffff 0xffec52023f1fffff

def z1023 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0xdcf683fc03c807e0 0xee7b41fe01e403f0

def z1024 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3cf7dbfffc000000 0x1e7bedfffe000000

def z1025 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x12819fffbc000000 0x0940cfffde000000

def z1026 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdff7a7fc03f807e0 0xeffbd3fe01fc03f0

def z1027 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdc2703fc03f807e0 0xee1381fe01fc03f0

def z1028 : W := mkw 0x0002600000850000 0x0001300000428000 0xc3fffc0003fff801 0xe1fffe0001fffc00

def z1029 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xd0f783fc03f801e0 0xe87bc1fe01fc00f0

def z1030 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x65395a3b8236e599 0xb29cad1dc11b72cc

def z1031 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9fe3bf23fff9f 0xfffcff1df91fffcf

def z1032 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x03fffc0003fef800 0x81fffe0001ff7c00

def z1033 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcffdbfc03fe67e0 0xee7fedfe01ff33f0

def z1034 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc000600 0x7ffbfffffe000300

def z1035 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc080000 0xfffbfffffe040000

def z1036 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x10295a3bb2366180 0x0814ad1dd91b30c0

def z1037 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc17f780003fff801 0xe0bfbc0001fffc00

def z1038 : W := mkw 0xfc259d353d28d8ab 0xfe12ce9a9e946c55 0x12819c3c3c38f9e0 0x8940ce1e1e1c7cf0

def z1039 : W := mkw 0xef07f5e649ed5240 0x7783faf324f6a920 0x8846a5c44dc91a60 0x442352e226e48d30

def z1040 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc2ffdc0003fef800 0xe17fee0001ff7c00

def z1041 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x7ff7fffffc000580 0xbffbfffffe0002c0

def z1042 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfcf783fc43f807fe 0xfe7bc1fe21fc03ff

def z1043 : W := mkw 0x12600a59b652afbb 0x8930052cdb2957dd 0xffffffffffffffff 0xffffffffffffffff

def z1044 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc30e000 0x9ffbfffffe187000

def z1045 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x3ffffffffc3ff801 0x9ffffffffe1ffc00

def z1046 : W := mkw 0xeb05976c03780740 0x7582cbb601bc03a0 0xdef79ffc03f807e0 0xef7bcffe01fc03f0

def z1047 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfd7e63c7ffc7061f 0x7ebf31e3ffe3830f

def z1048 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcf783fc03f907ff 0xee7bc1fe01fc83ff

def z1049 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b9da3fb23ee5f9 0xbbdced1fd91f72fc

def z1050 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xeffe63c3c3c7861f 0xf7ff31e1e1e3c30f

def z1051 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x1ef7dfffbc000000 0x0f7befffde000000

def z1052 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7b95a3bb237e79f 0xfbdcad1dd91bf3cf

def z1053 : W := mkw 0x33600b7db652affb 0x99b005bedb2957fd 0x3c0003fffc0007fe 0x1e0001fffe0003ff

def z1054 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xfff7fffffdc99801 0xfffbfffffee4cc00

def z1055 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7b95a3bb23ee7f9 0xfbdcad1dd91f73fc

def z1056 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x77b95a3bb2366580 0xbbdcad1dd91b32c0

def z1057 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xc86783fc03f807e0 0xe433c1fe01fc03f0

def z1058 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7ee3c7c3cf067f 0x76bf71e3e1e7833f

def z1059 : W := mkw 0x1000081120000000 0x0800040890000000 0xfff9fe3ffe3ff801 0xfffcff1fff1ffc00

def z1060 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x12a9de3fbe3ef9e0 0x8954ef1fdf1f7cf0

def z1061 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xfffffffffff76001 0x7ffffffffffbb000

def z1062 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc34efc0003fff801 0xe1a77e0001fffc00

def z1063 : W := mkw 0x0c02600001ad5000 0x0601300000d6a800 0xc3ff780003fff801 0xe1ffbc0001fffc00

def z1064 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9fa3ff23fe7ff 0xfffcfd1ff91ff3ff

def z1065 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x002f580003fef800 0x8017ac0001ff7c00

def z1066 : W := mkw 0xec27f5a65dadd8ab 0xf613fad32ed6ec55 0xffd6a5c47dc99fff 0xffeb52e23ee4cfff

def z1067 : W := mkw 0xcc05940001ad5000 0x6602ca0000d6a800 0xc3d9bc0003fff801 0xe1ecde0001fffc00

def z1068 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7e63c3c3f7e61f 0xf6bf31e1e1fbf30f

def z1069 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xd4b703f803f807e0 0xea5b81fc01fc03f0

def z1070 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfd7e63c7c3c707ff 0x7ebf31e3e1e383ff

def z1071 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b9de3bb23efd99 0xbbdcef1dd91f7ecc

def z1072 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x77b95a3bb236e001 0xbbdcad1dd91b7000

def z1073 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xedff63c3c3f7061f 0xf6ffb1e1e1fb830f

def z1074 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3f46fffffc000000 0x1fa37ffffe000000

def z1075 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc289180003fff801 0xe1448c0001fffc00

def z1076 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdff7dbfc03f807e0 0xeffbedfe01fc03f0

def z1077 : W := mkw 0x00200000140088ab 0x801000000a004455 0xbfd0a4047c091ffe 0x5fe852023e048fff

def z1078 : W := mkw 0xcc07f48241ad5000 0x6603fa4120d6a800 0xc3ffffc383fff801 0xe1ffffe1c1fffc00

def z1079 : W := mkw 0xa305836c02500740 0x5182c1b6012803a0 0xdcf783fc03c007e0 0x6e7bc1fe01e003f0

def z1080 : W := mkw 0xcc05940001285000 0x6602ca0000942800 0xc3ffdc0003fef801 0xe1ffee0001ff7c00

def z1081 : W := mkw 0xab05816c01780340 0x5582c0b600bc01a0 0x108781fc01f801e0 0x8843c0fe00fc00f0

def z1082 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc3fffc0003ffffe1 0xe1fffe0001fffff0

def z1083 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xefffffc3c3fffe1f 0xf7ffffe1e1ffff0f

def z1084 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3ff1fffffc000000 0x1ff8fffffe000000

def z1085 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x3ffffffffff7f801 0x1ffffffffffbfc00

def z1086 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xec2e43c3c3c7061f 0x761721e1e1e3830f

def z1087 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc389fc0003fff801 0xe1c4fe0001fffc00

def z1088 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7ff97a3bf236e599 0xbffcbd1df91b72cc

def z1089 : W := mkw 0x020262c242400600 0x0101316121200300 0xed7663c3c3c1061f 0x76bb31e1e1e0830f

def z1090 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x77b97e3bb237fd99 0xbbdcbf1dd91bfecc

def z1091 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x002f580003f7f801 0x0017ac0001fbfc00

def z1092 : W := mkw 0x54227c937c85d8ab 0xaa113e49be42ec55 0x23087c03fc07f81f 0x11843e01fe03fc0f

def z1093 : W := mkw 0x468276c2c2c75614 0x23413b616163ab0a 0xed7e67c3c3c71e1f 0x76bf33e1e1e38f0f

def z1094 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x77b95a3bb2366419 0x3bdcad1dd91b320c

def z1095 : W := mkw 0x2300036c02500740 0x118001b6012803a0 0x9c4603fc01c007e0 0x4e2301fe00e003f0

def z1096 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7ee7c7cfc7061f 0x76bf73e3e7e3830f

def z1097 : W := mkw 0x028260c2c0c70214 0x014130616063810a 0xed5e61c3c1c7061f 0x76af30e1e0e3830f

def z1098 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0x3ffffffffc070001 0x1ffffffffe038000

def z1099 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xc0295a3b823fffff 0xe014ad1dc11fffff

def z1100 : W := mkw 0x300269b768000000 0x180134dbb4000000 0x3ff6e7fffc000000 0x1ffb73fffe000000

def z1101 : W := mkw 0x300269b768000000 0x180134dbb4000000 0x3c4623fffc000000 0x1e2311fffe000000

def z1102 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff6a7c47c099fff 0xfffb53e23e04cfff

def z1103 : W := mkw 0x300269b768000000 0x180134dbb4000000 0x3c2643fffc000000 0x1e1321fffe000000

def z1104 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ec7bffffc000000 0x1f63dffffe000000

def z1105 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xe7fffe0383fff801 0xf3ffff01c1fffc00

def z1106 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xe7fffc0003fffc19 0xf3fffe0001fffe0c

def z1107 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xcc7e43c383c7061f 0x663f21e1c1e3830f

def z1108 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x20275bfbfc000000 0x1013adfdfe000000

def z1109 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x56b95a3bb236e580 0xab5cad1dd91b72c0

def z1110 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x7ff7fffffc008001 0xbffbfffffe004000

def z1111 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcf7a3fc43f907e6 0xee7bd1fe21fc83f3

def z1112 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0xffd6a5c47dc99801 0xffeb52e23ee4cc00

def z1113 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfcf783fc7ff807e0 0xfe7bc1fe3ffc03f0

def z1114 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0xbff7fffffdc80000 0x5ffbfffffee40000

def z1115 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b95a3bfe36e59f 0xbbdcad1dff1b72cf

def z1116 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xc0f783f803f807e0 0xe07bc1fc01fc03f0

def z1117 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x44395a3b82366400 0x221cad1dc11b3200

def z1118 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0xfffffdc47ffff801 0xfffffee23ffffc00

def z1119 : W := mkw 0xfc07fdb769285000 0x7e03fedbb4942800 0x7ffffffffe3ef801 0xbfffffffff1f7c00

def z1120 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x63295a3bb236e599 0xb194ad1dd91b72cc

def z1121 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x1ae7fffffc000000 0x0d73fffffe000000

def z1122 : W := mkw 0x4c02740001ad5000 0x26013a0000d6a800 0x03087c0003f7f801 0x01843e0001fbfc00

def z1123 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfdff63fbc3c7061f 0x7effb1fde1e3830f

def z1124 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3c67fffffc000000 0x1e33fffffe000000

def z1125 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0x3fffffffffc60000 0x1fffffffffe30000

def z1126 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdc7683fc03c807e0 0x6e3b41fe01e403f0

def z1127 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0xffffffffffc7061f 0x7fffffffffe3830f

def z1128 : W := mkw 0xf407fdb768005000 0x7a03fedbb4002800 0x3ff7fffffc00f800 0x1ffbfffffe007c00

def z1129 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b9fe3ffe3ffdff 0xbbdcff1fff1ffeff

def z1130 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3c0003fffc00061e 0x1e0001fffe00030f

def z1131 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff95a3bb236e799 0xfffcad1dd91b73cc

def z1132 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xcffffc0003fffe01 0xe7fffe0001ffff00

def z1133 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x13f7ffffbc000000 0x09fbffffde000000

def z1134 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x10a95a3b82366180 0x8854ad1dc11b30c0

def z1135 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xf7ff5a3bb3f6e599 0xfbffad1dd9fb72cc

def z1136 : W := mkw 0xf407fdb768855000 0x7a03fedbb442a800 0x3ff7fffffc011800 0x1ffbfffffe008c00

def z1137 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x20295a3bb2366018 0x1014ad1dd91b300c

def z1138 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xf7b97e3bfe3fffff 0xfbdcbf1dff1fffff

def z1139 : W := mkw 0x300009b768000000 0x180004dbb4000000 0xfd5023fffc01061f 0x7ea811fffe00830f

def z1140 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x3ffffffffffef800 0x9fffffffffff7c00

def z1141 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xe12e63c3c3c7061f 0x709731e1e1e3830f

def z1142 : W := mkw 0xef05976c03785740 0x7782cbb601bc2ba0 0xdcf787fc03f81fe0 0xee7bc3fe01fc0ff0

def z1143 : W := mkw 0xf407fdb768855000 0x7a03fedbb442a800 0xfffffffffc0ff801 0xfffffffffe07fc00

def z1144 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc099fe1 0xfffbfffffe04cff0

def z1145 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xbffffffffdcff801 0x5ffffffffee7fc00

def z1146 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfffee7c7ffcf07ff 0xffff73e3ffe783ff

def z1147 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x5cb703fc03f007e0 0xae5b81fe01f803f0

def z1148 : W := mkw 0x00200000140088ab 0x801000000a004455 0xdac0a4047c099fff 0xed6052023e04cfff

def z1149 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3e811bfffc000000 0x1f408dfffe000000

def z1150 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xfdf7c3ff83f807e0 0xfefbe1ffc1fc03f0

def z1151 : W := mkw 0xcc07f48241ad5000 0x6603fa4120d6a800 0xffffffc7fffff801 0xffffffe3fffffc00

def z1152 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x75395a3bb2366599 0x3a9cad1dd91b32cc

def z1153 : W := mkw 0x028260c2c0c70214 0x014130616063810a 0xe97e61c3c3c7021f 0x74bf30e1e1e3810f

def z1154 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xcfffffc003fff801 0xe7ffffe001fffc00

def z1155 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdef787fc3ff807e0 0xef7bc3fe1ffc03f0

def z1156 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc01001f 0x1ffbfffffe00800f

def z1157 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37b95a3bb236e180 0x9bdcad1dd91b70c0

def z1158 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0xfff9fe3fb23ffff9 0xfffcff1fd91ffffc

def z1159 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xfffffc047fffffe1 0xfffffe023ffffff0

def z1160 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x202e43c3c3c6001e 0x101721e1e1e3000f

def z1161 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7389583bb236e599 0xb9c4ac1dd91b72cc

def z1162 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x14295a3b82366580 0x0a14ad1dc11b32c0

def z1163 : W := mkw 0x00200000140088ab 0x801000000a004455 0xffd1bc047c39ffff 0xffe8de023e1cffff

def z1164 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x25395a3b82366000 0x129cad1dc11b3000

def z1165 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x7ffffffffe060001 0x3fffffffff030000

def z1166 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcff83fc03fee7e1 0xee7fc1fe01ff73f0

def z1167 : W := mkw 0xf0059db768000000 0x7802cedbb4000000 0x3c011bfffc000000 0x1e008dfffe000000

def z1168 : W := mkw 0xab05816c01780340 0x5582c0b600bc01a0 0x9cf783fc01f803e0 0xce7bc1fe00fc01f0

def z1169 : W := mkw 0x10400819b012a199 0x0820040cd80950cc 0x37b95a3bb036e199 0x9bdcad1dd81b70cc

def z1170 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xfffee7c7c3cf9fff 0xffff73e3e1e7cfff

def z1171 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x03b95a3b82366000 0x01dcad1dc11b3000

def z1172 : W := mkw 0x50a27c93fc8788bf 0xa8513e49fe43c45f 0x23087c03fc07981f 0x11843e01fe03cc0f

def z1173 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xd3fffc0403fff9e1 0xe9fffe0201fffcf0

def z1174 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x7ff7fffffc000419 0x3ffbfffffe00020c

def z1175 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37b95a3bb2366598 0x1bdcad1dd91b32cc

def z1176 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xbff7fffffdf9f800 0xdffbfffffefcfc00

def z1177 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff9da3ffe3ee7ff 0xfffced1fff1f73ff

def z1178 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xf7b9de3fbe3fffff 0xfbdcef1fdf1fffff

def z1179 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x7fb95bfffe36e001 0xbfdcadffff1b7000

def z1180 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xe94e61c3c3c7061f 0x74a730e1e1e3830f

def z1181 : W := mkw 0xf9259d3d3d3889eb 0xfc92ce9e9e9c44f5 0x12819c3c3c3899e0 0x8940ce1e1e1c4cf0

def z1182 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x23295a3bb2366000 0x1194ad1dd91b3000

def z1183 : W := mkw 0xcc05940001ad5000 0x6602ca0000d6a800 0x02899c0003fef800 0x8144ce0001ff7c00

def z1184 : W := mkw 0x00200000140088ab 0x801000000a004455 0xeb40a4047c099fff 0xf5a052023e04cfff

def z1185 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x03affc0003fff801 0x81d7fe0001fffc00

def z1186 : W := mkw 0x0ba0024897ff8fff 0x85d001244bffc7ff 0xc008000003ff9fff 0xe004000001ffcfff

def z1187 : W := mkw 0xcc05940001ad5000 0x6602ca0000d6a800 0xc009180003fff801 0xe0048c0001fffc00

def z1188 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff97a3ffe37e7ff 0xfffcbd1fff1bf3ff

def z1189 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc2afdc0003fff801 0xe157ee0001fffc00

def z1190 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x1cf783fc03f801e0 0x8e7bc1fe01fc00f0

def z1191 : W := mkw 0xec07f52401ad5000 0x7603fa9200d6a800 0xc3fffff803fff801 0xe1fffffc01fffc00

def z1192 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x7ff7fffffe300000 0xbffbffffff180000

def z1193 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x653e63c3c3c7041f 0x329f31e1e1e3820f

def z1194 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x37b95a3bb236e019 0x1bdcad1dd91b700c

def z1195 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0x3ff7fffffff00000 0x1ffbfffffff80000

def z1196 : W := mkw 0xab05816c01780340 0x5582c0b600bc01a0 0xd8f781fc03f803e0 0xec7bc0fe01fc01f0

def z1197 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b95e3bbe36fd99 0xbbdcaf1ddf1b7ecc

def z1198 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc010001 0x7ffbfffffe008000

def z1199 : W := mkw 0xb00589b768000000 0x5802c4dbb4000000 0x3ff7a7fffc000000 0x1ffbd3fffe000000

def z1200 : W := mkw 0x0c00000001ad5000 0x0600000000d6a800 0xc029580003fff801 0xe014ac0001fffc00

def z1201 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x7ff9da3fb236e599 0xbffced1fd91b72cc

def z1202 : W := mkw 0xa007e1a640000000 0x5003f0d320000000 0x3ff7e7fffc000000 0x1ffbf3fffe000000

def z1203 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x02275ffbbc000000 0x0113affdde000000

def z1204 : W := mkw 0xf807fdb769280000 0x7c03fedbb4940000 0xfffffffffffee001 0xffffffffffff7000

def z1205 : W := mkw 0xf0059d3528000000 0x7802ce9a94000000 0x3ff7dfffbc000000 0x1ffbefffde000000

def z1206 : W := mkw 0xf807fdb769ad0000 0x7c03fedbb4d68000 0xffffffffffff0001 0xffffffffffff8000

def z1207 : W := mkw 0x028262c2c2420614 0x014131616121030a 0xed7663c3c3c0061e 0x76bb31e1e1e0030f

def z1208 : W := mkw 0xfc07fdb769285000 0x7e03fedbb4942800 0xfff7fffffc39f801 0xfffbfffffe1cfc00

def z1209 : W := mkw 0x00200000140088ab 0x801000000a004455 0xffd8fc047c0fffff 0xffec7e023e07ffff

def z1210 : W := mkw 0xef05976c03785740 0x7782cbb601bc2ba0 0xdcf79bfc03f867e0 0xee7bcdfe01fc33f0

def z1211 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x7ff9fe3ffe3efdf9 0xbffcff1fff1f7efc

def z1212 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xdffffc0403fff801 0xeffffe0201fffc00

def z1213 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff97e3bfe37ff9f 0xfffcbf1dff1bffcf

def z1214 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x2d2e63c3c3c7061f 0x169731e1e1e3830f

def z1215 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x41395a3b82366001 0x209cad1dc11b3000

def z1216 : W := mkw 0xec07f5a649ad5000 0x7603fad324d6a800 0xdffffffc4ffff801 0xeffffffe27fffc00

def z1217 : W := mkw 0xf007fdb768850000 0x7803fedbb4428000 0xbff7fffffdc10000 0x5ffbfffffee08000

def z1218 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xd3fffc043ffff801 0xe9fffe021ffffc00

def z1219 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3f81fffffc000000 0x1fc0fffffe000000

def z1220 : W := mkw 0xf407fdb768855000 0x7a03fedbb442a800 0x7ffffffffe37f801 0xbfffffffff1bfc00

def z1221 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xed7ee7c3c3cf1e1f 0x76bf73e1e1e78f0f

def z1222 : W := mkw 0x468276c2c2c75614 0x23413b616163ab0a 0xeffeffc3c3cffe1f 0xf7ff7fe1e1e7ff0f

def z1223 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xac6e63c3c3c7061e 0x563731e1e1e3830f

def z1224 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xbfffffffffff7800 0x5fffffffffffbc00

def z1225 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ea7dffffc000000 0x1f53effffe000000

def z1226 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x77b95a3fbe36e5f9 0xbbdcad1fdf1b72fc

def z1227 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xef7e67c3ffc7061f 0x77bf33e1ffe3830f

def z1228 : W := mkw 0xef05976c03785740 0x7782cbb601bc2ba0 0xdfffdffc03feffe1 0xefffeffe01ff7ff0

def z1229 : W := mkw 0x0000020882120510 0x0000010441090288 0x77b95a3b8236e599 0xbbdcad1dc11b72cc

def z1230 : W := mkw 0xfc07fdb769285000 0x7e03fedbb4942800 0xfff7fffffff8f800 0xfffbfffffffc7c00

def z1231 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xcbfffc044ffff801 0xe5fffe0227fffc00

def z1232 : W := mkw 0xcc05940001ad5000 0x6602ca0000d6a800 0xc2ff9c0003fff801 0xe17fce0001fffc00

def z1233 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3c0003fffc0007e0 0x1e0001fffe0003f0

def z1234 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x37b7dfffbc000000 0x1bdbefffde000000

def z1235 : W := mkw 0x12400a59b252a799 0x0920052cd92953cc 0xf7b95a3bb3f6e799 0xfbdcad1dd9fb73cc

def z1236 : W := mkw 0xec07f5a641ad5000 0x7603fad320d6a800 0xffffffffc3fff801 0xffffffffe1fffc00

def z1237 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x75b95a3b82366599 0xbadcad1dc11b32cc

def z1238 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x7ff9fe3ffe36e7ff 0xbffcff1fff1b73ff

def z1239 : W := mkw 0x10400819a0122110 0x0820040cd0091088 0x0009583b80366000 0x0004ac1dc01b3000

def z1240 : W := mkw 0x12400a59a2522710 0x0920052cd1291388 0x002f5bfb83f66000 0x0017adfdc1fb3000

def z1241 : W := mkw 0xb007e9b768000000 0x5803f4dbb4000000 0x3df7e3fffc000000 0x1efbf1fffe000000

def z1242 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0x3c2f5bfffff66000 0x1e17adfffffb3000

def z1243 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x3c295a3ffe3667fe 0x1e14ad1fff1b33ff

def z1244 : W := mkw 0x028262cac2d70714 0x01413165616b838a 0xffff7bfbc3f7e79f 0xffffbdfde1fbf3cf

def z1245 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xef7e67c3c3c79e1f 0x77bf33e1e1e3cf0f

def z1246 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0x6d3e43c3c3c6061f 0x369f21e1e1e3030f

def z1247 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0xfff9de3fbe3efff9 0xfffcef1fdf1f7ffc

def z1248 : W := mkw 0x428276c2c2c70614 0x21413b616163830a 0xef7e7fc3c3c7061f 0x77bf3fe1e1e3830f

def z1249 : W := mkw 0xec07f52401ad5000 0x7603fa9200d6a800 0xfffffffc7ffff801 0xfffffffe3ffffc00

def z1250 : W := mkw 0xcc05940001ad5000 0x6602ca0000d6a800 0xc3b9dc0003fff801 0xe1dcee0001fffc00

def z1251 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x98e783fc03f803e0 0xcc73c1fe01fc01f0

def z1252 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc37f7c0003f7f801 0x61bfbe0001fbfc00

def z1253 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x9cc783fc01f807e0 0xce63c1fe00fc03f0

def z1254 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x24295a3b82366418 0x1214ad1dc11b320c

def z1255 : W := mkw 0x00200000140088ab 0x801000000a004455 0xfff0e607fc099fff 0xfff87303fe04cfff

def z1256 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3ff7fffffc089800 0x9ffbfffffe044c00

def z1257 : W := mkw 0x4c02740001ad5000 0x26013a0000d6a800 0xc3d8fc0003fff801 0xe1ec7e0001fffc00

def z1258 : W := mkw 0xeb05976c0b780740 0x7582cbb605bc03a0 0xdcf787fc0ff807e0 0xee7bc3fe07fc03f0

def z1259 : W := mkw 0x4c02740001ad5000 0x26013a0000d6a800 0xc008580003fff801 0xe0042c0001fffc00

def z1260 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xe3fffc0043fff81f 0xf1fffe0021fffc0f

def z1261 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xec7e43c3c3c6061e 0x763f21e1e1e3030f

def z1262 : W := mkw 0x10600819b412a9bb 0x8830040cda0954dd 0x3389fc3ffc3ff9ff 0x99c4fe1ffe1ffcff

def z1263 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7fffffc099e1f 0xfffbfffffe04cf0f

def z1264 : W := mkw 0x028002c2c2420614 0x014001616121030a 0x2c2603c3c3c0061e 0x161301e1e1e0030f

def z1265 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0x3d777bfffc000000 0x1ebbbdfffe000000

def z1266 : W := mkw 0xcc87f48241ad5004 0x6643fa4120d6a802 0xc3fffc0043fff807 0xe1fffe0021fffc03

def z1267 : W := mkw 0x4c00140001ad5000 0x26000a0000d6a800 0xc2081c0003fff801 0xe1040e0001fffc00

def z1268 : W := mkw 0x10600a19b612adbb 0x8830050cdb0956dd 0x7ff9fe3ffe37fd9f 0xbffcff1fff1bfecf

def z1269 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0x002703f803f801e0 0x801381fc01fc00f0

def z1270 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xa96e63c3c3c7021f 0x54b731e1e1e3810f

def z1271 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x53b95a3bb236e181 0xa9dcad1dd91b70c0

def z1272 : W := mkw 0x300009b768000000 0x180004dbb4000000 0x3d3043fffc000000 0x1e9821fffe000000

def z1273 : W := mkw 0x10400a19a2122510 0x0820050cd1091288 0x40295a3b82366580 0xa014ad1dc11b32c0

def z1274 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xdcf7a7fc4ff807e0 0xee7bd3fe27fc03f0

def z1275 : W := mkw 0x300269b768000000 0x180134dbb4000000 0x3ff77bfffc000000 0x1ffbbdfffe000000

def z1276 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xd8c781fc03f807e0 0xec63c0fe01fc03f0

def z1277 : W := mkw 0x028002c2c2420614 0x014001616121030a 0xed7e43c3c3c6061f 0x76bf21e1e1e3030f

def z1278 : W := mkw 0xf007fdb768000000 0x7803fedbb4000000 0xfff7ffffffc00000 0x7ffbffffffe00000

def z1279 : W := mkw 0xfc07fdb769ad5000 0x7e03fedbb4d6a800 0xffffffffffcf1801 0x7fffffffffe78c00

def z1280 : W := mkw 0xab05836c03780740 0x5582c1b601bc03a0 0xddffc3fc03fe07e1 0xeeffe1fe01ff03f0

def z1281 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x02295a3bb236e000 0x0114ad1dd91b7000

def z1282 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0x022f5c0003f6f800 0x0117ae0001fb7c00

def z1283 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x54b95a3b8236e599 0xaa5cad1dc11b72cc

def z1284 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xc86e63c3c3c7061f 0x643731e1e1e3830f

def z1285 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xcbfffc0043fffa07 0xe5fffe0021fffd03

def z1286 : W := mkw 0x468276c2c2c75614 0x23413b616163ab0a 0xed7e7bc3c3c7661f 0x76bf3de1e1e3b30f

def z1287 : W := mkw 0xcc07f40001ad5000 0x6603fa0000d6a800 0xc0ffd80003fff801 0xe07fec0001fffc00

def z1288 : W := mkw 0x70001db768000000 0x38000edbb4000000 0x3e001ffffc000000 0x1f000ffffe000000

def z1289 : W := mkw 0x4402740000855000 0x22013a000042a800 0xc3ff7c0003f7f801 0xe1ffbe0001fbfc00

def z1290 : W := mkw 0xb00589b768000000 0x5802c4dbb4000000 0x3c2703fffc000000 0x1e1381fffe000000

def z1291 : W := mkw 0x028262c2c2c70614 0x014131616163830a 0xeffee7c3c3c7061f 0x77ff73e1e1e3830f

def z1292 : W := mkw 0x10400a19b212a599 0x0820050cd90952cc 0x74295a3bb236e599 0xba14ad1dd91b72cc

def z1293 : W := mkw 0x028260c2c0c70214 0x014130616063810a 0xad7e63c3c1c7021f 0x56bf31e1e0e3810f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z9,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z10,z5]),(0,[z11,z0,z1,z7,z12,z4,z5]),(0,[z0,z1,z7,z13,z3,z4,z5])],[(0,[z0,z1,z14,z9,z3,z4,z5]),(0,[z0,z1,z15,z7,z3,z4,z5]),(0,[z0,z1,z16,z7,z3,z4,z5])],[(0,[z17,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z18,z7,z3,z4,z5]),(0,[z19,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z20,z21,z4,z5]),(0,[z0,z1,z7,z3,z4,z22,z23])],[(0,[z0,z1,z7,z24,z3,z4,z5]),(0,[z0,z1,z25,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z26,z5]),(0,[z0,z27,z1,z7,z3,z4,z23])],[(0,[z28,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z30,z3,z4,z5]),(0,[z0,z1,z7,z31,z3,z4,z5]),(0,[z32,z0,z1,z7,z33,z4,z5]),(0,[z32,z0,z1,z7,z3,z34,z5]),(0,[z0,z1,z35,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z36,z4])],[(1,[z17,z37,z7,z3,z4,z5]),(0,[z38,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z39,z7,z3,z4,z5]),(1,[z0,z1,z40,z3,z4,z5]),(0,[z0,z41,z1,z7,z3,z4,z5]),(0,[z0,z1,z42,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z43,z4,z5]),(0,[z0,z1,z7,z44,z3,z4,z5]),(0,[z0,z1,z7,z3,z36,z4,z23])],[(0,[z0,z1,z7,z45,z3,z4,z5]),(1,[z0,z1,z46,z7,z29,z3])],[(0,[z37,z1,z47,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z48,z5]),(0,[z49,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z50,z51,z5]),(0,[z0,z1,z7,z3,z4,z52,z53]),(0,[z54,z0,z7,z3,z4,z51,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z5,z55]),(0,[z0,z1,z7,z3,z4,z5,z56]),(0,[z0,z41,z57,z7,z3,z4,z5]),(0,[z54,z0,z58,z7,z3,z4,z5]),(1,[z59,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z60,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z61,z5])],[(0,[z0,z1,z7,z62,z3,z50,z5]),(1,[z32,z0,z1,z3,z34,z5]),(0,[z32,z0,z1,z7,z29,z3,z4]),(1,[z0,z1,z7,z29,z3,z23])],[(0,[z0,z1,z47,z7,z29,z3,z4]),(0,[z0,z37,z7,z3,z4,z5,z53]),(0,[z0,z1,z7,z3,z4,z63,z5]),(0,[z0,z1,z7,z3,z4,z5,z64])],[(0,[z65,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z3,z66,z4,z5]),(0,[z67,z1,z7,z3,z4,z5,z68]),(0,[z0,z1,z7,z69,z3,z4,z23]),(0,[z0,z1,z7,z3,z70,z4,z5]),(0,[z0,z1,z71,z7,z3,z4,z5]),(0,[z0,z72,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z73,z5,z23]),(0,[z0,z1,z7,z62,z3,z4,z74])],[(0,[z0,z1,z7,z3,z75,z4,z23])],[(0,[z0,z1,z14,z21,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z76]),(0,[z0,z1,z77,z7,z3,z4,z5])],[(0,[z78,z0,z1,z7,z3,z4,z23]),(0,[z79,z0,z1,z7,z3,z4,z5]),(0,[z0,z80,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z81,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z51]),(0,[z0,z1,z82,z7,z3,z4,z5]),(0,[z0,z1,z83,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z84,z3,z4,z5]),(0,[z0,z85,z1,z7,z3,z4,z5]),(0,[z0,z1,z86,z21,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z5,z23])],[(0,[z87,z0,z1,z7,z3,z4,z5]),(0,[z38,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z88,z5]),(0,[z0,z1,z7,z89,z3,z4,z5]),(0,[z0,z1,z7,z3,z90,z4,z5]),(0,[z91,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z92,z7,z3,z4,z5]),(0,[z93,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z94,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z23])],[(0,[z0,z1,z8,z95,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z34,z5]),(0,[z54,z0,z1,z7,z29,z3,z4]),(0,[z96,z0,z1,z7,z29,z3,z4])],[(0,[z0,z1,z14,z3,z4,z34,z5]),(0,[z0,z1,z7,z3,z73,z4,z97]),(0,[z0,z1,z7,z3,z4,z98,z5])],[(0,[z0,z1,z7,z3,z99,z4,z5]),(1,[z0,z1,z24,z3,z4,z5])],[(0,[z0,z1,z7,z100,z3,z73,z4]),(0,[z0,z1,z7,z3,z101,z4,z5])],[(0,[z1,z14,z7,z8,z3,z4,z5]),(0,[z0,z102,z1,z7,z3,z4,z5]),(0,[z0,z103,z58,z7,z3,z4,z5]),(0,[z0,z1,z7,z9,z21,z4,z5]),(0,[z0,z7,z3,z75,z4,z51,z5]),(0,[z0,z1,z7,z3,z104,z4,z5]),(0,[z0,z1,z7,z29,z62,z3,z4])],[(0,[z0,z1,z7,z3,z105,z4,z5]),(0,[z0,z1,z7,z106,z3,z4,z5]),(0,[z0,z1,z107,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z62,z3,z73,z5]),(0,[z0,z1,z7,z108,z3,z4,z5]),(0,[z0,z1,z109,z7,z29,z3,z4])],[(0,[z0,z1,z7,z3,z4,z110,z5]),(0,[z0,z1,z7,z3,z4,z111,z5])],[(0,[z0,z1,z7,z3,z112,z4,z5]),(0,[z32,z0,z1,z16,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z113,z5]),(0,[z0,z114,z1,z7,z3,z4,z23])],[(0,[z115,z0,z1,z7,z3,z4,z5])],[(0,[z0,z37,z1,z7,z3,z4,z23]),(0,[z116,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z117,z3,z4,z5]),(0,[z0,z1,z7,z118,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z119,z5])],[(0,[z0,z1,z8,z3,z4,z5,z120]),(0,[z121,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z122]),(0,[z0,z1,z123,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z124,z125,z5])],[(0,[z17,z37,z1,z7,z3,z4,z5]),(0,[z28,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z126,z3,z4,z5]),(0,[z0,z1,z7,z127,z3,z4,z5]),(0,[z128,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z129]),(0,[z0,z130,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z131,z3,z4,z23]),(1,[z0,z1,z132,z3,z4,z5])],[(1,[z0,z1,z7,z3,z50,z23]),(0,[z0,z1,z7,z3,z4,z133,z5]),(0,[z0,z1,z7,z3,z4,z4,z23])]],
   [[(0,[z78,z1,z47,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z134,z5]),(0,[z135,z0,z1,z24,z3,z4,z5]),(0,[z136,z1,z7,z3,z4,z52,z5]),(0,[z137,z0,z1,z7,z3,z4,z5]),(0,[z0,z103,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z138])],[(0,[z0,z1,z1,z7,z3,z4,z5]),(0,[z0,z1,z46,z8,z3,z4,z5]),(0,[z0,z1,z7,z139,z3,z4,z5]),(0,[z11,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z140,z7,z3,z4,z23])],[(0,[z0,z1,z141,z7,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z124,z5]),(0,[z142,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z143,z7,z3,z4,z5]),(0,[z0,z57,z1,z109,z3,z4,z5]),(0,[z0,z1,z7,z144,z3,z4,z5]),(0,[z0,z1,z145,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z146,z5])],[(0,[z0,z1,z7,z3,z147,z4,z5]),(0,[z32,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z124,z5]),(0,[z67,z136,z1,z7,z3,z4,z5]),(0,[z0,z148,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z149,z3,z75,z4]),(0,[z32,z0,z1,z7,z3,z4,z150])],[(0,[z0,z1,z151,z7,z3,z4,z5]),(0,[z0,z1,z14,z7,z3,z4,z5]),(0,[z152,z0,z1,z7,z3,z4,z5]),(0,[z136,z0,z1,z7,z29,z3,z4]),(0,[z153,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z154,z5]),(0,[z0,z27,z7,z3,z4,z98,z5]),(0,[z0,z1,z7,z20,z62,z4,z5]),(0,[z0,z1,z155,z7,z3,z4,z23])],[(0,[z0,z1,z7,z3,z4,z5,z156]),(0,[z67,z0,z1,z7,z157,z4,z5]),(0,[z158,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z159,z7,z3,z4,z5])],[(0,[z135,z0,z1,z7,z3,z73,z5]),(0,[z0,z160,z1,z7,z3,z4,z5]),(0,[z0,z1,z86,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z23,z161])],[(0,[z0,z1,z7,z3,z4,z162,z5]),(0,[z0,z1,z7,z163,z3,z4,z5]),(0,[z0,z1,z164,z7,z3,z4,z5])]],
   [[(0,[z165,z0,z1,z7,z3,z134,z5]),(0,[z0,z1,z7,z166,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z167,z5]),(1,[z0,z1,z155,z7,z131,z4])],[(0,[z0,z1,z7,z3,z73,z168,z5]),(0,[z0,z1,z7,z3,z4,z68,z23]),(0,[z0,z58,z7,z69,z3,z4,z5]),(0,[z169,z0,z1,z7,z3,z4,z5]),(0,[z170,z0,z1,z7,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z4,z171]),(0,[z0,z1,z7,z131,z4,z5,z22]),(0,[z0,z1,z7,z29,z131,z3,z4]),(0,[z0,z1,z7,z172,z3,z4,z5]),(0,[z0,z1,z173,z7,z29,z3,z4])],[(0,[z0,z1,z7,z3,z4,z174,z5]),(0,[z0,z1,z7,z3,z175,z4,z5]),(0,[z0,z1,z7,z176,z3,z4,z5]),(0,[z0,z1,z7,z177,z3,z4,z5])],[(0,[z0,z1,z7,z29,z3,z4,z52]),(0,[z0,z58,z7,z3,z75,z4,z5]),(0,[z0,z1,z7,z178,z3,z4,z5])],[(0,[z54,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z179,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z75,z4]),(0,[z0,z1,z7,z3,z4,z180,z5])],[(1,[z0,z1,z7,z3,z4,z5]),(0,[z78,z0,z1,z7,z3,z4,z110]),(0,[z0,z1,z14,z3,z4,z5,z68]),(0,[z0,z1,z46,z14,z3,z4,z5]),(0,[z0,z1,z7,z181,z3,z4,z5]),(0,[z0,z1,z7,z3,z51,z5,z23]),(0,[z0,z182,z1,z3,z4,z124,z5])],[(0,[z0,z1,z183,z8,z3,z4,z5]),(0,[z184,z0,z1,z7,z3,z4,z5]),(0,[z165,z0,z1,z7,z29,z3,z4]),(1,[z0,z1,z7,z126,z4,z5]),(0,[z0,z7,z69,z3,z185,z4,z5]),(1,[z0,z103,z7,z185,z4,z5]),(0,[z0,z1,z7,z3,z185,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z186]),(0,[z0,z1,z7,z3,z4,z168,z5])],[(0,[z0,z0,z1,z7,z3,z4,z5]),(0,[z187,z0,z1,z7,z3,z4,z5]),(0,[z188,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z189,z7,z3,z4,z5]),(0,[z190,z1,z7,z84,z3,z4,z5]),(0,[z0,z1,z7,z191,z3,z4,z5])]],
   [[(0,[z0,z192,z1,z8,z3,z4,z5]),(0,[z165,z0,z1,z106,z3,z4,z5]),(0,[z67,z0,z1,z40,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z53]),(0,[z0,z1,z7,z193,z3,z4,z5]),(0,[z0,z1,z7,z20,z3,z4,z23])],[(1,[z0,z1,z7,z3,z4,z194]),(0,[z0,z1,z14,z3,z195,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z196]),(0,[z0,z1,z7,z3,z4,z5,z197]),(0,[z198,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z46,z7,z3,z168,z5])],[(0,[z199,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z62,z3,z4,z5]),(0,[z0,z1,z7,z200,z3,z4,z5]),(0,[z0,z1,z7,z201,z3,z4,z5]),(0,[z0,z1,z7,z3,z202,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z68]),(0,[z203,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z204,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z205,z3,z4,z5]),(1,[z0,z1,z7,z176,z3,z4])],[(0,[z0,z1,z14,z62,z3,z4,z5]),(0,[z0,z1,z7,z3,z206,z4,z5])],[(0,[z190,z0,z1,z7,z66,z4,z5]),(0,[z0,z1,z7,z207,z3,z4,z5]),(0,[z0,z1,z7,z3,z36,z4,z5])],[(0,[z0,z1,z208,z8,z3,z4,z5]),(0,[z0,z1,z7,z209,z3,z4,z5]),(0,[z0,z1,z7,z3,z210,z4,z5]),(0,[z211,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z212,z5]),(0,[z0,z213,z1,z7,z3,z4,z23])],[(0,[z0,z1,z214,z14,z3,z4,z5]),(0,[z136,z0,z1,z163,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z215]),(0,[z0,z1,z7,z3,z4,z216,z5]),(1,[z0,z7,z177,z3,z4,z5])],[(0,[z0,z1,z7,z8,z3,z4,z23]),(0,[z165,z190,z1,z7,z3,z4,z5]),(0,[z1,z7,z84,z3,z66,z4,z5]),(0,[z49,z0,z1,z7,z3,z73,z5]),(0,[z0,z217,z1,z7,z3,z4,z5]),(0,[z0,z1,z218,z7,z3,z4,z5]),(0,[z0,z103,z1,z7,z185,z4,z5]),(0,[z0,z103,z1,z7,z4,z168,z5]),(0,[z0,z219,z1,z7,z3,z4,z5])]],
   [[(0,[z1,z7,z3,z73,z4,z50,z5]),(1,[z0,z1,z163,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z52,z23]),(1,[z11,z0,z69,z3,z4,z5]),(0,[z0,z1,z7,z220,z3,z4,z5]),(1,[z0,z1,z7,z3,z125,z5]),(0,[z0,z221,z1,z7,z3,z4,z5])],[(0,[z0,z1,z8,z222,z3,z4,z5]),(0,[z0,z1,z155,z7,z66,z4,z5]),(0,[z135,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z223,z4,z5]),(0,[z0,z1,z7,z20,z224,z4,z5]),(0,[z0,z1,z7,z225,z4,z5,z22])],[(0,[z0,z1,z7,z3,z4,z226,z5]),(0,[z0,z103,z1,z14,z3,z4,z5]),(0,[z0,z1,z14,z222,z3,z4,z5]),(0,[z0,z1,z7,z3,z227,z4,z5]),(0,[z0,z228,z1,z7,z3,z4,z5]),(0,[z0,z1,z229,z7,z3,z4,z5]),(0,[z0,z1,z7,z75,z4,z146,z5]),(1,[z0,z1,z7,z20,z62,z5])],[(0,[z0,z1,z7,z3,z4,z68,z53]),(0,[z230,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z231,z4,z5]),(0,[z0,z1,z7,z3,z232,z4,z5])],[(0,[z0,z233,z1,z7,z3,z4,z5]),(0,[z234,z0,z1,z7,z3,z4,z5]),(0,[z235,z0,z1,z7,z3,z4,z5])],[(0,[z165,z0,z1,z7,z3,z4,z174]),(0,[z0,z1,z40,z7,z3,z4,z5]),(0,[z0,z1,z7,z236,z3,z4,z5]),(1,[z54,z0,z7,z3,z51,z5]),(0,[z0,z1,z7,z237,z3,z4,z5]),(0,[z0,z238,z1,z7,z3,z4,z5])],[(0,[z78,z0,z1,z7,z3,z4,z5]),(0,[z17,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z8,z239,z3,z4,z5]),(0,[z0,z1,z240,z7,z3,z4,z5]),(1,[z0,z241,z7,z3,z4,z5]),(0,[z32,z242,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z243,z4,z5]),(0,[z0,z1,z8,z3,z4,z50,z5]),(0,[z244,z0,z1,z7,z3,z70,z5]),(0,[z0,z1,z7,z20,z3,z168,z5])]],
   [[(0,[z0,z245,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z246,z5]),(0,[z244,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z7,z247,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z5]),(0,[z0,z1,z7,z3,z4,z248,z5])],[(0,[z0,z1,z7,z3,z249,z4,z5]),(1,[z49,z1,z8,z3,z4,z5]),(0,[z0,z250,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z251,z3,z4,z5]),(0,[z0,z1,z252,z7,z3,z4,z5]),(0,[z0,z1,z7,z253,z3,z4,z5]),(0,[z0,z254,z1,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z124,z5,z186]),(1,[z0,z1,z7,z3,z255,z5])],[(0,[z78,z0,z1,z7,z3,z4,z194]),(0,[z0,z57,z1,z8,z3,z4,z5]),(1,[z0,z1,z256,z3,z4,z5]),(0,[z0,z1,z46,z7,z3,z75,z5]),(0,[z0,z182,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z222,z4,z168,z5]),(0,[z0,z1,z7,z3,z4,z257,z5])],[(0,[z0,z1,z7,z3,z4,z258,z5]),(0,[z49,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z259]),(0,[z0,z1,z7,z3,z260,z4,z5]),(0,[z0,z1,z7,z3,z224,z4,z23]),(0,[z0,z1,z7,z261,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z194]),(0,[z262,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z263,z4,z5]),(0,[z0,z1,z264,z7,z3,z4,z5]),(0,[z265,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z9,z3,z4,z23]),(0,[z0,z1,z7,z266,z3,z4,z5]),(0,[z0,z1,z7,z267,z3,z4,z5])],[(0,[z165,z0,z268,z7,z3,z4,z5]),(0,[z0,z269,z1,z7,z3,z4,z5])],[(0,[z0,z270,z1,z7,z3,z4,z5])],[(0,[z0,z1,z8,z3,z271,z4,z5]),(0,[z32,z0,z272,z7,z3,z4,z5])]],
   [[(1,[z0,z1,z8,z3,z4,z23]),(0,[z0,z1,z273,z7,z3,z4,z5]),(0,[z49,z0,z1,z274,z3,z4,z5]),(0,[z0,z1,z7,z3,z12,z4,z5]),(0,[z0,z1,z7,z3,z4,z275,z5]),(0,[z0,z1,z7,z276,z3,z4,z5]),(0,[z277,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z278,z7,z3,z4,z5])],[(1,[z78,z47,z7,z3,z4,z5]),(0,[z38,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z5,z279]),(0,[z0,z114,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z280,z4,z5]),(1,[z0,z1,z16,z7,z3,z23])],[(0,[z0,z1,z7,z3,z281,z4,z5]),(0,[z0,z1,z7,z3,z4,z282,z5]),(1,[z0,z41,z7,z9,z4,z5]),(0,[z0,z1,z7,z3,z4,z283,z5]),(0,[z0,z1,z7,z284,z3,z4,z5])],[(0,[z0,z37,z1,z7,z3,z4,z5]),(0,[z28,z1,z7,z3,z4,z50,z5])],[(0,[z244,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z66,z4]),(0,[z0,z1,z7,z247,z3,z4,z5]),(0,[z0,z103,z1,z285,z3,z4,z5]),(0,[z0,z103,z1,z7,z9,z4,z5]),(0,[z0,z58,z1,z7,z29,z3,z4])],[(1,[z0,z1,z7,z3,z286,z5]),(0,[z0,z1,z7,z3,z73,z51,z5]),(0,[z0,z1,z7,z9,z224,z4,z5]),(0,[z0,z1,z7,z3,z75,z4,z287]),(0,[z0,z1,z288,z7,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z5,z23]),(0,[z0,z1,z16,z7,z3,z289,z5]),(0,[z0,z1,z7,z131,z3,z4,z5]),(0,[z87,z0,z1,z7,z29,z3,z4])],[(0,[z0,z1,z7,z290,z3,z4,z5]),(0,[z0,z57,z1,z14,z3,z4,z5]),(0,[z190,z0,z1,z7,z3,z4,z5]),(0,[z135,z0,z1,z256,z3,z4,z5]),(0,[z0,z1,z7,z291,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z292,z5]),(0,[z0,z1,z7,z225,z3,z4,z22]),(0,[z0,z1,z293,z7,z3,z4,z5]),(0,[z294,z0,z1,z7,z3,z4,z23])],[(0,[z28,z49,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z66,z4,z23])]],
   [[(0,[z78,z0,z1,z7,z3,z295,z5]),(0,[z0,z1,z7,z296,z3,z4,z5]),(0,[z0,z297,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z21,z3,z4,z5]),(0,[z0,z1,z7,z298,z3,z4,z5]),(0,[z11,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z86,z109,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z299,z5]),(0,[z0,z1,z7,z3,z4,z5,z300]),(0,[z0,z1,z140,z7,z3,z4,z5]),(0,[z0,z1,z7,z301,z3,z4,z5]),(0,[z0,z302,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z303,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z287]),(1,[z0,z1,z7,z3,z4,z74]),(0,[z304,z0,z1,z7,z3,z4,z23])],[(0,[z0,z1,z305,z7,z3,z4,z5]),(0,[z0,z7,z69,z3,z4,z51,z5]),(0,[z0,z1,z7,z3,z4,z51,z5]),(0,[z0,z1,z306,z7,z3,z4,z5]),(0,[z0,z1,z7,z307,z3,z4,z5])],[(0,[z0,z1,z7,z308,z3,z4,z5]),(1,[z0,z1,z7,z3,z309,z5]),(0,[z11,z0,z57,z7,z3,z4,z5]),(0,[z310,z0,z1,z7,z3,z4,z5]),(0,[z244,z0,z1,z7,z3,z4,z53]),(0,[z0,z1,z7,z62,z3,z311,z4]),(1,[z0,z1,z7,z62,z3,z23]),(0,[z0,z1,z155,z7,z3,z4,z5])],[(0,[z78,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z14,z3,z4,z23]),(0,[z0,z1,z7,z312,z3,z4,z5])],[(0,[z28,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z313,z3,z4,z5]),(0,[z0,z1,z46,z7,z3,z51,z5])],[(0,[z28,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z314,z5]),(0,[z0,z1,z7,z315,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z316,z5]),(0,[z0,z1,z7,z317,z3,z4,z5]),(0,[z318,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z176,z222,z3,z4])],[(0,[z0,z1,z7,z29,z3,z185,z4]),(0,[z0,z1,z7,z3,z4,z319,z5]),(0,[z0,z1,z7,z320,z3,z4,z5])]],
   [[(0,[z17,z0,z1,z14,z3,z4,z5]),(0,[z0,z37,z7,z3,z185,z4,z5]),(0,[z67,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z52,z22]),(0,[z0,z1,z7,z3,z4,z321,z5]),(0,[z0,z1,z7,z322,z3,z4,z5])],[(0,[z0,z57,z1,z69,z3,z4,z5]),(0,[z0,z1,z7,z21,z185,z4,z5]),(0,[z0,z1,z7,z21,z4,z168,z5]),(0,[z0,z1,z7,z222,z3,z4,z323])],[(0,[z324,z0,z1,z7,z3,z4,z5]),(0,[z325,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z84,z3,z4,z5]),(0,[z0,z58,z1,z8,z3,z4,z5]),(0,[z32,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z326,z3,z4,z5]),(0,[z135,z0,z1,z7,z3,z50,z5]),(0,[z0,z1,z7,z327,z3,z4,z5]),(1,[z67,z1,z7,z3,z4,z68]),(1,[z0,z57,z109,z3,z4,z5]),(0,[z328,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z329,z4,z5])],[(0,[z0,z1,z47,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z23]),(0,[z0,z1,z14,z84,z3,z4,z5]),(0,[z0,z1,z39,z14,z3,z4,z5]),(0,[z0,z1,z7,z330,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z331]),(0,[z0,z1,z7,z332,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z333,z5]),(0,[z0,z1,z14,z3,z4,z5,z23]),(1,[z0,z1,z7,z291,z4,z5]),(0,[z0,z1,z7,z334,z3,z4,z5]),(0,[z335,z0,z1,z7,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z98]),(0,[z0,z1,z336,z7,z3,z4,z5]),(0,[z0,z1,z7,z337,z3,z4,z5])],[(0,[z0,z338,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z98,z5]),(0,[z0,z1,z7,z3,z4,z339,z5]),(0,[z0,z1,z7,z3,z73,z4,z23]),(0,[z340,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z341,z3,z4,z5]),(0,[z0,z1,z7,z225,z3,z4,z5]),(0,[z0,z1,z7,z3,z342,z4,z5])],[(0,[z78,z0,z1,z7,z3,z286,z5]),(0,[z0,z1,z14,z3,z4,z98,z5]),(0,[z59,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z289,z4,z5])],[(0,[z0,z1,z343,z7,z3,z4,z5]),(0,[z344,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z345,z7,z3,z4,z5]),(0,[z0,z182,z1,z7,z3,z4,z186]),(0,[z0,z1,z7,z20,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z295,z5]),(0,[z0,z1,z7,z346,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z347]),(1,[z135,z1,z7,z3,z50,z5]),(0,[z0,z1,z7,z3,z4,z348,z5]),(0,[z0,z1,z349,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z350,z5]),(0,[z165,z0,z1,z7,z84,z4,z5]),(0,[z165,z0,z1,z7,z3,z10,z5]),(1,[z0,z1,z7,z81,z4,z5]),(0,[z0,z41,z7,z69,z3,z4,z5]),(0,[z0,z351,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z23])],[(0,[z0,z1,z352,z7,z3,z4,z5]),(0,[z38,z28,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z3,z105,z4,z5]),(0,[z0,z1,z7,z353,z3,z4,z5]),(0,[z0,z1,z354,z7,z3,z4,z5]),(0,[z0,z58,z7,z9,z3,z4,z5]),(0,[z0,z1,z86,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z355])],[(0,[z54,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z84,z185,z4,z5]),(0,[z356,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z357,z7,z3,z4,z5]),(0,[z0,z182,z1,z183,z3,z4,z5]),(0,[z358,z0,z1,z7,z3,z4,z5]),(1,[z0,z359,z7,z3,z4,z5])],[(0,[z49,z1,z7,z3,z73,z4,z5]),(1,[z0,z360,z7,z3,z4,z5]),(0,[z0,z361,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z362,z3,z4,z5]),(1,[z0,z272,z7,z3,z4,z5]),(1,[z0,z1,z7,z33,z4,z5])],[(0,[z363,z0,z1,z7,z3,z4,z5]),(0,[z364,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z365]),(0,[z0,z1,z46,z7,z3,z4,z23])],[(0,[z0,z1,z7,z8,z3,z4,z5]),(0,[z0,z58,z1,z14,z3,z4,z5]),(0,[z366,z0,z1,z7,z3,z4,z5]),(0,[z136,z0,z1,z25,z3,z4,z5]),(0,[z0,z182,z1,z7,z3,z4,z124]),(0,[z0,z1,z7,z3,z4,z124,z23]),(0,[z0,z1,z7,z3,z4,z23,z367])],[(0,[z0,z1,z47,z14,z3,z4,z5]),(0,[z0,z1,z7,z368,z3,z4,z5]),(0,[z87,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z52,z5]),(0,[z0,z1,z7,z3,z4,z369,z5]),(0,[z0,z1,z7,z3,z4,z370,z5]),(0,[z0,z1,z7,z371,z3,z4,z5])]],
   [[(0,[z78,z17,z1,z7,z3,z4,z5]),(0,[z372,z0,z1,z7,z3,z4,z5]),(0,[z135,z0,z1,z7,z291,z4,z5]),(1,[z0,z1,z7,z100,z3,z4]),(1,[z0,z1,z25,z3,z4,z5]),(0,[z373,z0,z1,z7,z3,z4,z5]),(0,[z374,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z62,z3,z5,z23])],[(1,[z38,z1,z8,z3,z4,z5]),(0,[z0,z1,z109,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z161]),(1,[z0,z1,z7,z3,z75,z23]),(0,[z375,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z320,z225,z3,z5]),(0,[z0,z1,z7,z376,z3,z4,z5]),(1,[z0,z1,z7,z29,z3,z4])],[(0,[z0,z1,z377,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z378,z4,z5]),(0,[z0,z103,z1,z218,z3,z4,z5]),(0,[z244,z0,z27,z7,z3,z4,z5]),(0,[z379,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z380,z4,z5]),(1,[z0,z1,z106,z3,z4,z5]),(0,[z49,z0,z1,z7,z3,z50,z5]),(0,[z67,z0,z1,z7,z247,z4,z5]),(0,[z328,z0,z241,z7,z3,z4,z5]),(0,[z0,z381,z1,z7,z3,z4,z5]),(0,[z0,z382,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z191,z29,z3,z4])],[(0,[z135,z0,z1,z7,z3,z4,z347]),(0,[z0,z1,z7,z3,z75,z73,z5]),(1,[z0,z1,z330,z3,z4,z5]),(0,[z383,z0,z1,z7,z3,z4,z5]),(0,[z384,z0,z1,z7,z3,z4,z23])],[(0,[z0,z1,z385,z7,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z53]),(1,[z28,z1,z14,z3,z4,z5]),(0,[z135,z0,z1,z7,z81,z4,z5]),(0,[z0,z1,z386,z7,z3,z4,z5]),(0,[z0,z103,z1,z7,z20,z4,z5]),(0,[z0,z41,z1,z7,z9,z4,z5])],[(0,[z0,z1,z8,z3,z387,z4,z5]),(0,[z0,z1,z14,z3,z4,z5,z53]),(1,[z0,z1,z274,z3,z4,z5]),(0,[z0,z1,z7,z3,z388,z4,z5]),(0,[z0,z27,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z389,z5]),(0,[z0,z1,z390,z7,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z5,z68]),(1,[z0,z1,z7,z3,z391,z5]),(0,[z392,z0,z1,z7,z3,z4,z5]),(0,[z32,z0,z269,z7,z3,z4,z5]),(0,[z393,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z394,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z395,z5]),(0,[z0,z1,z7,z3,z4,z5,z396]),(0,[z0,z57,z109,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z397,z5]),(0,[z0,z1,z398,z7,z3,z4,z5]),(0,[z0,z1,z399,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z400,z4,z5])],[(0,[z0,z47,z7,z3,z4,z5,z53]),(0,[z0,z103,z1,z8,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z97]),(0,[z401,z0,z1,z7,z3,z4,z5]),(0,[z0,z109,z7,z69,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z402,z5]),(0,[z0,z182,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z225,z3,z255,z5])],[(0,[z403,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z162,z5]),(0,[z0,z103,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z224,z4,z5]),(0,[z0,z1,z183,z7,z3,z4,z23]),(0,[z404,z0,z1,z7,z3,z4,z5]),(0,[z0,z405,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z406,z4,z5]),(0,[z0,z1,z407,z7,z3,z4,z5]),(0,[z0,z1,z7,z408,z3,z4,z5]),(0,[z0,z1,z7,z409,z3,z4,z23])],[(1,[z0,z1,z7,z4,z146,z5]),(0,[z0,z1,z7,z3,z4,z5,z22]),(0,[z410,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z220,z29,z3,z4])],[(0,[z136,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z109,z14,z3,z4,z5]),(0,[z135,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z274,z7,z3,z4,z5]),(0,[z0,z1,z109,z3,z224,z4,z5]),(0,[z0,z1,z241,z7,z3,z4,z5]),(0,[z0,z1,z7,z411,z3,z4,z5])],[(0,[z412,z0,z1,z7,z3,z4,z5]),(0,[z413,z0,z1,z7,z3,z4,z5])],[(0,[z414,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z415,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z416]),(0,[z0,z1,z7,z3,z4,z5,z417])]],
   [[(0,[z38,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z8,z3,z185,z4,z5]),(0,[z0,z1,z8,z3,z4,z168,z5]),(0,[z0,z1,z8,z3,z4,z5,z186]),(0,[z0,z1,z7,z3,z4,z418,z5]),(1,[z0,z1,z7,z3,z4,z174]),(0,[z0,z1,z419,z7,z3,z4,z5]),(0,[z0,z1,z7,z420,z3,z4,z5])],[(0,[z17,z0,z1,z296,z3,z4,z5]),(0,[z0,z1,z189,z8,z3,z4,z5]),(0,[z0,z1,z14,z3,z185,z4,z5]),(0,[z0,z1,z14,z3,z4,z168,z5]),(0,[z0,z421,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z5,z186]),(0,[z422,z0,z1,z7,z3,z4,z5]),(0,[z0,z238,z1,z7,z29,z3,z4])],[(0,[z78,z0,z1,z7,z29,z3,z4]),(0,[z190,z0,z1,z7,z84,z4,z5])],[(0,[z0,z1,z423,z7,z3,z4,z5]),(0,[z0,z58,z1,z7,z3,z75,z5]),(0,[z0,z1,z16,z7,z3,z34,z5]),(0,[z0,z1,z7,z3,z4,z424,z5]),(0,[z0,z1,z7,z3,z4,z5,z425])],[(0,[z0,z47,z7,z3,z185,z4,z5]),(0,[z0,z37,z7,z3,z4,z51,z5]),(0,[z0,z1,z14,z3,z4,z5,z196]),(0,[z0,z1,z86,z14,z3,z4,z5]),(1,[z0,z1,z166,z3,z4,z5]),(0,[z0,z426,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z427,z4,z5]),(1,[z0,z1,z7,z3,z51,z23]),(0,[z0,z1,z7,z224,z4,z168,z5])],[(0,[z0,z268,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z428,z5]),(0,[z0,z1,z7,z69,z3,z4,z5]),(0,[z0,z1,z7,z3,z429,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z34]),(0,[z0,z1,z7,z222,z3,z4,z23])],[(0,[z0,z1,z7,z3,z4,z5,z430]),(0,[z0,z1,z7,z3,z66,z4,z5]),(0,[z67,z0,z1,z7,z3,z309,z5]),(0,[z0,z1,z7,z3,z431,z4,z5]),(0,[z0,z1,z432,z7,z3,z4,z5]),(0,[z0,z1,z7,z266,z3,z289,z4]),(0,[z0,z1,z7,z29,z3,z4,z186]),(0,[z0,z1,z7,z62,z4,z168,z5]),(0,[z0,z359,z7,z62,z3,z4,z5])],[(0,[z165,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z155,z7,z84,z4,z5]),(0,[z0,z1,z7,z433,z3,z4,z5]),(0,[z0,z1,z7,z3,z75,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z5,z434]),(1,[z0,z268,z7,z3,z4,z5]),(0,[z0,z1,z7,z435,z3,z4,z5]),(0,[z304,z0,z1,z7,z3,z4,z5]),(0,[z0,z436,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z437]),(0,[z0,z1,z16,z7,z29,z3,z4]),(1,[z0,z1,z278,z7,z3,z5]),(0,[z0,z1,z7,z438,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z425,z23])],[(0,[z49,z1,z7,z8,z3,z4,z5]),(0,[z136,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z439]),(0,[z0,z1,z7,z3,z4,z440,z5]),(0,[z0,z1,z7,z441,z3,z4,z5]),(0,[z442,z0,z1,z7,z3,z4,z5])],[(0,[z0,z443,z1,z7,z3,z4,z5]),(0,[z0,z1,z444,z7,z3,z4,z5]),(0,[z0,z1,z7,z445,z3,z4,z5])],[(1,[z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z446]),(1,[z0,z447,z7,z3,z4,z5]),(0,[z135,z0,z1,z7,z3,z4,z416]),(0,[z0,z1,z7,z3,z4,z50,z23]),(0,[z136,z0,z1,z7,z3,z4,z52]),(1,[z0,z1,z7,z3,z4,z150]),(1,[z0,z1,z16,z3,z289,z5])],[(0,[z165,z1,z7,z3,z66,z4,z5]),(0,[z0,z448,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z285,z3,z4,z5]),(0,[z0,z1,z7,z185,z224,z4,z5]),(0,[z0,z41,z1,z7,z29,z3,z4]),(0,[z54,z0,z1,z7,z3,z75,z5]),(0,[z244,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z449,z3,z4,z5])],[(0,[z0,z1,z7,z3,z450,z4,z5]),(0,[z0,z1,z7,z95,z3,z4,z5]),(0,[z0,z0,z1,z14,z3,z4,z5]),(0,[z328,z0,z1,z86,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z124])],[(0,[z0,z1,z7,z451,z3,z4,z5]),(0,[z0,z57,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z452,z5]),(0,[z0,z1,z16,z3,z289,z4,z5])],[(0,[z0,z37,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z453,z5]),(0,[z0,z1,z86,z69,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z454,z5]),(0,[z0,z1,z7,z149,z3,z4,z5]),(0,[z455,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z155,z7,z3,z4,z22])]],
   [[(0,[z199,z0,z1,z14,z3,z4,z5]),(0,[z0,z27,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z20,z66,z4,z5]),(0,[z0,z456,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z286,z4,z5]),(0,[z457,z0,z1,z7,z3,z4,z5]),(0,[z0,z458,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z171]),(0,[z32,z0,z1,z3,z4,z124,z5]),(0,[z0,z1,z7,z3,z4,z5,z459]),(0,[z460,z0,z1,z7,z3,z4,z5])],[(0,[z190,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z416]),(0,[z136,z0,z1,z7,z3,z4,z68]),(0,[z0,z1,z7,z461,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z462,z5]),(0,[z165,z0,z1,z14,z3,z4,z5]),(0,[z463,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z464,z4,z5]),(1,[z0,z1,z7,z465,z4,z5]),(1,[z0,z466,z7,z3,z4,z5])],[(0,[z0,z1,z14,z251,z3,z4,z5]),(0,[z0,z1,z7,z3,z73,z4,z5]),(0,[z0,z1,z7,z3,z4,z68,z22]),(0,[z0,z1,z7,z3,z4,z5,z467]),(0,[z11,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z222,z3,z168,z5])],[(0,[z468,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z469,z4,z5]),(0,[z0,z1,z7,z3,z4,z470,z5])],[(0,[z0,z1,z7,z3,z4,z471,z5]),(0,[z0,z1,z16,z8,z3,z4,z5]),(1,[z0,z444,z7,z3,z4,z5]),(0,[z0,z58,z1,z7,z3,z51,z5]),(0,[z472,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z306,z7,z29,z3,z4])],[(0,[z17,z0,z1,z8,z3,z4,z5]),(0,[z135,z0,z1,z14,z3,z4,z5]),(0,[z135,z0,z447,z7,z3,z4,z5]),(1,[z0,z473,z7,z3,z4,z5]),(0,[z67,z0,z360,z7,z3,z4,z5]),(0,[z474,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z183,z7,z3,z4,z186]),(0,[z0,z1,z278,z7,z3,z124,z5]),(0,[z0,z1,z155,z7,z29,z3,z4])]],
   [[(0,[z0,z1,z475,z7,z3,z4,z5]),(0,[z0,z1,z7,z476,z3,z4,z5]),(1,[z0,z1,z433,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z477,z5]),(0,[z0,z1,z7,z3,z4,z5,z478]),(0,[z0,z1,z7,z3,z4,z479,z5]),(0,[z0,z1,z7,z131,z225,z3,z4]),(0,[z0,z1,z7,z29,z3,z4,z5])],[(0,[z480,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z4,z5]),(0,[z0,z481,z1,z7,z3,z4,z5]),(0,[z0,z1,z482,z7,z3,z4,z5])],[(0,[z0,z41,z1,z8,z3,z4,z5]),(0,[z234,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z309,z4,z5]),(0,[z483,z0,z1,z7,z3,z4,z5]),(0,[z484,z0,z1,z7,z3,z4,z5]),(0,[z485,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z155,z7,z225,z4,z5])],[(1,[z0,z1,z7,z249,z4,z5]),(0,[z486,z0,z1,z7,z3,z4,z5]),(1,[z136,z1,z7,z3,z4,z52]),(0,[z0,z1,z7,z487,z3,z4,z5])],[(0,[z78,z0,z1,z14,z3,z4,z5]),(0,[z49,z0,z1,z8,z3,z4,z5]),(0,[z67,z0,z1,z7,z29,z3,z4]),(0,[z11,z0,z1,z7,z126,z4,z5]),(0,[z0,z1,z7,z21,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z186,z23]),(0,[z0,z1,z46,z7,z3,z4,z5])],[(0,[z488,z0,z1,z14,z3,z4,z5]),(1,[z0,z1,z285,z3,z4,z5]),(0,[z0,z1,z7,z3,z489,z4,z5]),(0,[z0,z1,z7,z3,z4,z124,z5])],[(0,[z0,z1,z7,z3,z490,z4,z5]),(0,[z54,z0,z1,z7,z3,z4,z259]),(0,[z0,z1,z7,z3,z4,z491,z5]),(0,[z328,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z150]),(0,[z0,z1,z7,z492,z3,z4,z5]),(0,[z0,z1,z7,z3,z289,z4,z365]),(0,[z0,z1,z183,z7,z3,z4,z124]),(0,[z0,z1,z132,z7,z3,z4,z23])],[(0,[z0,z1,z8,z131,z3,z4,z5]),(0,[z67,z0,z1,z330,z3,z4,z5]),(0,[z54,z0,z1,z7,z3,z51,z5]),(1,[z0,z1,z7,z3,z4,z323])]],
   [[(0,[z0,z1,z7,z493,z3,z4,z5]),(0,[z0,z1,z14,z131,z3,z4,z5]),(0,[z0,z1,z7,z3,z3,z4,z5]),(0,[z494,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z495]),(0,[z0,z496,z1,z7,z3,z4,z5]),(0,[z497,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z311,z4]),(0,[z0,z1,z7,z498,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z23,z499])],[(0,[z500,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z501,z3,z4,z5]),(0,[z0,z1,z7,z502,z3,z4,z5]),(0,[z0,z503,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z34,z23]),(0,[z0,z1,z7,z504,z3,z4,z5])],[(0,[z0,z1,z7,z66,z185,z4,z5]),(0,[z0,z1,z7,z66,z4,z168,z5]),(0,[z67,z0,z1,z7,z3,z391,z5]),(0,[z0,z41,z7,z9,z3,z4,z5])],[(0,[z0,z1,z14,z298,z3,z4,z5]),(0,[z135,z0,z473,z7,z3,z4,z5]),(0,[z0,z41,z1,z7,z185,z4,z5]),(0,[z0,z41,z1,z7,z4,z168,z5]),(0,[z0,z1,z272,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z168,z23]),(0,[z384,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z51,z5]),(1,[z0,z1,z7,z3,z10,z5]),(0,[z0,z1,z7,z9,z66,z4,z5]),(0,[z0,z1,z7,z3,z4,z125,z5])],[(0,[z0,z1,z14,z3,z4,z51,z5]),(0,[z0,z1,z214,z7,z3,z4,z5]),(0,[z505,z0,z1,z7,z3,z4,z5]),(0,[z190,z0,z1,z166,z3,z4,z5]),(0,[z0,z506,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z507,z4,z5]),(0,[z0,z1,z7,z508,z3,z4,z23]),(0,[z0,z509,z1,z7,z3,z4,z5])],[(0,[z87,z0,z1,z8,z3,z4,z5]),(0,[z0,z41,z1,z14,z3,z4,z5]),(0,[z165,z0,z510,z7,z3,z4,z5]),(0,[z0,z1,z7,z84,z3,z4,z23]),(0,[z0,z1,z7,z511,z3,z4,z5]),(0,[z0,z58,z1,z7,z3,z4,z23]),(1,[z242,z1,z7,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z512,z3,z4,z5])],[(0,[z0,z1,z47,z7,z3,z4,z23]),(0,[z0,z1,z7,z513,z3,z4,z5])]],
   [[(0,[z0,z47,z7,z3,z4,z51,z5]),(0,[z0,z1,z7,z3,z4,z514,z5]),(0,[z49,z0,z1,z14,z3,z4,z5]),(1,[z0,z1,z18,z3,z4,z5]),(0,[z0,z1,z7,z3,z75,z50,z5]),(0,[z0,z242,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z225,z4,z22])],[(0,[z0,z37,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z515,z3,z4,z5]),(1,[z32,z0,z1,z7,z3,z23]),(0,[z0,z1,z183,z7,z3,z4,z5])],[(0,[z67,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z8,z29,z3,z4]),(0,[z0,z1,z516,z7,z3,z4,z5])],[(0,[z0,z192,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z7,z29,z3,z4]),(0,[z517,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z518]),(0,[z519,z0,z1,z7,z3,z4,z5]),(0,[z0,z520,z1,z7,z3,z4,z5]),(0,[z521,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z522,z5]),(1,[z0,z1,z296,z3,z4,z5]),(0,[z190,z0,z1,z14,z3,z4,z5]),(0,[z0,z523,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z524,z4,z5])],[(0,[z0,z1,z7,z3,z4,z255,z5])],[(0,[z0,z1,z8,z3,z4,z333,z5]),(0,[z0,z1,z7,z84,z4,z168,z5]),(0,[z0,z1,z7,z3,z4,z5,z525]),(0,[z0,z526,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z168,z5,z23])],[(0,[z0,z1,z527,z8,z3,z4,z5]),(0,[z0,z1,z8,z225,z3,z4,z5]),(0,[z54,z0,z1,z7,z3,z4,z23]),(0,[z528,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z3,z289,z4,z34,z5]),(0,[z0,z213,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z74]),(0,[z0,z1,z529,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z8,z3,z289,z4,z5]),(0,[z0,z1,z14,z225,z3,z4,z5]),(0,[z165,z0,z1,z18,z3,z4,z5]),(0,[z0,z1,z530,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z157,z4,z5]),(0,[z32,z59,z1,z7,z3,z4,z5]),(0,[z531,z0,z1,z7,z3,z4,z5])],[(0,[z116,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z155,z14,z3,z4,z5]),(0,[z0,z1,z14,z3,z289,z4,z5]),(0,[z0,z532,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z347,z5]),(0,[z0,z1,z7,z3,z4,z5,z533]),(0,[z0,z1,z7,z3,z4,z5,z367]),(0,[z0,z534,z1,z7,z3,z4,z5])],[(0,[z0,z1,z535,z7,z3,z4,z5]),(0,[z121,z0,z1,z8,z3,z4,z5]),(1,[z165,z1,z7,z66,z4,z5]),(0,[z1,z7,z3,z4,z52,z5,z68]),(0,[z0,z1,z7,z3,z4,z5,z323])],[(0,[z0,z1,z536,z7,z3,z4,z5]),(0,[z0,z1,z7,z537,z3,z4,z5])],[(0,[z11,z0,z7,z69,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z538,z5]),(1,[z0,z1,z132,z3,z4,z23])],[(0,[z49,z0,z1,z433,z3,z4,z5]),(0,[z0,z1,z109,z7,z3,z4,z23]),(0,[z0,z182,z1,z7,z29,z3,z4])],[(0,[z539,z0,z1,z7,z3,z4,z5]),(0,[z0,z540,z1,z7,z3,z4,z5]),(0,[z67,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z73,z4]),(0,[z0,z1,z7,z3,z4,z98,z52]),(0,[z0,z103,z7,z3,z185,z4,z5]),(0,[z0,z1,z7,z3,z541,z4,z5]),(0,[z0,z1,z7,z3,z4,z23,z542]),(0,[z0,z1,z543,z7,z3,z4,z5])],[(0,[z17,z0,z47,z7,z3,z4,z5]),(1,[z1,z14,z8,z3,z4,z5]),(0,[z244,z0,z1,z7,z3,z283,z5]),(0,[z32,z0,z1,z46,z7,z3,z5])]],
   [[(0,[z17,z0,z37,z7,z3,z4,z5]),(0,[z0,z1,z8,z8,z3,z4,z5]),(0,[z328,z0,z1,z14,z3,z4,z5]),(0,[z67,z0,z1,z7,z3,z4,z52]),(0,[z328,z0,z1,z3,z224,z4,z5])],[(0,[z544,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z52,z5]),(0,[z152,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z50]),(0,[z0,z1,z7,z3,z545,z4,z5]),(0,[z54,z0,z1,z7,z3,z4,z546]),(0,[z0,z7,z62,z177,z3,z4,z5])],[(0,[z547,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z52,z5]),(0,[z0,z1,z7,z3,z4,z50,z5]),(0,[z0,z1,z7,z548,z3,z4,z5]),(0,[z0,z549,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z550,z3,z4,z5])],[(0,[z0,z1,z86,z8,z3,z4,z5]),(0,[z0,z41,z103,z7,z3,z4,z5]),(1,[z0,z1,z218,z3,z4,z5]),(0,[z244,z0,z1,z7,z3,z4,z5]),(0,[z551,z0,z1,z7,z3,z4,z5])],[(0,[z38,z0,z1,z7,z29,z3,z4]),(0,[z0,z250,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z16,z3,z4,z5]),(0,[z0,z1,z7,z100,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z552]),(0,[z0,z7,z3,z4,z98,z5,z53]),(0,[z553,z0,z1,z7,z3,z4,z5])],[(0,[z554,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z98,z68]),(0,[z0,z57,z1,z7,z3,z4,z5]),(0,[z555,z0,z1,z7,z3,z4,z5]),(0,[z244,z0,z7,z3,z4,z5,z53]),(0,[z0,z1,z556,z7,z3,z4,z5])],[(0,[z0,z1,z7,z557,z3,z4,z5]),(0,[z0,z1,z7,z9,z3,z4,z5]),(0,[z0,z558,z1,z7,z3,z4,z5])],[(0,[z559,z0,z1,z7,z3,z4,z5]),(0,[z67,z0,z1,z7,z3,z4,z68]),(1,[z244,z0,z7,z3,z4,z53]),(0,[z0,z1,z3,z289,z4,z124,z5]),(0,[z0,z359,z1,z7,z3,z4,z5])]],
   [[(0,[z328,z0,z466,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z560,z5])],[(0,[z561,z0,z1,z7,z3,z4,z5]),(0,[z562,z0,z1,z7,z3,z4,z5]),(0,[z67,z0,z444,z7,z3,z4,z5]),(0,[z136,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z69,z29,z3,z4]),(1,[z0,z1,z7,z3,z70,z5]),(0,[z0,z1,z7,z62,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z563,z23])],[(1,[z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z447,z7,z3,z4,z5]),(0,[z0,z1,z564,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z98]),(0,[z328,z0,z1,z7,z21,z4,z5])],[(0,[z0,z565,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z365]),(1,[z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z566,z3,z4,z5])],[(0,[z0,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z224,z4,z5]),(0,[z135,z1,z7,z3,z4,z50,z5]),(0,[z0,z1,z567,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z568,z4,z5]),(0,[z0,z1,z7,z3,z4,z569,z5]),(0,[z32,z0,z1,z3,z4,z34,z5]),(0,[z0,z1,z7,z29,z222,z3,z4]),(0,[z0,z1,z7,z3,z4,z355,z23])],[(0,[z0,z58,z47,z7,z3,z4,z5]),(0,[z0,z1,z7,z527,z3,z4,z5]),(0,[z28,z1,z14,z7,z3,z4,z5]),(0,[z0,z1,z14,z14,z3,z4,z5]),(0,[z0,z1,z14,z3,z224,z4,z5]),(0,[z11,z0,z1,z109,z3,z4,z5]),(0,[z0,z1,z7,z570,z3,z4,z5]),(0,[z0,z1,z86,z7,z224,z4,z5]),(0,[z0,z1,z7,z571,z3,z4,z5])],[(0,[z0,z58,z37,z7,z3,z4,z5]),(0,[z0,z1,z308,z8,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z5,z22]),(0,[z0,z1,z3,z4,z563,z5,z23])],[(1,[z0,z1,z572,z3,z4,z5]),(0,[z0,z27,z1,z8,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z5,z22]),(1,[z0,z1,z14,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z573,z5]),(0,[z0,z1,z7,z574,z3,z4,z5]),(0,[z32,z0,z1,z183,z3,z4,z5]),(0,[z0,z1,z7,z575,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z134,z4,z5]),(0,[z0,z1,z576,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z84,z3,z4]),(0,[z135,z49,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z577,z5]),(0,[z0,z1,z7,z3,z578,z4,z5]),(0,[z294,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z8,z3,z36,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z4])],[(0,[z1,z7,z8,z3,z4,z50,z5]),(0,[z579,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z3,z36,z4,z5]),(0,[z0,z57,z7,z3,z185,z4,z5]),(0,[z0,z1,z7,z3,z580,z4,z5]),(0,[z0,z1,z7,z465,z75,z4,z5])],[(0,[z0,z1,z385,z14,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z418,z5]),(0,[z165,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z581,z4,z5]),(0,[z582,z0,z1,z7,z3,z4,z5]),(0,[z583,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z21,z3,z4,z5])],[(1,[z0,z1,z7,z557,z4,z5]),(0,[z0,z1,z46,z7,z3,z73,z5]),(0,[z0,z1,z16,z7,z3,z5,z23]),(0,[z0,z1,z7,z3,z584,z4,z5]),(0,[z0,z1,z7,z29,z3,z4,z22])],[(1,[z0,z1,z7,z3,z4,z546]),(0,[z0,z1,z7,z585,z3,z4,z5]),(0,[z0,z1,z132,z7,z3,z4,z5])],[(0,[z17,z0,z1,z377,z3,z4,z5]),(0,[z0,z1,z7,z3,z586,z4,z5]),(0,[z135,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z587,z4,z5]),(0,[z0,z1,z7,z3,z50,z5,z23]),(0,[z0,z1,z7,z3,z4,z588,z5]),(0,[z0,z466,z1,z7,z3,z4,z5])],[(0,[z0,z1,z8,z69,z3,z4,z5]),(0,[z0,z182,z1,z14,z3,z4,z5]),(0,[z135,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z5,z97]),(0,[z589,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z28,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z69,z3,z4,z5]),(0,[z0,z473,z1,z7,z3,z4,z5]),(0,[z0,z1,z590,z7,z3,z4,z5]),(0,[z0,z1,z21,z3,z224,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z591]),(0,[z0,z1,z7,z3,z4,z34,z5])],[(0,[z0,z1,z8,z3,z75,z4,z5]),(0,[z0,z1,z14,z3,z66,z4,z5]),(0,[z0,z1,z7,z592,z3,z4,z5]),(0,[z593,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z86,z7,z21,z4,z5]),(0,[z0,z1,z7,z594,z3,z4,z5])],[(0,[z0,z1,z14,z3,z75,z4,z5]),(0,[z0,z1,z7,z29,z3,z289,z4]),(1,[z0,z1,z183,z3,z4,z186]),(0,[z0,z1,z7,z20,z222,z4,z5]),(0,[z0,z1,z595,z7,z3,z4,z5]),(1,[z0,z1,z3,z4,z563,z23]),(0,[z0,z1,z7,z29,z307,z3,z4])],[(0,[z78,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z256,z7,z3,z4,z5]),(0,[z0,z1,z596,z7,z3,z4,z5]),(1,[z0,z27,z7,z3,z4,z98]),(0,[z0,z1,z7,z29,z449,z3,z4])],[(0,[z0,z1,z7,z208,z3,z4,z5]),(0,[z0,z1,z7,z597,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z546,z5]),(0,[z0,z1,z7,z29,z3,z4,z168]),(0,[z0,z1,z7,z3,z598,z4,z5]),(0,[z0,z1,z7,z508,z3,z4,z5]),(0,[z0,z1,z7,z476,z29,z3,z4]),(0,[z0,z1,z7,z29,z29,z3,z4])],[(0,[z0,z1,z7,z599,z3,z4,z5]),(0,[z0,z1,z510,z7,z3,z4,z5]),(1,[z0,z1,z240,z3,z4,z5]),(0,[z0,z58,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z600,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z601,z7,z3,z4,z5]),(0,[z0,z1,z602,z7,z3,z4,z5])],[(0,[z0,z1,z47,z7,z3,z4,z5]),(0,[z0,z1,z7,z20,z84,z4,z5]),(0,[z603,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z604,z4,z5]),(0,[z0,z1,z7,z3,z4,z23,z23])],[(0,[z0,z421,z1,z14,z3,z4,z5]),(0,[z0,z360,z1,z7,z3,z4,z5]),(0,[z0,z1,z69,z3,z224,z4,z5]),(0,[z0,z1,z7,z605,z3,z4,z5]),(1,[z0,z269,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z33,z4,z5]),(0,[z606,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z487,z29,z3,z4])]],
   [[(0,[z78,z0,z1,z572,z3,z4,z5]),(0,[z0,z58,z57,z7,z3,z4,z5]),(0,[z0,z1,z46,z7,z29,z3,z4])],[(0,[z607,z0,z1,z7,z3,z4,z5]),(0,[z0,z41,z1,z7,z20,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z608]),(0,[z32,z0,z1,z7,z60,z4,z5]),(0,[z0,z1,z7,z3,z4,z609,z5]),(1,[z0,z182,z1,z3,z4,z124])],[(0,[z0,z103,z7,z3,z4,z51,z5]),(0,[z0,z7,z9,z3,z185,z4,z5]),(0,[z0,z1,z7,z610,z3,z4,z5]),(0,[z0,z27,z1,z7,z3,z4,z53]),(0,[z0,z1,z16,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z611,z5])],[(0,[z17,z0,z1,z7,z3,z4,z23]),(0,[z0,z612,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z120]),(0,[z0,z1,z7,z3,z4,z391,z5]),(0,[z0,z613,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z225,z3,z4])],[(0,[z614,z0,z1,z7,z3,z4,z5]),(0,[z494,z0,z1,z7,z29,z3,z4])],[(0,[z78,z0,z1,z7,z557,z4,z5]),(0,[z0,z1,z7,z3,z615,z4,z5]),(0,[z0,z1,z8,z3,z4,z462,z5]),(0,[z0,z1,z7,z616,z3,z4,z5]),(0,[z0,z1,z7,z617,z3,z4,z5]),(0,[z0,z1,z7,z3,z618,z4,z5])],[(0,[z0,z1,z572,z7,z3,z4,z5]),(0,[z0,z1,z8,z3,z73,z4,z5]),(0,[z0,z41,z1,z7,z3,z4,z23]),(0,[z54,z0,z1,z7,z3,z4,z5]),(0,[z96,z0,z1,z7,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z289,z5])],[(0,[z619,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z14,z3,z73,z4,z5]),(0,[z0,z620,z1,z7,z3,z4,z5]),(0,[z0,z1,z621,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z622,z4,z5]),(1,[z0,z1,z7,z320,z3,z5]),(0,[z0,z1,z46,z7,z3,z36,z5])]],
   [[(0,[z623,z0,z1,z7,z3,z4,z5]),(0,[z0,z37,z1,z8,z3,z4,z5]),(0,[z0,z443,z1,z14,z3,z4,z5]),(0,[z165,z0,z1,z7,z66,z4,z5]),(0,[z49,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z5,z624]),(0,[z0,z1,z7,z3,z4,z5,z625]),(0,[z626,z0,z1,z7,z3,z4,z5])],[(1,[z0,z1,z7,z3,z4,z110]),(0,[z0,z1,z7,z7,z3,z4,z5]),(1,[z0,z510,z7,z3,z4,z5]),(0,[z627,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z266,z3,z4]),(0,[z0,z1,z7,z3,z4,z628,z5]),(0,[z0,z509,z1,z7,z29,z3,z4])],[(0,[z0,z1,z8,z29,z3,z4,z5]),(0,[z0,z1,z7,z629,z3,z4,z5]),(0,[z630,z0,z1,z7,z3,z4,z5])],[(0,[z190,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z14,z29,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z197]),(0,[z631,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z465,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z499])],[(0,[z0,z1,z7,z3,z4,z5,z632]),(0,[z190,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z109,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z633,z4,z5])],[(0,[z634,z0,z1,z7,z3,z4,z5]),(0,[z11,z0,z1,z8,z3,z4,z5]),(1,[z0,z1,z7,z12,z4,z5]),(0,[z244,z0,z1,z7,z3,z4,z98]),(0,[z0,z1,z7,z635,z3,z4,z5]),(0,[z0,z1,z183,z7,z29,z3,z4])],[(0,[z0,z1,z7,z3,z4,z5,z636]),(0,[z0,z1,z7,z3,z637,z4,z5]),(0,[z0,z638,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z639,z4,z5]),(0,[z0,z1,z7,z20,z29,z3,z4])],[(0,[z0,z27,z47,z7,z3,z4,z5]),(0,[z0,z1,z640,z7,z3,z4,z5]),(0,[z0,z1,z7,z641,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z642,z5]),(0,[z0,z1,z46,z16,z7,z3,z5])]],
   [[(0,[z0,z27,z37,z7,z3,z4,z5]),(0,[z0,z1,z155,z8,z3,z4,z5]),(0,[z0,z1,z7,z66,z4,z5,z22]),(0,[z0,z1,z7,z3,z4,z643,z5]),(0,[z0,z1,z7,z3,z4,z51,z23]),(0,[z0,z1,z7,z3,z4,z644,z5]),(0,[z0,z1,z7,z3,z4,z5,z53])],[(0,[z645,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z387,z4,z5]),(0,[z0,z1,z273,z14,z3,z4,z5]),(0,[z0,z1,z7,z646,z3,z4,z5]),(0,[z0,z1,z647,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z648]),(0,[z0,z649,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z650,z3,z4,z5])],[(0,[z651,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z9,z84,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z68]),(0,[z0,z1,z7,z3,z4,z652,z5]),(0,[z653,z0,z1,z7,z3,z4,z5]),(0,[z87,z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z46,z7,z29,z3,z5])],[(0,[z0,z1,z7,z3,z4,z654,z5]),(0,[z165,z0,z1,z7,z3,z4,z197]),(0,[z0,z1,z7,z3,z50,z168,z5]),(0,[z0,z1,z7,z3,z4,z5,z655]),(0,[z0,z1,z183,z3,z289,z4,z5]),(0,[z0,z1,z7,z62,z222,z3,z5])],[(0,[z656,z0,z1,z7,z3,z4,z5]),(1,[z49,z1,z7,z3,z73,z5]),(0,[z0,z103,z1,z7,z3,z4,z5]),(0,[z0,z657,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z98,z23]),(0,[z531,z0,z1,z7,z29,z3,z4])],[(0,[z0,z1,z7,z3,z4,z5,z658]),(0,[z0,z1,z7,z3,z4,z659,z5]),(0,[z0,z1,z7,z409,z3,z4,z5]),(0,[z0,z1,z7,z29,z566,z3,z4])],[(0,[z0,z1,z7,z3,z195,z4,z5]),(0,[z67,z0,z1,z7,z3,z4,z23]),(0,[z660,z0,z1,z7,z3,z4,z5]),(0,[z0,z57,z7,z3,z4,z51,z5]),(0,[z661,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z283,z5])],[(0,[z78,z0,z1,z7,z249,z4,z5]),(0,[z328,z0,z1,z8,z3,z4,z5]),(0,[z0,z662,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z663,z3,z4,z5])]],
   [[(0,[z136,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z131,z3,z4,z52]),(0,[z328,z0,z1,z7,z3,z4,z23]),(0,[z0,z664,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z62,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z665,z5]),(0,[z0,z1,z155,z7,z131,z4,z5]),(0,[z0,z1,z7,z3,z4,z563,z5])],[(0,[z11,z0,z1,z14,z3,z4,z5]),(0,[z0,z1,z46,z7,z62,z3,z5]),(0,[z0,z1,z7,z3,z4,z666,z5])],[(0,[z667,z0,z1,z7,z3,z4,z5])],[(0,[z78,z0,z47,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z73,z23]),(0,[z0,z1,z668,z7,z3,z4,z5]),(0,[z0,z1,z7,z225,z3,z4,z23])],[(0,[z78,z0,z37,z7,z3,z4,z5]),(0,[z0,z1,z8,z20,z3,z4,z5]),(0,[z0,z1,z7,z84,z4,z5,z22]),(0,[z0,z1,z7,z669,z3,z4,z5]),(0,[z0,z1,z7,z3,z289,z4,z23]),(0,[z0,z1,z155,z7,z131,z3,z4]),(0,[z0,z1,z7,z29,z3,z400,z4])],[(0,[z0,z1,z14,z20,z3,z4,z5]),(0,[z0,z1,z7,z670,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z259]),(0,[z0,z1,z173,z7,z3,z4,z5])],[(0,[z190,z0,z1,z240,z3,z4,z5]),(0,[z671,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z60,z4,z5])],[(0,[z0,z1,z7,z2,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z672,z5]),(0,[z0,z673,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z131,z3,z4,z68]),(0,[z674,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z149,z3,z4]),(0,[z244,z0,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z222,z3,z4,z5]),(0,[z0,z675,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z676,z4,z5])]],
   [[(0,[z677,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z224,z4]),(0,[z0,z1,z678,z7,z3,z4,z5])],[(1,[z0,z1,z377,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z679]),(0,[z0,z57,z1,z7,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z542]),(0,[z0,z1,z7,z3,z680,z4,z5]),(0,[z328,z0,z1,z7,z224,z4,z5]),(0,[z0,z1,z7,z681,z3,z4,z5]),(0,[z0,z1,z682,z7,z3,z4,z5])],[(0,[z0,z1,z7,z683,z3,z4,z5]),(0,[z38,z1,z7,z8,z3,z4,z5]),(0,[z165,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z684,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z685,z5]),(1,[z0,z1,z7,z222,z168,z5]),(0,[z0,z1,z7,z3,z311,z4,z5])],[(0,[z0,z1,z7,z3,z686,z4,z5]),(0,[z0,z1,z7,z687,z3,z4,z5]),(1,[z328,z0,z1,z224,z4,z5])],[(0,[z0,z1,z7,z239,z3,z4,z5]),(0,[z688,z0,z1,z7,z3,z4,z5]),(0,[z11,z0,z1,z69,z3,z4,z5]),(0,[z0,z1,z689,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z21,z3,z4])],[(0,[z0,z41,z47,z7,z3,z4,z5]),(0,[z0,z1,z14,z7,z3,z4,z23]),(0,[z0,z1,z7,z29,z394,z3,z4])],[(0,[z0,z41,z37,z7,z3,z4,z5]),(1,[z0,z1,z8,z29,z3,z4]),(0,[z0,z7,z9,z3,z4,z51,z5]),(0,[z0,z1,z7,z3,z4,z690,z5]),(0,[z0,z1,z7,z3,z4,z171,z5]),(0,[z0,z1,z183,z3,z4,z5,z186])],[(0,[z0,z1,z183,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z53,z23]),(0,[z0,z1,z86,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z691,z4,z5]),(0,[z0,z1,z7,z20,z62,z3,z5]),(0,[z0,z1,z7,z3,z36,z5,z23])]],
   [[(0,[z0,z1,z46,z7,z3,z50,z5])],[(0,[z0,z1,z7,z692,z3,z4,z5]),(0,[z693,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z694,z4,z5]),(1,[z0,z1,z3,z4,z563,z5])],[(1,[z1,z8,z3,z4,z50,z5]),(1,[z0,z1,z7,z157,z4,z5]),(0,[z0,z695,z1,z7,z3,z4,z5])],[(0,[z0,z696,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z697,z4,z5]),(1,[z0,z1,z7,z3,z4,z287]),(1,[z0,z1,z86,z21,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z698])],[(1,[z0,z1,z7,z3,z295,z5]),(0,[z488,z0,z1,z7,z3,z4,z5]),(0,[z699,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z9,z3,z4]),(0,[z700,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z701,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z702])],[(0,[z0,z1,z7,z3,z271,z4,z5]),(0,[z0,z1,z14,z3,z4,z50,z5]),(0,[z0,z1,z703,z7,z3,z4,z5]),(0,[z0,z1,z7,z704,z3,z4,z5]),(0,[z0,z1,z132,z3,z4,z5,z23])],[(0,[z0,z182,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z705,z5]),(0,[z0,z1,z7,z706,z3,z4,z5]),(1,[z0,z1,z7,z3,z36,z23])],[(0,[z0,z1,z7,z3,z185,z4,z23]),(0,[z0,z1,z7,z3,z75,z5,z23]),(0,[z0,z1,z7,z3,z4,z168,z23])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z7,z3,z4,z110]),(0,[z0,z103,z285,z185,z4,z5]),(0,[z0,z1,z82,z7,z3,z23])],[(0,[z0,z696,z7,z185,z4,z5]),(0,[z0,z1,z7,z3,z707,z5]),(0,[z356,z1,z8,z3,z4,z5]),(0,[z294,z1,z7,z3,z4,z68]),(0,[z0,z103,z7,z29,z185,z4]),(0,[z242,z1,z7,z29,z3,z4])],[(0,[z78,z47,z572,z3,z4,z5]),(0,[z0,z1,z7,z3,z286,z23]),(0,[z0,z1,z7,z3,z4,z708]),(0,[z0,z1,z7,z3,z4,z197]),(0,[z0,z1,z132,z3,z4,z5])],[(0,[z0,z1,z14,z16,z3,z23]),(0,[z0,z709,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z50,z23]),(0,[z0,z1,z7,z3,z578,z23]),(0,[z0,z1,z278,z7,z3,z171]),(0,[z0,z1,z7,z20,z29,z62])],[(0,[z0,z1,z7,z3,z4,z710]),(0,[z0,z1,z7,z253,z3,z23])],[(0,[z0,z1,z8,z3,z4,z74]),(0,[z277,z1,z7,z3,z4,z68])],[(0,[z521,z1,z8,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z171]),(0,[z0,z1,z711,z3,z4,z5]),(0,[z0,z1,z712,z3,z4,z5]),(0,[z0,z1,z713,z3,z4,z5])],[(0,[z78,z47,z7,z557,z4,z5])],[(0,[z0,z1,z8,z3,z4,z323]),(0,[z0,z1,z14,z465,z4,z5]),(0,[z0,z1,z7,z3,z309,z23]),(0,[z0,z1,z7,z3,z4,z714]),(0,[z32,z0,z269,z3,z34,z5]),(0,[z0,z1,z7,z715,z168,z5])],[(0,[z0,z1,z7,z3,z4,z716]),(0,[z0,z1,z7,z3,z4,z717]),(0,[z0,z7,z3,z718,z51,z5]),(0,[z0,z269,z7,z3,z4,z150]),(0,[z0,z1,z3,z4,z719,z5])],[(0,[z0,z1,z7,z720,z4,z5]),(0,[z0,z1,z721,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z722])],[(0,[z0,z444,z14,z3,z4,z5]),(0,[z49,z1,z7,z3,z73,z5]),(0,[z0,z1,z723,z3,z4,z5])],[(0,[z0,z1,z7,z724,z3,z286]),(0,[z0,z1,z7,z3,z4,z725]),(0,[z0,z1,z8,z3,z168,z23]),(0,[z0,z473,z14,z3,z4,z5]),(0,[z0,z103,z7,z4,z659,z5]),(0,[z0,z726,z7,z3,z4,z5]),(0,[z0,z1,z155,z7,z131,z4])],[(0,[z0,z1,z8,z3,z10,z5]),(0,[z0,z1,z208,z3,z289,z5])],[(0,[z67,z1,z8,z3,z4,z68]),(0,[z1,z14,z512,z3,z4,z5]),(0,[z0,z1,z7,z3,z10,z174]),(0,[z0,z727,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z728,z5])],[(0,[z1,z8,z3,z75,z50,z5]),(0,[z1,z8,z3,z50,z168,z5]),(0,[z0,z729,z7,z3,z4,z5]),(0,[z0,z1,z7,z730,z4,z5]),(0,[z0,z731,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z14,z249,z4,z5]),(0,[z0,z1,z732,z3,z4,z5]),(0,[z277,z47,z7,z3,z4,z5]),(0,[z136,z1,z14,z3,z4,z52]),(0,[z0,z733,z14,z3,z4,z5]),(0,[z0,z1,z734,z3,z4,z5]),(0,[z32,z0,z272,z7,z3,z23]),(0,[z0,z1,z7,z487,z400,z4])],[(0,[z0,z1,z735,z3,z4,z5]),(0,[z0,z1,z377,z29,z3,z4]),(0,[z0,z1,z8,z225,z4,z22])],[(0,[z1,z14,z8,z29,z3,z4]),(0,[z0,z736,z1,z8,z4,z5]),(0,[z230,z1,z8,z3,z4,z5]),(0,[z0,z1,z18,z3,z4,z174]),(0,[z0,z1,z7,z3,z73,z23]),(0,[z737,z0,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z738]),(0,[z0,z359,z7,z20,z4,z5]),(0,[z0,z1,z7,z29,z739,z3])],[(0,[z0,z1,z7,z740,z3,z5]),(0,[z0,z444,z7,z3,z4,z68]),(0,[z0,z69,z185,z224,z4,z5]),(0,[z0,z1,z7,z3,z4,z741])],[(0,[z0,z7,z362,z3,z51,z5]),(0,[z0,z1,z7,z60,z4,z5])],[(0,[z0,z1,z2,z3,z4,z110]),(0,[z0,z1,z742,z3,z4,z5]),(0,[z0,z1,z743,z3,z4,z23]),(0,[z0,z744,z7,z3,z4,z5]),(0,[z0,z1,z7,z176,z3,z4]),(0,[z0,z1,z7,z394,z3,z23])],[(0,[z0,z1,z7,z745,z3,z134]),(0,[z358,z0,z1,z7,z3,z23])],[(0,[z0,z1,z7,z3,z4,z746]),(0,[z0,z360,z8,z3,z4,z5]),(0,[z455,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z747]),(0,[z0,z1,z7,z3,z4,z748]),(0,[z0,z359,z7,z3,z4,z23])],[(0,[z0,z1,z8,z3,z4,z365]),(0,[z136,z1,z7,z3,z4,z749]),(0,[z0,z1,z7,z33,z4,z23])],[(0,[z67,z1,z7,z449,z3,z4])],[(0,[z165,z1,z8,z66,z4,z5]),(0,[z0,z1,z7,z3,z750,z4]),(0,[z242,z1,z14,z3,z4,z5]),(0,[z751,z1,z7,z3,z4,z5])],[(0,[z0,z1,z752,z3,z4,z5]),(0,[z0,z1,z7,z181,z168,z5]),(0,[z0,z1,z7,z753,z4,z5]),(0,[z67,z1,z7,z3,z4,z749]),(0,[z0,z1,z7,z409,z168,z23]),(0,[z0,z1,z7,z3,z311,z23]),(0,[z0,z1,z7,z29,z320,z3]),(0,[z0,z1,z7,z508,z4,z22])],[(0,[z11,z0,z69,z126,z4,z5]),(0,[z0,z754,z7,z3,z4,z23])],[(0,[z78,z755,z7,z3,z4,z5]),(0,[z0,z1,z7,z756,z3,z4]),(0,[z152,z0,z1,z8,z3,z23])],[(0,[z757,z1,z7,z3,z4,z5]),(0,[z0,z758,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z286,z110]),(0,[z0,z1,z106,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z759])],[(0,[z1,z8,z3,z4,z50,z5]),(0,[z526,z1,z14,z3,z4,z5]),(0,[z54,z0,z7,z3,z51,z5]),(1,[z0,z7,z3,z4,z760]),(0,[z242,z1,z7,z3,z4,z171])],[(0,[z28,z1,z14,z3,z4,z23]),(0,[z0,z1,z7,z761,z4,z5])],[(0,[z0,z1,z7,z3,z295,z5]),(0,[z0,z762,z7,z3,z4,z5]),(0,[z0,z1,z274,z3,z4,z23]),(0,[z0,z1,z763,z224,z4,z5]),(0,[z59,z1,z7,z33,z4,z5]),(0,[z0,z1,z3,z4,z124,z150]),(0,[z0,z1,z7,z3,z611,z23])],[(0,[z0,z1,z7,z3,z391,z23])],[(0,[z0,z1,z7,z3,z255,z5]),(0,[z0,z1,z7,z3,z36,z23])],[(0,[z0,z1,z256,z3,z4,z5])],[(0,[z0,z1,z7,z3,z295,z194]),(0,[z121,z0,z1,z271,z4,z5])],[(0,[z0,z1,z764,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z70])],[(0,[z0,z1,z7,z765,z4,z5])],[(0,[z0,z1,z7,z3,z4,z766]),(0,[z0,z1,z8,z3,z70,z5]),(0,[z0,z767,z7,z3,z4,z5]),(0,[z0,z1,z768,z3,z4,z5]),(0,[z0,z1,z7,z3,z628,z23])],[(0,[z0,z1,z7,z769,z4,z5]),(0,[z0,z770,z7,z3,z4,z5])],[(0,[z0,z1,z40,z3,z4,z5]),(0,[z1,z8,z570,z3,z4,z5]),(0,[z1,z14,z771,z3,z4,z5]),(0,[z49,z1,z7,z3,z772,z5])],[(0,[z0,z1,z7,z3,z263,z23]),(0,[z0,z1,z16,z7,z3,z23])],[(0,[z0,z1,z308,z21,z4,z5]),(0,[z0,z773,z14,z3,z4,z5]),(0,[z0,z1,z7,z84,z4,z197]),(0,[z0,z1,z109,z12,z4,z5]),(0,[z32,z0,z1,z7,z60,z23]),(0,[z0,z1,z7,z131,z3,z255])],[(0,[z59,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z774,z4,z5]),(0,[z0,z1,z46,z8,z29,z3]),(0,[z0,z1,z7,z3,z4,z775]),(0,[z0,z1,z7,z776,z4,z5]),(0,[z0,z1,z777,z7,z3,z5])]],
   [[(0,[z0,z1,z8,z3,z51,z23]),(0,[z0,z1,z189,z3,z4,z186]),(0,[z0,z1,z778,z3,z4,z5]),(0,[z32,z0,z1,z3,z34,z5])],[(0,[z0,z1,z166,z3,z4,z23])],[(0,[z0,z1,z779,z3,z4,z5]),(0,[z0,z1,z780,z3,z4,z5]),(0,[z0,z1,z7,z476,z3,z23]),(0,[z781,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z295,z782]),(0,[z1,z8,z3,z50,z51,z5]),(0,[z0,z1,z8,z3,z4,z783])],[(0,[z244,z0,z14,z3,z4,z53]),(0,[z0,z1,z7,z784,z3,z4])],[(0,[z0,z1,z7,z3,z785,z5]),(0,[z0,z7,z3,z786,z4,z5]),(0,[z0,z1,z7,z787,z3,z4]),(0,[z0,z1,z7,z3,z168,z97]),(0,[z0,z1,z7,z3,z406,z23]),(0,[z0,z1,z7,z788,z4,z5])],[(0,[z0,z1,z18,z3,z10,z5])],[(0,[z0,z447,z8,z3,z4,z5]),(0,[z0,z1,z7,z62,z3,z23])],[(0,[z0,z447,z7,z3,z4,z23]),(0,[z0,z1,z7,z441,z3,z23]),(0,[z96,z0,z7,z394,z3,z4])],[(0,[z0,z1,z7,z3,z789,z5])],[(0,[z0,z1,z572,z557,z4,z5]),(0,[z0,z1,z8,z3,z790,z5]),(0,[z32,z0,z1,z183,z3,z23])],[(0,[z700,z37,z7,z3,z4,z5]),(0,[z458,z1,z8,z3,z4,z5]),(0,[z0,z1,z24,z3,z4,z5]),(0,[z0,z1,z791,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z792]),(0,[z28,z1,z274,z3,z4,z5]),(0,[z0,z1,z40,z157,z4,z5]),(0,[z0,z1,z272,z7,z3,z23])],[],[(0,[z0,z57,z109,z3,z4,z5]),(0,[z0,z1,z3,z4,z793,z186])],[(0,[z0,z1,z40,z247,z4,z5]),(0,[z242,z272,z7,z3,z4,z5]),(0,[z0,z1,z794,z3,z4,z5]),(1,[z0,z1,z7,z795,z4]),(0,[z0,z1,z796,z3,z4,z5])]],
   [[(0,[z0,z269,z8,z3,z4,z5]),(0,[z0,z1,z106,z3,z4,z197]),(0,[z0,z1,z7,z508,z4,z499])],[(0,[z0,z1,z14,z557,z4,z5]),(0,[z0,z1,z7,z3,z797,z5]),(0,[z0,z798,z7,z3,z4,z5])],[(0,[z0,z1,z14,z3,z4,z546])],[(0,[z78,z47,z2,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z799]),(0,[z800,z1,z7,z3,z4,z5]),(0,[z0,z238,z1,z7,z3,z23])],[(0,[z165,z1,z18,z66,z4,z5]),(0,[z135,z1,z7,z3,z50,z5])],[(0,[z0,z1,z7,z3,z4,z801]),(0,[z0,z1,z7,z802,z3,z4])],[(0,[z0,z1,z803,z3,z4,z5]),(1,[z1,z7,z3,z772,z5]),(0,[z11,z0,z804,z3,z4,z5])],[(0,[z0,z1,z7,z805,z4,z5]),(0,[z0,z1,z7,z3,z134,z5]),(0,[z0,z1,z7,z806,z3,z4])],[(0,[z0,z421,z385,z3,z4,z5]),(0,[z0,z1,z807,z3,z4,z5]),(0,[z0,z1,z3,z4,z124,z365])],[(0,[z0,z1,z3,z4,z808,z5])],[(0,[z0,z1,z7,z3,z4,z809]),(0,[z0,z1,z7,z3,z810,z5]),(0,[z0,z1,z3,z4,z811,z5]),(0,[z0,z1,z7,z684,z3,z23]),(0,[z0,z1,z812,z3,z4,z5])],[(0,[z0,z1,z7,z3,z210,z23])],[(0,[z0,z1,z572,z249,z4,z5]),(0,[z0,z1,z7,z3,z813,z5]),(0,[z211,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z100,z3,z4]),(0,[z49,z1,z274,z3,z73,z5]),(0,[z0,z1,z814,z3,z4,z5])],[(0,[z0,z1,z7,z29,z3,z4]),(0,[z38,z1,z8,z3,z4,z5])],[(0,[z32,z0,z1,z650,z3,z5]),(0,[z0,z1,z815,z3,z4,z5])],[(0,[z32,z242,z1,z7,z3,z23]),(0,[z0,z213,z1,z3,z4,z563])]],
   [[(0,[z0,z1,z7,z3,z816,z5]),(0,[z0,z1,z46,z7,z33,z5]),(0,[z32,z0,z1,z3,z563,z5]),(0,[z0,z1,z3,z4,z793,z5])],[(0,[z0,z1,z7,z3,z10,z23]),(0,[z0,z103,z7,z3,z51,z23]),(0,[z0,z1,z7,z44,z4,z22])],[(0,[z0,z1,z7,z817,z3,z4]),(0,[z0,z1,z7,z818,z3,z4]),(0,[z0,z1,z40,z3,z309,z5]),(0,[z410,z1,z7,z3,z4,z52]),(0,[z0,z1,z819,z3,z4,z5]),(0,[z0,z820,z7,z3,z4,z5])],[(0,[z1,z7,z3,z50,z355,z23]),(0,[z0,z1,z16,z266,z3,z289])],[(0,[z0,z1,z155,z14,z131,z4]),(0,[z0,z1,z821,z3,z4,z5])],[(0,[z49,z1,z8,z3,z73,z5]),(0,[z0,z1,z7,z126,z4,z5]),(0,[z0,z103,z7,z185,z4,z5]),(1,[z0,z7,z730,z4,z5]),(0,[z0,z1,z345,z7,z3,z23])],[(0,[z0,z510,z14,z3,z4,z5]),(0,[z0,z1,z14,z266,z3,z4]),(0,[z0,z822,z7,z3,z4,z5]),(0,[z531,z1,z7,z476,z3,z4])],[(0,[z49,z1,z7,z3,z99,z5])],[(0,[z0,z823,z7,z3,z4,z5]),(0,[z0,z1,z15,z7,z131,z4]),(0,[z11,z0,z69,z29,z3,z4]),(0,[z0,z1,z132,z3,z4,z150])],[(0,[z0,z1,z296,z3,z4,z23]),(0,[z0,z1,z7,z3,z51,z97]),(0,[z0,z1,z7,z824,z4,z5]),(0,[z825,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z337,z3,z23])],[(0,[z0,z1,z7,z3,z4,z826]),(0,[z0,z1,z14,z12,z4,z5]),(0,[z0,z1,z7,z3,z4,z827]),(0,[z32,z0,z1,z3,z685,z5])],[(0,[z128,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z416]),(0,[z0,z1,z7,z828,z4,z23])],[(0,[z0,z360,z7,z3,z4,z23])],[(0,[z0,z1,z7,z3,z243,z23]),(0,[z0,z1,z829,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z259]),(0,[z0,z1,z7,z3,z227,z23]),(0,[z0,z1,z46,z7,z149,z3])],[(0,[z0,z1,z163,z3,z4,z5]),(0,[z165,z1,z7,z66,z4,z23]),(0,[z0,z1,z7,z3,z4,z830]),(0,[z0,z1,z7,z831,z3,z4]),(0,[z0,z1,z7,z3,z125,z5])]],
   [[(0,[z0,z1,z330,z157,z4,z5]),(0,[z0,z1,z25,z3,z4,z23])],[(0,[z0,z1,z832,z3,z4,z5]),(0,[z0,z1,z833,z7,z3,z4]),(0,[z0,z1,z834,z3,z4,z5]),(0,[z0,z1,z7,z835,z3,z4])],[],[(0,[z0,z1,z2,z29,z3,z4]),(0,[z0,z1,z7,z836,z4,z5]),(0,[z0,z1,z14,z3,z283,z5]),(0,[z0,z1,z3,z50,z563,z23]),(0,[z0,z360,z40,z3,z4,z5])],[(0,[z0,z268,z7,z3,z4,z5]),(0,[z0,z1,z7,z837,z4,z5]),(0,[z91,z1,z7,z3,z73,z5]),(0,[z0,z662,z7,z3,z51,z5])],[(0,[z0,z1,z7,z66,z168,z23]),(0,[z0,z1,z838,z3,z4,z5]),(0,[z0,z241,z7,z3,z4,z5])],[(0,[z0,z1,z7,z66,z10,z5]),(0,[z0,z1,z7,z839,z4,z5]),(0,[z0,z1,z3,z4,z840,z5]),(0,[z0,z1,z7,z841,z4,z5])],[(0,[z0,z1,z14,z3,z4,z5]),(0,[z0,z47,z7,z249,z4,z5]),(0,[z0,z1,z842,z3,z4,z5]),(0,[z0,z1,z7,z3,z202,z23]),(0,[z32,z0,z1,z33,z34,z5])],[(0,[z0,z37,z7,z249,z4,z5]),(0,[z49,z1,z8,z3,z4,z5]),(0,[z0,z1,z218,z3,z4,z23]),(0,[z0,z1,z7,z843,z3,z5])],[(0,[z0,z1,z7,z844,z4,z5]),(0,[z0,z1,z7,z3,z4,z845]),(0,[z0,z1,z7,z846,z3,z4]),(0,[z0,z1,z7,z847,z4,z5]),(0,[z0,z1,z7,z4,z146,z287]),(0,[z0,z848,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z666]),(0,[z0,z1,z849,z3,z4,z5])],[(0,[z0,z1,z7,z90,z168,z5]),(0,[z0,z7,z850,z3,z4,z5])],[(0,[z755,z47,z7,z3,z4,z5]),(0,[z0,z1,z7,z745,z3,z4]),(0,[z0,z1,z7,z60,z4,z150]),(0,[z0,z182,z1,z7,z3,z125]),(0,[z0,z1,z7,z715,z4,z5]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z0,z1,z7,z3,z113,z23]),(0,[z0,z1,z132,z3,z4,z367])],[(0,[z1,z8,z3,z4,z248,z5]),(0,[z0,z1,z14,z149,z3,z4]),(0,[z0,z103,z1,z7,z168,z23])],[(0,[z0,z1,z7,z3,z4,z171]),(0,[z0,z359,z7,z62,z3,z23])],[(0,[z0,z1,z7,z3,z4,z852]),(0,[z1,z14,z706,z3,z4,z5]),(0,[z0,z1,z214,z7,z3,z23]),(0,[z0,z1,z40,z3,z391,z5]),(0,[z0,z1,z3,z4,z853,z5]),(0,[z0,z1,z7,z3,z70,z23])],[(0,[z0,z1,z8,z3,z4,z23]),(0,[z0,z1,z14,z222,z168,z5]),(0,[z0,z466,z7,z3,z4,z5]),(0,[z0,z1,z7,z465,z4,z5])]],
   [[(0,[z78,z47,z7,z3,z4,z5]),(0,[z0,z854,z7,z3,z4,z5]),(0,[z59,z1,z274,z3,z4,z5]),(0,[z0,z1,z132,z3,z168,z23])],[(0,[z93,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z10,z197]),(0,[z0,z1,z7,z3,z4,z855]),(0,[z0,z1,z7,z856,z3,z4]),(0,[z0,z41,z7,z9,z4,z5]),(0,[z0,z1,z857,z3,z4,z5]),(0,[z242,z1,z3,z4,z34,z5]),(0,[z0,z1,z858,z3,z4,z23])],[(0,[z0,z1,z7,z29,z3,z286]),(0,[z0,z444,z7,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z365]),(0,[z0,z1,z7,z859,z4,z5]),(0,[z0,z1,z7,z860,z4,z23])],[(0,[z0,z473,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z861]),(0,[z0,z41,z1,z7,z168,z23]),(0,[z0,z1,z7,z3,z146,z23]),(0,[z0,z1,z7,z149,z3,z23]),(0,[z0,z1,z183,z3,z4,z563]),(0,[z0,z1,z862,z3,z4,z5])],[(0,[z78,z47,z7,z3,z4,z194]),(0,[z0,z1,z863,z3,z4,z5]),(0,[z0,z1,z864,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z865]),(0,[z135,z1,z7,z3,z772,z5]),(0,[z866,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z867,z4,z5])],[(0,[z0,z868,z8,z3,z4,z5]),(0,[z0,z1,z7,z208,z3,z23])],[(0,[z318,z1,z14,z3,z4,z5])],[(0,[z0,z1,z869,z3,z4,z5]),(0,[z0,z1,z14,z157,z4,z5]),(0,[z0,z733,z7,z3,z4,z5]),(0,[z136,z1,z7,z3,z4,z52])],[(0,[z0,z1,z14,z3,z4,z287]),(0,[z375,z1,z14,z3,z4,z5]),(0,[z0,z870,z7,z3,z4,z5]),(0,[z0,z1,z21,z763,z4,z5])],[(0,[z0,z1,z7,z29,z557,z4]),(0,[z59,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z167,z23]),(0,[z0,z7,z871,z3,z4,z5]),(0,[z0,z1,z7,z739,z3,z5])],[(0,[z0,z1,z872,z7,z3,z4]),(0,[z0,z1,z8,z29,z3,z23]),(0,[z0,z873,z7,z3,z4,z5]),(0,[z0,z1,z7,z512,z3,z23]),(0,[z0,z1,z7,z795,z225,z4])],[(0,[z1,z208,z8,z3,z50,z5]),(0,[z0,z1,z874,z29,z3,z4]),(0,[z0,z1,z875,z29,z3,z4])],[(0,[z0,z1,z876,z3,z4,z5]),(0,[z582,z0,z1,z224,z4,z5]),(0,[z0,z1,z7,z3,z311,z4]),(0,[z0,z1,z877,z3,z4,z5]),(0,[z0,z1,z878,z3,z4,z5])],[(0,[z0,z879,z7,z3,z4,z5]),(0,[z0,z1,z880,z3,z4,z5]),(0,[z0,z1,z3,z563,z125,z23])],[(0,[z6,z0,z7,z3,z4,z53]),(0,[z0,z1,z7,z881,z3,z4]),(0,[z0,z1,z7,z818,z3,z73])],[(0,[z0,z27,z8,z3,z4,z98]),(0,[z1,z35,z14,z3,z4,z5]),(0,[z165,z1,z7,z66,z4,z197]),(0,[z0,z1,z7,z3,z75,z259]),(0,[z0,z1,z7,z29,z3,z518]),(0,[z0,z1,z7,z3,z676,z23])]],
   [[(0,[z0,z1,z7,z3,z882,z5]),(0,[z294,z1,z7,z3,z50,z5]),(0,[z0,z1,z7,z883,z3,z4]),(0,[z0,z1,z7,z465,z4,z287])],[],[(0,[z17,z37,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z884]),(0,[z0,z1,z7,z3,z4,z885]),(0,[z0,z444,z7,z157,z4,z5]),(1,[z0,z272,z7,z3,z23])],[(0,[z0,z1,z7,z291,z4,z5]),(0,[z0,z359,z7,z29,z3,z4])],[(0,[z152,z0,z1,z3,z34,z5]),(0,[z0,z421,z109,z3,z4,z5]),(0,[z0,z285,z3,z185,z4,z5]),(0,[z0,z269,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z886,z23])],[(0,[z152,z1,z8,z3,z50,z5]),(0,[z0,z1,z7,z3,z4,z887]),(0,[z0,z1,z106,z3,z134,z5]),(0,[z59,z1,z7,z3,z4,z150]),(0,[z0,z1,z7,z508,z168,z5]),(0,[z0,z7,z177,z3,z311,z4])],[(0,[z1,z107,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z888,z4]),(0,[z32,z0,z1,z3,z34,z150]),(0,[z0,z1,z16,z3,z563,z23])],[(0,[z0,z1,z7,z889,z3,z295]),(0,[z0,z1,z890,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z347]),(0,[z1,z7,z3,z772,z50,z5]),(0,[z0,z1,z891,z3,z4,z5])],[(0,[z0,z1,z7,z3,z892,z5]),(0,[z0,z1,z7,z81,z4,z5])],[(0,[z49,z1,z8,z3,z50,z5]),(0,[z0,z1,z893,z3,z4,z5]),(0,[z0,z1,z7,z3,z894,z5]),(0,[z0,z1,z895,z3,z4,z5]),(0,[z0,z1,z173,z307,z3,z4])],[(0,[z0,z1,z7,z3,z896,z5]),(0,[z0,z1,z897,z3,z4,z5])],[(0,[z0,z1,z8,z320,z3,z5]),(0,[z0,z1,z106,z29,z3,z4]),(0,[z0,z1,z7,z353,z168,z5]),(0,[z0,z1,z7,z3,z73,z416]),(0,[z0,z272,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z898,z5]),(0,[z0,z1,z7,z3,z4,z899]),(0,[z0,z182,z1,z278,z3,z124]),(0,[z0,z1,z7,z320,z3,z23])],[(0,[z0,z1,z7,z900,z4,z5]),(0,[z0,z1,z8,z3,z4,z110]),(0,[z474,z37,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z901,z5]),(0,[z0,z1,z7,z3,z598,z23])],[(0,[z0,z1,z274,z29,z3,z4]),(0,[z0,z1,z7,z763,z4,z5])],[(0,[z0,z1,z7,z902,z4,z5]),(0,[z0,z1,z7,z3,z903,z5]),(0,[z0,z1,z8,z3,z4,z197]),(0,[z32,z0,z1,z3,z162,z5]),(0,[z0,z1,z904,z3,z4,z5]),(0,[z0,z905,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z691,z23]),(0,[z0,z906,z7,z3,z4,z5])]],
   [[(0,[z78,z47,z7,z3,z286,z5]),(0,[z0,z1,z8,z3,z50,z23]),(0,[z0,z1,z14,z907,z4,z5]),(0,[z0,z1,z7,z415,z168,z5]),(0,[z0,z1,z7,z3,z75,z23])],[(0,[z0,z1,z7,z3,z246,z23]),(0,[z0,z1,z7,z3,z908,z5]),(0,[z0,z447,z24,z3,z4,z5]),(0,[z0,z1,z7,z3,z248,z23])],[(0,[z0,z909,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z134,z174]),(0,[z135,z1,z7,z29,z3,z50]),(0,[z0,z27,z7,z3,z4,z760])],[(0,[z0,z1,z7,z3,z4,z910]),(0,[z0,z1,z330,z3,z4,z5])],[(0,[z0,z1,z132,z3,z51,z23]),(0,[z0,z1,z7,z3,z719,z5]),(0,[z0,z1,z3,z36,z563,z23])],[(0,[z0,z1,z7,z911,z4,z5])],[(0,[z1,z8,z3,z4,z162,z5]),(0,[z0,z1,z7,z73,z146,z5]),(0,[z0,z1,z7,z912,z3,z4]),(0,[z0,z1,z7,z3,z913,z5])],[(0,[z0,z7,z804,z3,z4,z5]),(0,[z244,z0,z7,z3,z283,z53]),(0,[z0,z1,z7,z3,z914,z5])],[(0,[z0,z1,z18,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z97]),(0,[z0,z1,z7,z225,z255,z22])],[(0,[z0,z1,z7,z3,z4,z915]),(0,[z49,z1,z7,z3,z73,z23]),(0,[z0,z1,z7,z3,z916,z4])],[(0,[z0,z109,z804,z3,z4,z5]),(0,[z0,z1,z7,z3,z917,z23])],[(0,[z0,z1,z7,z29,z12,z4]),(0,[z0,z1,z7,z3,z282,z23]),(0,[z0,z1,z7,z4,z146,z5]),(0,[z0,z1,z7,z29,z4,z146]),(0,[z0,z1,z7,z795,z4,z22])],[(0,[z165,z1,z7,z29,z66,z4]),(0,[z0,z1,z166,z29,z3,z4]),(0,[z67,z1,z40,z3,z4,z68]),(0,[z0,z1,z7,z918,z4,z5])],[(0,[z0,z1,z7,z919,z3,z5])],[(0,[z0,z1,z14,z33,z4,z5]),(0,[z19,z0,z69,z3,z4,z5]),(0,[z0,z58,z7,z3,z507,z5])],[(0,[z0,z1,z8,z3,z73,z23]),(0,[z0,z1,z8,z126,z4,z5]),(0,[z0,z182,z1,z3,z4,z418]),(0,[z0,z1,z7,z29,z3,z10]),(0,[z0,z1,z920,z3,z4,z5]),(0,[z0,z1,z7,z3,z921,z5]),(0,[z0,z1,z7,z62,z3,z886]),(0,[z0,z1,z922,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z923,z5]),(0,[z0,z7,z276,z9,z4,z5]),(0,[z328,z0,z466,z224,z4,z5]),(0,[z32,z0,z269,z7,z3,z23])],[(0,[z0,z1,z7,z3,z924,z5]),(0,[z0,z1,z8,z740,z3,z5]),(0,[z606,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z99,z23]),(0,[z0,z1,z7,z925,z4,z5]),(0,[z0,z1,z3,z289,z125,z5])],[(0,[z265,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z60,z4,z5]),(0,[z0,z268,z106,z3,z4,z5])],[(0,[z0,z1,z572,z3,z4,z5]),(0,[z0,z1,z8,z176,z3,z4]),(0,[z1,z7,z3,z73,z50,z23])],[(0,[z0,z1,z7,z33,z4,z171])],[(0,[z393,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z88,z23])],[(0,[z0,z926,z7,z3,z4,z5]),(0,[z0,z1,z330,z247,z4,z5])],[(0,[z0,z1,z572,z3,z4,z194]),(0,[z0,z1,z7,z3,z4,z927]),(0,[z0,z928,z14,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z929]),(0,[z0,z1,z7,z3,z314,z23]),(0,[z0,z1,z278,z7,z3,z5]),(0,[z0,z1,z46,z7,z739,z3])],[(0,[z0,z1,z7,z557,z4,z5]),(0,[z0,z1,z8,z3,z750,z4]),(0,[z0,z1,z930,z3,z4,z5]),(0,[z0,z285,z3,z4,z51,z5]),(0,[z328,z0,z1,z224,z4,z23])],[(0,[z0,z192,z527,z3,z4,z5]),(0,[z0,z1,z14,z3,z391,z5]),(0,[z0,z1,z7,z81,z50,z5]),(0,[z0,z57,z229,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z546])],[(0,[z0,z1,z7,z3,z4,z931]),(0,[z1,z8,z3,z231,z4,z5]),(0,[z0,z1,z16,z3,z289,z5]),(0,[z0,z1,z7,z29,z33,z4]),(0,[z0,z932,z7,z29,z3,z4])],[(0,[z0,z1,z933,z3,z4,z5])],[(0,[z0,z1,z7,z557,z4,z194]),(0,[z0,z1,z7,z4,z934,z5]),(0,[z0,z1,z935,z3,z4,z5]),(0,[z0,z238,z1,z3,z4,z124]),(0,[z0,z1,z936,z29,z3,z4])],[(0,[z0,z7,z3,z4,z718,z5])],[(0,[z0,z1,z14,z3,z4,z194]),(0,[z54,z0,z8,z3,z51,z5]),(0,[z0,z1,z7,z937,z4,z5]),(0,[z0,z1,z7,z149,z3,z70]),(0,[z0,z938,z7,z3,z4,z5])],[(0,[z0,z755,z7,z3,z4,z5]),(0,[z0,z268,z7,z3,z4,z174])]],
   [[(0,[z0,z1,z8,z3,z295,z5]),(0,[z0,z762,z8,z3,z4,z5]),(0,[z0,z1,z86,z21,z4,z23])],[(0,[z0,z1,z183,z3,z4,z196]),(0,[z0,z1,z7,z3,z541,z23])],[(0,[z0,z1,z939,z3,z4,z5]),(0,[z0,z1,z7,z940,z3,z4]),(0,[z1,z8,z3,z260,z4,z5]),(0,[z0,z1,z8,z3,z255,z5]),(0,[z0,z1,z8,z3,z36,z23]),(0,[z0,z359,z7,z3,z311,z4])],[(0,[z0,z1,z7,z3,z941,z5])],[(0,[z0,z1,z7,z3,z942,z5]),(0,[z0,z444,z7,z3,z391,z5]),(0,[z0,z1,z7,z943,z4,z5]),(0,[z0,z1,z7,z29,z3,z685]),(0,[z0,z1,z7,z944,z4,z5])],[(0,[z945,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z946,z4,z5]),(0,[z0,z1,z7,z947,z3,z4])],[(0,[z0,z1,z7,z3,z4,z948])],[(0,[z0,z1,z7,z949,z4,z5]),(0,[z0,z1,z433,z3,z4,z5]),(0,[z0,z1,z7,z950,z3,z4]),(0,[z242,z1,z183,z3,z4,z5]),(0,[z0,z269,z7,z60,z4,z5]),(0,[z0,z1,z173,z7,z3,z125]),(1,[z0,z1,z7,z715,z5])],[(0,[z0,z1,z18,z3,z4,z197]),(0,[z0,z1,z7,z81,z73,z5]),(0,[z0,z7,z730,z3,z4,z5])],[(0,[z356,z0,z1,z7,z3,z23]),(0,[z0,z1,z330,z3,z309,z5]),(0,[z0,z951,z7,z3,z4,z5])],[(0,[z0,z1,z7,z249,z4,z5]),(0,[z0,z1,z952,z8,z3,z5]),(0,[z0,z1,z18,z3,z134,z5]),(0,[z953,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z954]),(0,[z0,z1,z955,z3,z4,z5])],[(0,[z0,z1,z956,z7,z3,z4]),(0,[z0,z241,z3,z224,z4,z5]),(0,[z413,z0,z1,z7,z3,z23]),(0,[z0,z1,z7,z20,z715,z5]),(0,[z0,z1,z7,z29,z267,z3])],[(0,[z0,z957,z7,z3,z4,z5]),(0,[z404,z1,z7,z3,z50,z5]),(0,[z0,z1,z285,z3,z4,z5])],[(0,[z0,z510,z7,z3,z4,z5]),(0,[z0,z1,z14,z247,z4,z5]),(0,[z0,z1,z14,z3,z4,z150]),(0,[z0,z1,z7,z3,z958,z5]),(0,[z0,z103,z7,z730,z4,z5]),(0,[z59,z1,z7,z3,z4,z23])],[(0,[z0,z1,z2,z557,z4,z5]),(0,[z0,z1,z7,z249,z4,z194]),(0,[z0,z1,z7,z959,z3,z4]),(0,[z0,z960,z7,z3,z4,z5]),(0,[z0,z1,z961,z3,z4,z5])],[(0,[z0,z447,z256,z3,z4,z5]),(0,[z0,z1,z7,z3,z50,z416])]],
   [[(0,[z0,z1,z962,z3,z4,z5]),(0,[z0,z1,z7,z346,z3,z23]),(0,[z67,z1,z330,z3,z4,z68]),(0,[z0,z1,z963,z3,z4,z23])],[(0,[z91,z1,z8,z3,z4,z5]),(0,[z589,z1,z7,z3,z73,z5]),(0,[z0,z1,z7,z12,z4,z5]),(0,[z0,z1,z7,z3,z397,z23]),(1,[z242,z1,z7,z3,z23])],[(0,[z0,z1,z7,z964,z4,z5]),(0,[z0,z8,z3,z786,z4,z5]),(0,[z49,z1,z24,z3,z4,z5]),(0,[z0,z1,z7,z3,z965,z5]),(0,[z0,z272,z7,z33,z4,z5]),(0,[z0,z1,z46,z7,z3,z311])],[(0,[z0,z37,z7,z3,z4,z194]),(0,[z0,z1,z7,z157,z4,z68]),(0,[z0,z966,z7,z3,z4,z5]),(0,[z0,z1,z306,z7,z566,z4])],[(0,[z0,z1,z296,z29,z3,z4]),(0,[z0,z1,z8,z62,z3,z23]),(0,[z0,z1,z7,z3,z4,z967]),(0,[z165,z1,z7,z66,z134,z5]),(0,[z0,z1,z46,z7,z100,z3]),(0,[z0,z57,z7,z12,z4,z5]),(0,[z0,z1,z7,z3,z4,z968]),(0,[z0,z1,z969,z3,z4,z5])],[(0,[z0,z1,z7,z970,z4,z5]),(0,[z242,z1,z7,z3,z4,z5]),(0,[z0,z1,z240,z3,z4,z23]),(0,[z0,z1,z7,z201,z3,z23]),(0,[z971,z1,z7,z3,z4,z5])],[(0,[z1,z8,z3,z4,z319,z5]),(0,[z0,z972,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z973,z5]),(0,[z0,z360,z7,z29,z3,z4]),(0,[z0,z1,z974,z3,z4,z5]),(0,[z0,z1,z7,z176,z222,z168])],[(0,[z0,z1,z7,z975,z3,z5]),(0,[z0,z1,z14,z976,z3,z4]),(0,[z0,z444,z7,z247,z4,z5]),(0,[z32,z0,z1,z7,z3,z23])],[(0,[z0,z1,z7,z3,z977,z5]),(0,[z0,z1,z24,z3,z4,z23]),(0,[z0,z1,z978,z7,z4,z5])],[(0,[z0,z1,z7,z979,z4,z5]),(0,[z0,z1,z14,z3,z286,z5]),(0,[z483,z47,z7,z3,z4,z5]),(0,[z0,z360,z330,z3,z4,z5]),(0,[z0,z1,z7,z3,z283,z5]),(0,[z0,z46,z7,z177,z3,z5])],[(0,[z0,z1,z25,z29,z3,z4])],[(0,[z0,z1,z208,z3,z387,z5]),(0,[z11,z0,z69,z12,z4,z5])],[(0,[z0,z1,z7,z320,z3,z311])],[(0,[z0,z1,z980,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z74])],[(0,[z0,z1,z7,z3,z295,z110]),(0,[z0,z1,z7,z981,z4,z5]),(0,[z54,z0,z7,z3,z718,z5])]],
   [[(0,[z0,z1,z2,z249,z4,z5]),(0,[z28,z1,z14,z29,z3,z4]),(0,[z0,z1,z14,z3,z309,z5]),(0,[z0,z1,z7,z881,z3,z10]),(0,[z0,z1,z7,z3,z982,z4]),(0,[z0,z1,z983,z3,z4,z5]),(0,[z0,z984,z7,z3,z4,z5])],[(0,[z0,z58,z7,z3,z263,z5]),(0,[z135,z1,z8,z3,z50,z5]),(0,[z59,z269,z7,z3,z4,z5]),(0,[z0,z1,z3,z719,z34,z5])],[(0,[z0,z1,z14,z985,z4,z5])],[(0,[z0,z268,z7,z3,z10,z5]),(0,[z0,z1,z7,z149,z3,z4]),(0,[z0,z1,z7,z986,z4,z5]),(0,[z0,z1,z132,z3,z4,z23])],[(0,[z0,z1,z8,z3,z134,z5]),(0,[z0,z1,z14,z3,z4,z987]),(0,[z0,z1,z988,z3,z4,z5])],[(0,[z0,z1,z377,z3,z4,z5]),(0,[z0,z1,z208,z8,z3,z23]),(0,[z0,z1,z14,z3,z168,z23]),(0,[z0,z1,z330,z3,z391,z5]),(0,[z0,z103,z7,z680,z4,z5])],[(0,[z1,z14,z8,z3,z4,z5]),(0,[z0,z1,z7,z989,z4,z5]),(0,[z0,z1,z7,z3,z90,z23]),(0,[z0,z1,z3,z289,z719,z5]),(0,[z0,z1,z990,z3,z4,z5])],[(0,[z67,z1,z14,z3,z4,z68])],[(0,[z190,z1,z14,z84,z4,z5]),(0,[z0,z773,z7,z3,z4,z5])],[(0,[z17,z755,z7,z3,z4,z5]),(0,[z0,z1,z8,z100,z3,z4]),(0,[z152,z0,z1,z7,z3,z23]),(0,[z0,z447,z7,z291,z4,z5]),(0,[z0,z1,z7,z739,z3,z36])],[(0,[z0,z1,z7,z249,z286,z5]),(0,[z0,z41,z7,z493,z4,z5]),(0,[z0,z1,z8,z29,z3,z4]),(0,[z0,z1,z8,z3,z75,z23]),(0,[z0,z1,z7,z3,z4,z991])],[(0,[z0,z1,z7,z3,z4,z992]),(0,[z0,z444,z7,z3,z309,z5]),(0,[z0,z103,z218,z185,z4,z5]),(0,[z993,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z994,z3,z4])],[(0,[z0,z1,z7,z3,z112,z23])],[(0,[z1,z390,z8,z3,z4,z5]),(0,[z0,z1,z14,z995,z4,z5]),(0,[z0,z447,z7,z3,z4,z347]),(0,[z135,z447,z7,z3,z50,z5]),(0,[z0,z1,z7,z3,z996,z5])],[(0,[z0,z1,z14,z997,z4,z5]),(0,[z0,z447,z7,z81,z4,z5]),(0,[z0,z1,z86,z236,z4,z5]),(0,[z244,z0,z7,z3,z4,z53]),(0,[z0,z1,z132,z29,z3,z23])],[(0,[z0,z1,z998,z3,z4,z5]),(0,[z0,z1,z804,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z999]),(0,[z32,z59,z1,z3,z34,z5])]],
   [[(0,[z0,z1,z7,z1000,z4,z5]),(0,[z0,z359,z14,z3,z4,z5]),(0,[z11,z0,z251,z3,z4,z5]),(0,[z0,z85,z109,z3,z4,z5]),(0,[z0,z1,z1001,z3,z4,z5])],[(0,[z0,z360,z14,z3,z4,z5]),(0,[z165,z268,z7,z66,z4,z5]),(0,[z0,z1,z640,z7,z29,z3]),(0,[z0,z1,z7,z600,z3,z23]),(0,[z0,z272,z7,z3,z4,z150]),(0,[z0,z1,z16,z3,z719,z5])],[(0,[z0,z103,z8,z185,z4,z5]),(0,[z0,z1,z7,z1002,z4,z5]),(0,[z0,z1003,z14,z3,z4,z5]),(0,[z0,z1,z14,z3,z4,z365]),(0,[z67,z444,z7,z3,z4,z68]),(0,[z0,z57,z804,z3,z4,z5]),(0,[z0,z1,z7,z146,z5,z23]),(0,[z32,z0,z1,z7,z33,z23])],[(0,[z0,z1,z7,z126,z4,z23]),(0,[z0,z103,z7,z185,z4,z23]),(0,[z737,z0,z7,z3,z4,z23])],[(0,[z0,z1,z7,z3,z886,z4])],[(0,[z0,z1,z7,z1004,z3,z5])],[(0,[z603,z1,z14,z3,z4,z5]),(0,[z0,z447,z7,z29,z3,z4]),(0,[z0,z1,z7,z60,z4,z23]),(0,[z0,z182,z1,z3,z4,z793])],[(0,[z0,z1,z1005,z3,z4,z5]),(0,[z0,z1,z1006,z3,z4,z5]),(0,[z0,z1,z7,z548,z3,z23]),(0,[z1007,z1,z7,z3,z4,z5]),(0,[z1008,z1,z7,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z416]),(0,[z0,z1,z7,z66,z4,z197]),(0,[z379,z1,z7,z66,z4,z5]),(0,[z19,z0,z1,z224,z4,z5]),(0,[z384,z0,z7,z3,z51,z5]),(0,[z0,z1,z7,z3,z4,z917])],[(0,[z17,z37,z7,z3,z4,z5]),(0,[z0,z1,z7,z1009,z4,z5]),(0,[z0,z1,z14,z1010,z4,z5]),(0,[z0,z1,z7,z3,z4,z1011]),(0,[z0,z1,z7,z3,z4,z1012]),(0,[z0,z1,z86,z29,z21,z4]),(0,[z0,z1,z1013,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1014,z5]),(0,[z0,z1,z46,z7,z29,z3])],[(0,[z0,z1,z1015,z3,z4,z5])],[(0,[z0,z1,z8,z3,z125,z5]),(0,[z169,z0,z1,z7,z3,z23]),(0,[z0,z1,z7,z1016,z3,z4]),(0,[z0,z1,z7,z449,z3,z23])],[(0,[z0,z1,z7,z62,z3,z97]),(0,[z0,z1,z163,z3,z4,z23]),(0,[z0,z1,z7,z3,z125,z23]),(0,[z0,z1,z7,z753,z4,z23])],[(0,[z0,z1,z7,z1017,z4,z5]),(0,[z0,z1018,z7,z3,z4,z5]),(0,[z0,z1019,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z1020,z5])],[(0,[z0,z1,z278,z14,z3,z5]),(0,[z0,z1,z7,z3,z4,z1021]),(0,[z0,z269,z7,z29,z3,z4]),(0,[z1022,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z225,z400,z4])]],
   [[(0,[z17,z37,z377,z3,z4,z5]),(0,[z59,z1,z7,z60,z4,z5]),(0,[z0,z758,z7,z3,z4,z23]),(0,[z0,z1,z29,z3,z563,z23])],[(0,[z0,z1,z7,z1023,z4,z5]),(0,[z0,z268,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1024]),(0,[z0,z1,z7,z3,z4,z1025]),(0,[z32,z0,z1,z29,z3,z34]),(0,[z0,z1,z183,z3,z4,z186])],[(0,[z1,z8,z3,z4,z50,z23]),(0,[z0,z241,z8,z3,z4,z5]),(0,[z0,z1,z7,z1026,z4,z5]),(0,[z54,z0,z7,z3,z51,z23])],[(0,[z0,z1,z7,z1027,z4,z5]),(0,[z0,z241,z7,z3,z4,z23]),(0,[z0,z1,z3,z4,z124,z793])],[(0,[z0,z1,z7,z3,z295,z23]),(0,[z0,z1,z771,z3,z4,z5]),(0,[z0,z447,z7,z3,z4,z416]),(0,[z0,z1,z132,z3,z50,z23]),(0,[z0,z1,z7,z3,z283,z98])],[(0,[z1028,z0,z1,z7,z3,z5]),(0,[z0,z1,z7,z3,z522,z23]),(0,[z0,z1,z14,z3,z4,z174]),(0,[z0,z1,z7,z3,z391,z68]),(0,[z136,z1,z25,z3,z4,z52]),(0,[z0,z41,z7,z29,z9,z4]),(0,[z0,z7,z9,z3,z51,z23])],[(0,[z49,z1,z8,z3,z4,z23]),(0,[z0,z1,z8,z844,z4,z5]),(0,[z0,z1,z7,z3,z255,z23])],[(0,[z0,z1,z7,z1029,z4,z5]),(0,[z0,z1,z1030,z3,z4,z5]),(0,[z0,z250,z1,z3,z4,z124]),(0,[z0,z1,z7,z907,z4,z5]),(0,[z0,z1,z256,z3,z4,z23]),(0,[z0,z1,z1031,z3,z4,z5]),(0,[z0,z1,z7,z3,z232,z23]),(0,[z0,z1,z132,z3,z4,z124]),(0,[z0,z1,z849,z3,z4,z23])],[(0,[z0,z1,z7,z3,z1032,z5]),(0,[z0,z57,z527,z3,z4,z5]),(0,[z0,z1,z14,z1033,z4,z5]),(1,[z0,z1,z7,z146,z23]),(0,[z0,z182,z1,z3,z4,z124])],[(0,[z0,z1,z14,z3,z51,z23]),(0,[z0,z1,z214,z14,z3,z23])],[(0,[z0,z1,z8,z3,z4,z171]),(0,[z0,z1,z7,z687,z3,z23]),(0,[z0,z7,z3,z4,z5,z760])],[(0,[z0,z1,z7,z3,z4,z1034]),(0,[z0,z1,z8,z3,z4,z852]),(0,[z0,z510,z106,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1035]),(0,[z0,z1,z1036,z3,z4,z5])],[(0,[z0,z1,z8,z465,z4,z5]),(0,[z0,z466,z8,z3,z4,z5]),(0,[z242,z1,z7,z33,z4,z5])],[(0,[z78,z47,z8,z3,z4,z5]),(0,[z0,z854,z8,z3,z4,z5]),(0,[z0,z1,z40,z3,z4,z23]),(0,[z671,z0,z1,z7,z3,z23]),(0,[z32,z0,z1,z132,z3,z23]),(0,[z0,z1,z155,z7,z795,z4])],[(0,[z0,z1,z7,z3,z1037,z5]),(0,[z0,z41,z8,z9,z4,z5]),(0,[z0,z1,z7,z29,z222,z168]),(0,[z0,z1,z7,z62,z172,z5]),(0,[z0,z7,z3,z4,z23,z1038])],[(0,[z0,z444,z8,z3,z4,z5]),(0,[z0,z1,z3,z4,z1039,z5])]],
   [[(0,[z0,z1,z7,z3,z1040,z5]),(0,[z0,z1,z7,z3,z4,z1041]),(0,[z0,z473,z8,z3,z4,z5]),(0,[z0,z447,z14,z3,z4,z5]),(0,[z0,z1,z7,z266,z3,z4])],[(0,[z0,z1,z7,z1042,z4,z5]),(0,[z0,z1,z1043,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1044]),(0,[z0,z7,z3,z75,z51,z23]),(0,[z32,z0,z1,z3,z34,z23]),(0,[z0,z1,z7,z62,z168,z23])],[],[(0,[z0,z27,z7,z3,z4,z226]),(0,[z49,z1,z876,z3,z4,z5]),(0,[z0,z1,z18,z29,z3,z4]),(0,[z0,z1,z7,z3,z75,z97]),(0,[z0,z1,z132,z3,z73,z23]),(0,[z1,z7,z3,z4,z749,z68]),(0,[z0,z1,z7,z3,z4,z1045])],[(0,[z136,z1,z8,z3,z4,z52]),(0,[z0,z1,z7,z4,z1046,z5]),(0,[z32,z0,z1,z3,z125,z5])],[(0,[z0,z47,z7,z3,z4,z194]),(0,[z0,z1047,z7,z29,z3,z4])],[(0,[z0,z1,z572,z3,z286,z5]),(0,[z0,z1,z7,z1048,z4,z5])],[(0,[z0,z1,z1049,z3,z4,z5]),(0,[z0,z1050,z7,z3,z4,z5]),(0,[z0,z41,z7,z730,z4,z5])],[(0,[z0,z1,z7,z3,z4,z1051]),(0,[z1,z8,z504,z3,z4,z5]),(0,[z0,z510,z7,z3,z4,z174]),(0,[z244,z0,z7,z3,z4,z760])],[(0,[z0,z1,z1052,z3,z4,z5]),(0,[z0,z1,z8,z3,z311,z4])],[(0,[z0,z7,z285,z185,z4,z5]),(0,[z0,z1,z3,z763,z4,z5]),(0,[z0,z1,z877,z3,z4,z23])],[(0,[z0,z1,z7,z557,z286,z5]),(0,[z0,z272,z7,z3,z5,z23])],[(0,[z1,z214,z8,z3,z4,z5]),(0,[z0,z1,z7,z362,z3,z23])],[(0,[z0,z1,z7,z1053,z3,z5]),(0,[z0,z444,z7,z3,z4,z52]),(0,[z0,z1,z7,z3,z400,z23])],[(0,[z0,z1,z155,z8,z131,z4]),(0,[z0,z1,z14,z3,z4,z1054]),(0,[z0,z928,z7,z3,z4,z5])],[(0,[z0,z1,z1055,z3,z4,z5]),(0,[z0,z1,z7,z3,z73,z287]),(0,[z0,z57,z109,z3,z4,z23]),(0,[z0,z269,z7,z3,z4,z171]),(0,[z0,z1,z3,z563,z168,z23])]],
   [[(0,[z0,z736,z1,z7,z4,z5]),(0,[z0,z1,z8,z291,z4,z5]),(0,[z32,z0,z1,z14,z3,z23]),(0,[z0,z1,z1056,z3,z4,z5]),(0,[z0,z1,z7,z3,z573,z23]),(0,[z0,z1,z794,z3,z4,z23])],[(0,[z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z1057,z4,z5]),(0,[z0,z1,z8,z3,z4,z887]),(0,[z0,z1058,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z3,z215]),(0,[z242,z1,z16,z3,z4,z5]),(0,[z0,z1,z7,z3,z33,z23])],[(0,[z0,z520,z7,z9,z4,z5])],[(0,[z0,z1,z8,z3,z4,z347]),(0,[z0,z1,z14,z3,z4,z323]),(0,[z0,z1,z7,z605,z3,z23])],[(0,[z0,z1,z7,z3,z4,z194]),(0,[z0,z1,z8,z81,z4,z5]),(0,[z661,z1,z14,z3,z4,z5]),(0,[z135,z1,z7,z3,z50,z23]),(0,[z373,z0,z1,z7,z3,z23])],[(0,[z0,z1,z218,z29,z3,z4]),(0,[z0,z1,z132,z3,z36,z23])],[(0,[z0,z1,z1059,z3,z4,z5]),(0,[z0,z1,z893,z3,z4,z23])],[(0,[z0,z272,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z134,z23]),(0,[z0,z1,z305,z7,z3,z23]),(0,[z0,z1,z7,z3,z168,z323])],[(0,[z0,z1,z14,z3,z10,z5]),(0,[z0,z458,z7,z3,z4,z53]),(0,[z0,z1,z7,z222,z168,z5])],[(0,[z0,z1,z1060,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1061]),(0,[z0,z268,z18,z3,z4,z5]),(0,[z630,z1,z7,z84,z4,z5]),(0,[z0,z7,z177,z3,z4,z5])],[(0,[z0,z1,z7,z3,z1062,z5]),(0,[z242,z1,z7,z3,z4,z150]),(0,[z0,z1,z3,z4,z811,z23])],[(0,[z78,z47,z7,z3,z4,z110]),(0,[z11,z0,z69,z3,z4,z5]),(0,[z0,z1,z1063,z7,z3,z5])],[(0,[z0,z1,z14,z225,z4,z22]),(0,[z0,z7,z69,z12,z4,z5]),(0,[z0,z1,z1064,z3,z4,z5]),(1,[z0,z1,z7,z739,z3]),(0,[z0,z1,z814,z3,z4,z23])],[(0,[z38,z1,z8,z3,z4,z23]),(0,[z589,z1,z8,z3,z4,z5]),(0,[z0,z532,z7,z9,z4,z5]),(0,[z671,z0,z7,z3,z51,z5]),(0,[z0,z1,z7,z3,z1065,z5]),(0,[z0,z1,z173,z7,z3,z23]),(0,[z0,z1,z7,z20,z62,z5]),(0,[z0,z1,z3,z4,z1066,z5])],[]],
   [[(0,[z1,z771,z8,z3,z4,z5]),(0,[z1,z8,z29,z3,z4,z50]),(0,[z0,z1,z3,z4,z563,z5])],[(0,[z0,z1,z7,z3,z1067,z5]),(0,[z0,z1,z7,z157,z4,z5]),(0,[z0,z1,z330,z3,z4,z23]),(0,[z0,z1,z7,z149,z4,z146]),(0,[z32,z0,z1,z3,z563,z23]),(0,[z494,z1,z7,z449,z3,z4])],[(0,[z0,z1,z155,z7,z501,z4]),(0,[z0,z1,z7,z3,z4,z287]),(0,[z358,z0,z1,z224,z4,z5]),(0,[z0,z1,z7,z21,z168,z23]),(0,[z0,z1068,z7,z3,z4,z5])],[(0,[z0,z1,z7,z1069,z4,z5]),(0,[z0,z1070,z7,z3,z4,z5])],[(0,[z0,z1,z1071,z3,z4,z5]),(0,[z0,z1,z1072,z3,z4,z5]),(0,[z0,z1,z285,z9,z4,z5]),(0,[z54,z0,z7,z3,z51,z259]),(0,[z0,z1073,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1074])],[(0,[z0,z1,z8,z3,z4,z97]),(1,[z0,z804,z3,z4,z5]),(0,[z0,z1,z1075,z7,z3,z5]),(0,[z0,z1,z7,z1076,z4,z5]),(0,[z1077,z1,z7,z3,z4,z5]),(0,[z0,z1,z16,z3,z289,z365]),(0,[z0,z1,z821,z3,z4,z23])],[],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z7,z3,z1078,z5]),(0,[z165,z1,z14,z66,z4,z5]),(0,[z0,z1,z7,z1079,z4,z5])],[(0,[z0,z1,z8,z4,z146,z5]),(0,[z0,z1,z7,z29,z3,z391]),(0,[z0,z1,z7,z3,z1080,z5]),(0,[z0,z1,z7,z177,z3,z23]),(0,[z0,z1,z132,z62,z3,z23])],[],[(0,[z0,z1,z7,z1081,z4,z5])],[(0,[z0,z1,z2,z3,z4,z194]),(0,[z0,z1,z336,z7,z3,z23])],[(0,[z0,z510,z7,z84,z4,z5]),(0,[z0,z510,z7,z3,z10,z5]),(0,[z0,z1,z159,z7,z3,z23])],[(0,[z0,z1,z7,z3,z1082,z5]),(0,[z0,z41,z7,z670,z4,z5]),(0,[z54,z0,z7,z29,z3,z51])],[(0,[z116,z0,z69,z3,z4,z5]),(0,[z0,z1083,z7,z3,z4,z5]),(0,[z0,z1,z7,z1084,z3,z4]),(0,[z0,z1,z7,z3,z134,z1085]),(0,[z0,z1086,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z1087,z5])],[(0,[z0,z1,z1088,z3,z4,z5]),(0,[z0,z1,z16,z8,z3,z23]),(0,[z0,z1,z7,z976,z3,z4]),(0,[z0,z1089,z7,z3,z4,z5])]],
   [[(0,[z28,z1,z7,z3,z50,z23]),(0,[z0,z1,z240,z29,z3,z4]),(0,[z0,z1,z1090,z3,z4,z5]),(0,[z0,z1,z7,z3,z1091,z5])],[(0,[z0,z1,z7,z3,z286,z5]),(0,[z0,z1,z7,z3,z643,z23]),(0,[z0,z1,z7,z1092,z4,z5]),(0,[z0,z7,z1093,z3,z4,z5])],[(0,[z0,z1,z1094,z3,z4,z5]),(0,[z328,z0,z241,z224,z4,z5])],[(0,[z0,z1,z7,z1095,z4,z5]),(0,[z0,z1,z7,z420,z3,z23])],[(0,[z0,z1,z7,z3,z654,z23]),(0,[z0,z1096,z7,z3,z4,z5]),(0,[z0,z1097,z14,z3,z4,z5]),(0,[z32,z0,z1,z60,z34,z5])],[(0,[z0,z1,z8,z557,z4,z5]),(0,[z0,z1,z7,z3,z286,z194]),(0,[z1,z8,z3,z50,z5,z23]),(0,[z0,z268,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z1098]),(0,[z0,z1,z7,z3,z604,z23]),(0,[z0,z1,z278,z7,z3,z23])],[(0,[z0,z1,z8,z3,z4,z546]),(0,[z0,z1,z14,z3,z70,z5])],[(0,[z0,z1,z1099,z3,z4,z5]),(0,[z0,z1,z7,z29,z247,z4]),(0,[z0,z1,z7,z831,z3,z75])],[(0,[z0,z1,z7,z1100,z3,z4]),(0,[z0,z1,z14,z3,z4,z23]),(0,[z0,z1,z7,z3,z134,z197]),(0,[z0,z1,z7,z1101,z3,z4]),(0,[z1102,z1,z7,z3,z4,z5]),(0,[z0,z1,z29,z3,z4,z563])],[(0,[z0,z1,z7,z1103,z3,z4]),(0,[z0,z250,z1,z3,z4,z333]),(0,[z0,z1,z16,z3,z195,z5]),(0,[z0,z1,z7,z3,z4,z1104]),(0,[z0,z1,z7,z3,z665,z23])],[(0,[z165,z510,z7,z66,z4,z5]),(0,[z0,z1,z7,z465,z149,z4]),(0,[z340,z0,z1,z7,z3,z23])],[(0,[z0,z1,z7,z3,z4,z987]),(0,[z0,z1,z7,z3,z1105,z5])],[(0,[z0,z1,z7,z3,z1106,z5]),(0,[z0,z1,z86,z298,z4,z5]),(0,[z0,z1107,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1108])],[(0,[z0,z1,z1109,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1110]),(0,[z0,z1,z183,z307,z3,z4]),(0,[z0,z114,z7,z3,z4,z425])],[(0,[z0,z1,z7,z1111,z4,z5]),(0,[z0,z1,z132,z3,z75,z23]),(0,[z0,z1,z7,z715,z3,z5]),(0,[z0,z1,z132,z29,z3,z4])],[(0,[z78,z47,z7,z3,z295,z5]),(0,[z0,z1,z3,z4,z1112,z5]),(0,[z0,z1,z874,z3,z4,z5]),(0,[z0,z1,z875,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z1113,z4,z5]),(0,[z0,z1,z7,z465,z4,z23]),(0,[z0,z466,z7,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z1114]),(0,[z0,z1,z7,z3,z538,z23])],[(0,[z78,z47,z7,z3,z4,z23]),(0,[z688,z0,z7,z3,z51,z5]),(0,[z0,z1,z1115,z3,z4,z5]),(0,[z0,z7,z3,z4,z5,z1038])],[(0,[z593,z37,z7,z3,z4,z5]),(0,[z0,z1,z7,z1116,z4,z5]),(0,[z49,z1,z7,z100,z3,z73]),(0,[z0,z41,z7,z9,z4,z23])],[(0,[z234,z0,z1,z105,z4,z5]),(0,[z0,z1,z7,z3,z50,z287]),(0,[z49,z1,z7,z29,z3,z73]),(0,[z0,z444,z7,z3,z4,z23]),(0,[z0,z41,z7,z4,z611,z5])],[(0,[z1,z7,z839,z66,z4,z5]),(0,[z0,z473,z7,z3,z4,z23]),(0,[z0,z1,z1117,z3,z4,z5])],[(0,[z158,z1,z8,z3,z4,z5]),(0,[z0,z1,z14,z3,z1118,z5]),(0,[z0,z1,z743,z3,z4,z5]),(0,[z0,z1,z433,z3,z4,z23]),(0,[z0,z1,z7,z3,z4,z1119]),(0,[z0,z1,z285,z20,z4,z5]),(0,[z242,z1,z7,z3,z5,z23]),(0,[z0,z1,z7,z504,z168,z5]),(0,[z0,z1,z7,z867,z4,z23]),(0,[z294,z1,z7,z3,z4,z161])],[],[(0,[z0,z1,z2,z3,z286,z5]),(0,[z0,z1,z8,z249,z4,z5]),(0,[z152,z0,z1,z3,z462,z5]),(0,[z0,z1,z7,z157,z309,z5]),(0,[z0,z359,z7,z3,z4,z5])],[(0,[z0,z27,z14,z3,z4,z98]),(0,[z0,z1,z1120,z3,z4,z5]),(0,[z0,z1,z7,z3,z489,z23]),(0,[z0,z1,z7,z33,z4,z5]),(0,[z0,z1,z62,z3,z563,z23])],[],[(0,[z0,z1,z7,z3,z4,z1121]),(0,[z0,z510,z8,z3,z4,z5]),(0,[z626,z1,z8,z3,z4,z5]),(0,[z0,z1,z8,z266,z3,z4]),(0,[z0,z7,z177,z3,z73,z5]),(0,[z0,z1,z7,z739,z3,z23]),(0,[z0,z509,z7,z220,z3,z4])],[(0,[z1,z14,z127,z3,z4,z5]),(0,[z0,z1,z7,z1122,z3,z5]),(0,[z0,z1123,z7,z3,z4,z5])],[(0,[z0,z269,z14,z3,z4,z5]),(0,[z0,z754,z7,z3,z4,z5])],[(0,[z0,z1,z7,z889,z3,z4]),(0,[z335,z47,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z1124]),(0,[z0,z1,z8,z12,z4,z5]),(0,[z613,z1,z14,z3,z4,z5]),(0,[z383,z1,z7,z3,z73,z5]),(0,[z0,z1,z7,z3,z4,z749]),(0,[z0,z7,z730,z185,z4,z5]),(1,[z0,z1,z3,z4,z793])],[(0,[z0,z1,z7,z3,z4,z1125]),(0,[z0,z1,z106,z3,z4,z5]),(0,[z49,z1,z7,z3,z73,z97]),(0,[z0,z1,z46,z7,z3,z171]),(0,[z0,z1,z7,z131,z795,z4])]],
   [[(1,[z755,z7,z3,z4,z5]),(0,[z0,z47,z7,z3,z51,z23]),(0,[z0,z1,z7,z50,z146,z5]),(0,[z0,z1,z7,z605,z168,z5])],[(0,[z0,z37,z7,z3,z51,z23]),(0,[z28,z1,z14,z3,z4,z5]),(0,[z294,z1,z7,z3,z50,z23]),(0,[z0,z1,z357,z7,z29,z3]),(0,[z0,z1,z7,z1126,z4,z5])],[(0,[z0,z1,z274,z3,z4,z5]),(0,[z242,z1,z8,z3,z4,z5]),(0,[z620,z1,z14,z3,z4,z5]),(0,[z0,z1,z285,z185,z4,z5]),(0,[z0,z1,z285,z4,z168,z5])],[(0,[z0,z1,z7,z3,z586,z23]),(0,[z0,z1,z7,z29,z81,z4]),(0,[z0,z1,z7,z3,z4,z1127]),(0,[z0,z1,z7,z3,z391,z5]),(0,[z0,z1,z7,z29,z157,z4]),(0,[z242,z1,z214,z3,z4,z5]),(0,[z0,z1,z173,z132,z3,z23])],[(0,[z0,z1,z14,z320,z3,z5]),(0,[z0,z1,z7,z291,z4,z23]),(0,[z0,z1,z7,z20,z568,z5]),(0,[z0,z1,z7,z3,z4,z1128]),(0,[z0,z359,z7,z20,z62,z5])],[(0,[z0,z1,z8,z975,z3,z5]),(0,[z0,z268,z7,z3,z4,z197])],[(0,[z0,z1,z14,z3,z4,z110]),(0,[z0,z1,z1129,z3,z4,z5]),(0,[z0,z1,z7,z508,z168,z23])],[(0,[z0,z1,z7,z1130,z3,z4]),(0,[z0,z1,z8,z3,z283,z5])],[(0,[z0,z1,z14,z3,z4,z197]),(0,[z0,z1,z7,z3,z10,z1011]),(0,[z0,z1,z3,z4,z563,z365])],[(0,[z0,z1,z1131,z3,z4,z5]),(0,[z0,z1,z7,z3,z1132,z5]),(0,[z0,z1,z7,z3,z4,z1133]),(0,[z0,z1,z7,z81,z4,z23]),(0,[z0,z1,z590,z21,z4,z5]),(0,[z0,z1,z7,z224,z168,z23]),(0,[z0,z1,z183,z3,z4,z150]),(0,[z0,z1,z7,z3,z255,z22])],[(0,[z0,z1,z1134,z3,z4,z5]),(0,[z0,z1,z7,z75,z146,z23]),(0,[z0,z1,z241,z224,z4,z5])],[],[(0,[z0,z1,z7,z3,z4,z174]),(0,[z0,z1,z1135,z3,z4,z5]),(0,[z0,z272,z7,z3,z4,z23]),(0,[z0,z7,z20,z62,z177,z5])],[(0,[z0,z1,z7,z3,z4,z1136])],[(0,[z1,z8,z3,z4,z672,z5]),(0,[z1,z8,z3,z676,z4,z5]),(0,[z0,z1,z7,z715,z222,z5]),(0,[z0,z1,z1137,z3,z4,z5]),(0,[z0,z1,z1138,z3,z4,z5])],[(0,[z0,z1,z7,z1139,z3,z4]),(0,[z199,z0,z251,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z749])]],
   [[(0,[z0,z1,z7,z3,z4,z1140]),(0,[z0,z1,z8,z149,z3,z4]),(0,[z0,z1,z166,z3,z4,z5]),(0,[z0,z1141,z7,z3,z4,z5])],[(0,[z49,z1,z14,z3,z73,z5]),(0,[z0,z1,z7,z4,z1142,z5]),(0,[z0,z7,z9,z730,z4,z5]),(0,[z0,z1,z155,z7,z409,z4])],[(0,[z0,z1,z7,z3,z4,z1143]),(0,[z0,z1,z7,z3,z772,z5]),(0,[z660,z0,z7,z3,z4,z53]),(0,[z0,z1,z7,z3,z4,z1144])],[(0,[z0,z1,z833,z8,z3,z4]),(0,[z0,z1,z8,z989,z4,z5]),(0,[z0,z1,z7,z157,z391,z5])],[(0,[z0,z1,z7,z3,z4,z782]),(0,[z0,z8,z177,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1145]),(0,[z242,z1,z46,z7,z3,z5]),(0,[z0,z1146,z7,z3,z4,z5])],[(0,[z0,z1,z7,z1147,z4,z5]),(0,[z0,z14,z177,z3,z4,z5]),(0,[z0,z1,z7,z3,z73,z74]),(0,[z0,z1,z69,z12,z4,z5]),(0,[z1148,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z1149,z3,z4])],[(0,[z0,z1,z7,z247,z391,z5]),(0,[z0,z148,z7,z185,z4,z5]),(0,[z59,z272,z7,z3,z4,z5])],[(0,[z1,z46,z8,z3,z50,z5]),(0,[z0,z1,z7,z247,z4,z5]),(0,[z0,z1,z7,z1150,z4,z5]),(0,[z242,z269,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z150]),(0,[z0,z1,z7,z795,z4,z5])],[(0,[z0,z1,z14,z3,z73,z23]),(0,[z0,z1,z40,z29,z3,z4])],[(0,[z0,z1,z7,z3,z1151,z5]),(0,[z0,z1,z1152,z3,z4,z5])],[(0,[z0,z1,z14,z3,z4,z259]),(0,[z0,z1,z24,z291,z4,z5]),(0,[z0,z1,z7,z3,z283,z53]),(0,[z244,z0,z7,z3,z70,z53]),(0,[z0,z1153,z7,z3,z4,z5])],[(0,[z0,z1,z7,z29,z249,z4]),(0,[z667,z1,z8,z3,z4,z5]),(0,[z244,z0,z8,z3,z4,z53]),(0,[z0,z1,z14,z60,z4,z5]),(0,[z0,z1,z7,z502,z4,z22]),(0,[z0,z1,z7,z3,z1154,z5]),(0,[z59,z1,z7,z29,z3,z4]),(0,[z0,z1,z183,z7,z3,z125]),(0,[z0,z1,z7,z795,z3,z4])],[(0,[z0,z1,z8,z3,z4,z287]),(0,[z0,z1,z7,z4,z146,z23])],[(0,[z0,z1,z7,z1155,z4,z5]),(0,[z0,z1,z8,z1000,z4,z5]),(0,[z0,z1,z7,z476,z3,z391]),(0,[z0,z272,z46,z7,z3,z5])],[(0,[z0,z1,z7,z3,z4,z1156]),(0,[z0,z1,z1157,z3,z4,z5]),(0,[z0,z1,z24,z3,z4,z347]),(0,[z135,z1,z24,z3,z50,z5]),(0,[z49,z1,z433,z3,z73,z5]),(0,[z0,z932,z7,z3,z4,z5]),(0,[z0,z1,z1158,z3,z4,z5]),(1,[z0,z7,z177,z3,z23])],[(0,[z0,z1,z24,z81,z4,z5]),(0,[z0,z1,z682,z21,z4,z5]),(0,[z0,z1,z7,z3,z1159,z5])]],
   [[(0,[z0,z1,z7,z3,z133,z23]),(0,[z531,z1,z7,z3,z4,z52]),(0,[z0,z1,z936,z3,z4,z5])],[(0,[z0,z1,z7,z60,z4,z171]),(0,[z0,z182,z1,z3,z124,z125]),(0,[z0,z1160,z7,z3,z4,z5])],[(0,[z0,z1,z1161,z3,z4,z5]),(0,[z0,z1,z1162,z3,z4,z5]),(0,[z0,z1,z7,z301,z3,z23]),(0,[z0,z1,z132,z3,z4,z563])],[(0,[z0,z510,z18,z3,z4,z5]),(0,[z0,z1,z7,z3,z642,z23]),(0,[z0,z182,z1,z3,z4,z563])],[(0,[z0,z1,z572,z3,z4,z23]),(1,[z1,z8,z3,z50,z23]),(0,[z1,z8,z44,z3,z4,z5]),(0,[z1163,z1,z7,z3,z4,z5])],[(0,[z0,z1,z46,z14,z29,z3]),(0,[z0,z1,z1164,z3,z4,z5])],[(0,[z17,z37,z8,z3,z4,z5]),(0,[z384,z0,z7,z3,z51,z23])],[(0,[z0,z1,z24,z29,z3,z4]),(0,[z0,z1,z7,z3,z4,z1165]),(0,[z32,z59,z1,z7,z3,z23]),(0,[z0,z1,z7,z1166,z4,z5]),(0,[z0,z1,z306,z7,z3,z23])],[(0,[z0,z1,z7,z3,z4,z1167]),(0,[z1,z8,z62,z3,z50,z5]),(0,[z0,z448,z7,z3,z4,z98]),(0,[z0,z1,z7,z3,z4,z74])],[(0,[z0,z1,z7,z557,z4,z23]),(0,[z0,z1,z14,z3,z295,z5]),(0,[z0,z1,z7,z1168,z4,z5]),(0,[z0,z1,z1169,z3,z4,z5]),(0,[z0,z1,z7,z3,z659,z23]),(0,[z0,z1170,z7,z3,z4,z5])],[(0,[z0,z1,z214,z3,z195,z5]),(0,[z0,z1,z7,z3,z309,z5]),(0,[z328,z0,z1,z763,z4,z5]),(0,[z0,z1,z7,z312,z3,z23]),(0,[z0,z1,z7,z3,z694,z23]),(0,[z0,z1,z1171,z3,z4,z5])],[(0,[z0,z1,z7,z1172,z4,z5]),(0,[z0,z1,z7,z3,z1173,z5]),(0,[z0,z1,z8,z1017,z4,z5]),(0,[z0,z1018,z8,z3,z4,z5]),(0,[z0,z1,z14,z3,z255,z5]),(0,[z0,z1,z14,z3,z36,z23]),(0,[z0,z549,z69,z3,z4,z5]),(0,[z0,z1,z16,z3,z289,z23]),(0,[z0,z1,z7,z3,z4,z323])],[(0,[z0,z1,z7,z3,z4,z1174]),(0,[z0,z1,z872,z8,z3,z4]),(0,[z328,z0,z1,z105,z4,z5]),(0,[z0,z1,z7,z985,z4,z5]),(0,[z0,z1,z1175,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1176]),(0,[z32,z0,z1,z3,z719,z5])],[(0,[z1,z7,z8,z3,z50,z23])],[(0,[z0,z7,z177,z3,z50,z5]),(0,[z0,z1,z183,z3,z4,z365]),(0,[z304,z1,z7,z3,z4,z355])],[(0,[z0,z1,z7,z3,z168,z23]),(0,[z0,z1,z1177,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z286,z1140]),(0,[z0,z1,z7,z3,z10,z5]),(0,[z0,z1,z7,z3,z718,z5]),(0,[z0,z1,z1178,z3,z4,z5]),(0,[z0,z1,z7,z1179,z3,z4])],[(0,[z404,z1,z7,z66,z4,z5]),(0,[z67,z1,z7,z3,z4,z68]),(0,[z0,z1180,z7,z3,z4,z5]),(0,[z242,z1,z3,z4,z124,z5]),(0,[z0,z7,z177,z3,z4,z74])],[(0,[z0,z7,z3,z4,z5,z1181])],[(0,[z0,z1,z7,z3,z672,z23]),(0,[z472,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z29,z291,z4]),(0,[z0,z1,z7,z222,z168,z323]),(0,[z0,z1,z1182,z3,z4,z5])],[(0,[z0,z1,z7,z3,z1183,z5]),(0,[z1184,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z225,z4,z22])],[(0,[z0,z1,z7,z3,z1185,z5]),(0,[z0,z1,z1186,z7,z3,z4]),(0,[z59,z1,z14,z3,z4,z5]),(0,[z0,z1,z24,z3,z4,z416]),(0,[z0,z7,z465,z4,z51,z5]),(0,[z0,z1,z7,z20,z62,z74]),(0,[z0,z1,z7,z944,z4,z23])],[(0,[z0,z1,z14,z29,z3,z23]),(0,[z1,z7,z3,z4,z52,z749])],[(0,[z0,z1,z7,z29,z3,z295]),(0,[z0,z1,z7,z995,z4,z5])],[(0,[z0,z1,z296,z3,z4,z5]),(0,[z0,z1,z7,z997,z4,z5])],[(0,[z0,z1,z7,z249,z295,z5]),(0,[z38,z1,z8,z29,z3,z4]),(0,[z0,z7,z3,z4,z760,z53])],[(0,[z0,z1,z7,z3,z1187,z5]),(0,[z519,z1,z14,z3,z4,z5]),(0,[z0,z1,z7,z828,z4,z5]),(0,[z0,z1,z7,z3,z690,z23]),(0,[z0,z1,z7,z3,z171,z23])],[(0,[z0,z1,z7,z249,z4,z23]),(0,[z0,z360,z7,z3,z4,z5]),(0,[z0,z1,z1188,z3,z4,z5]),(0,[z59,z1,z7,z3,z4,z171]),(0,[z0,z1,z955,z3,z4,z23])],[(0,[z562,z0,z7,z3,z4,z53]),(0,[z137,z1,z8,z3,z4,z5]),(0,[z0,z1003,z7,z3,z4,z5]),(0,[z0,z7,z3,z51,z425,z23]),(0,[z0,z1,z7,z3,z4,z365]),(0,[z32,z0,z1,z3,z34,z171])],[(0,[z0,z1,z7,z3,z1189,z5]),(0,[z0,z1,z14,z62,z3,z23]),(0,[z0,z444,z40,z3,z4,z5]),(0,[z0,z1,z7,z247,z309,z5]),(0,[z0,z1,z285,z3,z4,z23])],[(0,[z0,z1,z7,z1190,z4,z5]),(0,[z165,z1,z7,z66,z4,z5]),(0,[z0,z510,z7,z3,z4,z23]),(0,[z135,z1,z7,z3,z50,z416])],[(0,[z0,z1,z25,z3,z4,z5]),(0,[z0,z1,z7,z3,z1191,z5]),(0,[z0,z160,z7,z3,z75,z5]),(0,[z0,z1,z7,z3,z4,z1192]),(0,[z0,z272,z7,z60,z4,z5])]],
   [[(0,[z460,z1,z8,z3,z4,z5]),(0,[z0,z1193,z7,z3,z4,z5]),(0,[z0,z1,z1194,z3,z4,z5]),(0,[z0,z1,z7,z276,z3,z23]),(0,[z0,z241,z86,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z1195]),(0,[z67,z1,z7,z157,z4,z68]),(0,[z0,z1,z7,z1196,z4,z5])],[(0,[z0,z1,z572,z3,z4,z110]),(0,[z0,z1,z1197,z3,z4,z5]),(0,[z0,z1,z7,z12,z4,z23]),(0,[z0,z1,z7,z3,z51,z259])],[(0,[z0,z1,z7,z3,z4,z1198]),(0,[z0,z1,z7,z1010,z4,z5]),(0,[z0,z1,z7,z3,z1199,z4])],[(0,[z0,z1,z1200,z7,z3,z5]),(0,[z0,z1,z1201,z3,z4,z5]),(0,[z0,z1,z7,z209,z4,z22]),(0,[z0,z1,z7,z3,z258,z23]),(0,[z67,z1,z7,z247,z4,z68]),(0,[z0,z966,z7,z3,z4,z23])],[(0,[z0,z1,z7,z1202,z3,z4]),(0,[z32,z0,z1,z16,z3,z23]),(0,[z384,z0,z7,z3,z4,z542])],[(0,[z0,z1,z7,z3,z4,z1203]),(0,[z0,z1,z7,z3,z4,z1204]),(0,[z242,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z131,z566,z4])],[(0,[z0,z1,z7,z557,z4,z110]),(0,[z0,z447,z7,z3,z73,z5]),(0,[z0,z1,z218,z3,z4,z5]),(1,[z0,z1,z7,z33,z23])],[(0,[z0,z1,z256,z291,z4,z5]),(1,[z0,z285,z185,z4,z5]),(0,[z0,z1,z974,z3,z4,z23])],[(0,[z662,z1,z8,z3,z4,z5]),(0,[z0,z1,z7,z3,z50,z74]),(0,[z0,z1,z7,z3,z275,z23])],[(0,[z0,z1,z8,z1053,z3,z5]),(0,[z0,z268,z7,z3,z134,z5]),(0,[z0,z1,z106,z3,z4,z174])],[(0,[z0,z1097,z7,z3,z4,z5]),(0,[z0,z360,z7,z157,z4,z5]),(0,[z0,z1,z163,z29,z3,z4]),(0,[z0,z1,z7,z3,z283,z23])],[(0,[z121,z0,z1,z224,z4,z5]),(0,[z0,z1,z14,z3,z50,z23]),(0,[z0,z1,z256,z3,z4,z347]),(0,[z135,z1,z256,z3,z50,z5]),(0,[z0,z1,z7,z3,z568,z23]),(0,[z0,z1,z3,z75,z563,z23])],[(0,[z0,z1,z14,z3,z134,z5]),(0,[z0,z473,z24,z3,z4,z5]),(0,[z0,z1,z256,z81,z4,z5]),(0,[z0,z1,z7,z3,z70,z5])],[(0,[z0,z1,z8,z3,z4,z5]),(0,[z235,z0,z7,z3,z51,z5]),(0,[z0,z360,z7,z247,z4,z5]),(0,[z0,z1,z7,z33,z4,z150]),(0,[z0,z1,z132,z16,z3,z23]),(0,[z0,z1,z278,z7,z29,z3]),(0,[z0,z1,z306,z7,z3,z255])],[(0,[z0,z1,z7,z3,z292,z23]),(0,[z0,z1,z7,z3,z4,z1205]),(0,[z0,z1,z7,z3,z4,z1206]),(0,[z0,z1207,z7,z3,z4,z5])]],
   [[(0,[z0,z268,z7,z29,z3,z4]),(1,[z0,z241,z224,z4,z5]),(0,[z0,z1,z858,z3,z4,z5])],[(0,[z1,z755,z7,z3,z4,z5]),(0,[z0,z103,z7,z574,z4,z5]),(0,[z0,z1,z7,z860,z4,z5]),(0,[z0,z241,z7,z29,z3,z4]),(0,[z0,z984,z7,z3,z4,z23])],[(0,[z0,z1,z8,z3,z4,z194]),(0,[z0,z1,z7,z1033,z4,z5])],[(0,[z17,z37,z296,z3,z4,z5]),(0,[z488,z0,z1,z7,z3,z23]),(0,[z0,z510,z7,z66,z4,z5]),(0,[z0,z1,z7,z3,z51,z23]),(0,[z244,z0,z7,z394,z3,z4])],[(0,[z0,z1,z7,z3,z4,z1208]),(0,[z49,z1,z8,z29,z3,z4]),(0,[z379,z1,z7,z3,z4,z68]),(0,[z1209,z1,z7,z3,z4,z5])],[(0,[z0,z1,z256,z29,z3,z4]),(1,[z0,z1,z763,z4,z5]),(0,[z0,z1,z988,z3,z4,z23])],[(0,[z0,z1,z7,z4,z1210,z5]),(0,[z0,z1,z377,z3,z4,z23]),(0,[z0,z1,z8,z222,z168,z5]),(0,[z0,z1,z7,z3,z4,z783]),(0,[z135,z473,z7,z3,z50,z5]),(0,[z0,z57,z7,z3,z51,z23]),(0,[z0,z1,z1211,z3,z4,z5])],[(0,[z1,z14,z8,z3,z4,z23]),(0,[z0,z1,z7,z3,z1212,z5]),(0,[z67,z1,z7,z3,z309,z68]),(0,[z0,z361,z7,z185,z4,z5])],[(0,[z0,z245,z7,z185,z4,z5]),(0,[z0,z1,z1213,z3,z4,z5])],[(0,[z0,z1,z7,z249,z4,z110]),(0,[z0,z1,z278,z8,z3,z5]),(0,[z0,z1214,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z464,z23]),(0,[z0,z1,z7,z3,z321,z23]),(0,[z0,z1,z7,z29,z3,z639])],[(0,[z0,z447,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z840,z97]),(0,[z0,z1,z1215,z3,z4,z5]),(0,[z0,z1,z7,z3,z1216,z5]),(0,[z0,z1,z7,z739,z3,z4])],[(0,[z383,z1,z8,z3,z4,z5]),(0,[z0,z103,z14,z185,z4,z5]),(0,[z0,z1,z14,z126,z4,z5]),(0,[z0,z1,z7,z84,z168,z23]),(1,[z0,z69,z12,z4,z5]),(0,[z0,z466,z7,z29,z3,z4])],[(0,[z78,z47,z7,z29,z3,z4]),(0,[z0,z1,z7,z669,z62,z5]),(0,[z0,z1,z3,z563,z125,z5]),(0,[z0,z7,z62,z177,z3,z23])],[(0,[z0,z1,z7,z3,z790,z5]),(0,[z488,z0,z1,z3,z162,z5])],[(0,[z0,z1,z8,z157,z4,z5]),(0,[z0,z510,z7,z3,z4,z197]),(0,[z0,z1,z7,z3,z4,z1217]),(0,[z0,z359,z7,z3,z4,z74]),(0,[z0,z1,z3,z4,z563,z23])],[(0,[z0,z1,z7,z3,z303,z23]),(0,[z0,z1,z14,z176,z3,z4]),(0,[z0,z473,z7,z29,z3,z4])]],
   [[(0,[z0,z1,z7,z3,z1218,z5]),(0,[z0,z549,z7,z185,z4,z5])],[(0,[z0,z1,z8,z247,z4,z5]),(0,[z0,z1,z14,z3,z4,z416]),(0,[z0,z1,z768,z3,z4,z97]),(0,[z0,z360,z7,z3,z309,z5]),(0,[z0,z1,z46,z7,z146,z5])],[(0,[z0,z1,z7,z3,z4,z1219])],[(0,[z0,z1,z256,z3,z4,z416]),(0,[z0,z269,z7,z3,z4,z5]),(0,[z0,z270,z7,z185,z4,z5]),(0,[z0,z103,z7,z193,z4,z5]),(0,[z0,z1,z7,z3,z4,z1220])],[(0,[z0,z1221,z7,z3,z4,z5]),(0,[z0,z7,z1222,z3,z4,z5]),(0,[z0,z41,z285,z3,z4,z5]),(0,[z0,z1,z7,z62,z715,z5]),(0,[z0,z7,z29,z177,z3,z4])],[(0,[z0,z1,z572,z3,z295,z5]),(0,[z0,z1,z14,z3,z125,z5]),(0,[z0,z1,z16,z3,z563,z5])],[(0,[z0,z1223,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1224]),(0,[z0,z1,z7,z291,z4,z347]),(0,[z135,z1,z7,z291,z50,z5])],[(0,[z0,z1,z8,z1081,z4,z5]),(0,[z0,z1,z308,z95,z4,z5]),(0,[z32,z242,z1,z3,z34,z5])],[(0,[z0,z1,z7,z3,z4,z1225]),(0,[z0,z1,z1226,z3,z4,z5]),(0,[z0,z1,z952,z7,z3,z5]),(0,[z0,z1,z7,z3,z4,z1054]),(0,[z0,z1227,z7,z3,z4,z5]),(0,[z0,z57,z432,z3,z4,z5]),(0,[z0,z1,z7,z3,z154,z23]),(0,[z0,z1,z7,z20,z420,z5]),(0,[z0,z1,z7,z513,z3,z23]),(0,[z0,z1,z7,z3,z370,z23]),(0,[z0,z1,z878,z29,z3,z4])],[(0,[z1,z8,z3,z4,z470,z5]),(0,[z0,z1,z86,z763,z4,z5])],[(0,[z0,z1,z7,z557,z295,z5]),(0,[z54,z0,z14,z3,z51,z5]),(0,[z135,z1,z7,z3,z50,z347]),(0,[z0,z238,z1,z191,z3,z4])],[(0,[z0,z1083,z8,z3,z4,z5]),(0,[z0,z1,z8,z1084,z3,z4]),(0,[z0,z1,z3,z4,z1014,z23]),(0,[z0,z241,z14,z3,z4,z5]),(0,[z0,z1,z7,z81,z4,z347]),(0,[z135,z1,z7,z81,z50,z5]),(0,[z32,z0,z272,z3,z34,z5])],[(0,[z0,z1,z7,z157,z4,z52]),(0,[z0,z7,z69,z3,z51,z23])],[(0,[z0,z1,z956,z8,z3,z4]),(0,[z0,z473,z7,z3,z4,z416]),(0,[z1,z24,z3,z4,z50,z5]),(0,[z0,z57,z109,z29,z3,z4])],[(0,[z0,z1,z8,z3,z286,z5]),(0,[z0,z1,z106,z3,z10,z5]),(0,[z0,z148,z1,z224,z4,z5]),(0,[z0,z1,z7,z4,z1228,z5]),(0,[z1229,z0,z1,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1230])],[(0,[z1,z7,z3,z73,z772,z5]),(0,[z0,z1,z3,z4,z1020,z23]),(0,[z0,z1,z7,z1092,z4,z23])]],
   [[(0,[z483,z1,z7,z66,z4,z5]),(0,[z0,z27,z7,z3,z4,z425])],[(0,[z335,z1,z7,z3,z50,z5]),(0,[z0,z1,z7,z3,z395,z23]),(0,[z699,z0,z69,z3,z4,z5]),(0,[z0,z1,z7,z3,z43,z23])],[(0,[z0,z1,z7,z100,z3,z309]),(0,[z0,z1,z354,z7,z3,z23]),(0,[z0,z58,z7,z3,z75,z23])],[(0,[z1,z8,z312,z3,z4,z5]),(0,[z0,z1,z7,z3,z1231,z5]),(0,[z0,z767,z14,z3,z4,z5]),(0,[z67,z1,z7,z3,z391,z68]),(0,[z0,z1,z7,z29,z3,z309]),(0,[z0,z1,z7,z3,z1232,z5])],[(0,[z0,z1,z8,z3,z309,z5]),(0,[z0,z1,z7,z1233,z3,z4]),(0,[z1,z7,z3,z4,z772,z5]),(0,[z0,z1,z7,z3,z633,z23])],[(0,[z0,z466,z14,z3,z4,z5]),(0,[z136,z1,z163,z3,z4,z52]),(0,[z0,z241,z7,z21,z4,z5])],[(0,[z78,z47,z14,z3,z4,z5]),(0,[z0,z1,z7,z465,z29,z4])],[(0,[z0,z1,z7,z3,z4,z1234]),(0,[z0,z1,z18,z3,z4,z5]),(0,[z0,z41,z14,z9,z4,z5]),(0,[z0,z1,z1235,z3,z4,z5]),(0,[z0,z1,z7,z3,z1236,z5]),(0,[z384,z0,z7,z3,z4,z53]),(0,[z0,z272,z7,z29,z3,z4])],[(0,[z0,z1,z1237,z3,z4,z5]),(0,[z79,z0,z7,z3,z51,z5]),(0,[z0,z1,z7,z33,z5,z23]),(0,[z0,z1,z1238,z3,z4,z5])],[(0,[z0,z1,z14,z3,z4,z861]),(0,[z0,z443,z1,z3,z4,z418]),(0,[z0,z1047,z7,z3,z4,z5]),(0,[z653,z1,z7,z3,z4,z52]),(0,[z242,z1,z7,z60,z4,z5]),(0,[z0,z1,z7,z29,z3,z125])],[(0,[z1,z876,z8,z3,z4,z5]),(0,[z32,z0,z1,z8,z3,z23]),(0,[z0,z1,z1239,z3,z4,z5]),(0,[z0,z1,z1240,z3,z4,z5]),(0,[z0,z1,z7,z3,z1241,z4]),(0,[z0,z1,z3,z51,z563,z23])],[(0,[z37,z755,z7,z3,z4,z5]),(0,[z0,z447,z7,z3,z50,z5]),(0,[z0,z473,z256,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1242])],[(0,[z0,z1,z1243,z3,z4,z5]),(0,[z0,z1,z39,z3,z4,z196]),(0,[z165,z1,z106,z66,z4,z5]),(0,[z0,z1244,z7,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1112,z23]),(0,[z0,z1245,z7,z3,z4,z5]),(0,[z0,z1,z7,z291,z4,z416]),(0,[z0,z360,z7,z3,z391,z5]),(0,[z0,z804,z69,z3,z4,z5]),(0,[z0,z7,z3,z4,z98,z760])],[(0,[z0,z1246,z7,z3,z4,z5]),(0,[z32,z0,z1,z3,z124,z23]),(0,[z32,z0,z1,z7,z3,z917])],[(0,[z1,z7,z3,z839,z4,z5]),(0,[z0,z1,z330,z29,z3,z4])]],
   [[(0,[z0,z47,z7,z3,z295,z5]),(0,[z0,z1,z1247,z3,z4,z5]),(0,[z0,z1,z7,z62,z3,z323]),(0,[z0,z7,z1248,z3,z4,z5]),(0,[z0,z1,z3,z4,z1039,z23])],[(0,[z0,z37,z7,z3,z295,z5]),(0,[z0,z1,z7,z3,z1249,z5]),(0,[z0,z1,z7,z3,z1250,z5]),(0,[z0,z1,z7,z3,z4,z259]),(0,[z0,z1,z7,z29,z3,z255])],[(0,[z0,z1,z14,z3,z311,z4]),(0,[z0,z1,z7,z81,z4,z416])],[(0,[z0,z1,z7,z1251,z4,z5]),(0,[z0,z1,z7,z3,z1252,z5])],[(0,[z0,z359,z8,z3,z4,z5])],[(0,[z0,z1,z189,z3,z4,z120]),(0,[z0,z1,z8,z33,z4,z5]),(0,[z0,z1,z7,z1253,z4,z5]),(0,[z0,z1,z1254,z3,z4,z5])],[(0,[z78,z47,z7,z249,z4,z5]),(0,[z373,z0,z69,z3,z4,z5])],[(0,[z328,z0,z1,z224,z4,z5]),(0,[z0,z1,z7,z3,z452,z23]),(0,[z0,z1,z16,z7,z3,z365])],[(1,[z1,z771,z3,z4,z5]),(0,[z0,z69,z3,z12,z4,z5]),(0,[z1255,z1,z7,z3,z4,z5]),(0,[z328,z0,z1,z29,z224,z4])],[(0,[z0,z1,z7,z3,z4,z1256]),(0,[z170,z1,z8,z3,z4,z5]),(0,[z0,z1,z14,z291,z4,z5]),(0,[z165,z1,z7,z66,z4,z174]),(0,[z0,z1,z7,z1257,z3,z5]),(0,[z0,z1,z7,z4,z1258,z5])],[(0,[z0,z1,z7,z1259,z3,z5]),(0,[z0,z1,z7,z89,z4,z22])],[(0,[z0,z1,z7,z3,z1260,z5]),(0,[z0,z1261,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z760])],[(0,[z0,z1,z1262,z3,z4,z5]),(0,[z0,z1,z273,z298,z4,z5]),(0,[z0,z1,z1200,z14,z3,z5])],[(0,[z0,z1,z14,z3,z4,z347]),(0,[z135,z1,z14,z3,z50,z5]),(0,[z0,z1,z7,z3,z4,z1263]),(0,[z0,z242,z1,z7,z3,z23]),(0,[z0,z359,z7,z4,z168,z5]),(0,[z0,z7,z177,z3,z5,z23])],[(0,[z28,z1,z771,z3,z4,z5]),(0,[z0,z1,z14,z81,z4,z5]),(0,[z0,z1,z7,z3,z223,z23])],[(0,[z0,z1,z572,z29,z3,z4]),(0,[z0,z1264,z7,z3,z4,z5]),(0,[z0,z1,z86,z21,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z1265]),(0,[z0,z1,z8,z3,z391,z5]),(0,[z0,z1,z7,z3,z1266,z5])],[(0,[z1,z7,z771,z3,z4,z5]),(0,[z0,z272,z14,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z23]),(0,[z0,z1,z7,z1267,z3,z5])],[(0,[z0,z1,z16,z29,z3,z289]),(0,[z0,z1,z1268,z3,z4,z5])],[(0,[z1,z274,z8,z3,z4,z5]),(0,[z0,z58,z7,z465,z4,z5]),(0,[z0,z1,z7,z1269,z4,z5])],[(0,[z0,z1270,z7,z3,z4,z5]),(0,[z0,z1,z14,z100,z3,z4]),(0,[z0,z473,z7,z291,z4,z5])],[(0,[z0,z1,z1271,z3,z4,z5]),(0,[z0,z1,z14,z29,z3,z4]),(0,[z38,z1,z771,z3,z4,z5]),(0,[z0,z1,z14,z3,z75,z23]),(0,[z0,z1,z7,z29,z126,z4]),(0,[z0,z1,z183,z3,z4,z793])],[(0,[z0,z1,z7,z724,z3,z4]),(0,[z0,z272,z7,z3,z4,z171])],[(0,[z116,z0,z239,z3,z4,z5]),(0,[z0,z1,z1059,z3,z4,z23]),(0,[z0,z868,z7,z3,z4,z5]),(0,[z0,z1,z7,z20,z201,z5]),(0,[z0,z1,z7,z1272,z3,z4]),(0,[z0,z1,z7,z220,z3,z23]),(0,[z0,z1,z1273,z3,z4,z5])],[(0,[z0,z1,z8,z3,z4,z174]),(0,[z0,z473,z7,z3,z4,z347]),(0,[z0,z1,z7,z597,z3,z23])],[(0,[z0,z473,z7,z81,z4,z5]),(0,[z0,z1,z7,z3,z316,z23]),(0,[z0,z269,z7,z33,z4,z5]),(0,[z0,z1,z7,z222,z168,z23])],[(0,[z0,z1,z7,z1274,z4,z5]),(0,[z488,z0,z1,z14,z3,z23]),(0,[z0,z1,z7,z1275,z3,z4]),(0,[z0,z7,z177,z3,z4,z23])],[(0,[z0,z1,z7,z100,z3,z23]),(0,[z0,z1,z3,z73,z563,z23])],[(0,[z0,z1,z7,z1276,z4,z5]),(0,[z11,z0,z69,z3,z4,z23]),(0,[z0,z1277,z7,z3,z4,z5]),(0,[z0,z1,z7,z20,z62,z311]),(0,[z0,z1,z7,z29,z3,z23])],[(0,[z0,z1,z14,z3,z4,z97]),(0,[z0,z1,z7,z3,z391,z52]),(0,[z0,z58,z285,z3,z4,z5]),(0,[z0,z1,z7,z465,z75,z23]),(1,[z0,z1,z3,z719,z5])],[(0,[z0,z1,z7,z3,z1118,z5]),(0,[z0,z1,z7,z84,z10,z5]),(0,[z0,z1,z963,z3,z4,z5]),(1,[z1,z7,z3,z4,z749]),(0,[z0,z1,z7,z20,z62,z23]),(0,[z0,z1,z3,z4,z1066,z23])]],
   [[(0,[z0,z1,z7,z3,z4,z1278]),(0,[z0,z1,z132,z3,z4,z186])],[(0,[z0,z1,z14,z4,z146,z5]),(0,[z0,z444,z7,z29,z3,z4])],[(0,[z0,z1,z7,z818,z3,z23]),(0,[z0,z1,z7,z157,z4,z23]),(0,[z0,z1,z7,z3,z4,z1279]),(0,[z0,z27,z7,z3,z4,z98]),(0,[z0,z1,z140,z7,z409,z4])],[(0,[z0,z510,z7,z3,z134,z5]),(0,[z0,z1,z433,z29,z3,z4]),(0,[z0,z1,z7,z1280,z4,z5]),(0,[z0,z1,z1281,z3,z4,z5]),(0,[z0,z1,z7,z3,z1282,z5])],[(0,[z0,z1,z240,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z150]),(0,[z0,z444,z330,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z793])],[(0,[z0,z1,z1283,z3,z4,z5]),(0,[z0,z1,z7,z247,z4,z23]),(0,[z0,z1,z1072,z3,z4,z23])],[(0,[z0,z1,z2,z3,z295,z5]),(0,[z0,z1284,z7,z3,z4,z5]),(0,[z0,z1,z7,z29,z60,z4])],[(0,[z1028,z0,z1,z8,z3,z5])],[(0,[z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z7,z3,z1285,z5]),(0,[z1,z8,z3,z4,z5,z459]),(0,[z152,z1,z7,z3,z50,z5]),(0,[z0,z1,z7,z3,z4,z1085]),(0,[z0,z1,z285,z29,z3,z4])],[(0,[z0,z510,z7,z29,z3,z4]),(0,[z0,z1,z7,z29,z3,z134]),(0,[z0,z7,z1286,z3,z4,z5]),(0,[z0,z1,z7,z220,z3,z283]),(0,[z0,z1,z7,z29,z1113,z4])],[(0,[z0,z102,z7,z185,z4,z5]),(0,[z0,z1,z7,z3,z1287,z5]),(0,[z0,z1,z7,z3,z507,z23]),(0,[z0,z1,z7,z1288,z3,z4]),(0,[z0,z509,z7,z3,z4,z98]),(0,[z0,z1,z7,z29,z1116,z4])],[(0,[z67,z360,z7,z3,z4,z68]),(0,[z0,z1,z7,z1289,z3,z5])],[(0,[z0,z1,z7,z3,z1290,z4]),(0,[z54,z0,z7,z3,z51,z546]),(0,[z0,z241,z7,z224,z4,z5])],[(0,[z0,z268,z14,z3,z4,z5]),(0,[z165,z1,z7,z66,z10,z5]),(0,[z165,z1,z7,z839,z4,z5]),(0,[z0,z1291,z7,z3,z4,z5]),(0,[z0,z58,z7,z3,z568,z5])],[(0,[z0,z1,z1292,z3,z4,z5]),(0,[z136,z1,z7,z3,z4,z355]),(0,[z0,z1,z7,z29,z3,z283]),(0,[z0,z1,z7,z320,z3,z5]),(0,[z0,z1,z7,z320,z225,z22])],[(0,[z1,z8,z3,z4,z479,z5]),(0,[z0,z1,z7,z831,z3,z23]),(0,[z0,z1293,z7,z3,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 494).take 487) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 981).take 447) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1428)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [494, 487, 447] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 127).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 127).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 247).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 368).take 111).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 479).take 33).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [127, 120, 121, 111, 33] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_36332

theorem PEqualNP.Outside.L_meta_36332 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277054112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36332.solve