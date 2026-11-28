import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42584

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
  Nat.testBit (4276813032 * 2 ^ 32 + 4276807680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x106221b018561b42#64 ++ 0x00106221b018561b#64 ++ 0x33e223f038fe3fbd#64 ++ 0x7833e223f038fe3f#64 : BitVec 256),
   (0x4500ec50cb32c514#64 ++ 0x084500ec50cb32c5#64 ++ 0xcd03fc71cf33c7fb#64 ++ 0xd8cd03fc71cf33c7#64 : BitVec 256),
   (0x0a0c36860dc36898#64 ++ 0x050a0c36860dc368#64 ++ 0x0e3c3f8e0fc3f8f7#64 ++ 0xef0e3c3f8e0fc3f8#64 : BitVec 256),
   (0xb037400b7001b6e0#64 ++ 0x12b037400b7001b6#64 ++ 0xf03fc00ff003ffef#64 ++ 0xb7f03fc00ff003ff#64 : BitVec 256),
   (0xef80000da6a80000#64 ++ 0x23ef80000da6a800#64 ++ 0xffc0000ffffc009f#64 ++ 0xbbffc0000ffffc00#64 : BitVec 256),
   (0xfffb9b6000000000#64 ++ 0x43fffb9b60000000#64 ++ 0xfffffff00000007f#64 ++ 0x47fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0fc3f8f7 0xef0e3c3f8e0fc3f8

def z1 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f038fe3fbd 0x7833e223f038fe3f

def z2 : W := mkw 0x4500cc50c330c514 0x084500cc50c330c5 0xcd03dc71c731c74a 0x90cd03dc71c731c7

def z3 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff003ffef 0xb7f03fc00ff003ff

def z4 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000ffffc009f 0xbbffc0000ffffc00

def z5 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff00000007f 0x47fffffff0000000

def z6 : W := mkw 0x0a08160405804018 0x050a081604058040 0x0c001c0007000000 0x000c001c00070000

def z7 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71cf33c7fb 0xd8cd03fc71cf33c7

def z8 : W := mkw 0x4f0cde46c7a1e49c 0x0d4f0cde46c7a1e4 0xcc1ddc0fc701c042 0x87cc1ddc0fc701c0

def z9 : W := mkw 0x0004000200012080 0x0000040002000120 0x003c000e0003f8e7 0xa7003c000e0003f8

def z10 : W := mkw 0x0a0836840dc24818 0x050a0836840dc248 0x0e003f800fc00010 0x480e003f800fc000

def z11 : W := mkw 0x0a00000404800000 0x010a000004048000 0x0e0000000fc00010 0x080e0000000fc000

def z12 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x003ffff000000060 0x44003ffff0000000

def z13 : W := mkw 0x4500c850c2308504 0x084500c850c23085 0xcd03fc71c030077b 0x50cd03fc71c03007

def z14 : W := mkw 0x106201a010441a42 0x00106201a010441a 0x32e0038030cc3804 0x2032e0038030cc38

def z15 : W := mkw 0x4500cc40c320c414 0x084500cc40c320c4 0xcc01dc01c701c042 0x80cc01dc01c701c0

def z16 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf3ffc00ff8ffffff 0xbff3ffc00ff8ffff

def z17 : W := mkw 0x4f0cfed6cff3ed9c 0x0d4f0cfed6cff3ed 0xcf3fffffcff3ffff 0xffcf3fffffcff3ff

def z18 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffffffffc00ff 0xfffffffffffffc00

def z19 : W := mkw 0x004001a000440802 0x00004001a0004408 0x02c0038000cc0000 0x0002c0038000cc00

def z20 : W := mkw 0xb037000b300132e0 0x12b037000b300132 0x303e000e30023fad 0x37303e000e30023f

def z21 : W := mkw 0xef999a4000000000 0x43ef999a40000000 0xffdddc000000005f 0x07ffdddc00000000

def z22 : W := mkw 0x000c368209436898 0x04000c3682094368 0x0c3c3f800f03f8f3 0xcc0c3c3f800f03f8

def z23 : W := mkw 0x0004400ff6a9b6e0 0x300004400ff6a9b6 0x0000000fffffff80 0xb80000000fffffff

def z24 : W := mkw 0x557bff70cb32c514 0x48557bff70cb32c5 0xcd3ffff1cf33c7fb 0xdccd3ffff1cf33c7

def z25 : W := mkw 0x1062013010141342 0x0010620130101413 0x31c20070303c0708 0x1031c20070303c07

def z26 : W := mkw 0x1a6e37b61dd77bda 0x051a6e37b61dd77b 0x3ffe3ffe3fffffff 0xff3ffe3ffe3fffff

def z27 : W := mkw 0x45c0896000000000 0x4045c08960000000 0x01c0007000000000 0x0001c00070000000

def z28 : W := mkw 0xb033400970009660 0x12b0334009700096 0xf003c001f0000708 0x10f003c001f00007

def z29 : W := mkw 0x0a0c36060d836098 0x050a0c36060d8360 0x0c1c3c0e0f03c0f3 0xcf0c1c3c0e0f03c0

def z30 : W := mkw 0x0000209018561b42 0x000000209018561b 0x0000000038fe3f80 0x380000000038fe3f

def z31 : W := mkw 0xfffbbbf018561b42 0x43fffbbbf018561b 0xfffffff038fe3fff 0x7ffffffff038fe3f

def z32 : W := mkw 0x000424860dc36898 0x04000424860dc368 0x0000000e0fc3f880 0xa80000000e0fc3f8

def z33 : W := mkw 0x0000000010001240 0x0000000000100012 0x0000000030023f80 0x300000000030023f

def z34 : W := mkw 0x1062012000000000 0x0010620120000000 0x002223f000000020 0x40002223f0000000

def z35 : W := mkw 0xfff3896000000000 0x43fff38960000000 0xffc3c0700000001f 0x03ffc3c070000000

def z36 : W := mkw 0x1062edf05956df56 0x081062edf05956df 0x0023fff00003ff60 0x400023fff00003ff

def z37 : W := mkw 0x004021b008560902 0x00004021b0085609 0x03c023f008fc0010 0x4803c023f008fc00

def z38 : W := mkw 0xa015400b6001a4a0 0x12a015400b6001a4 0xc01dc00fc001c042 0x87c01dc00fc001c0

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0xc003c0000000006b 0x00c003c000000000

def z40 : W := mkw 0xf533884000000000 0x02f5338840000000 0xfd3ffc700000007f 0x47fd3ffc70000000

def z41 : W := mkw 0xef80ec5defbac514 0x2bef80ec5defbac5 0xffc3fc7fffffc7ff 0xfbffc3fc7fffffc7

def z42 : W := mkw 0xb033000000000000 0x02b0330000000000 0xf03fc0000000006f 0x07f03fc000000000

def z43 : W := mkw 0xef88120da6a80000 0x23ef88120da6a800 0xfffc3f8ffffc00ff 0xfffffc3f8ffffc00

def z44 : W := mkw 0xef80000404800000 0x03ef800004048000 0xffc0000e0fc0009f 0xabffc0000e0fc000

def z45 : W := mkw 0x0000000da6a80000 0x200000000da6a800 0x0000000fc7000000 0x800000000fc70000

def z46 : W := mkw 0xba3f128f34c13ae8 0x17ba3f128f34c13a 0x323c038e30c03804 0x27323c038e30c038

def z47 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xcc3ffff000000062 0x47cc3ffff0000000

def z48 : W := mkw 0xbae201ad34cc1a42 0x23bae201ad34cc1a 0x32e0038e30cc3804 0x2332e0038e30cc38

def z49 : W := mkw 0x4fc89b6000000000 0x414fc89b60000000 0x0fc03ff000000010 0x400fc03ff0000000

def z50 : W := mkw 0xef999a4000000000 0x43ef999a40000000 0xcc1ddc0000000042 0x07cc1ddc00000000

def z51 : W := mkw 0x0000240009024010 0x0000002400090240 0x0c003c000f03c0f3 0xc80c003c000f03c0

def z52 : W := mkw 0x4500c850c2308504 0x084500c850c23085 0xc103c071c0300708 0x10c103c071c03007

def z53 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff0003f0c 0x37f03fc00ff0003f

def z54 : W := mkw 0xffffdb6b7001b6e0 0x53ffffdb6b7001b6 0xfffffffff003ffff 0xf7fffffffff003ff

def z55 : W := mkw 0x0000ec504912c514 0x080000ec504912c5 0x0003fc700003c760 0x400003fc700003c7

def z56 : W := mkw 0x0000208008420800 0x0000002080084208 0x0220238008c238b5 0x680220238008c238

def z57 : W := mkw 0x0a0c160605816098 0x050a0c1606058160 0x0c1c1c0e0701c042 0x870c1c1c0e0701c0

def z58 : W := mkw 0xfffbbfe40dc24818 0x47fffbbfe40dc248 0xfffffff00fc0007f 0x4ffffffff00fc000

def z59 : W := mkw 0xfffb132000000000 0x43fffb1320000000 0xfffc03800000001f 0x07fffc0380000000

def z60 : W := mkw 0x103740025001b6e0 0x10103740025001b6 0x003fc0000003ff60 0x04003fc0000003ff

def z61 : W := mkw 0xa000000920000000 0x02a0000009200000 0xf000000ff000008f 0xb3f000000ff00000

def z62 : W := mkw 0x4500ac508b324114 0x084500ac508b3241 0xcd003c71cf30009b 0xd8cd003c71cf3000

def z63 : W := mkw 0x0000208008420800 0x0000002080084208 0x0200238008c00010 0x480200238008c000

def z64 : W := mkw 0x5562edf0db76df56 0x085562edf0db76df 0xffe3fff1ffffffff 0xf8ffe3fff1ffffff

def z65 : W := mkw 0x000440024001a480 0x00000440024001a4 0xc03fc00fc003ffef 0xb7c03fc00fc003ff

def z66 : W := mkw 0xba3f528f74c1bee8 0x17ba3f528f74c1be 0xf23fc38ff0c3ffef 0xb7f23fc38ff0c3ff

def z67 : W := mkw 0x1062013010141342 0x0010620130101413 0x33e223f0303c073d 0x5033e223f0303c07

def z68 : W := mkw 0xefd99b6000000000 0x43efd99b60000000 0xcfddfff000000052 0x47cfddfff0000000

def z69 : W := mkw 0xffb7400ff6a9b6e0 0x33ffb7400ff6a9b6 0xfc3fc00ff703ffef 0xb7fc3fc00ff703ff

def z70 : W := mkw 0xfffbff7defbac514 0x6bfffbff7defbac5 0xffffffffffffc7ff 0xffffffffffffffc7

def z71 : W := mkw 0xb033000920000000 0x02b0330009200000 0xf03fc00ff00000ef 0xb7f03fc00ff00000

def z72 : W := mkw 0x4500000082200000 0x0045000000822000 0xc1000001c0300008 0x10c1000001c03000

def z73 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xcfc0000fcffc0012 0x8bcfc0000fcffc00

def z74 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcc03fc71c703c762 0xc0cc03fc71c703c7

def z75 : W := mkw 0xe591884000000000 0x42e5918840000000 0xc001c00000000000 0x00c001c000000000

def z76 : W := mkw 0xef8c368fafeb6898 0x27ef8c368fafeb68 0xfffc3f8ffffff8ff 0xfffffc3f8ffffff8

def z77 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff038fc00ff 0x7ffffffff038fc00

def z78 : W := mkw 0xf5f3a9f018561b42 0x42f5f3a9f018561b 0xf3e3e3f038fe3fbd 0x78f3e3e3f038fe3f

def z79 : W := mkw 0xf5f7c96b7001b6e0 0x52f5f7c96b7001b6 0xf1ffc07ff003ffef 0xb7f1ffc07ff003ff

def z80 : W := mkw 0xb037601b7813b7e0 0x12b037601b7813b7 0xf13fe07ff833ffff 0xfff13fe07ff833ff

def z81 : W := mkw 0x4500884082200000 0x0045008840822000 0xcd03fc71cf3000fb 0xd8cd03fc71cf3000

def z82 : W := mkw 0x106201b010541b42 0x00106201b010541b 0x33e203f030fc3f0c 0x3033e203f030fc3f

def z83 : W := mkw 0xffff9b6200012080 0x43ffff9b62000120 0xfffffffe0003f8ff 0xe7fffffffe0003f8

def z84 : W := mkw 0x000424860dc36898 0x04000424860dc368 0x0c003c0e0fc3f8f3 0xe80c003c0e0fc3f8

def z85 : W := mkw 0x0a0c128604c12888 0x050a0c128604c128 0x023c038e00c03804 0x27023c038e00c038

def z86 : W := mkw 0xffffbfe60dc36898 0x47ffffbfe60dc368 0xfffffffe0fc3f8ff 0xeffffffffe0fc3f8

def z87 : W := mkw 0xef80884da6a80000 0x23ef80884da6a800 0xffc3fc7ffffc00ff 0xfbffc3fc7ffffc00

def z88 : W := mkw 0xbafb132000000000 0x43bafb1320000000 0x32fc038000000004 0x0732fc0380000000

def z89 : W := mkw 0xef999a4da6a80000 0x63ef999a4da6a800 0xffdddc0ffffc00df 0xbfffdddc0ffffc00

def z90 : W := mkw 0xef80000486a80000 0x23ef80000486a800 0xffc000000ffc001f 0x0bffc000000ffc00

def z91 : W := mkw 0x000c368209436898 0x04000c3682094368 0x003c3f800003f860 0x44003c3f800003f8

def z92 : W := mkw 0xffe221b018561b42 0x03ffe221b018561b 0xffe223f038fe3fbf 0x7bffe223f038fe3f

def z93 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0c3c3f8e0703f862 0xc70c3c3f8e0703f8

def z94 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x33fffff00000007d 0x4433fffff0000000

def z95 : W := mkw 0x4500000082200000 0x0045000000822000 0xcd000001cf30009b 0x98cd000001cf3000

def z96 : W := mkw 0x4f80000486a80000 0x214f80000486a800 0x0fc000000ffc0010 0x080fc000000ffc00

def z97 : W := mkw 0x00006410cb32c514 0x0800006410cb32c5 0x00000001cf33c780 0x9800000001cf33c7

def z98 : W := mkw 0x0a08120000000000 0x010a081200000000 0x0e3c3f8000000077 0x470e3c3f80000000

def z99 : W := mkw 0x4500000082200000 0x0045000000822000 0xffc00001fffc009f 0xb8ffc00001fffc00

def z100 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0c1c1c0e0fc3f8c2 0xaf0c1c1c0e0fc3f8

def z101 : W := mkw 0x1062012000000000 0x0010620120000000 0x33e223f00000003d 0x4033e223f0000000

def z102 : W := mkw 0x0000000d24880000 0x200000000d248800 0x0000000e30cc0000 0x200000000e30cc00

def z103 : W := mkw 0x4504ec52cb33e594 0x084504ec52cb33e5 0xcd3ffc7fcf33ffff 0xffcd3ffc7fcf33ff

def z104 : W := mkw 0xfffb9b6404800000 0x43fffb9b64048000 0xfffffffe0fc000ff 0xeffffffffe0fc000

def z105 : W := mkw 0x0a00000404800000 0x010a000004048000 0x0e00000e0fc00097 0xab0e00000e0fc000

def z106 : W := mkw 0x0a4c37b60dd7699a 0x050a4c37b60dd769 0x0ffc3ffe0ffff8f7 0xef0ffc3ffe0ffff8

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x33c0000038fc009d 0x3833c0000038fc00

def z108 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xcc00000fc7000002 0x83cc00000fc70000

def z109 : W := mkw 0x1022209018561b42 0x001022209018561b 0x3022000038fe3fad 0x383022000038fe3f

def z110 : W := mkw 0x4fc8ff70cb32c514 0x494fc8ff70cb32c5 0xcfc3fff1cf33c7fb 0xd8cfc3fff1cf33c7

def z111 : W := mkw 0x1a7fbfe60dc36898 0x451a7fbfe60dc368 0x0e3ffffe0fc3f8f7 0xef0e3ffffe0fc3f8

def z112 : W := mkw 0x00199a4000000000 0x4000199a40000000 0x001ddc0000000040 0x04001ddc00000000

def z113 : W := mkw 0x4fc89b6486a80000 0x614fc89b6486a800 0x0fc03ff00ffc0010 0x480fc03ff00ffc00

def z114 : W := mkw 0xaa1d560f6581e4b8 0x17aa1d560f6581e4 0xcc1ddc0fc701c042 0x87cc1ddc0fc701c0

def z115 : W := mkw 0xffffffef7dc3fef8 0x57ffffffef7dc3fe 0xffffffffffc3ffff 0xffffffffffffc3ff

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001c000008b 0x90c0000001c00000

def z117 : W := mkw 0x000cfed24953ed9c 0x0c000cfed24953ed 0x003ffff00003ff60 0x44003ffff00003ff

def z118 : W := mkw 0xffe2012da6a80000 0x23ffe2012da6a800 0xffe223fffffc00bf 0xfbffe223fffffc00

def z119 : W := mkw 0x0000000da6a80000 0x200000000da6a800 0x0000000ffffc0080 0xb80000000ffffc00

def z120 : W := mkw 0xaa80000d24880000 0x23aa80000d248800 0x32c0000e30cc0004 0x2332c0000e30cc00

def z121 : W := mkw 0x4f089a4000000000 0x014f089a40000000 0xcf3ffff00000007f 0x47cf3ffff0000000

def z122 : W := mkw 0x0000201008120100 0x0000002010081201 0x0000000008320780 0x1800000000083207

def z123 : W := mkw 0xffb3000da6a80000 0x23ffb3000da6a800 0xffffc00ffffc00ff 0xbfffffc00ffffc00

def z124 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33c223f038fc0718 0x5833c223f038fc07

def z125 : W := mkw 0x1022208018421a40 0x001022208018421a 0x3222238038c23fbd 0x783222238038c23f

def z126 : W := mkw 0x0000201008120100 0x0000002010081201 0x01022070083207b9 0x5801022070083207

def z127 : W := mkw 0x0a0c36960dd36998 0x050a0c36960dd369 0x0f3e3ffe0ff3ffff 0xff0f3e3ffe0ff3ff

def z128 : W := mkw 0x0a0c7696cff3ed9c 0x0d0a0c7696cff3ed 0x0e3c3f8fcff3fff7 0xff0e3c3f8fcff3ff

def z129 : W := mkw 0x1a6e37a61dc77ada 0x051a6e37a61dc77a 0x3efc3f8e3fcff8f7 0xef3efc3f8e3fcff8

def z130 : W := mkw 0x004021b018561b42 0x00004021b018561b 0x03c023f038fe3f90 0x7803c023f038fe3f

def z131 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf003c00ff003ff88 0xb0f003c00ff003ff

def z132 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x023c3f8e00c3f864 0x67023c3f8e00c3f8

def z133 : W := mkw 0xffb7400ff6a9b6e0 0x33ffb7400ff6a9b6 0xffffc00fffffffff 0xbfffffc00fffffff

def z134 : W := mkw 0x000440025001b6e0 0x10000440025001b6 0x000000000003ff00 0x00000000000003ff

def z135 : W := mkw 0xf533ec50cb32c514 0x0af533ec50cb32c5 0xfd3ffc71cf33c7ff 0xdffd3ffc71cf33c7

def z136 : W := mkw 0x106261b058569f42 0x00106261b058569f 0xf3e3e3f1f8ffffff 0xf8f3e3e3f1f8ffff

def z137 : W := mkw 0x0000400040008400 0x0000004000400084 0xc003c001c003c7eb 0x90c003c001c003c7

def z138 : W := mkw 0xf537ec5bfb33f7f4 0x1af537ec5bfb33f7 0xfd3ffc7fff33ffff 0xfffd3ffc7fff33ff

def z139 : W := mkw 0xbaff13a604c12888 0x47baff13a604c128 0x32fc038e00c03804 0x2732fc038e00c038

def z140 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0x303c000ff003ff84 0xb7303c000ff003ff

def z141 : W := mkw 0x4500ecd0cb72cd14 0x084500ecd0cb72cd 0xcf23fff1cff3ffff 0xf8cf23fff1cff3ff

def z142 : W := mkw 0x106e37b219577bda 0x04106e37b219577b 0x003e3ff00003ff60 0x44003e3ff00003ff

def z143 : W := mkw 0xe580000da6a80000 0x22e580000da6a800 0xf1c0000ffffc0088 0xb8f1c0000ffffc00

def z144 : W := mkw 0xf5f3896000000000 0x42f5f38960000000 0xf1c3c07000000008 0x00f1c3c070000000

def z145 : W := mkw 0x5562ed70cb32c514 0x085562ed70cb32c5 0xffe3fff1cf33c7ff 0xd8ffe3fff1cf33c7

def z146 : W := mkw 0xa015400b7001b6e0 0x12a015400b7001b6 0xc01dc00ff003ffc2 0xb7c01dc00ff003ff

def z147 : W := mkw 0x4fc89b6000000000 0x414fc89b60000000 0xcfc3fff00000007b 0x40cfc3fff0000000

def z148 : W := mkw 0xfffb9b6082200000 0x43fffb9b60822000 0xfffffff1cf3000ff 0xdffffffff1cf3000

def z149 : W := mkw 0x0000240009024010 0x0000002400090240 0x0c003c000f000010 0x480c003c000f0000

def z150 : W := mkw 0xf5f3896000000000 0x42f5f38960000000 0xf1ffc0700000006f 0x07f1ffc070000000

def z151 : W := mkw 0x4504ecd6cff3ed9c 0x0c4504ecd6cff3ed 0xcd03fc7fcff3fffb 0xf8cd03fc7fcff3ff

def z152 : W := mkw 0x4500cc40c320c414 0x084500cc40c320c4 0xcd01dc01cf31c0db 0x98cd01dc01cf31c0

def z153 : W := mkw 0xfffbbbf018561b42 0x43fffbbbf018561b 0xfffffff000023f7f 0x47fffffff000023f

def z154 : W := mkw 0xb037000200012080 0x02b0370002000120 0xf03fc00e0003f8ef 0xa7f03fc00e0003f8

def z155 : W := mkw 0xaa80000d24880000 0x23aa80000d248800 0xf2c0000ff0cc008f 0xb3f2c0000ff0cc00

def z156 : W := mkw 0x4500ec504912c514 0x084500ec504912c5 0xcd03fc700003c77b 0x40cd03fc700003c7

def z157 : W := mkw 0xa004400b7001b6e0 0x12a004400b7001b6 0xf000000ff003ff8f 0xb3f000000ff003ff

def z158 : W := mkw 0x00046496cff3ed9c 0x0c00046496cff3ed 0x0000000fcff3ff80 0xb80000000fcff3ff

def z159 : W := mkw 0xf5fb9b6000000000 0x42f5fb9b60000000 0xf1fffff000000068 0x44f1fffff0000000

def z160 : W := mkw 0x4fccbfe60dc36898 0x454fccbfe60dc368 0x0ffc3ffe0fc3f8f7 0xef0ffc3ffe0fc3f8

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c0000008fc0010 0x0803c0000008fc00

def z162 : W := mkw 0xf537400bf221b6e0 0x12f537400bf221b6 0xfd3fc00fff33ffff 0xbffd3fc00fff33ff

def z163 : W := mkw 0x0a0c128604c12888 0x050a0c128604c128 0x0e3c038e0fc03897 0xaf0e3c038e0fc038

def z164 : W := mkw 0xfffb9b69a2280000 0x63fffb9b69a22800 0xfffffff1f03c007f 0x57fffffff1f03c00

def z165 : W := mkw 0x0a0c168605c16898 0x050a0c168605c168 0x0e3c1f8e07c1f846 0xa70e3c1f8e07c1f8

def z166 : W := mkw 0x4f80000486a80000 0x214f80000486a800 0x3fc000003ffc009d 0x383fc000003ffc00

def z167 : W := mkw 0x00004010c2308504 0x0800004010c23085 0x00000001c0300700 0x1000000001c03007

def z168 : W := mkw 0xba3f768f7dc3fef8 0x17ba3f768f7dc3fe 0xfe3fff8fffc3ffff 0xfffe3fff8fffc3ff

def z169 : W := mkw 0xb07761bb7857bfe2 0x12b07761bb7857bf 0xf3ffe3fff8ffffff 0xfff3ffe3fff8ffff

def z170 : W := mkw 0x106221b008560902 0x00106221b0085609 0x33e223f008fc003d 0x4833e223f008fc00

def z171 : W := mkw 0xfffbbf6009024010 0x43fffbbf60090240 0xfffffff00f03c0ff 0xcffffffff00f03c0

def z172 : W := mkw 0x4f8836848fea4818 0x254f8836848fea48 0x0fc03f800ffc0010 0x480fc03f800ffc00

def z173 : W := mkw 0xbafb9b6000000000 0x43bafb9b60000000 0x32fffff000000064 0x4732fffff0000000

def z174 : W := mkw 0x1a6221b41cd61b42 0x011a6221b41cd61b 0x3fe223fe3ffe3fbf 0xfb3fe223fe3ffe3f

def z175 : W := mkw 0x4f80000000000000 0x014f800000000000 0x0fc0000000000010 0x000fc00000000000

def z176 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xc103c071cf33c788 0x98c103c071cf33c7

def z177 : W := mkw 0x5562896000000000 0x0055628960000000 0xffe3fff00000007f 0x40ffe3fff0000000

def z178 : W := mkw 0xffe221bdbefe1b42 0x23ffe221bdbefe1b 0xffe223fffffe3fbf 0xfbffe223fffffe3f

def z179 : W := mkw 0xbae221bd3cde1b42 0x23bae221bd3cde1b 0x33e223fe38fe3fbd 0x7b33e223fe38fe3f

def z180 : W := mkw 0xba3f36860dc36898 0x07ba3f36860dc368 0xfe3fff8e0fc3f8ff 0xeffe3fff8e0fc3f8

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z182 : W := mkw 0xffb3400df6a89660 0x33ffb3400df6a896 0xffc3c00ffffc079f 0xbbffc3c00ffffc07

def z183 : W := mkw 0x0000209018561b42 0x000000209018561b 0x0102207038fe3fb9 0x780102207038fe3f

def z184 : W := mkw 0x0a00000404800000 0x010a000004048000 0x0c00000e07000002 0x830c00000e070000

def z185 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0x3fc0000e3ffc0014 0x2b3fc0000e3ffc00

def z186 : W := mkw 0xfffbdb6040008400 0x43fffbdb60400084 0xfffffff1c003c7ff 0xd7fffffff1c003c7

def z187 : W := mkw 0x557b9b6000000000 0x40557b9b60000000 0xcd3ffff00000007b 0x44cd3ffff0000000

def z188 : W := mkw 0x106225b019565b52 0x00106225b019565b 0x3fe23ff03fffffff 0xf83fe23ff03fffff

def z189 : W := mkw 0x4500ec40cb22c414 0x084500ec40cb22c4 0xcc01fc01cf03c0f3 0xc8cc01fc01cf03c0

def z190 : W := mkw 0xb033400970009660 0x12b0334009700096 0xf03fc001f000076f 0x17f03fc001f00007

def z191 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xffffffffc700007f 0xc7ffffffffc70000

def z192 : W := mkw 0xe500ec59eb32c514 0x0ae500ec59eb32c5 0xfd03fc7fff33c7ff 0xfbfd03fc7fff33c7

def z193 : W := mkw 0x4500ac4009024010 0x004500ac40090240 0xcd03fc700f03c0fb 0xc8cd03fc700f03c0

def z194 : W := mkw 0xef80201daeba0100 0x23ef80201daeba01 0xffc2207ffffe07bf 0xfbffc2207ffffe07

def z195 : W := mkw 0xbafb132000000000 0x43bafb1320000000 0x33fe23f00000003d 0x4733fe23f0000000

def z196 : W := mkw 0x4f0cbed68ff3699c 0x0d4f0cbed68ff369 0x0f3c3ffe0ff3f8f7 0xef0f3c3ffe0ff3f8

def z197 : W := mkw 0x0a08120404800000 0x010a081204048000 0x0e3c3f8e0fc000f7 0xef0e3c3f8e0fc000

def z198 : W := mkw 0x0a08128404c00808 0x050a08128404c008 0x0200038000c00000 0x000200038000c000

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x31c00000303c0008 0x1031c00000303c00

def z200 : W := mkw 0xaa8c128f24c92888 0x27aa8c128f24c928 0x32fc038e30cc3804 0x2732fc038e30cc38

def z201 : W := mkw 0xffe2edfdfffedf56 0x2bffe2edfdfffedf 0xffe3ffffffffffff 0xfbffe3ffffffffff

def z202 : W := mkw 0x0004609b7857bfe2 0x100004609b7857bf 0x0000000ff8ffff80 0xb80000000ff8ffff

def z203 : W := mkw 0x1062edf05956df56 0x081062edf05956df 0x33e3fff038fffffd 0x7833e3fff038ffff

def z204 : W := mkw 0xffffbff61dd77bda 0x47ffffbff61dd77b 0xfffffffe3fffffff 0xfffffffffe3fffff

def z205 : W := mkw 0xff3ffedffff3fffc 0x1fff3ffedffff3ff 0xff3ffffffff3ffff 0xffff3ffffffff3ff

def z206 : W := mkw 0x0004000200012080 0x0000040002000120 0x003c00000003f860 0x04003c00000003f8

def z207 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x002223f000023f20 0x40002223f000023f

def z208 : W := mkw 0xbaff132b300132e0 0x53baff132b300132 0x32fc038e30003804 0x2732fc038e300038

def z209 : W := mkw 0xef80240dafaa4010 0x23ef80240dafaa40 0xffc03c0fffffc0ff 0xfbffc03c0fffffc0

def z210 : W := mkw 0xfff761bffeffbfe2 0x33fff761bffeffbf 0xffffe3ffffffffff 0xffffffe3ffffffff

def z211 : W := mkw 0x4fc021b48efe0902 0x214fc021b48efe09 0x0fc023f00ffc0010 0x480fc023f00ffc00

def z212 : W := mkw 0xe5000009a2200000 0x02e5000009a22000 0xfd00000fff30009f 0xbbfd00000fff3000

def z213 : W := mkw 0x106265b0db76df56 0x08106265b0db76df 0x33e223f1ffffffbd 0xf833e223f1ffffff

def z214 : W := mkw 0xef80000000000000 0x03ef800000000000 0xffc000000000001f 0x03ffc00000000000

def z215 : W := mkw 0x45006410cb32c514 0x0845006410cb32c5 0xcd000001cf33c79b 0x98cd000001cf33c7

def z216 : W := mkw 0x4f889a4000000000 0x414f889a40000000 0x0c001c0000000000 0x000c001c00000000

def z217 : W := mkw 0x1073896000000000 0x4010738960000000 0x0003c07000000000 0x000003c070000000

def z218 : W := mkw 0x5562ed70db36d756 0x085562ed70db36d7 0xfdc3fc71ff3fc7fb 0xd8fdc3fc71ff3fc7

def z219 : W := mkw 0xe5800009a2280000 0x22e5800009a22800 0xf1c00001f03c0008 0x10f1c00001f03c00

def z220 : W := mkw 0xfffbbbf008560902 0x43fffbbbf0085609 0xfffffff008fc007f 0x4ffffffff008fc00

def z221 : W := mkw 0xb07761bb7857bfe2 0x12b07761bb7857bf 0xf03fe3fff003ffef 0xf7f03fe3fff003ff

def z222 : W := mkw 0xba3f368f3dc37af8 0x17ba3f368f3dc37a 0x3e3c3f8e3fc3f8f7 0xef3e3c3f8e3fc3f8

def z223 : W := mkw 0x0a0836840dc24818 0x050a0836840dc248 0x0e3c3f800fc00077 0x4f0e3c3f800fc000

def z224 : W := mkw 0xfff3896da6a80000 0x63fff3896da6a800 0xffc3c07ffffc009f 0xbbffc3c07ffffc00

def z225 : W := mkw 0x107761b25857bfe2 0x10107761b25857bf 0x003fe3f00003ff60 0x44003fe3f00003ff

def z226 : W := mkw 0xfffb9b6486a80000 0x63fffb9b6486a800 0xfffffff00ffc007f 0x4ffffffff00ffc00

def z227 : W := mkw 0x0a0424860dc36898 0x050a0424860dc368 0x0e00000e0fc3f897 0xab0e00000e0fc3f8

def z228 : W := mkw 0x0000040001004010 0x0000000400010040 0x0c001c000701c042 0x800c001c000701c0

def z229 : W := mkw 0x0004040605816098 0x0400040406058160 0x0000000e0701c000 0x800000000e0701c0

def z230 : W := mkw 0x1037ec525913f7f4 0x181037ec525913f7 0x003ffc700003ff60 0x44003ffc700003ff

def z231 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x002223f038fe3fa0 0x78002223f038fe3f

def z232 : W := mkw 0x4500884000000000 0x0045008840000000 0xcd03fc700000007b 0x40cd03fc70000000

def z233 : W := mkw 0xa004000b20012080 0x02a004000b200120 0xf03c000ff003f8ef 0xb7f03c000ff003f8

def z234 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd01fc71cf31c052 0xc8cd01fc71cf31c0

def z235 : W := mkw 0x000064104912c514 0x08000064104912c5 0x000000000003c700 0x00000000000003c7

def z236 : W := mkw 0xfffb132da6a80000 0x63fffb132da6a800 0xfffc038ffffc009f 0xbffffc038ffffc00

def z237 : W := mkw 0x0000884000000000 0x0000008840000000 0x0003fc7000000060 0x400003fc70000000

def z238 : W := mkw 0xffe2013db6bc1342 0x23ffe2013db6bc13 0xffc2007ffffc079f 0xbbffc2007ffffc07

def z239 : W := mkw 0xb0f3012000000000 0x42b0f30120000000 0x30c0000000000000 0x0030c00000000000

def z240 : W := mkw 0x4500ac508b324114 0x084500ac508b3241 0x0d003c700f300010 0x480d003c700f3000

def z241 : W := mkw 0xb037000b300132e0 0x12b037000b300132 0x303c000e30003804 0x27303c000e300038

def z242 : W := mkw 0x0a0c120200012080 0x010a0c1202000120 0x0e3c3f8e0003f8f7 0xe70e3c3f8e0003f8

def z243 : W := mkw 0x0004400b7001b6e0 0x100004400b7001b6 0x0000000ff003ff80 0xb00000000ff003ff

def z244 : W := mkw 0x000064004902c410 0x00000064004902c4 0xcc03fc01cf03c7fb 0xd8cc03fc01cf03c7

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000008300099 0x1801000000083000

def z246 : W := mkw 0x0000cc404100c414 0x080000cc404100c4 0x0001dc000001c040 0x000001dc000001c0

def z247 : W := mkw 0x5fe221b49efe1b42 0x215fe221b49efe1b 0x3fe223f03ffe3fbd 0x783fe223f03ffe3f

def z248 : W := mkw 0x1a6e13a614c53aca 0x051a6e13a614c53a 0x32fc038e30cc3804 0x2732fc038e30cc38

def z249 : W := mkw 0xb033400970009660 0x12b0334009700096 0xf003c001f003c7eb 0x90f003c001f003c7

def z250 : W := mkw 0xef9d9e4605816098 0x47ef9d9e46058160 0xcc1ddc0e0701c042 0x87cc1ddc0e0701c0

def z251 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xc03fc00fc003ff62 0x87c03fc00fc003ff

def z252 : W := mkw 0x1037400b7001b6e0 0x101037400b7001b6 0x003fc00ff003ffe0 0xb4003fc00ff003ff

def z253 : W := mkw 0x103f76825943fef8 0x14103f76825943fe 0x003fff800003ff60 0x44003fff800003ff

def z254 : W := mkw 0x0a0c32860cc32888 0x050a0c32860cc328 0x023c238e08c238b5 0x6f023c238e08c238

def z255 : W := mkw 0xfffffbfb7857bfe2 0x53fffffbfb7857bf 0xfffffffff8ffffff 0xfffffffffff8ffff

def z256 : W := mkw 0x0a08328008420800 0x010a083280084208 0x0e3c3f8008c238f7 0x6f0e3c3f8008c238

def z257 : W := mkw 0xfffb9b6920000000 0x43fffb9b69200000 0xfffffffff00000ff 0xf7fffffffff00000

def z258 : W := mkw 0xfffbdf60c320c414 0x4bfffbdf60c320c4 0xfffffff1c701c07f 0xc7fffffff1c701c0

def z259 : W := mkw 0xb03740025001b6e0 0x12b03740025001b6 0xf03fc0000003ff6f 0x07f03fc0000003ff

def z260 : W := mkw 0x0004000200012080 0x0000040002000120 0x0000000e0003f880 0xa00000000e0003f8

def z261 : W := mkw 0xffbf768fffebfef8 0x37ffbf768fffebfe 0xffffff8fffffffff 0xffffffff8fffffff

def z262 : W := mkw 0xb03f768b7943fef8 0x16b03f768b7943fe 0xf03fff8ff003ffef 0xf7f03fff8ff003ff

def z263 : W := mkw 0x000024108b324114 0x08000024108b3241 0x000000000f300000 0x08000000000f3000

def z264 : W := mkw 0x0a0cfed64dd3ed9c 0x0d0a0cfed64dd3ed 0x0e3ffffe0fc3fff7 0xef0e3ffffe0fc3ff

def z265 : W := mkw 0xfffbbbe008420800 0x43fffbbbe0084208 0xfffffff008c238ff 0x6ffffffff008c238

def z266 : W := mkw 0xa011000000000000 0x02a0110000000000 0xc01dc00000000042 0x07c01dc000000000

def z267 : W := mkw 0xaa80000da6a80000 0x23aa80000da6a800 0x32c0000ffffc0084 0xbb32c0000ffffc00

def z268 : W := mkw 0x1062013010141342 0x0010620130101413 0x33c2007038fc079d 0x3833c2007038fc07

def z269 : W := mkw 0x1a2e36861dc37ad8 0x051a2e36861dc37a 0x3e3e3f8e3fc3ffff 0xff3e3e3f8e3fc3ff

def z270 : W := mkw 0xffffdb6ff6a9b6e0 0x73ffffdb6ff6a9b6 0xffffffffffffffff 0xffffffffffffffff

def z271 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x302223f030023fad 0x70302223f030023f

def z272 : W := mkw 0x1a7b9b6000000000 0x411a7b9b60000000 0x0e3ffff000000077 0x470e3ffff0000000

def z273 : W := mkw 0x0000000da6a80000 0x200000000da6a800 0x33c0000ffffc009d 0xb833c0000ffffc00

def z274 : W := mkw 0x4500000082200000 0x0045000000822000 0x0d0000000f300010 0x080d0000000f3000

def z275 : W := mkw 0x106e37b219577bda 0x04106e37b219577b 0x33fe3ff038fffffd 0x7c33fe3ff038ffff

def z276 : W := mkw 0x0004240209036090 0x0000042402090360 0x0c3c3c0e0f03f8f7 0xef0c3c3c0e0f03f8

def z277 : W := mkw 0x0000209018561b42 0x000000209018561b 0x0000000000023f00 0x000000000000023f

def z278 : W := mkw 0x0004000b300132e0 0x100004000b300132 0x0000000e30003800 0x200000000e300038

def z279 : W := mkw 0xbaff37a60dc36898 0x47baff37a60dc368 0x3efc3f8e0fc3f8f7 0xef3efc3f8e0fc3f8

def z280 : W := mkw 0x0000001000100100 0x0000000010001001 0x0102007000300708 0x1001020070003007

def z281 : W := mkw 0xef8c128fa6e92888 0x27ef8c128fa6e928 0xfffc038ffffc389f 0xbffffc038ffffc38

def z282 : W := mkw 0x5562a9f018561b42 0x005562a9f018561b 0xffe3fff038fe3fff 0x78ffe3fff038fe3f

def z283 : W := mkw 0x4500c84040008400 0x004500c840400084 0xcd03fc71c003c7fb 0xd0cd03fc71c003c7

def z284 : W := mkw 0x0008368009424818 0x0400083680094248 0x00003f8000000000 0x4000003f80000000

def z285 : W := mkw 0x000c368209436898 0x04000c3682094368 0x023c3f8008c3f8f5 0x6c023c3f8008c3f8

def z286 : W := mkw 0x5562edf0db76df56 0x085562edf0db76df 0xcd23fff1cf33fffb 0xd8cd23fff1cf33ff

def z287 : W := mkw 0x4f0cbec60dc36898 0x054f0cbec60dc368 0xcf3ffffe0fc3f8ff 0xefcf3ffffe0fc3f8

def z288 : W := mkw 0xb07fdb6b7001b6e0 0x52b07fdb6b7001b6 0xf03ffffff003ffef 0xf7f03ffffff003ff

def z289 : W := mkw 0xef80c85de6b88504 0x2bef80c85de6b885 0xffc3c07ffffc079f 0xbbffc3c07ffffc07

def z290 : W := mkw 0xffa2000db6a81240 0x23ffa2000db6a812 0xffe2000ffffe3fbf 0xbbffe2000ffffe3f

def z291 : W := mkw 0x00006410cb32c514 0x0800006410cb32c5 0x01022071cf33c7b9 0xd801022071cf33c7

def z292 : W := mkw 0xfffbbf708b324114 0x4bfffbbf708b3241 0xfffffff00f30007f 0x4ffffffff00f3000

def z293 : W := mkw 0x4500c840c2208404 0x084500c840c22084 0xc001c001c0000000 0x00c001c001c00000

def z294 : W := mkw 0x5562e9f0da769f46 0x085562e9f0da769f 0xf3e3e3f1f8fe3fbd 0x78f3e3e3f1f8fe3f

def z295 : W := mkw 0x4500a85008120100 0x004500a850081201 0xcd03fc70083207fb 0x58cd03fc70083207

def z296 : W := mkw 0x4500884000000000 0x0045008840000000 0xc103c07000000008 0x00c103c070000000

def z297 : W := mkw 0xbafb13a010441a42 0x43bafb13a010441a 0x32fc038030cc3804 0x2732fc038030cc38

def z298 : W := mkw 0xb033000010001240 0x02b0330000100012 0xf03fc00030023fef 0x37f03fc00030023f

def z299 : W := mkw 0xef80400de6a88400 0x23ef80400de6a884 0xffc3c00fffffc7ff 0xbbffc3c00fffffc7

def z300 : W := mkw 0xef80cc4de7a8c414 0x2bef80cc4de7a8c4 0xffc1dc0ffffdc0df 0xbbffc1dc0ffffdc0

def z301 : W := mkw 0x450020108a320100 0x00450020108a3201 0xcd022071cf3207bb 0xd8cd022071cf3207

def z302 : W := mkw 0x107bff704912c514 0x48107bff704912c5 0x003ffff00003c760 0x44003ffff00003c7

def z303 : W := mkw 0x0000240009024010 0x0000002400090240 0x00003c000003c060 0x4000003c000003c0

def z304 : W := mkw 0xfffbdb70c2308504 0x4bfffbdb70c23085 0xfffffff1c030077f 0x57fffffff1c03007

def z305 : W := mkw 0x1062013010141342 0x0010620130101413 0x0002007000000700 0x0000020070000007

def z306 : W := mkw 0xef999a4000000000 0x43ef999a40000000 0xcd1ffc700000007b 0x47cd1ffc70000000

def z307 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xfc00000ff700008f 0xb3fc00000ff70000

def z308 : W := mkw 0xef95400fe6a9a4a0 0x33ef95400fe6a9a4 0xffddc00ffffdc0df 0xbfffddc00ffffdc0

def z309 : W := mkw 0x4fc8bf708b324114 0x494fc8bf708b3241 0x0fc03ff00f300010 0x480fc03ff00f3000

def z310 : W := mkw 0x00006490db76df56 0x0800006490db76df 0x00000001ffffff80 0xb800000001ffffff

def z311 : W := mkw 0x0000000000000000 0x0000000000000000 0x32c0000030cc0004 0x2032c0000030cc00

def z312 : W := mkw 0x0000400040008400 0x0000004000400084 0xc001c001c001c042 0x80c001c001c001c0

def z313 : W := mkw 0x1022000010001240 0x0010220000100012 0x33e2000038fe3fbd 0x3833e2000038fe3f

def z314 : W := mkw 0xa000000da6a80000 0x22a000000da6a800 0xf000000ffffc008f 0xbbf000000ffffc00

def z315 : W := mkw 0xb077412b7001b6e0 0x12b077412b7001b6 0xf3ffe3fff003ffff 0xf7f3ffe3fff003ff

def z316 : W := mkw 0x1033400050009660 0x1010334000500096 0x0003c00000000700 0x000003c000000007

def z317 : W := mkw 0xe515ec5beb33e5b4 0x1ae515ec5beb33e5 0xcd1ffc7fcf33c7fb 0xdfcd1ffc7fcf33c7

def z318 : W := mkw 0xa000000920000000 0x02a0000009200000 0xc000000fc0000002 0x83c000000fc00000

def z319 : W := mkw 0x00489b6000000000 0x4000489b60000000 0x00003ff000000000 0x4000003ff0000000

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c0000000f000093 0x880c0000000f0000

def z321 : W := mkw 0xf533c859f2309764 0x1af533c859f23097 0xf103c071f0300708 0x10f103c071f03007

def z322 : W := mkw 0x4f80000486a80000 0x214f80000486a800 0x0fc0000e0ffc0097 0xab0fc0000e0ffc00

def z323 : W := mkw 0xfffb9b6d24880000 0x63fffb9b6d248800 0xfffffffe30cc007f 0x67fffffffe30cc00

def z324 : W := mkw 0x1062213008120100 0x0010622130081201 0x33e223f0083207bd 0x5833e223f0083207

def z325 : W := mkw 0x1033000000000000 0x0010330000000000 0x003fc00000000060 0x04003fc000000000

def z326 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71cf300718 0x58cd03fc71cf3007

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x00020000000207a9 0x1000020000000207

def z328 : W := mkw 0x5ffb9b6000000000 0x415ffb9b60000000 0x0ffffff000000070 0x440ffffff0000000

def z329 : W := mkw 0x0040013000140102 0x0000400130001401 0x01c00070003c0000 0x0001c00070003c00

def z330 : W := mkw 0x4500cc40c320c414 0x084500cc40c320c4 0xcc03dc01c703c7eb 0x90cc03dc01c703c7

def z331 : W := mkw 0x107761b25857bfe2 0x10107761b25857bf 0x33ffe3f038fffffd 0x7c33ffe3f038ffff

def z332 : W := mkw 0xaa80000d24880000 0x23aa80000d248800 0x33c0000e38fc009d 0x3b33c0000e38fc00

def z333 : W := mkw 0x0008120000000000 0x0000081200000000 0x003c3f8000000060 0x44003c3f80000000

def z334 : W := mkw 0x4580000082280000 0x2045800000822800 0x01c00000003c0000 0x0001c00000003c00

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x33c000000000001d 0x0033c00000000000

def z336 : W := mkw 0x00006410cb32c514 0x0800006410cb32c5 0xc003c001cf33c7eb 0x98c003c001cf33c7

def z337 : W := mkw 0x4fc89b6000000000 0x414fc89b60000000 0x0ffc3ff000000077 0x470ffc3ff0000000

def z338 : W := mkw 0x0004248209436898 0x0400042482094368 0x000000000003f800 0x00000000000003f8

def z339 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf01fc00ff001c74a 0x97f01fc00ff001c7

def z340 : W := mkw 0xb06221b938561b42 0x02b06221b938561b 0xf3e223fff8fe3fbf 0xfbf3e223fff8fe3f

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000008c00095 0x280200000008c000

def z342 : W := mkw 0x106661bb7857bfe2 0x10106661bb7857bf 0x33e223fff8ffffbd 0xf833e223fff8ffff

def z343 : W := mkw 0xef8c160fa7a96098 0x27ef8c160fa7a960 0xcc1c1c0fc701c042 0x87cc1c1c0fc701c0

def z344 : W := mkw 0x4500ac508b324114 0x084500ac508b3241 0x0d023c700f3207b9 0x580d023c700f3207

def z345 : W := mkw 0xb022000930001240 0x02b0220009300012 0xf022000ff0023faf 0xb3f022000ff0023f

def z346 : W := mkw 0x0000201008120100 0x0000002010081201 0x0100207008300010 0x4801002070083000

def z347 : W := mkw 0x1062012000000000 0x0010620120000000 0x32e0038000000004 0x0032e00380000000

def z348 : W := mkw 0x0000000082200000 0x0000000000822000 0x00000001cf300080 0x9800000001cf3000

def z349 : W := mkw 0x0a08120000000000 0x010a081200000000 0x023c038000000004 0x07023c0380000000

def z350 : W := mkw 0xef84248fafeb6898 0x27ef84248fafeb68 0xffc0000ffffff89f 0xbbffc0000ffffff8

def z351 : W := mkw 0x0004400b7001b6e0 0x100004400b7001b6 0xc003c00ff003ffeb 0xb0c003c00ff003ff

def z352 : W := mkw 0x45004000c2208400 0x0045004000c22084 0xcd03c001cf33c7fb 0x98cd03c001cf33c7

def z353 : W := mkw 0x1a3f76865dc3fef8 0x151a3f76865dc3fe 0x0e3fff8e0fc3fff7 0xef0e3fff8e0fc3ff

def z354 : W := mkw 0xf537cc4bf321f6f4 0x1af537cc4bf321f6 0xfc3fdc0ff703ffef 0xb7fc3fdc0ff703ff

def z355 : W := mkw 0x4f80000486a80000 0x214f80000486a800 0x0c00000007000000 0x000c000000070000

def z356 : W := mkw 0xefc021bdaefe0902 0x23efc021bdaefe09 0xffc023fffffc009f 0xfbffc023fffffc00

def z357 : W := mkw 0xb037640b7903f6f0 0x12b037640b7903f6 0xfc3ffc0fff03ffff 0xfffc3ffc0fff03ff

def z358 : W := mkw 0x0000ac5009124114 0x080000ac50091241 0x00003c7000000000 0x4000003c70000000

def z359 : W := mkw 0x0a00000404800000 0x010a000004048000 0x3fc0000e3ffc009f 0xbb3fc0000e3ffc00

def z360 : W := mkw 0x1022000010001240 0x0010220000100012 0x3022000030023fad 0x303022000030023f

def z361 : W := mkw 0xef99fe50cb32c514 0x4bef99fe50cb32c5 0xcd1ffc71cf33c7fb 0xdfcd1ffc71cf33c7

def z362 : W := mkw 0xf5f38969a2280000 0x62f5f38969a22800 0xf1c3c071f03c0008 0x10f1c3c071f03c00

def z363 : W := mkw 0xb073413970149762 0x12b0734139701497 0xf1c3c071f03c0708 0x10f1c3c071f03c07

def z364 : W := mkw 0x0a0c160605816098 0x050a0c1606058160 0x0c3c1c0e0703f8e7 0xa70c3c1c0e0703f8

def z365 : W := mkw 0x0a04000604812080 0x010a040006048120 0x0e3c000e0fc3f8f7 0xaf0e3c000e0fc3f8

def z366 : W := mkw 0xffffbfefafeb6898 0x67ffffbfefafeb68 0xfffffffffffff8ff 0xfffffffffffffff8

def z367 : W := mkw 0x107fdb625001b6e0 0x50107fdb625001b6 0x003ffff00003ff60 0x44003ffff00003ff

def z368 : W := mkw 0xf5f3c970c2308504 0x4af5f3c970c23085 0xf1c3c071c0300708 0x10f1c3c071c03007

def z369 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xf3ffc3f00000000c 0x07f3ffc3f0000000

def z370 : W := mkw 0x103740025001b6e0 0x10103740025001b6 0x303fc0003003ffed 0x34303fc0003003ff

def z371 : W := mkw 0xb037000b300132e0 0x12b037000b300132 0xf03c000ff000388f 0xb7f03c000ff00038

def z372 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xce00000fcfc00097 0xabce00000fcfc000

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000003000008d 0x3030000000300000

def z374 : W := mkw 0x0a0c76864dc3ec98 0x050a0c76864dc3ec 0xce3fff8fcfc3ffff 0xffce3fff8fcfc3ff

def z375 : W := mkw 0xef80ac5dafba4114 0x2bef80ac5dafba41 0xffc03c7ffffc009f 0xfbffc03c7ffffc00

def z376 : W := mkw 0x0000641defbac514 0x280000641defbac5 0x0000000fffffc780 0xb80000000fffffc7

def z377 : W := mkw 0xef80641defbac514 0x2bef80641defbac5 0xffc0000fffffc79f 0xbbffc0000fffffc7

def z378 : W := mkw 0xf537c85bf231b7e4 0x1af537c85bf231b7 0xf13fc07ff033ffef 0xb7f13fc07ff033ff

def z379 : W := mkw 0x0000c85040108504 0x080000c850401085 0x0003c07000000700 0x000003c070000007

def z380 : W := mkw 0xbafb33b018561b42 0x43bafb33b018561b 0x33fe23f038fe3fbd 0x7f33fe23f038fe3f

def z381 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0x303fc00e3003ff64 0x27303fc00e3003ff

def z382 : W := mkw 0x0000008000400800 0x0000000080004008 0x0220038000c03804 0x200220038000c038

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000038fc0080 0x380000000038fc00

def z384 : W := mkw 0x004021b008560902 0x00004021b0085609 0x03c223f008fe07b9 0x5803c223f008fe07

def z385 : W := mkw 0x0a0c768f7dc3fef8 0x150a0c768f7dc3fe 0x0e3c3f8fffc3fff7 0xff0e3c3f8fffc3ff

def z386 : W := mkw 0x0a00000404800000 0x010a000004048000 0x0200000e00c00004 0x230200000e00c000

def z387 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x022223f008c23fb5 0x68022223f008c23f

def z388 : W := mkw 0xb037641bfb33f7f4 0x1ab037641bfb33f7 0xf03fc00fff33ffef 0xbff03fc00fff33ff

def z389 : W := mkw 0xf533ec59fb32d774 0x1af533ec59fb32d7 0xfd03fc71ff33c7fb 0xd8fd03fc71ff33c7

def z390 : W := mkw 0xfffb9b6010001240 0x43fffb9b60100012 0xfffffff030023fff 0x77fffffff030023f

def z391 : W := mkw 0x0004208208432880 0x0000042082084328 0x023c238e08c3f8f7 0xef023c238e08c3f8

def z392 : W := mkw 0xfffbff70cb32c514 0x4bfffbff70cb32c5 0xfffffff1cf33c7ff 0xdffffffff1cf33c7

def z393 : W := mkw 0x4500000da6a80000 0x204500000da6a800 0xcd00000ffffc009b 0xb8cd00000ffffc00

def z394 : W := mkw 0x000c368209436898 0x04000c3682094368 0x003c3f8e0003f8e7 0xe7003c3f8e0003f8

def z395 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x32e0038038fe3f84 0x3832e0038038fe3f

def z396 : W := mkw 0x1062213018161342 0x0010622130181613 0x31c22070383e07b9 0x5831c22070383e07

def z397 : W := mkw 0x106201a010441a42 0x00106201a010441a 0x33e0038038fc389d 0x3833e0038038fc38

def z398 : W := mkw 0xba7f77bf7dd7fffa 0x17ba7f77bf7dd7ff 0xffffffffffffffff 0xffffffffffffffff

def z399 : W := mkw 0xfffbbb7008120100 0x43fffbbb70081201 0xfffffff0083207ff 0x5ffffffff0083207

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c000000000067 0x07003c0000000000

def z401 : W := mkw 0xef80208daeea0800 0x23ef80208daeea08 0xffe0238ffffe38bf 0xfbffe0238ffffe38

def z402 : W := mkw 0x0ac8132000000000 0x410ac81320000000 0x02c0038000000000 0x0002c00380000000

def z403 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x012223f008323fb9 0x58012223f008323f

def z404 : W := mkw 0x0a4837b40dd6491a 0x050a4837b40dd649 0x0fc03ff00ffc0010 0x480fc03ff00ffc00

def z405 : W := mkw 0x000024840dc24818 0x04000024840dc248 0x000000000fc00000 0x08000000000fc000

def z406 : W := mkw 0xba3f560f7581f6f8 0x17ba3f560f7581f6 0xfc3fdc0ff703ffef 0xb7fc3fdc0ff703ff

def z407 : W := mkw 0xb033000930001260 0x12b0330009300012 0x3000000030000000 0x0030000000300000

def z408 : W := mkw 0xb037400ff6a9b6e0 0x32b037400ff6a9b6 0xf03fc00fffffffef 0xbff03fc00fffffff

def z409 : W := mkw 0xef999a4000000000 0x43ef999a40000000 0xce3dff8000000077 0x47ce3dff80000000

def z410 : W := mkw 0xb033000000000000 0x02b0330000000000 0xf003c00000000008 0x00f003c000000000

def z411 : W := mkw 0x0000209dbefe1b42 0x200000209dbefe1b 0x0000000ffffe3f80 0xb80000000ffffe3f

def z412 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xffc3fc71ffffc7ff 0xf8ffc3fc71ffffc7

def z413 : W := mkw 0x4f80000486a80000 0x214f80000486a800 0xcfc00001cffc009b 0x98cfc00001cffc00

def z414 : W := mkw 0x4f8c36868feb6898 0x254f8c36868feb68 0x0ffc3f8e0ffff8f7 0xef0ffc3f8e0ffff8

def z415 : W := mkw 0x1062012000000000 0x0010620120000000 0x31c2007000000008 0x0031c20070000000

def z416 : W := mkw 0xba3b120000000000 0x03ba3b1200000000 0xfe3fff800000007f 0x47fe3fff80000000

def z417 : W := mkw 0x00006410cb32c514 0x0800006410cb32c5 0x0c003c01cf33c7f3 0xd80c003c01cf33c7

def z418 : W := mkw 0xef80000920000000 0x03ef800009200000 0xffc0000ff000009f 0xb3ffc0000ff00000

def z419 : W := mkw 0x4500ac508b324114 0x084500ac508b3241 0x0d003c700f33c0f3 0xc80d003c700f33c0

def z420 : W := mkw 0x0a08360009024010 0x010a083600090240 0x0e3c3f800f03c0f7 0xcf0e3c3f800f03c0

def z421 : W := mkw 0x1062012000000000 0x0010620120000000 0x33e223f038fc00bd 0x7833e223f038fc00

def z422 : W := mkw 0x1062012010041242 0x0010620120100412 0x30c00000300c0000 0x0030c00000300c00

def z423 : W := mkw 0x0000001010141342 0x0000000010101413 0x00000000303c0700 0x1000000000303c07

def z424 : W := mkw 0x4f08fe50cb32c514 0x094f08fe50cb32c5 0xcf3ffff1cf33c7ff 0xdfcf3ffff1cf33c7

def z425 : W := mkw 0xb033400040008400 0x02b0334000400084 0xf03fc001c003c7ef 0x97f03fc001c003c7

def z426 : W := mkw 0xa000000000000000 0x02a0000000000000 0xf00000000000000f 0x03f0000000000000

def z427 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfddfdc700000004a 0x07fddfdc70000000

def z428 : W := mkw 0xb037648f7dc3fef8 0x16b037648f7dc3fe 0xf03fc00fffc3ffef 0xbff03fc00fffc3ff

def z429 : W := mkw 0x0000601048128500 0x0000006010481285 0xc103e071c833c7fb 0xd8c103e071c833c7

def z430 : W := mkw 0x0000201008120100 0x0000002010081201 0x0002207000020720 0x4000022070000207

def z431 : W := mkw 0x106201a010441a42 0x00106201a010441a 0x0020038000003800 0x0000200380000038

def z432 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xcc00000ffffc0082 0xbbcc00000ffffc00

def z433 : W := mkw 0x004021b008560902 0x00004021b0085609 0x33c023f038fc009d 0x7833c023f038fc00

def z434 : W := mkw 0xaa80000d24880000 0x23aa80000d248800 0x3ec0000e3fcc0097 0xab3ec0000e3fcc00

def z435 : W := mkw 0x004021b008560902 0x00004021b0085609 0x000023f000000000 0x40000023f0000000

def z436 : W := mkw 0x0a0c36961dd77bda 0x050a0c36961dd77b 0x0e3c3f8e3ffffff7 0xff0e3c3f8e3fffff

def z437 : W := mkw 0xef999a4da6a80000 0x63ef999a4da6a800 0xcc1ddc0fc7000042 0x87cc1ddc0fc70000

def z438 : W := mkw 0x0000208008420800 0x0000002080084208 0x0020238000023820 0x4000202380000238

def z439 : W := mkw 0xf5f3ed70cb32c514 0x4af5f3ed70cb32c5 0xfdc3fc71cf33c7fb 0xd8fdc3fc71cf33c7

def z440 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xfec0000ff7cc0006 0xa3fec0000ff7cc00

def z441 : W := mkw 0xfffbbbfdbefe1b42 0x63fffbbbfdbefe1b 0xfffffffffffe3fff 0xfffffffffffffe3f

def z442 : W := mkw 0x0a0836840dc24818 0x050a0836840dc248 0x0e003f8e0fc00097 0xeb0e003f8e0fc000

def z443 : W := mkw 0x0000ec504912c514 0x080000ec504912c5 0xc003fc71c003c7eb 0xd0c003fc71c003c7

def z444 : W := mkw 0xef8c36860dc36898 0x07ef8c36860dc368 0xfffc3f8e0fc3f8ff 0xeffffc3f8e0fc3f8

def z445 : W := mkw 0x0000208008420800 0x0000002080084208 0x0000000008c23880 0x280000000008c238

def z446 : W := mkw 0x4500c850c2308504 0x084500c850c23085 0xcd03c071cf30079b 0x98cd03c071cf3007

def z447 : W := mkw 0xffe201adb6ec1a42 0x23ffe201adb6ec1a 0xffe0038ffffc389f 0xbbffe0038ffffc38

def z448 : W := mkw 0x0a0836840dc24818 0x050a0836840dc248 0x0e003f800fc3c0f3 0xc80e003f800fc3c0

def z449 : W := mkw 0x4f80ec54cfbac514 0x294f80ec54cfbac5 0xcfc3fc71cfffc7fb 0xd8cfc3fc71cfffc7

def z450 : W := mkw 0xef84400ff6a9b6e0 0x33ef84400ff6a9b6 0xffc0000fffffff9f 0xbbffc0000fffffff

def z451 : W := mkw 0x0000ec504912c514 0x080000ec504912c5 0x0c03fc700f03c7f3 0xc80c03fc700f03c7

def z452 : W := mkw 0xef800009a2280000 0x23ef800009a22800 0xffc00001f03c001f 0x13ffc00001f03c00

def z453 : W := mkw 0xef80ec5defbac514 0x2bef80ec5defbac5 0xcd03fc7fcf33c7fb 0xdbcd03fc7fcf33c7

def z454 : W := mkw 0x10260002100132c0 0x0010260002100132 0x303e000e3003ffef 0xb7303e000e3003ff

def z455 : W := mkw 0xa080000920080000 0x22a0800009200800 0x30c00000300c0000 0x0030c00000300c00

def z456 : W := mkw 0x4540edf0cb76cd16 0x084540edf0cb76cd 0xcfc3fff1cfffc7fb 0xd8cfc3fff1cfffc7

def z457 : W := mkw 0xb037ec5b7913f7f4 0x1ab037ec5b7913f7 0xf03ffc7ff003ffef 0xf7f03ffc7ff003ff

def z458 : W := mkw 0xb07b9b6000000000 0x42b07b9b60000000 0xf03ffff00000006f 0x47f03ffff0000000

def z459 : W := mkw 0xb07701ab30453ae2 0x12b07701ab30453a 0x32fc038e30cc3804 0x2732fc038e30cc38

def z460 : W := mkw 0x4500000000000000 0x0045000000000000 0xcd0000000000001b 0x00cd000000000000

def z461 : W := mkw 0xbab7400f7489b6e0 0x33bab7400f7489b6 0xf2ffc00ff0cfffef 0xb7f2ffc00ff0cfff

def z462 : W := mkw 0x4f08fed4cff2cd1c 0x0d4f08fed4cff2cd 0xcf03fff1cff3c7fb 0xd8cf03fff1cff3c7

def z463 : W := mkw 0x0000248009424810 0x0000002480094248 0x0e203f800fc3f8f7 0xe80e203f800fc3f8

def z464 : W := mkw 0x4f08bed48ff2491c 0x0d4f08bed48ff249 0x0f003ff00ff00010 0x480f003ff00ff000

def z465 : W := mkw 0xe580000000000000 0x02e5800000000000 0xf1c0000000000008 0x00f1c00000000000

def z466 : W := mkw 0xf577edfbfb77fff6 0x1af577edfbfb77ff 0xffffffffffffffff 0xffffffffffffffff

def z467 : W := mkw 0xb07741ab7045bee2 0x12b07741ab7045be 0xf2ffc38ff0cfffef 0xb7f2ffc38ff0cfff

def z468 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e1c3f8e0fc1c052 0xcf0e1c3f8e0fc1c0

def z469 : W := mkw 0x107bbbf018561b42 0x40107bbbf018561b 0x003ffff000023f60 0x44003ffff000023f

def z470 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x32e223f030ce3f24 0x6032e223f030ce3f

def z471 : W := mkw 0xa011400960008420 0x12a0114009600084 0xc001c001c0000000 0x00c001c001c00000

def z472 : W := mkw 0x106201a010441a42 0x00106201a010441a 0x33e223f030cc383d 0x6033e223f030cc38

def z473 : W := mkw 0xffb7000fb6a932e0 0x33ffb7000fb6a932 0xfffc000ffffc389f 0xbffffc000ffffc38

def z474 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x023c038e0fc3f884 0xaf023c038e0fc3f8

def z475 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0x3ffc3ff000000014 0x473ffc3ff0000000

def z476 : W := mkw 0xef99de40c320c414 0x4bef99de40c320c4 0xcc1ddc01c701c042 0x87cc1ddc01c701c0

def z477 : W := mkw 0xffee37bfbfff7bda 0x27ffee37bfbfff7b 0xfffe3fffffffffff 0xfffffe3fffffffff

def z478 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x31e223f0303e3f28 0x5031e223f0303e3f

def z479 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc001f003ff68 0x14f03fc001f003ff

def z480 : W := mkw 0x5537ec52db33f7f4 0x185537ec52db33f7 0xcd3ffc71cf33fffb 0xdccd3ffc71cf33ff

def z481 : W := mkw 0xffffdb625001b6e0 0x53ffffdb625001b6 0xfffffff00003ff7f 0x47fffffff00003ff

def z482 : W := mkw 0x0000ec50cb32c514 0x080000ec50cb32c5 0x0003fc71cf33c7e0 0xd80003fc71cf33c7

def z483 : W := mkw 0xb073012000000000 0x02b0730120000000 0xf3ffe3f00000007f 0x47f3ffe3f0000000

def z484 : W := mkw 0x0000209018561b42 0x000000209018561b 0x33c0000038fe3f9d 0x3833c0000038fe3f

def z485 : W := mkw 0x0a0c128604c12888 0x050a0c128604c128 0x023c038e00c3f8e7 0xa7023c038e00c3f8

def z486 : W := mkw 0xef80884000000000 0x03ef808840000000 0xffc3fc700000007f 0x43ffc3fc70000000

def z487 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xc103fc71c033c768 0x50c103fc71c033c7

def z488 : W := mkw 0x0000000486a80000 0x200000000486a800 0x000000000ffc0000 0x08000000000ffc00

def z489 : W := mkw 0x4f0cfec6cfe3ec9c 0x0d4f0cfec6cfe3ec 0xce3dff8fcfc3f8f7 0xefce3dff8fcfc3f8

def z490 : W := mkw 0x0a0836840dc24818 0x050a0836840dc248 0x0e203f800fc238b5 0x680e203f800fc238

def z491 : W := mkw 0xfffffff6cff3ed9c 0x4ffffffff6cff3ed 0xffffffffcff3ffff 0xffffffffffcff3ff

def z492 : W := mkw 0xf5f3897010141342 0x42f5f38970101413 0xf1c3c070303c0708 0x10f1c3c070303c07

def z493 : W := mkw 0x0000400040008400 0x0000004000400084 0x0003c0000003c760 0x000003c0000003c7

def z494 : W := mkw 0xf5f3896000000000 0x42f5f38960000000 0xf3e3e3f00000003d 0x40f3e3e3f0000000

def z495 : W := mkw 0x5fea9b6000000000 0x415fea9b60000000 0x3fe23ff00000003d 0x403fe23ff0000000

def z496 : W := mkw 0x1022201018121340 0x0010222010181213 0x3122207038323fbd 0x783122207038323f

def z497 : W := mkw 0xfffbff704912c514 0x4bfffbff704912c5 0xfffffff00003c77f 0x47fffffff00003c7

def z498 : W := mkw 0xb033400970009660 0x12b0334009700096 0xf023c001f0023fad 0x30f023c001f0023f

def z499 : W := mkw 0xef88120000000000 0x03ef881200000000 0xfffc3f800000007f 0x47fffc3f80000000

def z500 : W := mkw 0xfffbfff0db76df56 0x4bfffbfff0db76df 0xfffffff1ffffffff 0xfffffffff1ffffff

def z501 : W := mkw 0x5522ec50db32d754 0x085522ec50db32d7 0xfd23fc71ff33ffff 0xf8fd23fc71ff33ff

def z502 : W := mkw 0xffffff7bfb33f7f4 0x5bffffff7bfb33f7 0xffffffffff33ffff 0xffffffffffff33ff

def z503 : W := mkw 0xffe2012000000000 0x03ffe20120000000 0xffe223f00000003f 0x43ffe223f0000000

def z504 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0fc03814 0x6f0e3c3f8e0fc038

def z505 : W := mkw 0xbafb132d24880000 0x63bafb132d248800 0x32fc038e30cc0004 0x2732fc038e30cc00

def z506 : W := mkw 0x0a08120000000000 0x010a081200000000 0x0c1c1c0000000042 0x070c1c1c00000000

def z507 : W := mkw 0x1026400b7001b6e0 0x101026400b7001b6 0x3022000ff003ffad 0xb03022000ff003ff

def z508 : W := mkw 0x106221a018461a42 0x00106221a018461a 0x32e0238038ce38b5 0x6832e0238038ce38

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x0220238000000035 0x4002202380000000

def z510 : W := mkw 0xaa80000d24880000 0x23aa80000d248800 0x0000000e00000000 0x030000000e000000

def z511 : W := mkw 0x1022000010001240 0x0010220000100012 0x0022000000023f20 0x000022000000023f

def z512 : W := mkw 0x1a6e37b61dd77bda 0x051a6e37b61dd77b 0x0e3e3ffe0fc3fff7 0xef0e3e3ffe0fc3ff

def z513 : W := mkw 0x0004641bfb33f7f4 0x180004641bfb33f7 0x0000000fff33ff80 0xb80000000fff33ff

def z514 : W := mkw 0x000424860dc36898 0x04000424860dc368 0x003c000e0fc3f8e7 0xaf003c000e0fc3f8

def z515 : W := mkw 0x4f0cfe56cfb3e59c 0x0d4f0cfe56cfb3e5 0xcd1ffc7fcf33c7fb 0xdfcd1ffc7fcf33c7

def z516 : W := mkw 0x4500885082300104 0x0845008850823001 0x0100007000300000 0x0001000070003000

def z517 : W := mkw 0xffbfda4b7001b6e0 0x53ffbfda4b7001b6 0xfc3fdc0ff003ffef 0xb7fc3fdc0ff003ff

def z518 : W := mkw 0x0a0c128604c12888 0x050a0c128604c128 0x0e3c3f8e00c03877 0x670e3c3f8e00c038

def z519 : W := mkw 0x0000241009124110 0x0000002410091241 0x0d023c700f33c7fb 0xd80d023c700f33c7

def z520 : W := mkw 0x1a6e33b61cd73bca 0x051a6e33b61cd73b 0x33fe23fe38fe3fbd 0x7f33fe23fe38fe3f

def z521 : W := mkw 0x1022000010001240 0x0010220000100012 0x3020000030003804 0x2030200000300038

def z522 : W := mkw 0x450cfed2cb73ed9c 0x0c450cfed2cb73ed 0xcd3ffff1cf33fffb 0xdccd3ffff1cf33ff

def z523 : W := mkw 0x4f00000486a00000 0x014f00000486a000 0xcf00000fcff0009f 0xbbcf00000fcff000

def z524 : W := mkw 0xef8cfedfeffbed9c 0x2fef8cfedfeffbed 0xffffffffffffffff 0xffffffffffffffff

def z525 : W := mkw 0x556221b09a761b42 0x00556221b09a761b 0xffe223f1fffe3fbf 0xf8ffe223f1fffe3f

def z526 : W := mkw 0xb033400970009660 0x12b0334009700096 0xf003c00ff000078f 0xb3f003c00ff00007

def z527 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x3ffc3f8e3ffff8ff 0xff3ffc3f8e3ffff8

def z528 : W := mkw 0xef9dbec60dc36898 0x47ef9dbec60dc368 0xce3dff8e0fc3f8f7 0xefce3dff8e0fc3f8

def z529 : W := mkw 0xaa8c368f2dcb6898 0x27aa8c368f2dcb68 0x3efc3f8e3fcff8f7 0xef3efc3f8e3fcff8

def z530 : W := mkw 0x0a0c368209436898 0x050a0c3682094368 0x0e3c3f800003f877 0x470e3c3f800003f8

def z531 : W := mkw 0x106221bdbefe1b42 0x20106221bdbefe1b 0x33e223fffffe3fbd 0xf833e223fffffe3f

def z532 : W := mkw 0xe580c859e2388504 0x2ae580c859e23885 0xf1c3c071f03c0708 0x10f1c3c071f03c07

def z533 : W := mkw 0x000c160201016098 0x04000c1602010160 0x001c1c000001c040 0x04001c1c000001c0

def z534 : W := mkw 0x106621b218573bc2 0x00106621b218573b 0x33fe23fe38ffffff 0xff33fe23fe38ffff

def z535 : W := mkw 0xfffb9be010441a42 0x43fffb9be010441a 0xfffffff030cc387f 0x67fffffff030cc38

def z536 : W := mkw 0x0000400040008400 0x0000004000400084 0x00000001c003c780 0x9000000001c003c7

def z537 : W := mkw 0xffff9b6b300132e0 0x53ffff9b6b300132 0xfffffffe3000387f 0x67fffffffe300038

def z538 : W := mkw 0x000424961dd77bda 0x04000424961dd77b 0x0000000e3fffff80 0xb80000000e3fffff

def z539 : W := mkw 0x000c36860dc36898 0x04000c36860dc368 0x003c3f8e0fc3f8e0 0xec003c3f8e0fc3f8

def z540 : W := mkw 0x00000009a2280000 0x2000000009a22800 0x00000001f03c0000 0x1000000001f03c00

def z541 : W := mkw 0x0000ec504912c514 0x080000ec504912c5 0x0103fc700833c7f9 0x580103fc700833c7

def z542 : W := mkw 0xf5b34009f2289660 0x32f5b34009f22896 0xf1c3c001f03c0708 0x10f1c3c001f03c07

def z543 : W := mkw 0xef80ec50cb32c514 0x0bef80ec50cb32c5 0xffc3fc71cf33c7ff 0xdbffc3fc71cf33c7

def z544 : W := mkw 0xb037608b7843bee0 0x12b037608b7843be 0xf23fe38ff8c3ffff 0xfff23fe38ff8c3ff

def z545 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfefddf8000000046 0x07fefddf80000000

def z546 : W := mkw 0xa015400b6001a4a0 0x12a015400b6001a4 0xc01fc00fc003c7eb 0x97c01fc00fc003c7

def z547 : W := mkw 0xaa1d768f6dc3ecb8 0x17aa1d768f6dc3ec 0xce3dff8fcfc3f8f7 0xefce3dff8fcfc3f8

def z548 : W := mkw 0x5562c970d2349746 0x085562c970d23497 0xf1c3c071f03c0708 0x10f1c3c071f03c07

def z549 : W := mkw 0x0004400b6001a4a0 0x100004400b6001a4 0x0000000fc001c000 0x800000000fc001c0

def z550 : W := mkw 0x4f80000da6a80000 0x214f80000da6a800 0x0fc0000ffffc0090 0xb80fc0000ffffc00

def z551 : W := mkw 0xf5f3c96970009660 0x52f5f3c969700096 0xf1c3c071f0000708 0x10f1c3c071f00007

def z552 : W := mkw 0x106625b61dd77bda 0x04106625b61dd77b 0x33e223fe3fffffbd 0xf833e223fe3fffff

def z553 : W := mkw 0x0000008010441a42 0x000000008010441a 0x0000000030cc3800 0x200000000030cc38

def z554 : W := mkw 0xf5f3896000000000 0x42f5f38960000000 0xfdc3fc700000007b 0x40fdc3fc70000000

def z555 : W := mkw 0x4fc8bbf008560902 0x414fc8bbf0085609 0x0fc03ff008fc0010 0x480fc03ff008fc00

def z556 : W := mkw 0x0000400970009660 0x1000004009700096 0x00000001f0000700 0x1000000001f00007

def z557 : W := mkw 0x103740025001b6e0 0x10103740025001b6 0xc03fc001c003ffeb 0x94c03fc001c003ff

def z558 : W := mkw 0xb07361b978569f62 0x12b07361b978569f 0xf3e3e3f1f8fe3fbd 0x78f3e3e3f1f8fe3f

def z559 : W := mkw 0xa000400960008400 0x02a0004009600084 0xf003c00ff003c7ef 0xb3f003c00ff003c7

def z560 : W := mkw 0xaa80000000000000 0x03aa800000000000 0x32c0000000000004 0x0332c00000000000

def z561 : W := mkw 0x1a6a33b018561b42 0x011a6a33b018561b 0x3ffe3ff038fe3fff 0x7f3ffe3ff038fe3f

def z562 : W := mkw 0xef80000000000000 0x03ef800000000000 0xffc0000038fc009f 0x3bffc0000038fc00

def z563 : W := mkw 0x4500e850ca328504 0x084500e850ca3285 0xc103e071c83207b9 0x58c103e071c83207

def z564 : W := mkw 0xe5800009a2280000 0x22e5800009a22800 0xf3c00001f8fc009d 0x38f3c00001f8fc00

def z565 : W := mkw 0xaa99120000000000 0x43aa991200000000 0x001c000000000000 0x07001c0000000000

def z566 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcc01dc01cf33c7c2 0x98cc01dc01cf33c7

def z567 : W := mkw 0x0000200008020000 0x0000002000080200 0x00002000080200b1 0x4800002000080200

def z568 : W := mkw 0xef8c160fa7a96098 0x27ef8c160fa7a960 0xffdc1c0ffffdc0df 0xbfffdc1c0ffffdc0

def z569 : W := mkw 0xefc89b6000000000 0x43efc89b60000000 0xffc03ff00000001f 0x43ffc03ff0000000

def z570 : W := mkw 0x0a0c368fafeb6898 0x250a0c368fafeb68 0x0e3c3f8ffffff8f7 0xff0e3c3f8ffffff8

def z571 : W := mkw 0x107bbbf018561b42 0x40107bbbf018561b 0x33fffff038fe3ffd 0x7c33fffff038fe3f

def z572 : W := mkw 0xef84000fa6a92080 0x23ef84000fa6a920 0xfffc000ffffff8ff 0xbffffc000ffffff8

def z573 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0x0d003c71cf33c790 0xd80d003c71cf33c7

def z574 : W := mkw 0xef88368dafea4818 0x27ef88368dafea48 0xffc03f8ffffc009f 0xfbffc03f8ffffc00

def z575 : W := mkw 0xef80000082200000 0x03ef800000822000 0xffc00001cf30009f 0x9bffc00001cf3000

def z576 : W := mkw 0x1a6a37b41dd65b5a 0x051a6a37b41dd65b 0x3fe23ff03ffe3fbd 0x783fe23ff03ffe3f

def z577 : W := mkw 0xffffbfe209436898 0x47ffffbfe2094368 0xfffffff00003f87f 0x47fffffff00003f8

def z578 : W := mkw 0x1022000000000000 0x0010220000000000 0x302200000000002d 0x0030220000000000

def z579 : W := mkw 0x107b132000000000 0x40107b1320000000 0x003c038000000000 0x04003c0380000000

def z580 : W := mkw 0x001540024001a4a0 0x10001540024001a4 0x001dc0000001c040 0x04001dc0000001c0

def z581 : W := mkw 0x5feabbf018561b42 0x415feabbf018561b 0x3fe23ff038fe3fbd 0x783fe23ff038fe3f

def z582 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xffc3fff000000018 0x40ffc3fff0000000

def z583 : W := mkw 0xa015400b6001a4a0 0x12a015400b6001a4 0xf01dc00ff001c0cf 0xb7f01dc00ff001c0

def z584 : W := mkw 0xf5e20139b23c1342 0x22f5e20139b23c13 0xf1c20071f03c0708 0x10f1c20071f03c07

def z585 : W := mkw 0x0a00000000000000 0x010a000000000000 0x0e00000000000017 0x030e000000000000

def z586 : W := mkw 0x4fc8bfe40dc24818 0x454fc8bfe40dc248 0x0fc03ff00fc00010 0x480fc03ff00fc000

def z587 : W := mkw 0xb033000000000000 0x02b0330000000000 0x303c000000000004 0x07303c0000000000

def z588 : W := mkw 0x1062013010141342 0x0010620130101413 0x31e20070303e3fad 0x3031e20070303e3f

def z589 : W := mkw 0x0a0020840cc20800 0x010a0020840cc208 0x0e20238e0fc238b7 0xeb0e20238e0fc238

def z590 : W := mkw 0xb037000b300132e0 0x12b037000b300132 0xf03fc00e3000386f 0x27f03fc00e300038

def z591 : W := mkw 0xf5b7400bf229b6e0 0x32f5b7400bf229b6 0xf1ffc00ff03fffef 0xb7f1ffc00ff03fff

def z592 : W := mkw 0xbafb132000000000 0x43bafb1320000000 0xf2ffc3800000006f 0x07f2ffc380000000

def z593 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x03e223f008fe3f30 0x4803e223f008fe3f

def z594 : W := mkw 0x0000000404800000 0x0000000004048000 0x0000000e0fc00080 0xa80000000e0fc000

def z595 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xf3c0000ff0fc000c 0x33f3c0000ff0fc00

def z596 : W := mkw 0x4500c850c2308504 0x084500c850c23085 0xc103c071c033c7eb 0x90c103c071c033c7

def z597 : W := mkw 0x0000209008560902 0x0000002090085609 0x0000000008fc0000 0x080000000008fc00

def z598 : W := mkw 0x0000201008120100 0x0000002010081201 0x33c2207038fe07bd 0x7833c2207038fe07

def z599 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e023f038fc3814 0x6833e023f038fc38

def z600 : W := mkw 0x10370002100132e0 0x1010370002100132 0x003c000000003800 0x04003c0000000038

def z601 : W := mkw 0xfffbdb6970009660 0x53fffbdb69700096 0xfffffff1f000077f 0x57fffffff1f00007

def z602 : W := mkw 0x0000208008420800 0x0000002080084208 0x33e0238038fe38bd 0x7833e0238038fe38

def z603 : W := mkw 0x1062012010001240 0x0010620120100012 0x33e223f030023fbd 0x7033e223f030023f

def z604 : W := mkw 0x1a6a132000000000 0x011a6a1320000000 0x3ffe3ff00000007f 0x473ffe3ff0000000

def z605 : W := mkw 0x4500ecd0db76df56 0x084500ecd0db76df 0xcd03fc71fffffffb 0xf8cd03fc71ffffff

def z606 : W := mkw 0x4f80ac548fba4114 0x294f80ac548fba41 0x0fc03c700ffc0010 0x480fc03c700ffc00

def z607 : W := mkw 0x4500ec5defbac514 0x284500ec5defbac5 0xcd03fc7fffffc7fb 0xf8cd03fc7fffffc7

def z608 : W := mkw 0x0000240009024010 0x0000002400090240 0x000000000f03c080 0x88000000000f03c0

def z609 : W := mkw 0x4504ec5bfb33f7f4 0x184504ec5bfb33f7 0xcd03fc7fff33fffb 0xf8cd03fc7fff33ff

def z610 : W := mkw 0x0a08120000000000 0x010a081200000000 0x0e003f8000000010 0x400e003f80000000

def z611 : W := mkw 0x4540adf08b764916 0x084540adf08b7649 0x0fc03ff00ffc0010 0x480fc03ff00ffc00

def z612 : W := mkw 0x1a6e37a60dc36898 0x051a6e37a60dc368 0x3ffe3ffe0fc3f8ff 0xef3ffe3ffe0fc3f8

def z613 : W := mkw 0xbab7000f348932e0 0x33bab7000f348932 0x32fc000e30cc3804 0x2732fc000e30cc38

def z614 : W := mkw 0xa000000920000000 0x02a0000009200000 0xf3c0000ff8fc009f 0xbbf3c0000ff8fc00

def z615 : W := mkw 0xe5800009a2280000 0x22e5800009a22800 0xf1c0000ff03c008f 0xb3f1c0000ff03c00

def z616 : W := mkw 0x4f0c36868fe36898 0x054f0c36868fe368 0xcf3c3f8fcff3f8ff 0xffcf3c3f8fcff3f8

def z617 : W := mkw 0xffff9f6605816098 0x47ffff9f66058160 0xfffffffe0701c07f 0xc7fffffffe0701c0

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000e00000087 0xa30000000e000000

def z619 : W := mkw 0x000424860dc36898 0x04000424860dc368 0x0220238e0fc3f8b5 0xe80220238e0fc3f8

def z620 : W := mkw 0x5f6efff6dff7ffde 0x0d5f6efff6dff7ff 0xffffffffffffffff 0xffffffffffffffff

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000003c0e3 0x80000000000003c0

def z622 : W := mkw 0x0a0024040d824010 0x010a0024040d8240 0x0e003c0e0fc3c0f7 0xeb0e003c0e0fc3c0

def z623 : W := mkw 0xef80000d24880000 0x23ef80000d248800 0xffc0000e30cc001f 0x23ffc0000e30cc00

def z624 : W := mkw 0xef8c368fafeb6898 0x27ef8c368fafeb68 0xce3c3f8fcfc3f8f7 0xefce3c3f8fcfc3f8

def z625 : W := mkw 0xffb7400b7001b6e0 0x13ffb7400b7001b6 0xffffc00ff003ffff 0xb7ffffc00ff003ff

def z626 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x31c2007038fe3f88 0x3831c2007038fe3f

def z627 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xcd00000fcf30009b 0x9bcd00000fcf3000

def z628 : W := mkw 0xaa00000d24800000 0x03aa00000d248000 0xfe00000fffc0009f 0xbbfe00000fffc000

def z629 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000fc700001f 0x83ffc0000fc70000

def z630 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f000023f3d 0x4033e223f000023f

def z631 : W := mkw 0x1022400050009640 0x0010224000500096 0xf023c001f003ffef 0xb0f023c001f003ff

def z632 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0x0d03fc700f33c770 0x480d03fc700f33c7

def z633 : W := mkw 0x0004000200012080 0x0000040002000120 0x001c000e0001c042 0x87001c000e0001c0

def z634 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc00001fffc0018 0x18ffc00001fffc00

def z635 : W := mkw 0x00004400c320c414 0x0800004400c320c4 0x00000001c701c000 0x8000000001c701c0

def z636 : W := mkw 0xb037000b300132e0 0x12b037000b300132 0x303c000e3003f8e7 0xa7303c000e3003f8

def z637 : W := mkw 0xe580ec59eb3ac514 0x2ae580ec59eb3ac5 0xfdc3fc71ff3fc7fb 0xd8fdc3fc71ff3fc7

def z638 : W := mkw 0x4500cc40c320c414 0x084500cc40c320c4 0xcd03fc71c701c07b 0xc0cd03fc71c701c0

def z639 : W := mkw 0x5562adf09b765b56 0x085562adf09b765b 0x3fe23ff03ffe3fbd 0x783fe23ff03ffe3f

def z640 : W := mkw 0xa000000920000000 0x02a0000009200000 0xf0000001f0000008 0x10f0000001f00000

def z641 : W := mkw 0xb037609b7857bfe2 0x12b037609b7857bf 0xf03fc00ff8ffffef 0xbff03fc00ff8ffff

def z642 : W := mkw 0x0004248fafeb6898 0x240004248fafeb68 0x0000000ffffff880 0xb80000000ffffff8

def z643 : W := mkw 0x0000209018561b42 0x000000209018561b 0x0220238038fe3fb5 0x780220238038fe3f

def z644 : W := mkw 0x0000000920000000 0x0000000009200000 0x0000000ff0000080 0xb00000000ff00000

def z645 : W := mkw 0x0000400040008400 0x0000004000400084 0xc003c001c0000708 0x10c003c001c00007

def z646 : W := mkw 0xb07321b018561b42 0x02b07321b018561b 0xf3ffe3f038fe3fff 0x7ff3ffe3f038fe3f

def z647 : W := mkw 0xef9dda4b6001a4a0 0x53ef9dda4b6001a4 0xcc1ddc0fc001c042 0x87cc1ddc0fc001c0

def z648 : W := mkw 0xe5800009a2280000 0x22e5800009a22800 0xfdc00001ff3c009b 0x98fdc00001ff3c00

def z649 : W := mkw 0x0004400b7001b6e0 0x100004400b7001b6 0x003c000ff003ffe7 0xb7003c000ff003ff

def z650 : W := mkw 0x4500ac508b324114 0x084500ac508b3241 0xcd03fc700f30007b 0x48cd03fc700f3000

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c003c0000000073 0x400c003c00000000

def z652 : W := mkw 0x0040012000000000 0x0000400120000000 0x03c023f000000010 0x4003c023f0000000

def z653 : W := mkw 0x0004648f7dc3fef8 0x140004648f7dc3fe 0x0000000fffc3ff80 0xb80000000fffc3ff

def z654 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03dc00ff001f846 0xa7f03dc00ff001f8

def z655 : W := mkw 0xffffdb6b6001a4a0 0x53ffffdb6b6001a4 0xffffffffc001c07f 0xc7ffffffffc001c0

def z656 : W := mkw 0x107fbfe209436898 0x44107fbfe2094368 0x003ffff00003f860 0x44003ffff00003f8

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200000000238a5 0x2000200000000238

def z658 : W := mkw 0xef80209dbefe1b42 0x23ef80209dbefe1b 0xffc0000ffffe3f9f 0xbbffc0000ffffe3f

def z659 : W := mkw 0xfffb9b7010141342 0x43fffb9b70101413 0xfffffff0303c077f 0x57fffffff0303c07

def z660 : W := mkw 0x000c128200412888 0x04000c1282004128 0x003c038000003800 0x04003c0380000038

def z661 : W := mkw 0x450024008b224010 0x00450024008b2240 0xcd003c01cf33c0fb 0xd8cd003c01cf33c0

def z662 : W := mkw 0x4500884000000000 0x0045008840000000 0xcc01dc0000000042 0x00cc01dc00000000

def z663 : W := mkw 0x0a0c120604812088 0x050a0c1206048120 0x001c000e00000000 0x07001c000e000000

def z664 : W := mkw 0x106221a008420800 0x00106221a0084208 0x33e223f008c238bd 0x6833e223f008c238

def z665 : W := mkw 0xffb3000000000000 0x03ffb30000000000 0xffffc0000000007f 0x07ffffc000000000

def z666 : W := mkw 0xbafb132000000000 0x43bafb1320000000 0x3efc3f8000000077 0x473efc3f80000000

def z667 : W := mkw 0x4500000082200000 0x0045000000822000 0xcc000001c7000002 0x80cc000001c70000

def z668 : W := mkw 0x4500884000000000 0x0045008840000000 0x0d003c7000000010 0x400d003c70000000

def z669 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f800fc3f870 0x4c0e3c3f800fc3f8

def z670 : W := mkw 0x0000209008520900 0x0000002090085209 0x032223f008f23fbd 0x78032223f008f23f

def z671 : W := mkw 0x0004000200012080 0x0000040002000120 0x003c000e00003804 0x27003c000e000038

def z672 : W := mkw 0xb077413b7015b7e2 0x12b077413b7015b7 0xf1ffc07ff03fffef 0xb7f1ffc07ff03fff

def z673 : W := mkw 0x0a0c160605816098 0x050a0c1606058160 0x0e3c3f8e0701c077 0xc70e3c3f8e0701c0

def z674 : W := mkw 0x0a0c160605816098 0x050a0c1606058160 0x0e1c1c0e0fc1c0d7 0xaf0e1c1c0e0fc1c0

def z675 : W := mkw 0xba3f520b7001b6e0 0x13ba3f520b7001b6 0xfe3fff8ff003ffff 0xf7fe3fff8ff003ff

def z676 : W := mkw 0xefc89b6da6a80000 0x63efc89b6da6a800 0xffc03ffffffc009f 0xfbffc03ffffffc00

def z677 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xfdc0000ff73c000a 0x93fdc0000ff73c00

def z678 : W := mkw 0xa015400b6001a4a0 0x12a015400b6001a4 0xc03dc00fc003f8e7 0xa7c03dc00fc003f8

def z679 : W := mkw 0xba37400f7481b6e0 0x13ba37400f7481b6 0xfe3fc00fffc3ffff 0xbffe3fc00fffc3ff

def z680 : W := mkw 0x103740025001b6e0 0x10103740025001b6 0x003fc00e0003ffe7 0xa7003fc00e0003ff

def z681 : W := mkw 0x0a00000da6a80000 0x210a00000da6a800 0x0e00000ffffc0097 0xbb0e00000ffffc00

def z682 : W := mkw 0xbaff532b7001b6e0 0x53baff532b7001b6 0xf2ffc38ff003ffef 0xb7f2ffc38ff003ff

def z683 : W := mkw 0xffff9be604c12888 0x47ffff9be604c128 0xfffffffe00c0387f 0x67fffffffe00c038

def z684 : W := mkw 0xf5e221b9ba7e1b42 0x22f5e221b9ba7e1b 0xf3e223f1f8fe3fbd 0x78f3e223f1f8fe3f

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x0102207000000039 0x4001022070000000

def z686 : W := mkw 0xf537c84b7001b6e0 0x12f537c84b7001b6 0xfd3ffc7ff003ffff 0xf7fd3ffc7ff003ff

def z687 : W := mkw 0x0004008604c12888 0x040004008604c128 0x0000000e00c03800 0x200000000e00c038

def z688 : W := mkw 0xb07721bb38573be2 0x12b07721bb38573b 0x33fe23fe38fe3fbd 0x7f33fe23fe38fe3f

def z689 : W := mkw 0xa015000b200120a0 0x12a015000b200120 0x001c000e00000000 0x07001c000e000000

def z690 : W := mkw 0x0a80000404880000 0x210a800004048800 0x02c0000000cc0000 0x0002c0000000cc00

def z691 : W := mkw 0xe515cc4be321e4b4 0x1ae515cc4be321e4 0xcc1ddc0fc701c042 0x87cc1ddc0fc701c0

def z692 : W := mkw 0xffb7ec5fffbbf7f4 0x3bffb7ec5fffbbf7 0xfffffc7fffffffff 0xfffffffc7fffffff

def z693 : W := mkw 0x1022000010001240 0x0010220000100012 0x3002000030000708 0x1030020000300007

def z694 : W := mkw 0x4f00ec54cfb2c514 0x094f00ec54cfb2c5 0xcf03fc7fcff3c7ff 0xfbcf03fc7fcff3c7

def z695 : W := mkw 0xb037400b6001a4a0 0x12b037400b6001a4 0xf03fc00fc001c06f 0x87f03fc00fc001c0

def z696 : W := mkw 0x45008c4083204014 0x0845008c40832040 0x0c001c0007000000 0x000c001c00070000

def z697 : W := mkw 0xef80000000000000 0x03ef800000000000 0xcc00000000000002 0x03cc000000000000

def z698 : W := mkw 0xa000000920000000 0x02a0000009200000 0x3000000e30000004 0x233000000e300000

def z699 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e003f8e0fc3f890 0xe80e003f8e0fc3f8

def z700 : W := mkw 0xe5800009a2280000 0x22e5800009a22800 0xc0000001c0000000 0x00c0000001c00000

def z701 : W := mkw 0x004021b008560902 0x00004021b0085609 0x03e023f008fe38b5 0x6803e023f008fe38

def z702 : W := mkw 0xef80cc4de7a8c414 0x2bef80cc4de7a8c4 0xcc01dc0fc701c042 0x83cc01dc0fc701c0

def z703 : W := mkw 0xaa0c368f2dc36898 0x07aa0c368f2dc368 0xfe3c3f8fffc3f8ff 0xfffe3c3f8fffc3f8

def z704 : W := mkw 0xffbb9a4000000000 0x43ffbb9a40000000 0xfc3fdc000000006f 0x07fc3fdc00000000

def z705 : W := mkw 0x106201a010441a42 0x00106201a010441a 0x32e2038030ce3fad 0x3032e2038030ce3f

def z706 : W := mkw 0xef95400fe6a9a4a0 0x33ef95400fe6a9a4 0xcc1dc00fc701c042 0x87cc1dc00fc701c0

def z707 : W := mkw 0xf5fb9b69a2280000 0x62f5fb9b69a22800 0xf1fffff1f03c0068 0x54f1fffff1f03c00

def z708 : W := mkw 0x0a00000da6a80000 0x210a00000da6a800 0x3fc0000ffffc009f 0xbb3fc0000ffffc00

def z709 : W := mkw 0xa004400b6001a480 0x02a004400b6001a4 0xf03fc00ff003ffef 0xb7f03fc00ff003ff

def z710 : W := mkw 0xfffb9b6486a80000 0x63fffb9b6486a800 0xfffffff1cffc00ff 0xdffffffff1cffc00

def z711 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x3fe23ff038fe3fff 0x783fe23ff038fe3f

def z712 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03dc00ff003ffc6 0xb7f03dc00ff003ff

def z713 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x33fffff038fc00fd 0x7c33fffff038fc00

def z714 : W := mkw 0xfffb9b6d24800000 0x43fffb9b6d248000 0xffffffffffc000ff 0xffffffffffffc000

def z715 : W := mkw 0xef99bad018561b42 0x43ef99bad018561b 0xcc1ddc0038fe3fc2 0x3fcc1ddc0038fe3f

def z716 : W := mkw 0x107321b018561b42 0x00107321b018561b 0x33ffe3f038fe3ffd 0x7c33ffe3f038fe3f

def z717 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000ffffc0016 0xabffc0000ffffc00

def z718 : W := mkw 0x557b9b6082200000 0x40557b9b60822000 0xcd3ffff1cf3000fb 0xdccd3ffff1cf3000

def z719 : W := mkw 0xbafb9b6000000000 0x43bafb9b60000000 0x3efffff000000077 0x473efffff0000000

def z720 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffe0238ffffc00bf 0xfbffe0238ffffc00

def z721 : W := mkw 0x0000209008520900 0x0000002090085209 0x33e223f038fe3fbd 0x7833e223f038fe3f

def z722 : W := mkw 0xf57b9b6000000000 0x42f57b9b60000000 0xfd3ffff00000007f 0x47fd3ffff0000000

def z723 : W := mkw 0x4fccdb6b7001b6e0 0x514fccdb6b7001b6 0x0fc03ffff003ff90 0xf00fc03ffff003ff

def z724 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffe0000ffffe38bf 0xbbffe0000ffffe38

def z725 : W := mkw 0xaa80ec5d6d9ac514 0x2baa80ec5d6d9ac5 0x32c3fc7e30cfc764 0x6332c3fc7e30cfc7

def z726 : W := mkw 0x1a7b9b6000000000 0x411a7b9b60000000 0x0c3ffff000000062 0x470c3ffff0000000

def z727 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x3efc3f8e3fcff8f7 0xef3efc3f8e3fcff8

def z728 : W := mkw 0xa000000da6a80000 0x22a000000da6a800 0xf3c0000ffffc009f 0xbbf3c0000ffffc00

def z729 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xcc3fffffc7000062 0xc7cc3fffffc70000

def z730 : W := mkw 0x5fb74006d6a9b6e0 0x315fb74006d6a9b6 0x0fffc0000fffff70 0x0c0fffc0000fffff

def z731 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf23fe38ff003ffff 0xf7f23fe38ff003ff

def z732 : W := mkw 0xe58c368bab6b6898 0x26e58c368bab6b68 0xf1fc3f81f03ff868 0x54f1fc3f81f03ff8

def z733 : W := mkw 0xf573896000000000 0x02f5738960000000 0xfffffff00000007f 0x47fffffff0000000

def z734 : W := mkw 0xfffb9b6082200000 0x43fffb9b60822000 0xfffffff1fffc00ff 0xfffffffff1fffc00

def z735 : W := mkw 0xa080000da6a80000 0x22a080000da6a800 0x30c0000ffffc0080 0xb830c0000ffffc00

def z736 : W := mkw 0xf5f7ade60dc36898 0x46f5f7ade60dc368 0xf1c3c07e0fc3f888 0xa8f1c3c07e0fc3f8

def z737 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x3e3c3f8e3fc3f8ff 0xff3e3c3f8e3fc3f8

def z738 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000fffffc0ff 0xbbffc0000fffffc0

def z739 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfdfffff00000006a 0x47fdfffff0000000

def z740 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff00f0000ff 0xcffffffff00f0000

def z741 : W := mkw 0xbafb7730cb32c514 0x4bbafb7730cb32c5 0x32fc0381cf33c784 0x9f32fc0381cf33c7

def z742 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff00000001c 0x47fffffff0000000

def z743 : W := mkw 0x103740025001b6e0 0x10103740025001b6 0xc03fc00fc003ffef 0xb7c03fc00fc003ff

def z744 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33fe23f038fe3fff 0x7f33fe23f038fe3f

def z745 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf2ffc00ff0cfffef 0xb7f2ffc00ff0cfff

def z746 : W := mkw 0x1a6e1736159573da 0x051a6e1736159573 0x3dde1c7e373dc74a 0x973dde1c7e373dc7

def z747 : W := mkw 0xa05561bb6857ada2 0x12a05561bb6857ad 0xc3dde3ffc8fdc052 0xcfc3dde3ffc8fdc0

def z748 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcc03fc71c703c7eb 0xd0cc03fc71c703c7

def z749 : W := mkw 0x107b9b6da6a80000 0x60107b9b6da6a800 0x003ffffffffc00e0 0xfc003ffffffffc00

def z750 : W := mkw 0xef889a4da6a80000 0x23ef889a4da6a800 0xfffffffffffc00ff 0xfffffffffffffc00

def z751 : W := mkw 0xb077412b7001b6e0 0x12b077412b7001b6 0xf3ffe3fff8ffffff 0xfff3ffe3fff8ffff

def z752 : W := mkw 0xef88120da6a80000 0x23ef88120da6a800 0xfffc038ffffc009f 0xbffffc038ffffc00

def z753 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffffe000000ff 0xe7fffffffe000000

def z754 : W := mkw 0x557b9b6000000000 0x40557b9b60000000 0x0d3ffff000000070 0x440d3ffff0000000

def z755 : W := mkw 0xfffb9b69a2280000 0x63fffb9b69a22800 0xfffffff1f8fc00ff 0x7ffffffff1f8fc00

def z756 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xc03fc00fc003ffe7 0xa7c03fc00fc003ff

def z757 : W := mkw 0x4fc89b6000000000 0x414fc89b60000000 0xcffffff00000007f 0x47cffffff0000000

def z758 : W := mkw 0xef80884da6a80000 0x23ef80884da6a800 0xffc1dc0ffffc00df 0xbbffc1dc0ffffc00

def z759 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffffff7cc007f 0xe7fffffffff7cc00

def z760 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xf3fffff00000006c 0x47f3fffff0000000

def z761 : W := mkw 0xb0fb9b6000000000 0x42b0fb9b60000000 0x30fffff000000060 0x4430fffff0000000

def z762 : W := mkw 0xffe221bdbefe1b42 0x23ffe221bdbefe1b 0xcc2223ffc7023f22 0xc3cc2223ffc7023f

def z763 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xcffffff000000072 0x47cffffff0000000

def z764 : W := mkw 0x107b9b6010001240 0x40107b9b60100012 0x303ffff030023fed 0x74303ffff030023f

def z765 : W := mkw 0x4f0cdad6c6f1ad8c 0x0d4f0cdad6c6f1ad 0xc33fc3ffc0f03f0c 0x37c33fc3ffc0f03f

def z766 : W := mkw 0xba3b768d7dc2de78 0x17ba3b768d7dc2de 0xfe03ff81ffc00718 0x58fe03ff81ffc007

def z767 : W := mkw 0x4500cc50c330c514 0x084500cc50c330c5 0xcc03dc71c701c742 0x80cc03dc71c701c7

def z768 : W := mkw 0x4500000da6a80000 0x204500000da6a800 0xffc0000ffffc009f 0xb8ffc0000ffffc00

def z769 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xfd03fc71ff33c7ff 0xf8fd03fc71ff33c7

def z770 : W := mkw 0xef88120da6a80000 0x23ef88120da6a800 0xffc03f8ffffc009f 0xfbffc03f8ffffc00

def z771 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcc03fc71cf03c7f3 0xc8cc03fc71cf03c7

def z772 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xffffffffcfc000ff 0xefffffffffcfc000

def z773 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xfec0000ffffc0086 0xbbfec0000ffffc00

def z774 : W := mkw 0x000c368209436898 0x04000c3682094368 0x0c3c3f8e0f03f8f7 0xef0c3c3f8e0f03f8

def z775 : W := mkw 0xef889a4da6a80000 0x63ef889a4da6a800 0xffc01c0ffffc009f 0xbbffc01c0ffffc00

def z776 : W := mkw 0x1afb9b6000000000 0x411afb9b60000000 0x02fffff000000060 0x4402fffff0000000

def z777 : W := mkw 0x4500ecd0cb72cd14 0x084500ecd0cb72cd 0xcd03fc71cff3fffb 0xf8cd03fc71cff3ff

def z778 : W := mkw 0x0a0c36960dd36998 0x050a0c36960dd369 0x0e3c3f8e0ff3fff7 0xff0e3c3f8e0ff3ff

def z779 : W := mkw 0x4f88bed48ffa491c 0x2d4f88bed48ffa49 0x0fc03ff00ffc0010 0x480fc03ff00ffc00

def z780 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x303ffff00000006d 0x44303ffff0000000

def z781 : W := mkw 0xfffb9b6010001240 0x43fffb9b60100012 0xfffffff03000077f 0x57fffffff0300007

def z782 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff003ff8c 0xb7f03fc00ff003ff

def z783 : W := mkw 0x5ffb9b6000000000 0x415ffb9b60000000 0x0c3ffff000000060 0x440c3ffff0000000

def z784 : W := mkw 0x0004400b7001b6e0 0x100004400b7001b6 0xc03fc00ff003ffef 0xb7c03fc00ff003ff

def z785 : W := mkw 0xfffb9b6404800000 0x43fffb9b64048000 0xfffffffe3ffc00ff 0xfffffffffe3ffc00

def z786 : W := mkw 0x5562cde0d364de56 0x085562cde0d364de 0xfee1df81f7cdf846 0xa0fee1df81f7cdf8

def z787 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xc03fc00ff003ffe2 0xb7c03fc00ff003ff

def z788 : W := mkw 0x4500c840c2208400 0x004500c840c22084 0xcd03fc71cf33c7fb 0xd8cd03fc71cf33c7

def z789 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffffe3ffc007f 0x6ffffffffe3ffc00

def z790 : W := mkw 0x107f77b25957fffa 0x14107f77b25957ff 0x003ffff00003ff60 0x44003ffff00003ff

def z791 : W := mkw 0xefd99b6000000000 0x43efd99b60000000 0xcffdfff000000077 0x47cffdfff0000000

def z792 : W := mkw 0x00089a4000000000 0x0000089a40000000 0x003ffff000000060 0x44003ffff0000000

def z793 : W := mkw 0x4500ecd0cb72cd14 0x084500ecd0cb72cd 0xcf03fff1cff3c7fb 0xd8cf03fff1cff3c7

def z794 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000ffffc0098 0xb8ffc0000ffffc00

def z795 : W := mkw 0x000464924953ed9c 0x0c000464924953ed 0x000000000003ff00 0x00000000000003ff

def z796 : W := mkw 0xfffb9b6d24880000 0x63fffb9b6d248800 0xfffffffe0000007f 0x47fffffffe000000

def z797 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0xc03ffff00000006b 0x44c03ffff0000000

def z798 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc2207ffffc00bf 0xfbffc2207ffffc00

def z799 : W := mkw 0x000064104912c510 0x00000064104912c5 0xcd03fc71cf33c7fb 0xd8cd03fc71cf33c7

def z800 : W := mkw 0xe5000009a2200000 0x02e5000009a22000 0xffc0000ffffc009f 0xbbffc0000ffffc00

def z801 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcf03fc71cff3c7ff 0xf8cf03fc71cff3c7

def z802 : W := mkw 0x106225b019565b52 0x00106225b019565b 0x33e223f03fffffbd 0xf833e223f03fffff

def z803 : W := mkw 0xfffb9b6010001240 0x43fffb9b60100012 0xfffffff03000387f 0x67fffffff0300038

def z804 : W := mkw 0xe580000da6a80000 0x22e580000da6a800 0xf1c0000ffffc008f 0xbbf1c0000ffffc00

def z805 : W := mkw 0x557b9b6000000000 0x40557b9b60000000 0xcc3ffff000000062 0x44cc3ffff0000000

def z806 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfc3ffff00000006f 0x47fc3ffff0000000

def z807 : W := mkw 0x1a7b9b6000000000 0x411a7b9b60000000 0x0e3ffff000000070 0x440e3ffff0000000

def z808 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xffdffff00000005a 0x47ffdffff0000000

def z809 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc03c0ffffc00ff 0xfbffc03c0ffffc00

def z810 : W := mkw 0x0000000da6a80000 0x200000000da6a800 0x31c0000ffffc0088 0xb831c0000ffffc00

def z811 : W := mkw 0xefd99b6da6a80000 0x63efd99b6da6a800 0xffddfffffffc00df 0xffffddfffffffc00

def z812 : W := mkw 0xbafb9b6d24880000 0x63bafb9b6d248800 0x32fffffe30cc0064 0x6732fffffe30cc00

def z813 : W := mkw 0xb07b9b6920000000 0x42b07b9b69200000 0xf03ffffff00000ef 0xf7f03ffffff00000

def z814 : W := mkw 0xaa80000da6a80000 0x23aa80000da6a800 0x33c0000ffffc009d 0xbb33c0000ffffc00

def z815 : W := mkw 0x1062012010001240 0x0010620120100012 0x33e223f038fe3fbd 0x7833e223f038fe3f

def z816 : W := mkw 0xbaff132f348932e0 0x73baff132f348932 0x32fc038e30cc3804 0x2732fc038e30cc38

def z817 : W := mkw 0xfffb9b6010001240 0x43fffb9b60100012 0xfffffff000023f7f 0x47fffffff000023f

def z818 : W := mkw 0x107b9b6010001240 0x40107b9b60100012 0x003ffff000023f60 0x44003ffff000023f

def z819 : W := mkw 0xfffb9b6920000000 0x43fffb9b69200000 0xfffffffe3000007f 0x67fffffffe300000

def z820 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71cf33c772 0xc8cd03fc71cf33c7

def z821 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0fc3f894 0xef0e3c3f8e0fc3f8

def z822 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffffff73c007f 0xd7fffffffff73c00

def z823 : W := mkw 0x0a0c36960dd36998 0x050a0c36960dd369 0x3ffe3ffe3fffffff 0xff3ffe3ffe3fffff

def z824 : W := mkw 0xef9dda4fe6a9a4a0 0x73ef9dda4fe6a9a4 0xcc1ddc0fc701c042 0x87cc1ddc0fc701c0

def z825 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf01fc00ff003ffca 0xb7f01fc00ff003ff

def z826 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xce3ffff000000077 0x47ce3ffff0000000

def z827 : W := mkw 0x0000ec504912c514 0x080000ec504912c5 0xcc03fc71cf03c7fb 0xd8cc03fc71cf03c7

def z828 : W := mkw 0xfffb9b6920000000 0x43fffb9b69200000 0xffffffffc000007f 0xc7ffffffffc00000

def z829 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0x3ffffff000000074 0x473ffffff0000000

def z830 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xffffffffcf3000ff 0xdfffffffffcf3000

def z831 : W := mkw 0xf537ac5bbb3373f4 0x1af537ac5bbb3373 0x3d3c3c7e3f303814 0x6f3d3c3c7e3f3038

def z832 : W := mkw 0xfffb9b6486a80000 0x63fffb9b6486a800 0xfffffffe0ffc00ff 0xeffffffffe0ffc00

def z833 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x3ffc3f8e0fc3f8ff 0xef3ffc3f8e0fc3f8

def z834 : W := mkw 0x0a0c160605816098 0x050a0c1606058160 0x0e3c3f8e0703f8f7 0xe70e3c3f8e0703f8

def z835 : W := mkw 0xef88120da6a80000 0x23ef88120da6a800 0xffdc1c0ffffc00df 0xbfffdc1c0ffffc00

def z836 : W := mkw 0xf573c979f2349766 0x1af573c979f23497 0xf1c3c071f03c0708 0x10f1c3c071f03c07

def z837 : W := mkw 0xb07b9b6000000000 0x42b07b9b60000000 0x303ffff000000064 0x47303ffff0000000

def z838 : W := mkw 0x106221b018561b42 0x00106221b018561b 0xf3e3e3f038fe3fff 0x78f3e3e3f038fe3f

def z839 : W := mkw 0xefd99b6000000000 0x43efd99b60000000 0xcc1dfff000000042 0x47cc1dfff0000000

def z840 : W := mkw 0xb077412b7005b6e2 0x12b077412b7005b6 0xf0ffc00ff00fffef 0xb7f0ffc00ff00fff

def z841 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0c3c3f8e0703f8e7 0xe70c3c3f8e0703f8

def z842 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff008fc007f 0x4ffffffff008fc00

def z843 : W := mkw 0x4f046496cff3ed9c 0x0d4f046496cff3ed 0xcf00000fcff3ff9f 0xbbcf00000fcff3ff

def z844 : W := mkw 0xef80884da6a80000 0x23ef80884da6a800 0xffc3c07ffffc009f 0xbbffc3c07ffffc00

def z845 : W := mkw 0xbaff13af34c13ae8 0x57baff13af34c13a 0x32fc038e30c03804 0x2732fc038e30c038

def z846 : W := mkw 0xfffb9b69a2200000 0x43fffb9b69a22000 0xffffffffff3000ff 0xffffffffffff3000

def z847 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f038fe3f38 0x5833e223f038fe3f

def z848 : W := mkw 0x4500cc50c330c514 0x084500cc50c330c5 0xcd03dc71cf31c7db 0x98cd03dc71cf31c7

def z849 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x03fffff000000070 0x4403fffff0000000

def z850 : W := mkw 0xfffb9b6920080000 0x63fffb9b69200800 0xfffffff0300c007f 0x47fffffff0300c00

def z851 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd3ffc71cf33c7ff 0xdfcd3ffc71cf33c7

def z852 : W := mkw 0x106225b019565b52 0x00106225b019565b 0x3fe23ff03ffe3fbd 0x783fe23ff03ffe3f

def z853 : W := mkw 0xfffb9b6930001260 0x53fffb9b69300012 0xfffffff03000007f 0x47fffffff0300000

def z854 : W := mkw 0xf5fb9b6000000000 0x42f5fb9b60000000 0xf1fffff00000006f 0x47f1fffff0000000

def z855 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71c703c77b 0xc0cd03fc71c703c7

def z856 : W := mkw 0xaa80000da6a80000 0x23aa80000da6a800 0xf2c0000ffffc008f 0xbbf2c0000ffffc00

def z857 : W := mkw 0x0004649feffbed9c 0x2c0004649feffbed 0x0000000fffffff80 0xb80000000fffffff

def z858 : W := mkw 0x5ffb9b6000000000 0x415ffb9b60000000 0xcffffff00000007b 0x44cffffff0000000

def z859 : W := mkw 0xa015400b7001b6e0 0x12a015400b7001b6 0xc01dc00fc003ff42 0x87c01dc00fc003ff

def z860 : W := mkw 0xf5f3c969f2289660 0x72f5f3c969f22896 0xf1c3c071f03c0708 0x10f1c3c071f03c07

def z861 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00fc003ff6f 0x87f03fc00fc003ff

def z862 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0c3c3f8e0f03f8f3 0xcf0c3c3f8e0f03f8

def z863 : W := mkw 0xf5f3c979f2309764 0x5af5f3c979f23097 0xf1c3c071f0300708 0x10f1c3c071f03007

def z864 : W := mkw 0xfffb9b6d24880000 0x63fffb9b6d248800 0xfffffffff0cc00ff 0xf7fffffffff0cc00

def z865 : W := mkw 0xef91884da6a80000 0x63ef91884da6a800 0xffc1c00ffffc009f 0xbbffc1c00ffffc00

def z866 : W := mkw 0x5f7b9b6000000000 0x415f7b9b60000000 0xcf3ffff00000007f 0x47cf3ffff0000000

def z867 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0703f877 0xc70e3c3f8e0703f8

def z868 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71ffffc7fb 0xf8cd03fc71ffffc7

def z869 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xffc3fc71cf33c7ff 0xd8ffc3fc71cf33c7

def z870 : W := mkw 0xef999a4da6a80000 0x63ef999a4da6a800 0xfffdff8ffffc00ff 0xfffffdff8ffffc00

def z871 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xfc3ffc0ff003ffff 0xf7fc3ffc0ff003ff

def z872 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xcd3ffff00000007b 0x47cd3ffff0000000

def z873 : W := mkw 0x106225b019565b52 0x00106225b019565b 0x33e23ff038fffffd 0x7833e23ff038ffff

def z874 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e023f038fe3f94 0x7833e023f038fe3f

def z875 : W := mkw 0xb077412b7001b6e0 0x12b077412b7001b6 0xf03fe3fff003ffef 0xf7f03fe3fff003ff

def z876 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71cf31c75a 0xd8cd03fc71cf31c7

def z877 : W := mkw 0xfffb9b6486a80000 0x63fffb9b6486a800 0xfffffff00700007f 0x47fffffff0070000

def z878 : W := mkw 0xfffb9b69a2280000 0x63fffb9b69a22800 0xfffffff1ff3c00ff 0xdffffffff1ff3c00

def z879 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff003ff66 0xa7f03fc00ff003ff

def z880 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0xce3c3f8fcfc3f8ff 0xffce3c3f8fcfc3f8

def z881 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33c223f038fe3f98 0x7833c223f038fe3f

def z882 : W := mkw 0x00046492cb73ed9c 0x0c00046492cb73ed 0x00000001cf33ff80 0x9800000001cf33ff

def z883 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff003ff6a 0x97f03fc00ff003ff

def z884 : W := mkw 0xef80884da6a80000 0x23ef80884da6a800 0xffc03c7ffffc009f 0xfbffc03c7ffffc00

def z885 : W := mkw 0x557b9b6000000000 0x40557b9b60000000 0xc13ffff000000068 0x44c13ffff0000000

def z886 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223fe38fe3fbf 0xfb33e223fe38fe3f

def z887 : W := mkw 0x0a0c36960dd36998 0x050a0c36960dd369 0x0f3c3ffe0ff3f8f7 0xef0f3c3ffe0ff3f8

def z888 : W := mkw 0x0a0c168605c16898 0x050a0c168605c168 0x0e3c1f8e0fc1f8d7 0xaf0e3c1f8e0fc1f8

def z889 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xfffc000ffffc00ff 0xbffffc000ffffc00

def z890 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff00003c0ff 0xc7fffffff00003c0

def z891 : W := mkw 0xfffb9b69a2280000 0x63fffb9b69a22800 0xfffffffff03c00ff 0xf7fffffffff03c00

def z892 : W := mkw 0x45089a4000000000 0x0045089a40000000 0xcd3ffff00000007b 0x44cd3ffff0000000

def z893 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xffffffffcffc007f 0xcfffffffffcffc00

def z894 : W := mkw 0xfffb9b6930001240 0x43fffb9b69300012 0xfffffffff0023fff 0xf7fffffffff0023f

def z895 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc2000ffffe07bf 0xbbffc2000ffffe07

def z896 : W := mkw 0xfffb9b6d24880000 0x63fffb9b6d248800 0xfffffffe38fc00ff 0x7ffffffffe38fc00

def z897 : W := mkw 0x5ffb9b6000000000 0x415ffb9b60000000 0x0ffffff000000077 0x470ffffff0000000

def z898 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x0c3ffff000000073 0x440c3ffff0000000

def z899 : W := mkw 0xef8cde4fe7a9e49c 0x2fef8cde4fe7a9e4 0xcc1ddc0fc701c042 0x87cc1ddc0fc701c0

def z900 : W := mkw 0x0004248209436890 0x0000042482094368 0x0e3c3f8e0fc3f8f7 0xef0e3c3f8e0fc3f8

def z901 : W := mkw 0x4580ec50cb3ac514 0x284580ec50cb3ac5 0xcdc3fc71cf3fc7fb 0xd8cdc3fc71cf3fc7

def z902 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x31fffff000000068 0x4431fffff0000000

def z903 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71cf33c798 0xd8cd03fc71cf33c7

def z904 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c1f8e0fc3f8c6 0xaf0e3c1f8e0fc3f8

def z905 : W := mkw 0x00046496dff7ffde 0x0c00046496dff7ff 0x0000000fffffff80 0xb80000000fffffff

def z906 : W := mkw 0x1a7b9b6404800000 0x411a7b9b64048000 0x0e3ffffe0fc000f7 0xef0e3ffffe0fc000

def z907 : W := mkw 0xbafb9b6000000000 0x43bafb9b60000000 0x33fffff00000007d 0x4733fffff0000000

def z908 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff0300000ff 0x77fffffff0300000

def z909 : W := mkw 0xfffb9b6404800000 0x43fffb9b64048000 0xfffffff00fc0007f 0x4ffffffff00fc000

def z910 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0fc1f856 0xef0e3c3f8e0fc1f8

def z911 : W := mkw 0xfffb9b6010001240 0x43fffb9b60100012 0xfffffff038fe3fff 0x7ffffffff038fe3f

def z912 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x32fffff000000064 0x4432fffff0000000

def z913 : W := mkw 0x1a7b9b6000000000 0x411a7b9b60000000 0x023ffff000000064 0x47023ffff0000000

def z914 : W := mkw 0x55fb9b6000000000 0x4055fb9b60000000 0x01fffff000000060 0x4401fffff0000000

def z915 : W := mkw 0x0a0c120604812080 0x010a0c1206048120 0x0e3c3f8e0fc3f8f7 0xef0e3c3f8e0fc3f8

def z916 : W := mkw 0x4500cc50c330c514 0x084500cc50c330c5 0xcd03fc71c731c77b 0xd0cd03fc71c731c7

def z917 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff0000207ff 0x57fffffff0000207

def z918 : W := mkw 0xfffb9b6920000000 0x43fffb9b69200000 0xfffffffff8fc00ff 0xfffffffffff8fc00

def z919 : W := mkw 0xefd99b6000000000 0x43efd99b60000000 0xffddfff00000005f 0x47ffddfff0000000

def z920 : W := mkw 0xef91000da6a80000 0x23ef91000da6a800 0xffddc00ffffc00df 0xbfffddc00ffffc00

def z921 : W := mkw 0x106201b010541b42 0x00106201b010541b 0x33e223f030fc3f3d 0x7033e223f030fc3f

def z922 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf23fc00ff8c3ffff 0xbff23fc00ff8c3ff

def z923 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71cf33c778 0x58cd03fc71cf33c7

def z924 : W := mkw 0x0a0c168605c16898 0x050a0c168605c168 0x0e3c1f8e07c3f8e7 0xa70e3c1f8e07c3f8

def z925 : W := mkw 0xefd99b6da6a80000 0x63efd99b6da6a800 0xcfddffffcffc0052 0xcfcfddffffcffc00

def z926 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f038fc3f1c 0x7833e223f038fc3f

def z927 : W := mkw 0xb077412b7001b6e0 0x12b077412b7001b6 0xf1ffc07ff003ffef 0xb7f1ffc07ff003ff

def z928 : W := mkw 0xb0b7400b7009b6e0 0x32b0b7400b7009b6 0xf0ffc00ff00fffef 0xb7f0ffc00ff00fff

def z929 : W := mkw 0xef84649feffbed9c 0x2fef84649feffbed 0xffc0000fffffff9f 0xbbffc0000fffffff

def z930 : W := mkw 0xfffb9b6082200000 0x43fffb9b60822000 0xfffffff1c030007f 0x57fffffff1c03000

def z931 : W := mkw 0x0a0c168605c16898 0x050a0c168605c168 0x0e3c3f8e07c1f877 0xe70e3c3f8e07c1f8

def z932 : W := mkw 0x106201b010541b42 0x00106201b010541b 0x33e203f038fc3f9d 0x3833e203f038fc3f

def z933 : W := mkw 0x0a0c360209036090 0x010a0c3602090360 0x0e3c3f8e0f03f8f7 0xef0e3c3f8e0f03f8

def z934 : W := mkw 0xef999a4da6a80000 0x63ef999a4da6a800 0xffdffc7ffffc00ff 0xffffdffc7ffffc00

def z935 : W := mkw 0x106221b018561b42 0x00106221b018561b 0xf3e223f1f8fe3fbf 0xf8f3e223f1f8fe3f

def z936 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xfdc3fc71ff3fc7fb 0xd8fdc3fc71ff3fc7

def z937 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3e3f8e0fc3ffff 0xff0e3e3f8e0fc3ff

def z938 : W := mkw 0xef99120da6a80000 0x63ef99120da6a800 0xffdc000ffffc009f 0xbfffdc000ffffc00

def z939 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff8ffffef 0xbff03fc00ff8ffff

def z940 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff0000238ff 0x67fffffff0000238

def z941 : W := mkw 0xa015400b7001b6e0 0x12a015400b7001b6 0xc03dc00ff003ffe7 0xb7c03dc00ff003ff

def z942 : W := mkw 0x4500ec404902c410 0x004500ec404902c4 0xcd03fc71cf03c7fb 0xd8cd03fc71cf03c7

def z943 : W := mkw 0x4f00000486a00000 0x014f00000486a000 0xffc0000ffffc009f 0xbbffc0000ffffc00

def z944 : W := mkw 0x0004649ffff3fffc 0x1c0004649ffff3ff 0x0000000ffff3ff80 0xb80000000ffff3ff

def z945 : W := mkw 0x4f089a4486a00000 0x014f089a4486a000 0xcf3fffffcff000ff 0xffcf3fffffcff000

def z946 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xf3c0000ffffc008c 0xbbf3c0000ffffc00

def z947 : W := mkw 0x0a0c36960dd7699a 0x050a0c36960dd769 0x0e3c3f8e0ffff8f7 0xef0e3c3f8e0ffff8

def z948 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0c3c3f8e0fc3f8e2 0xef0c3c3f8e0fc3f8

def z949 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e07c3f866 0xe70e3c3f8e07c3f8

def z950 : W := mkw 0x1077edf25957fff6 0x181077edf25957ff 0x003ffff00003ff60 0x44003ffff00003ff

def z951 : W := mkw 0xa015400b7001b6e0 0x12a015400b7001b6 0xf01dc00ff003ffcf 0xb7f01dc00ff003ff

def z952 : W := mkw 0xff3b9a4000000000 0x03ff3b9a40000000 0xff3ffff00000007f 0x47ff3ffff0000000

def z953 : W := mkw 0xfffb9b6d24880000 0x63fffb9b6d248800 0xfffffffe3fcc00ff 0xeffffffffe3fcc00

def z954 : W := mkw 0xfffb9b6db6a81240 0x63fffb9b6db6a812 0xfffffffffffe3fff 0xfffffffffffffe3f

def z955 : W := mkw 0xfffb9b6010041242 0x43fffb9b60100412 0xfffffff0300c007f 0x47fffffff0300c00

def z956 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0x3fc0000ffffc0094 0xbb3fc0000ffffc00

def z957 : W := mkw 0x00599b6000000000 0x4000599b60000000 0x001dfff000000040 0x44001dfff0000000

def z958 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff000000078 0x44fffffff0000000

def z959 : W := mkw 0x5ffb9b6000000000 0x415ffb9b60000000 0x3ffffff00000007d 0x443ffffff0000000

def z960 : W := mkw 0xb0f7412b7001b6e0 0x52b0f7412b7001b6 0xf0ffc00ff003ffef 0xb7f0ffc00ff003ff

def z961 : W := mkw 0xb07b9b6000000000 0x42b07b9b60000000 0xf3fffff00000007f 0x47f3fffff0000000

def z962 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcfc3fc71cfffc7fb 0xd8cfc3fc71cfffc7

def z963 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e3ffff8f7 0xff0e3c3f8e3ffff8

def z964 : W := mkw 0xfffb9b6920000000 0x43fffb9b69200000 0xfffffff1f000007f 0x57fffffff1f00000

def z965 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf3ffc00ff003ffff 0xb7f3ffc00ff003ff

def z966 : W := mkw 0x4500ecd0cb72cd14 0x084500ecd0cb72cd 0xcd23fff1cf33fffb 0xd8cd23fff1cf33ff

def z967 : W := mkw 0x106efff25957ffde 0x0c106efff25957ff 0x003ffff00003ff60 0x44003ffff00003ff

def z968 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0fc3f872 0xcf0e3c3f8e0fc3f8

def z969 : W := mkw 0x004021b018561b42 0x00004021b018561b 0x33c023f038fe3f9d 0x7833c023f038fe3f

def z970 : W := mkw 0xba7b132000000000 0x03ba7b1320000000 0xfffffff00000007f 0x47fffffff0000000

def z971 : W := mkw 0xfffb9b6486a80000 0x63fffb9b6486a800 0xfffffff03ffc00ff 0x7ffffffff03ffc00

def z972 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd23fc71cf33ffff 0xf8cd23fc71cf33ff

def z973 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf1ffc00ff03fffef 0xb7f1ffc00ff03fff

def z974 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcc03fc71cf33c7e2 0xd8cc03fc71cf33c7

def z975 : W := mkw 0x4500cc40c320c414 0x084500cc40c320c4 0xcd03fc71c703c7fb 0xd0cd03fc71c703c7

def z976 : W := mkw 0xf5fb9b6000000000 0x42f5fb9b60000000 0xc03ffff000000060 0x44c03ffff0000000

def z977 : W := mkw 0xaa80000da6a80000 0x23aa80000da6a800 0x3ec0000ffffc0097 0xbb3ec0000ffffc00

def z978 : W := mkw 0x557b9b6000000000 0x40557b9b60000000 0xfffffff00000007f 0x44fffffff0000000

def z979 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0xce3fff8e0fc3f8ff 0xefce3fff8e0fc3f8

def z980 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03dc71cf33c7ca 0x98cd03dc71cf33c7

def z981 : W := mkw 0xef999a4000000000 0x43ef999a40000000 0xcf3ffff00000007f 0x47cf3ffff0000000

def z982 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f030fe3f2c 0x7033e223f030fe3f

def z983 : W := mkw 0xaa00000d24800000 0x03aa00000d248000 0xffc0000ffffc009f 0xbbffc0000ffffc00

def z984 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000ffffc001c 0x3bffc0000ffffc00

def z985 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcf23fff1cf33c7ff 0xd8cf23fff1cf33c7

def z986 : W := mkw 0x106201b010541b42 0x00106201b010541b 0x33e203f030fe3fad 0x3033e203f030fe3f

def z987 : W := mkw 0xef889a4000000000 0x03ef889a40000000 0xfffffff00000007f 0x47fffffff0000000

def z988 : W := mkw 0xe580000da6a80000 0x22e580000da6a800 0xfdc0000ffffc009b 0xb8fdc0000ffffc00

def z989 : W := mkw 0xbafb9b6000000000 0x43bafb9b60000000 0x003ffff000000060 0x47003ffff0000000

def z990 : W := mkw 0xfffb9b6082200000 0x43fffb9b60822000 0xfffffff1c700007f 0xc7fffffff1c70000

def z991 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xfdc0000ffffc008a 0xbbfdc0000ffffc00

def z992 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e203f038fe3f8c 0x3833e203f038fe3f

def z993 : W := mkw 0xefd99b6000000000 0x43efd99b60000000 0xcfdffff00000007b 0x47cfdffff0000000

def z994 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x3fe223f03ffe3fbf 0xf83fe223f03ffe3f

def z995 : W := mkw 0x0000000da6a80000 0x200000000da6a800 0x32c0000ffffc0084 0xb832c0000ffffc00

def z996 : W := mkw 0x5f6a9b6000000000 0x015f6a9b60000000 0xfffffff00000007f 0x47fffffff0000000

def z997 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf13fe07ff003ffff 0xf7f13fe07ff003ff

def z998 : W := mkw 0x102640025001b6c0 0x00102640025001b6 0xf03fc00ff003ffef 0xb7f03fc00ff003ff

def z999 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x003ffff000000067 0x47003ffff0000000

def z1000 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff1c00000ff 0xd7fffffff1c00000

def z1001 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f038fe3f34 0x6833e223f038fe3f

def z1002 : W := mkw 0xfffb9b6404800000 0x43fffb9b64048000 0xfffffffe00c0007f 0x67fffffffe00c000

def z1003 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0e3c3f8e0fc3f874 0x6f0e3c3f8e0fc3f8

def z1004 : W := mkw 0xfffb9b69a2280000 0x63fffb9b69a22800 0xfffffff1c000007f 0x47fffffff1c00000

def z1005 : W := mkw 0xb07b9b6000000000 0x42b07b9b60000000 0xf03ffff000000068 0x44f03ffff0000000

def z1006 : W := mkw 0xb077412b7001b6e0 0x12b077412b7001b6 0xf2ffc38ff003ffef 0xb7f2ffc38ff003ff

def z1007 : W := mkw 0x0a0c36960dd36998 0x050a0c36960dd369 0x0e3e3ffe0fc3fff7 0xef0e3e3ffe0fc3ff

def z1008 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xc03fc00fc003ffeb 0x97c03fc00fc003ff

def z1009 : W := mkw 0x0004649f7dd7fffa 0x140004649f7dd7ff 0x0000000fffffff80 0xb80000000fffffff

def z1010 : W := mkw 0x106221b018561b42 0x00106221b018561b 0x33e223f038ffffff 0xf833e223f038ffff

def z1011 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc3c00ffffc00ff 0xbbffc3c00ffffc00

def z1012 : W := mkw 0xfffb9b6082200000 0x43fffb9b60822000 0xfffffff00f30007f 0x4ffffffff00f3000

def z1013 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff0303c007f 0x57fffffff0303c00

def z1014 : W := mkw 0x4500cc50c330c514 0x084500cc50c330c5 0xcd03dc71c733c7eb 0x90cd03dc71c733c7

def z1015 : W := mkw 0xa015400b7001b6e0 0x12a015400b7001b6 0xc01fc00ff003ffeb 0xb7c01fc00ff003ff

def z1016 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff0083000ff 0x5ffffffff0083000

def z1017 : W := mkw 0x4f48bff48ff6491e 0x0d4f48bff48ff649 0x0fc03ff00ffc0010 0x480fc03ff00ffc00

def z1018 : W := mkw 0xfffb9b6404800000 0x43fffb9b64048000 0xfffffffe0700007f 0xc7fffffffe070000

def z1019 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffdfff000000056 0x47fffdfff0000000

def z1020 : W := mkw 0xe580000da6a80000 0x22e580000da6a800 0xf3c0000ffffc009d 0xb8f3c0000ffffc00

def z1021 : W := mkw 0xa015400b6001a4a0 0x12a015400b6001a4 0xc03fc00fc003ffef 0xb7c03fc00fc003ff

def z1022 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffff1fffc007f 0x5ffffffff1fffc00

def z1023 : W := mkw 0xfffb9b6486a00000 0x43fffb9b6486a000 0xffffffffcff000ff 0xffffffffffcff000

def z1024 : W := mkw 0x0004649bfb77fff6 0x180004649bfb77ff 0x0000000fffffff80 0xb80000000fffffff

def z1025 : W := mkw 0x4500ecd0cb76cd16 0x084500ecd0cb76cd 0xcd03fc71cfffc7fb 0xd8cd03fc71cfffc7

def z1026 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0f3e3ffe0fc3f8ff 0xef0f3e3ffe0fc3f8

def z1027 : W := mkw 0xfffb9b6404880000 0x63fffb9b64048800 0xfffffff000cc007f 0x47fffffff000cc00

def z1028 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffffff0fc007f 0x77fffffffff0fc00

def z1029 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfefffff000000066 0x47fefffff0000000

def z1030 : W := mkw 0xfffb9b6da6a80000 0x63fffb9b6da6a800 0xfffffffff70000ff 0xf7fffffffff70000

def z1031 : W := mkw 0x0a8c36860dcb6898 0x250a8c36860dcb68 0x0efc3f8e0fcff8f7 0xef0efc3f8e0fcff8

def z1032 : W := mkw 0x0a0c168605c16898 0x050a0c168605c168 0x0c3c1f8e0701f842 0x870c3c1f8e0701f8

def z1033 : W := mkw 0xf5fb9b6000000000 0x42f5fb9b60000000 0xfdfffff00000007b 0x44fdfffff0000000

def z1034 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0ffc3f8e0ffff8f7 0xef0ffc3f8e0ffff8

def z1035 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc7fcf33c7ff 0xfbcd03fc7fcf33c7

def z1036 : W := mkw 0x000464964dd3ed9c 0x0c000464964dd3ed 0x0000000e0fc3ff80 0xa80000000e0fc3ff

def z1037 : W := mkw 0xef80000da6a80000 0x23ef80000da6a800 0xffc0000ffffc001a 0x9bffc0000ffffc00

def z1038 : W := mkw 0x4500ecd0cb72cd14 0x084500ecd0cb72cd 0xffe3fff1ffffffff 0xf8ffe3fff1ffffff

def z1039 : W := mkw 0x0a0c36860dc36898 0x050a0c36860dc368 0x0f3c3f8e0ff3f8ff 0xff0f3c3f8e0ff3f8

def z1040 : W := mkw 0xb07b9b6000000000 0x42b07b9b60000000 0xc03ffff000000062 0x47c03ffff0000000

def z1041 : W := mkw 0x4500ec50cb32c514 0x084500ec50cb32c5 0xcd03fc71c733c76a 0xd0cd03fc71c733c7

def z1042 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf03fc00ff003ff6c 0x37f03fc00ff003ff

def z1043 : W := mkw 0x0a089a4000000000 0x010a089a40000000 0x0e3ffff000000077 0x470e3ffff0000000

def z1044 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xfc3fc00fff03ffff 0xbffc3fc00fff03ff

def z1045 : W := mkw 0xb037400b7001b6e0 0x12b037400b7001b6 0xf13fc00ff833ffff 0xbff13fc00ff833ff

def z1046 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x013ffff000000079 0x44013ffff0000000

def z1047 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff030cc007f 0x67fffffff030cc00

def z1048 : W := mkw 0xf5fb9b6000000000 0x42f5fb9b60000000 0xf3fffff00000007d 0x44f3fffff0000000

def z1049 : W := mkw 0xb03740024001a480 0x02b03740024001a4 0xf03fc00fc003ffef 0xb7f03fc00fc003ff

def z1050 : W := mkw 0xbafb9b6000000000 0x43bafb9b60000000 0xf2fffff00000006f 0x47f2fffff0000000

def z1051 : W := mkw 0xba7f13af34c53aea 0x17ba7f13af34c53a 0x32fc038e30cc3804 0x2732fc038e30cc38

def z1052 : W := mkw 0x1a7b9b6000000000 0x411a7b9b60000000 0x3ffffff00000007f 0x473ffffff0000000

def z1053 : W := mkw 0x4fc8bff48ff2491c 0x4d4fc8bff48ff249 0x0fc03ff00ff00010 0x480fc03ff00ff000

def z1054 : W := mkw 0xfffb9b6082280000 0x63fffb9b60822800 0xfffffff0003c007f 0x47fffffff0003c00

def z1055 : W := mkw 0x5ffb9b6486a80000 0x615ffb9b6486a800 0x0ffffff00ffc0070 0x4c0ffffff00ffc00

def z1056 : W := mkw 0x107b9b6000000000 0x40107b9b60000000 0x023ffff000000075 0x44023ffff0000000

def z1057 : W := mkw 0x4f80000da6a80000 0x214f80000da6a800 0x3fc0000ffffc009d 0xb83fc0000ffffc00

def z1058 : W := mkw 0xfffb9b6000000000 0x43fffb9b60000000 0xfffffff008c000ff 0x6ffffffff008c000

def z1059 : W := mkw 0xba7b9b6000000000 0x43ba7b9b60000000 0xfe3ffff00000007f 0x47fe3ffff0000000

def z1060 : W := mkw 0x4fd99b6000000000 0x414fd99b60000000 0x0fddfff000000050 0x440fddfff0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z8,z3,z4,z5]),(0,[z9,z10,z1,z7,z3,z4,z5]),(0,[z11,z0,z1,z7,z3,z4,z5]),(0,[z10,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z13,z7,z3,z4,z5]),(0,[z0,z14,z15,z7,z3,z4,z5]),(1,[z0,z1,z7,z16,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z5])],[(0,[z0,z1,z7,z17,z3,z4,z5]),(0,[z9,z0,z1,z7,z3,z4,z18]),(0,[z19,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z20,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z21,z5]),(0,[z22,z0,z1,z7,z3,z4,z5]),(0,[z23,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z24,z3,z4])],[(0,[z25,z1,z26,z7,z3,z4,z5]),(0,[z0,z1,z7,z27,z3,z4,z5]),(0,[z0,z1,z7,z28,z3,z4,z18]),(0,[z29,z0,z1,z7,z3,z4,z5]),(0,[z30,z0,z1,z7,z3,z4,z31])],[(0,[z32,z0,z1,z7,z3,z4,z18]),(0,[z33,z0,z1,z7,z3,z4,z5]),(0,[z0,z34,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z4,z35,z5]),(0,[z0,z1,z36,z7,z3,z4,z5]),(0,[z37,z0,z7,z38,z3,z4,z5]),(0,[z39,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z40,z5])],[(0,[z0,z1,z15,z3,z4,z41,z5]),(0,[z0,z1,z12,z7,z42,z3,z4])],[(1,[z0,z1,z7,z3,z43,z5]),(0,[z0,z1,z7,z3,z44,z4,z5]),(0,[z45,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z46,z4,z5]),(0,[z0,z1,z7,z3,z4,z47,z5]),(0,[z0,z1,z7,z3,z48,z4,z5]),(0,[z0,z1,z7,z49,z3,z4,z50]),(0,[z0,z1,z7,z42,z3,z4,z18])]],
   [[(0,[z51,z0,z1,z52,z3,z4,z5]),(0,[z0,z1,z7,z53,z3,z4,z5]),(0,[z0,z1,z7,z38,z4,z5,z54]),(0,[z55,z0,z1,z7,z3,z4,z18])],[(0,[z56,z1,z26,z7,z3,z4,z5]),(0,[z57,z0,z25,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z58]),(0,[z0,z14,z1,z12,z7,z3,z4]),(1,[z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z3,z4,z59,z5]),(0,[z0,z60,z1,z7,z61,z4,z5]),(0,[z0,z1,z62,z7,z3,z4,z5])],[(0,[z63,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z17,z64,z3,z4,z5]),(0,[z65,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z66,z4,z5]),(0,[z0,z67,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z68,z5]),(0,[z0,z1,z7,z3,z4,z69,z5]),(0,[z0,z1,z7,z3,z4,z5,z70]),(0,[z0,z1,z7,z71,z3,z4,z5])],[(0,[z0,z1,z72,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z73,z4,z5]),(1,[z0,z1,z74,z3,z4,z5])],[(0,[z0,z1,z7,z3,z75,z4,z5]),(0,[z0,z1,z7,z3,z76,z5,z18]),(0,[z0,z1,z7,z3,z4,z5,z77])],[(1,[z0,z1,z7,z3,z76,z18]),(0,[z0,z1,z7,z3,z4,z78,z5]),(0,[z0,z1,z7,z3,z4,z79,z5]),(0,[z0,z1,z7,z3,z80,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z54]),(0,[z0,z1,z81,z7,z3,z4,z5])],[(1,[z0,z82,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z83]),(0,[z84,z0,z1,z7,z3,z4,z5])],[(0,[z85,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z86]),(0,[z0,z1,z7,z3,z4,z87,z5]),(0,[z0,z1,z7,z3,z88,z4,z18])]],
   [[(0,[z0,z1,z7,z3,z4,z4,z5]),(0,[z0,z1,z7,z3,z50,z89,z5]),(0,[z0,z1,z7,z3,z90,z4,z5])],[(0,[z91,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z92,z5]),(0,[z0,z1,z12,z7,z3,z4,z4])],[(0,[z1,z26,z7,z17,z3,z4,z5]),(0,[z93,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z94,z7,z3,z4,z5]),(0,[z0,z1,z95,z7,z3,z4,z5]),(0,[z0,z1,z7,z96,z61,z3,z5])],[(0,[z97,z98,z0,z1,z7,z3,z4]),(0,[z0,z1,z99,z7,z3,z4,z5]),(1,[z0,z1,z94,z7,z3,z4]),(0,[z100,z0,z1,z7,z3,z4,z5]),(0,[z0,z101,z7,z3,z4,z5,z31]),(0,[z102,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z103,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z104]),(0,[z105,z0,z1,z7,z3,z4,z18]),(0,[z0,z106,z1,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z108,z5]),(0,[z0,z109,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z110,z3,z4,z5]),(0,[z0,z1,z12,z111,z7,z3,z4])],[(0,[z0,z14,z1,z64,z3,z4,z5]),(0,[z112,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z54]),(0,[z0,z1,z7,z113,z3,z4,z18])],[(0,[z0,z1,z7,z114,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z115]),(0,[z116,z0,z1,z7,z3,z4,z5])],[(0,[z117,z0,z1,z7,z3,z4,z5]),(0,[z9,z0,z1,z7,z28,z4,z5]),(0,[z0,z1,z7,z3,z4,z118,z5]),(0,[z119,z0,z1,z7,z120,z3,z5])]],
   [[(0,[z0,z1,z7,z121,z17,z3,z4]),(0,[z122,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z123,z5])],[(0,[z0,z124,z1,z7,z3,z4,z5]),(0,[z0,z125,z1,z7,z3,z4,z5]),(0,[z126,z127,z1,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z12,z7,z120,z3,z4]),(0,[z0,z128,z1,z7,z3,z4,z5])],[(0,[z51,z85,z1,z7,z3,z4,z5]),(0,[z0,z1,z129,z7,z3,z4,z5]),(0,[z130,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z131,z3,z4,z5]),(0,[z132,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z61,z4,z133,z5]),(0,[z134,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z135,z5])],[(0,[z0,z1,z136,z7,z3,z4,z5]),(0,[z137,z0,z1,z7,z4,z138,z5])],[(0,[z0,z1,z7,z3,z139,z4,z5]),(0,[z0,z1,z7,z140,z3,z4,z5]),(0,[z119,z0,z1,z12,z7,z3,z5])],[(0,[z56,z0,z25,z7,z3,z4,z5]),(0,[z56,z0,z1,z141,z3,z4,z5]),(0,[z0,z1,z142,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z143,z4,z5]),(0,[z0,z1,z7,z3,z4,z144,z5]),(0,[z0,z1,z7,z145,z3,z4,z5]),(0,[z0,z101,z1,z7,z146,z4,z5]),(0,[z0,z1,z7,z147,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z148]),(0,[z0,z1,z7,z3,z4,z41,z18])],[(0,[z149,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z52,z15,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z150,z5]),(0,[z0,z1,z7,z151,z3,z4,z5]),(0,[z0,z1,z152,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z153]),(0,[z0,z1,z12,z12,z7,z3,z4])]],
   [[(0,[z57,z0,z26,z7,z3,z4,z5]),(0,[z0,z1,z7,z154,z3,z4,z5]),(0,[z30,z0,z1,z7,z3,z4,z50]),(0,[z0,z1,z7,z155,z3,z4,z5]),(0,[z0,z1,z12,z7,z61,z3,z4]),(0,[z0,z60,z1,z7,z3,z133,z5]),(0,[z0,z1,z156,z7,z3,z4,z5]),(0,[z0,z1,z7,z24,z3,z4,z5]),(0,[z0,z1,z7,z157,z3,z4,z5])],[(1,[z158,z0,z1,z7,z3,z4]),(0,[z105,z0,z1,z7,z3,z4,z159])],[(0,[z98,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z95,z3,z4,z41,z5]),(0,[z97,z0,z1,z7,z3,z88,z4]),(0,[z0,z1,z7,z160,z3,z4,z5])],[(0,[z65,z0,z1,z7,z17,z4,z5]),(0,[z161,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z162,z5]),(0,[z163,z0,z1,z7,z3,z4,z5])],[(0,[z10,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z164]),(0,[z126,z165,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z166,z3,z4,z5])],[(0,[z167,z0,z1,z7,z3,z4,z5]),(0,[z9,z0,z1,z7,z168,z4,z5]),(0,[z0,z7,z38,z3,z169,z4,z5]),(0,[z0,z170,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z171]),(0,[z0,z1,z7,z172,z3,z4,z5]),(0,[z107,z0,z1,z7,z16,z4,z5]),(0,[z0,z1,z95,z7,z3,z173,z4])],[(0,[z0,z1,z174,z7,z3,z4,z5]),(0,[z0,z1,z7,z175,z3,z4,z5])]],
   [[(0,[z51,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z176,z7,z3,z4,z5]),(0,[z0,z1,z7,z177,z3,z4,z5]),(0,[z0,z7,z3,z108,z4,z178,z5]),(0,[z0,z1,z95,z7,z3,z4,z148]),(0,[z0,z1,z7,z3,z179,z4,z5]),(0,[z0,z1,z7,z3,z180,z4,z5])],[(0,[z181,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z52,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z182,z5]),(0,[z91,z105,z1,z7,z3,z4,z5]),(0,[z98,z0,z1,z7,z3,z4,z86]),(0,[z183,z0,z1,z7,z3,z4,z5])],[(0,[z184,z0,z1,z7,z3,z4,z5]),(0,[z10,z1,z7,z28,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z76,z5]),(0,[z0,z1,z7,z3,z185,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z186]),(0,[z0,z1,z7,z187,z3,z4,z5]),(0,[z0,z1,z7,z96,z4,z133,z5])],[(0,[z51,z0,z188,z7,z3,z4,z5]),(0,[z91,z0,z1,z7,z3,z76,z5]),(1,[z55,z0,z1,z120,z3,z5])],[(0,[z0,z1,z189,z7,z3,z4,z5]),(0,[z0,z1,z7,z190,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z191]),(0,[z0,z1,z7,z3,z192,z4,z5])],[(0,[z0,z1,z193,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z194,z5]),(0,[z0,z1,z7,z3,z195,z4,z5]),(0,[z0,z101,z1,z7,z3,z4,z31]),(0,[z0,z1,z7,z196,z3,z4,z5]),(0,[z197,z0,z1,z7,z3,z4,z18])],[(0,[z198,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z168,z4]),(0,[z119,z0,z1,z12,z7,z3,z4])],[(0,[z199,z0,z1,z7,z3,z4,z5]),(1,[z51,z1,z17,z3,z4,z5]),(0,[z0,z1,z7,z200,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z201,z5]),(0,[z202,z0,z1,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z4,z47]),(0,[z0,z1,z203,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z5,z204]),(0,[z0,z1,z7,z3,z4,z205,z5]),(0,[z206,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z168,z4,z18]),(0,[z91,z0,z1,z12,z7,z3,z4]),(0,[z0,z207,z1,z7,z3,z4,z5]),(1,[z0,z207,z1,z7,z3,z18]),(0,[z0,z1,z7,z3,z208,z4,z5])],[(0,[z0,z1,z7,z3,z4,z209,z5]),(1,[z0,z14,z15,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z210,z5]),(0,[z107,z0,z1,z74,z3,z4,z5]),(0,[z0,z1,z7,z211,z3,z4,z5]),(0,[z0,z1,z7,z3,z212,z4,z5]),(0,[z0,z1,z213,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z214,z4,z18]),(0,[z0,z1,z12,z215,z7,z3,z4])],[(0,[z126,z0,z14,z7,z3,z4,z5]),(0,[z0,z1,z7,z216,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z89,z5]),(0,[z0,z1,z7,z3,z4,z138,z18]),(0,[z0,z1,z217,z12,z7,z3,z4])],[(0,[z85,z1,z26,z7,z3,z4,z5]),(0,[z0,z1,z7,z218,z3,z4,z5]),(0,[z0,z1,z52,z7,z3,z4,z18]),(0,[z1,z7,z3,z219,z4,z76,z5]),(0,[z37,z0,z1,z7,z38,z4,z5]),(1,[z119,z0,z1,z12,z7,z3])],[(0,[z0,z1,z12,z7,z28,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z220]),(0,[z0,z1,z7,z3,z221,z4,z5]),(0,[z0,z1,z7,z3,z222,z4,z5]),(0,[z223,z0,z1,z7,z3,z4,z5])],[(0,[z56,z0,z26,z7,z3,z4,z5]),(0,[z51,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z4,z224,z5]),(0,[z0,z1,z225,z7,z3,z4,z5]),(0,[z107,z0,z7,z3,z4,z178,z5]),(0,[z97,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z96,z3,z4,z226]),(0,[z227,z0,z1,z7,z3,z4,z5])],[(0,[z228,z0,z1,z7,z3,z4,z5]),(0,[z229,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z74,z7,z3,z4,z5]),(0,[z0,z230,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z173,z4,z5])],[(0,[z0,z1,z7,z61,z3,z4,z5]),(0,[z0,z231,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z232,z7,z3,z4,z18])],[(1,[z57,z25,z7,z3,z4,z5]),(0,[z0,z1,z7,z233,z3,z4,z5]),(1,[z0,z1,z7,z3,z219,z18]),(0,[z0,z1,z7,z64,z3,z4,z18]),(0,[z0,z1,z234,z7,z3,z4,z5]),(0,[z0,z1,z7,z49,z3,z4,z18]),(0,[z235,z0,z1,z7,z3,z4,z18])],[(0,[z0,z101,z1,z7,z3,z4,z18]),(0,[z0,z7,z3,z4,z50,z5,z31]),(0,[z0,z1,z7,z3,z4,z236,z5])],[(0,[z1,z26,z7,z3,z4,z76,z5]),(0,[z237,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z238,z5]),(0,[z0,z1,z7,z3,z239,z4,z5]),(0,[z37,z0,z1,z7,z169,z4,z5]),(0,[z0,z1,z240,z7,z241,z4,z5]),(0,[z242,z0,z1,z7,z3,z4,z5]),(0,[z243,z0,z1,z7,z3,z4,z18])],[],[(0,[z244,z0,z1,z7,z3,z4,z5]),(0,[z245,z0,z1,z7,z3,z4,z5]),(0,[z246,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z247,z3,z4,z5])],[(0,[z0,z1,z248,z7,z3,z4,z5]),(0,[z0,z1,z12,z26,z7,z3,z4]),(0,[z0,z1,z7,z249,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z250,z5]),(0,[z0,z1,z240,z7,z3,z4,z5])]],
   [[(0,[z37,z0,z1,z7,z3,z4,z5]),(0,[z107,z0,z207,z7,z3,z4,z5]),(1,[z0,z1,z7,z251,z4,z5]),(0,[z0,z252,z1,z7,z3,z4,z5])],[(0,[z0,z253,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z219,z5,z18]),(0,[z98,z0,z1,z12,z7,z3,z4]),(0,[z254,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z255]),(0,[z256,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z257])],[(0,[z0,z1,z7,z3,z4,z5,z258]),(0,[z0,z1,z7,z3,z4,z133,z18]),(0,[z0,z1,z7,z259,z3,z4,z5])],[(0,[z260,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z261,z5]),(0,[z0,z1,z7,z3,z262,z4,z5]),(0,[z0,z1,z7,z3,z4,z50,z5]),(0,[z263,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z187,z120,z3,z4])],[(0,[z0,z264,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z87,z5])],[(1,[z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z265]),(0,[z0,z1,z7,z266,z3,z4,z5])],[(0,[z0,z1,z12,z7,z17,z3,z4]),(1,[z9,z1,z7,z168,z4,z5]),(1,[z0,z1,z7,z267,z3,z5]),(0,[z0,z1,z7,z96,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z18,z54])],[(0,[z0,z268,z1,z7,z3,z4,z5]),(0,[z0,z1,z269,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z178,z5]),(0,[z0,z1,z7,z120,z3,z5,z18]),(0,[z0,z1,z7,z267,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z270]),(0,[z0,z271,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z272,z7,z3,z219,z4]),(0,[z273,z0,z1,z7,z3,z4,z5]),(0,[z137,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z274,z7,z3,z4,z5]),(0,[z181,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z275,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z219,z4,z18]),(0,[z126,z0,z7,z64,z3,z4,z5]),(0,[z276,z0,z1,z7,z3,z4,z5]),(0,[z277,z0,z1,z7,z3,z4,z18])],[(0,[z0,z1,z12,z7,z3,z4,z86]),(0,[z32,z0,z1,z232,z7,z3,z4]),(0,[z278,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z279,z4,z5])],[(0,[z1,z7,z3,z4,z144,z5,z86]),(0,[z126,z0,z1,z7,z3,z4,z18]),(0,[z0,z101,z1,z7,z3,z4,z50])],[(0,[z280,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z281,z5]),(0,[z0,z60,z1,z7,z38,z4,z5]),(0,[z119,z0,z207,z1,z7,z3,z5]),(0,[z0,z1,z7,z282,z3,z4,z5]),(0,[z0,z1,z283,z7,z3,z4,z5])],[(0,[z284,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z64,z3,z4]),(0,[z285,z0,z1,z7,z3,z4,z5])],[(0,[z0,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z286,z3,z4,z5]),(0,[z0,z1,z7,z287,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z288,z4])],[(0,[z0,z1,z7,z3,z4,z289,z5]),(1,[z91,z1,z7,z3,z219,z5]),(0,[z0,z1,z7,z3,z4,z290,z5]),(0,[z0,z207,z1,z12,z7,z3,z4]),(0,[z291,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z108,z4,z5]),(0,[z0,z1,z7,z3,z4,z50,z54]),(0,[z0,z1,z7,z3,z4,z5,z292]),(0,[z55,z0,z1,z95,z3,z4,z5])],[(0,[z0,z1,z293,z7,z3,z4,z5]),(0,[z158,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z294,z3,z4,z5]),(0,[z0,z1,z7,z38,z3,z4,z18]),(0,[z0,z1,z295,z7,z3,z4,z5])],[(0,[z0,z1,z296,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z297,z4,z5]),(0,[z0,z1,z7,z298,z3,z4,z5]),(0,[z30,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z4,z299,z5]),(0,[z119,z0,z1,z7,z3,z4,z5])],[(0,[z0,z25,z14,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z300,z5]),(0,[z0,z1,z301,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z41,z18]),(0,[z0,z1,z302,z7,z3,z4,z5])],[(0,[z91,z1,z26,z7,z3,z4,z5]),(0,[z303,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z304]),(0,[z0,z1,z7,z28,z3,z4,z5]),(0,[z227,z0,z1,z12,z7,z3,z4])],[(0,[z0,z305,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z306,z5]),(0,[z0,z60,z1,z7,z169,z4,z5]),(0,[z0,z1,z7,z3,z307,z4,z5]),(0,[z0,z1,z7,z3,z4,z308,z5]),(0,[z0,z1,z7,z309,z3,z4,z5])],[(0,[z0,z1,z217,z7,z3,z4,z5]),(0,[z310,z0,z1,z7,z3,z4,z5]),(0,[z311,z0,z1,z7,z3,z4,z5]),(0,[z312,z0,z1,z7,z3,z4,z5]),(0,[z0,z313,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z314,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z178,z18]),(1,[z0,z1,z7,z315,z4,z5])]],
   [[(0,[z0,z1,z12,z7,z3,z88,z4])],[(1,[z85,z1,z52,z3,z4,z5]),(0,[z0,z316,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z317,z4,z5]),(0,[z0,z1,z7,z318,z3,z4,z5]),(0,[z0,z60,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z42,z3,z4,z5])],[(0,[z10,z0,z1,z240,z7,z4,z5]),(0,[z0,z1,z7,z3,z169,z4,z18]),(0,[z237,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z169,z4,z133,z5]),(1,[z0,z1,z7,z3,z4,z148]),(0,[z319,z0,z1,z7,z3,z4,z5])],[(0,[z320,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z321,z5])],[(0,[z0,z1,z7,z322,z3,z4,z5]),(0,[z107,z119,z0,z1,z7,z3,z5]),(0,[z0,z1,z7,z3,z4,z5,z323]),(0,[z0,z324,z1,z7,z3,z4,z5]),(0,[z0,z325,z1,z7,z3,z4,z5])],[(0,[z0,z1,z326,z7,z3,z4,z5]),(0,[z91,z1,z7,z3,z219,z4,z5]),(0,[z327,z0,z1,z7,z3,z4,z5]),(0,[z0,z207,z7,z3,z108,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z31]),(0,[z0,z1,z7,z328,z3,z4,z5])],[(0,[z57,z0,z1,z7,z3,z4,z18]),(0,[z329,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z143,z5]),(0,[z0,z1,z330,z7,z3,z4,z5]),(0,[z37,z0,z1,z12,z7,z3,z4])]],
   [[(0,[z0,z1,z7,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z68]),(0,[z0,z1,z331,z7,z3,z4,z5])],[(0,[z0,z1,z7,z332,z3,z4,z5]),(0,[z333,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z334,z3,z4,z5]),(0,[z335,z0,z1,z7,z3,z4,z5]),(0,[z55,z0,z1,z7,z120,z3,z5]),(0,[z336,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z49,z3,z4])],[(0,[z0,z1,z7,z337,z3,z4,z5]),(0,[z0,z1,z12,z7,z38,z3,z4]),(0,[z338,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z12,z7,z3,z5,z18])],[(0,[z0,z1,z7,z339,z3,z4,z5]),(0,[z57,z25,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z340,z4,z5]),(1,[z0,z1,z12,z7,z3,z4])],[(0,[z341,z0,z1,z7,z3,z4,z5]),(0,[z32,z0,z1,z7,z3,z4,z144]),(0,[z0,z1,z342,z7,z3,z4,z5]),(0,[z0,z1,z215,z7,z3,z4,z5])],[(0,[z0,z82,z1,z7,z3,z4,z5]),(1,[z65,z0,z1,z7,z4,z5]),(0,[z105,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z343,z5]),(0,[z0,z1,z344,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z251,z4,z5]),(0,[z0,z1,z7,z345,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z31]),(0,[z243,z0,z1,z7,z42,z4,z5])],[(1,[z0,z1,z7,z3,z89,z5]),(0,[z137,z0,z1,z12,z7,z3,z4])]],
   [[(0,[z32,z1,z7,z3,z4,z144,z5]),(0,[z346,z0,z1,z7,z3,z4,z5]),(0,[z0,z347,z1,z7,z3,z4,z5]),(0,[z348,z0,z1,z7,z3,z4,z5]),(1,[z97,z0,z1,z3,z88,z4])],[(0,[z349,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z350,z5]),(1,[z107,z0,z1,z7,z3,z18]),(0,[z351,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z352,z7,z3,z4,z5]),(0,[z0,z1,z353,z7,z3,z4,z5])],[(0,[z0,z25,z7,z64,z3,z4,z5]),(0,[z85,z1,z52,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z354,z5]),(0,[z0,z1,z7,z355,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z356,z5])],[(0,[z0,z1,z7,z3,z357,z4,z5]),(0,[z107,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z16,z4,z5]),(0,[z358,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z18])],[(0,[z0,z1,z2,z7,z3,z4,z5]),(0,[z359,z0,z1,z7,z3,z4,z5]),(0,[z0,z25,z1,z7,z3,z4,z18]),(0,[z119,z0,z1,z7,z3,z76,z5]),(0,[z0,z15,z7,z64,z3,z4,z5]),(0,[z0,z360,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z4,z361,z5]),(0,[z137,z0,z1,z3,z4,z138,z5]),(0,[z0,z1,z7,z3,z4,z362,z18])],[(0,[z0,z1,z7,z3,z363,z4,z5]),(0,[z364,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z241,z3,z4]),(0,[z365,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z111,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z366]),(0,[z0,z1,z7,z3,z41,z5,z18]),(0,[z0,z1,z367,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z368,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z369,z5]),(0,[z0,z370,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z41,z5]),(0,[z0,z1,z7,z371,z3,z4,z5])],[(0,[z0,z1,z7,z3,z372,z4,z5]),(0,[z85,z0,z1,z52,z3,z4,z5]),(0,[z373,z0,z1,z7,z3,z4,z5]),(0,[z0,z374,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z375,z5]),(0,[z376,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z377,z5]),(1,[z0,z60,z1,z7,z96,z5])],[(0,[z0,z1,z7,z3,z4,z378,z5]),(0,[z379,z0,z1,z7,z3,z4,z5]),(1,[z107,z0,z7,z3,z178,z5]),(0,[z0,z1,z95,z7,z3,z41,z5])],[(1,[z10,z1,z7,z28,z4,z5]),(1,[z30,z0,z7,z3,z4,z50]),(0,[z0,z1,z7,z3,z380,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z18])],[(0,[z56,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z381,z3,z4,z5])],[(0,[z382,z0,z1,z7,z3,z4,z5]),(0,[z383,z0,z1,z7,z3,z4,z5]),(0,[z384,z0,z1,z7,z3,z4,z5]),(0,[z0,z385,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z71,z3,z4,z18])],[(0,[z386,z0,z1,z7,z3,z4,z5]),(0,[z0,z387,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z388,z4,z5])],[(0,[z0,z1,z7,z3,z4,z389,z5]),(1,[z0,z1,z7,z3,z4,z390]),(0,[z391,z0,z1,z7,z3,z4,z5]),(0,[z97,z0,z1,z7,z3,z4,z392]),(0,[z0,z1,z393,z7,z3,z4,z5]),(0,[z394,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z226])]],
   [[(0,[z1,z52,z7,z17,z3,z4,z5]),(1,[z137,z0,z1,z4,z138,z5]),(0,[z0,z395,z1,z7,z3,z4,z5]),(0,[z0,z60,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z18,z270])],[],[(0,[z0,z396,z1,z7,z3,z4,z5]),(0,[z0,z397,z1,z7,z3,z4,z5]),(0,[z0,z1,z232,z7,z3,z4,z392]),(0,[z319,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z398,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z399]),(0,[z273,z0,z1,z7,z3,z50,z5])],[(0,[z400,z0,z1,z7,z3,z4,z5]),(0,[z91,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z12,z7,z3,z4,z50]),(0,[z0,z1,z7,z120,z3,z4,z323]),(0,[z0,z325,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z4,z401,z5]),(0,[z51,z1,z7,z17,z3,z4,z5]),(0,[z0,z402,z1,z7,z3,z4,z5]),(0,[z0,z1,z95,z7,z3,z4,z18]),(0,[z0,z403,z1,z7,z3,z4,z5])],[(0,[z0,z404,z1,z7,z3,z4,z5]),(0,[z405,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z328,z61,z3,z4]),(0,[z0,z1,z7,z3,z4,z18,z70])],[(0,[z0,z1,z7,z3,z406,z4,z5]),(1,[z0,z1,z7,z3,z214,z18])]],
   [[(0,[z0,z1,z7,z407,z3,z4,z5]),(0,[z243,z0,z1,z7,z49,z4,z5]),(0,[z0,z1,z7,z3,z408,z4,z5])],[(0,[z56,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z409,z5]),(0,[z137,z10,z0,z1,z7,z4,z5]),(0,[z0,z1,z7,z410,z3,z4,z5]),(0,[z411,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z168,z4,z5]),(0,[z37,z0,z360,z7,z3,z4,z5]),(1,[z0,z1,z412,z3,z4,z5]),(0,[z0,z1,z7,z413,z3,z4,z5]),(0,[z0,z1,z7,z414,z3,z4,z5])],[(0,[z0,z415,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z416,z4,z5]),(0,[z0,z1,z7,z3,z4,z18,z86]),(0,[z417,z0,z1,z7,z3,z4,z5]),(1,[z0,z360,z7,z169,z4,z5]),(0,[z0,z1,z7,z3,z4,z31,z54]),(1,[z0,z1,z240,z241,z4,z5]),(0,[z0,z1,z7,z3,z418,z4,z5]),(0,[z0,z1,z7,z3,z214,z4,z5])],[(0,[z0,z1,z419,z7,z3,z4,z5]),(0,[z0,z14,z1,z15,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z138,z5]),(0,[z420,z0,z1,z7,z3,z4,z5]),(0,[z0,z421,z1,z7,z3,z4,z18])],[(0,[z0,z422,z1,z7,z3,z4,z5]),(0,[z423,z0,z1,z7,z3,z4,z5]),(0,[z105,z1,z7,z3,z4,z76,z5]),(0,[z105,z0,z1,z12,z7,z3,z4]),(0,[z333,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z424,z3,z4,z5]),(0,[z0,z1,z7,z425,z3,z4,z5])],[(0,[z0,z1,z7,z426,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z427,z5]),(0,[z51,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z428,z4,z5]),(0,[z0,z127,z1,z7,z3,z4,z5]),(0,[z429,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z430,z0,z1,z7,z3,z4,z5]),(0,[z0,z431,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z432,z4,z5]),(0,[z137,z0,z1,z7,z241,z4,z5]),(0,[z433,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z434,z3,z4,z5]),(0,[z137,z9,z0,z1,z7,z4,z5]),(1,[z165,z1,z7,z3,z4,z5]),(0,[z435,z0,z1,z7,z3,z4,z5]),(0,[z0,z436,z1,z7,z3,z4,z5]),(0,[z137,z0,z1,z240,z3,z4,z5]),(0,[z0,z1,z232,z7,z3,z87,z5]),(0,[z0,z1,z7,z3,z4,z437,z18])],[(0,[z438,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z439,z5]),(0,[z0,z1,z7,z3,z440,z4,z5]),(0,[z107,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z5,z441]),(0,[z442,z0,z1,z7,z3,z4,z5]),(0,[z443,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z444,z5])],[(0,[z445,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z64,z3,z4,z5]),(0,[z0,z360,z7,z3,z169,z4,z5]),(0,[z235,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z49,z3,z4,z5]),(0,[z0,z1,z12,z7,z157,z3,z4])],[(0,[z0,z1,z446,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z447,z5]),(1,[z0,z1,z7,z3,z4,z77]),(0,[z448,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z328,z3,z4]),(0,[z0,z1,z7,z449,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z450,z5])],[(0,[z451,z0,z1,z7,z3,z4,z5]),(0,[z98,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z452,z4,z5]),(0,[z0,z1,z7,z3,z4,z453,z5])],[(0,[z0,z26,z7,z64,z3,z4,z5]),(0,[z0,z454,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z455,z3,z4,z5]),(0,[z0,z1,z7,z456,z3,z4,z5]),(0,[z0,z1,z7,z3,z457,z4,z5]),(0,[z0,z1,z7,z3,z458,z4,z5]),(0,[z243,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z121,z3,z4,z5]),(0,[z10,z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z459,z4,z5]),(0,[z0,z1,z460,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z461,z4,z5]),(0,[z0,z60,z1,z7,z96,z4,z5])]],
   [[(0,[z0,z1,z7,z462,z3,z4,z5]),(0,[z463,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z49,z42,z3,z4])],[(0,[z0,z1,z26,z7,z3,z4,z5]),(0,[z85,z0,z1,z17,z3,z4,z5]),(1,[z0,z1,z7,z464,z4,z5]),(0,[z0,z1,z7,z3,z465,z4,z5]),(0,[z0,z1,z7,z3,z4,z466,z5])],[(0,[z0,z1,z7,z3,z467,z4,z5]),(0,[z468,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z469,z7,z3,z4,z5]),(0,[z0,z470,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z120,z3,z4,z18])],[(0,[z0,z1,z7,z471,z3,z4,z5]),(0,[z51,z0,z82,z7,z3,z4,z5]),(0,[z0,z207,z1,z7,z3,z5,z18])],[(1,[z0,z1,z7,z3,z4,z104]),(1,[z0,z1,z7,z146,z4,z5]),(0,[z0,z472,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z473,z5]),(0,[z474,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z15,z17,z3,z4,z5]),(0,[z9,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z12,z7,z3,z169,z4]),(0,[z0,z1,z7,z3,z4,z18,z31]),(0,[z0,z1,z7,z3,z4,z475,z5]),(0,[z0,z1,z120,z3,z4,z41,z5])]],
   [[(0,[z119,z0,z1,z7,z3,z219,z5]),(0,[z32,z0,z1,z7,z3,z4,z5]),(0,[z97,z32,z0,z1,z7,z3,z4]),(0,[z0,z14,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z4,z476,z5])],[(0,[z0,z1,z7,z3,z4,z477,z5]),(0,[z0,z478,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z479,z3,z4,z5]),(1,[z98,z1,z7,z3,z4,z86]),(0,[z0,z1,z64,z3,z4,z41,z5]),(0,[z0,z1,z7,z169,z4,z5,z54]),(0,[z0,z1,z241,z3,z4,z138,z5]),(0,[z0,z1,z7,z480,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z481]),(0,[z482,z0,z1,z7,z3,z4,z5])],[(0,[z91,z0,z1,z7,z3,z219,z5]),(1,[z0,z1,z272,z7,z3,z4]),(0,[z0,z1,z12,z7,z3,z219,z4]),(0,[z0,z1,z7,z3,z483,z4,z5]),(1,[z0,z1,z7,z3,z4,z323]),(0,[z484,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z219,z4,z5]),(0,[z277,z0,z1,z7,z3,z4,z5]),(0,[z0,z207,z1,z7,z3,z4,z18]),(0,[z485,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z95,z3,z41,z5]),(0,[z0,z1,z7,z3,z4,z486,z5])],[(0,[z0,z14,z26,z7,z3,z4,z5]),(0,[z0,z1,z487,z7,z3,z4,z5]),(0,[z0,z1,z7,z146,z3,z4,z5]),(1,[z0,z1,z7,z3,z173,z4]),(0,[z488,z0,z1,z7,z3,z4,z5])],[(1,[z0,z1,z141,z3,z4,z5]),(0,[z126,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z489,z3,z4,z5]),(0,[z490,z0,z1,z7,z3,z4,z5]),(0,[z55,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z491]),(0,[z85,z0,z1,z7,z3,z4,z18]),(0,[z0,z101,z1,z7,z315,z4,z5]),(0,[z0,z1,z7,z3,z4,z492,z5]),(0,[z493,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z95,z7,z3,z4])],[(0,[z0,z1,z7,z3,z4,z494,z5]),(0,[z32,z0,z1,z7,z3,z4,z86]),(0,[z0,z1,z7,z495,z3,z4,z5]),(0,[z0,z496,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z241,z3,z4,z18]),(0,[z0,z1,z7,z3,z4,z5,z497]),(0,[z0,z1,z7,z3,z4,z18,z366])]],
   [[(0,[z0,z1,z7,z498,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z499,z5]),(0,[z0,z1,z7,z3,z4,z5,z500]),(0,[z0,z1,z7,z501,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z502])],[],[(0,[z32,z98,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z61,z3,z4,z18])],[(0,[z0,z1,z15,z7,z3,z4,z18]),(0,[z0,z1,z7,z38,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z503,z5]),(0,[z504,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z505,z4,z18])],[(0,[z506,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z164]),(0,[z30,z0,z1,z7,z3,z4,z5]),(0,[z0,z507,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z88,z4,z5]),(0,[z0,z1,z7,z3,z4,z18,z18])],[(0,[z56,z57,z1,z7,z3,z4,z5]),(0,[z10,z0,z1,z7,z28,z4,z5])],[(0,[z51,z0,z1,z12,z7,z3,z4]),(0,[z0,z508,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z96,z3,z4])],[(0,[z509,z0,z1,z7,z3,z4,z5]),(0,[z57,z1,z7,z17,z3,z4,z5]),(0,[z0,z1,z7,z464,z17,z4,z5]),(0,[z0,z1,z7,z510,z3,z4,z5]),(0,[z0,z511,z1,z7,z3,z4,z5]),(0,[z0,z1,z512,z7,z3,z4,z5])]],
   [[(0,[z107,z0,z1,z412,z3,z4,z5]),(0,[z513,z0,z1,z7,z3,z4,z5]),(0,[z514,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z515,z3,z4,z5]),(0,[z0,z1,z516,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z517,z5]),(0,[z518,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z42,z3,z4,z54])],[(0,[z519,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z520,z7,z3,z4,z5]),(0,[z0,z521,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z113,z3,z4,z5])],[(0,[z0,z1,z7,z522,z3,z4,z5]),(0,[z0,z60,z1,z7,z96,z3,z5])],[(0,[z0,z1,z7,z523,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z524,z5]),(0,[z0,z1,z7,z3,z169,z4,z5]),(1,[z0,z1,z7,z3,z4,z191])],[(0,[z91,z57,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z525,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z392]),(0,[z0,z1,z7,z49,z4,z5,z54]),(0,[z243,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z526,z3,z4,z5]),(0,[z0,z1,z272,z7,z3,z4,z5]),(1,[z527,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z528,z5]),(0,[z0,z1,z7,z3,z4,z50,z18]),(0,[z0,z1,z7,z529,z3,z4,z5]),(0,[z530,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z531,z7,z3,z4,z5])],[(0,[z0,z1,z7,z17,z3,z4,z18]),(0,[z0,z1,z7,z3,z532,z4,z5])]],
   [[(0,[z533,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z121,z3,z4]),(0,[z0,z1,z534,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z535]),(0,[z536,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z537])],[(0,[z57,z0,z1,z7,z3,z4,z5]),(1,[z56,z26,z7,z3,z4,z5]),(0,[z538,z0,z1,z7,z3,z4,z5]),(0,[z0,z360,z1,z7,z38,z4,z5]),(0,[z0,z1,z7,z96,z3,z4,z18]),(0,[z539,z0,z1,z7,z3,z4,z5])],[(0,[z540,z0,z1,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z4,z77]),(0,[z541,z0,z1,z7,z3,z4,z5]),(0,[z119,z0,z1,z7,z3,z41,z5]),(0,[z0,z1,z12,z232,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z542,z5]),(0,[z0,z1,z7,z3,z4,z543,z5])],[(0,[z0,z1,z7,z3,z544,z4,z5]),(0,[z10,z0,z1,z7,z168,z4,z5]),(0,[z0,z1,z7,z3,z4,z545,z5]),(0,[z0,z1,z7,z546,z3,z4,z5]),(0,[z0,z1,z7,z547,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z178]),(0,[z0,z1,z7,z61,z3,z4,z257])],[(0,[z0,z1,z7,z548,z3,z4,z5]),(0,[z549,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z550,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z551,z5])],[(0,[z9,z0,z1,z12,z7,z3,z4]),(0,[z105,z0,z1,z7,z3,z4,z104]),(0,[z0,z1,z552,z7,z3,z4,z5]),(0,[z553,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z3,z88,z4,z5,z392]),(0,[z0,z1,z7,z3,z4,z5,z392])],[(0,[z0,z1,z7,z3,z4,z554,z5]),(0,[z0,z1,z7,z555,z3,z4,z5])],[(0,[z556,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z76]),(0,[z32,z0,z1,z12,z7,z3,z4]),(0,[z0,z527,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z108,z4,z191]),(0,[z0,z557,z1,z7,z3,z4,z5])]],
   [[(1,[z37,z0,z7,z38,z4,z5]),(1,[z0,z1,z7,z120,z3,z18])],[(0,[z484,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z558,z4,z5]),(1,[z105,z1,z7,z3,z76,z5]),(0,[z0,z360,z1,z7,z169,z4,z5]),(0,[z0,z1,z7,z559,z3,z4,z5]),(0,[z0,z1,z7,z560,z3,z4,z5])],[(0,[z0,z1,z561,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z562,z4,z5]),(0,[z0,z1,z81,z7,z3,z4,z18])],[(0,[z0,z1,z563,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z564,z4,z5]),(0,[z126,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z565,z3,z4,z5]),(1,[z93,z1,z7,z3,z4,z5]),(0,[z0,z1,z566,z7,z3,z4,z5]),(0,[z55,z0,z1,z12,z7,z3,z4]),(1,[z0,z1,z7,z61,z133,z5])],[(0,[z567,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z568,z5]),(1,[z0,z1,z7,z3,z4,z159]),(0,[z0,z1,z7,z3,z4,z569,z5]),(0,[z119,z0,z1,z7,z3,z4,z18]),(0,[z0,z570,z1,z7,z3,z4,z5]),(0,[z0,z1,z571,z7,z3,z4,z5])],[(0,[z0,z25,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z572,z5]),(0,[z0,z360,z1,z7,z3,z4,z5]),(0,[z0,z1,z573,z7,z3,z4,z5]),(0,[z0,z1,z7,z42,z4,z5,z54]),(0,[z0,z1,z7,z3,z4,z4,z18]),(1,[z0,z1,z12,z7,z3,z18]),(0,[z0,z1,z7,z3,z4,z362,z5])],[(0,[z0,z1,z7,z3,z4,z574,z5]),(0,[z0,z1,z12,z7,z3,z4,z138]),(0,[z0,z1,z7,z3,z575,z4,z5])]],
   [[(0,[z0,z1,z576,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z577])],[(1,[z127,z1,z7,z3,z4,z5]),(0,[z0,z578,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z4,z257])],[(0,[z0,z1,z7,z3,z315,z4,z5]),(0,[z0,z1,z579,z7,z3,z4,z5]),(0,[z197,z0,z1,z7,z3,z4,z5])],[(0,[z105,z0,z1,z7,z3,z76,z5]),(0,[z580,z0,z1,z7,z3,z4,z5]),(1,[z0,z207,z7,z3,z108,z5]),(0,[z30,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z581,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z582,z5]),(1,[z126,z0,z64,z3,z4,z5]),(0,[z243,z0,z1,z7,z38,z4,z5]),(0,[z0,z1,z7,z583,z3,z4,z5]),(0,[z0,z60,z1,z7,z3,z4,z18])],[(0,[z0,z1,z7,z3,z4,z5,z5]),(0,[z0,z1,z7,z3,z4,z584,z5]),(0,[z30,z0,z7,z3,z4,z50,z5])],[(0,[z56,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z188,z7,z3,z4,z5]),(0,[z585,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z586,z3,z4,z5]),(0,[z0,z1,z7,z587,z3,z4,z5])],[(0,[z0,z588,z1,z7,z3,z4,z5]),(0,[z589,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z590,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z133])]],
   [[(0,[z0,z1,z52,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z591,z5]),(0,[z126,z0,z1,z64,z3,z4,z5]),(0,[z55,z0,z1,z64,z3,z4,z5]),(0,[z0,z1,z7,z3,z592,z4,z5]),(0,[z0,z593,z1,z7,z3,z4,z5])],[(0,[z594,z0,z1,z7,z3,z4,z5]),(0,[z0,z207,z1,z7,z3,z178,z5]),(0,[z134,z0,z1,z7,z3,z4,z18])],[(0,[z0,z1,z7,z3,z595,z4,z5]),(0,[z9,z1,z7,z3,z168,z4,z5]),(0,[z0,z1,z596,z7,z3,z4,z5]),(0,[z597,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z38,z4,z133,z5]),(0,[z598,z0,z1,z7,z3,z4,z5]),(0,[z97,z0,z1,z7,z3,z4,z5])],[(0,[z0,z599,z1,z7,z3,z4,z5]),(0,[z0,z600,z1,z7,z3,z4,z5]),(0,[z97,z0,z1,z3,z88,z4,z5])],[(0,[z9,z0,z1,z240,z7,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z601]),(0,[z602,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z144,z18]),(0,[z0,z1,z94,z7,z3,z108,z4]),(0,[z0,z603,z1,z7,z3,z4,z5])],[(0,[z0,z1,z604,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z144]),(0,[z243,z0,z1,z7,z169,z4,z5]),(0,[z0,z1,z7,z605,z3,z4,z5]),(0,[z0,z1,z7,z606,z3,z4,z5]),(0,[z0,z1,z232,z7,z3,z4,z5]),(0,[z0,z1,z7,z607,z3,z4,z5])],[(0,[z608,z0,z1,z7,z3,z4,z5]),(0,[z107,z0,z1,z7,z3,z5,z18]),(0,[z0,z1,z232,z7,z267,z3,z5]),(0,[z0,z1,z7,z609,z3,z4,z5])],[(0,[z85,z57,z1,z7,z3,z4,z5]),(0,[z610,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z611,z3,z4,z5]),(0,[z0,z1,z612,z7,z3,z4,z5]),(0,[z0,z101,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z613,z4,z5])]],
   [[(0,[z57,z1,z7,z3,z4,z76,z5]),(0,[z57,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z614,z3,z4,z5]),(0,[z0,z1,z240,z7,z4,z138,z5]),(0,[z0,z1,z240,z241,z3,z4,z5])],[(0,[z0,z1,z7,z464,z3,z4,z5]),(0,[z0,z1,z7,z3,z615,z4,z5]),(0,[z0,z1,z7,z3,z4,z43,z5]),(0,[z0,z1,z7,z616,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z5,z617]),(0,[z618,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z251,z3,z4,z5])],[(0,[z619,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z620,z3,z4,z5]),(0,[z621,z0,z1,z7,z3,z4,z5]),(0,[z98,z0,z1,z232,z7,z3,z4]),(0,[z107,z527,z1,z7,z3,z4,z5]),(0,[z622,z0,z1,z7,z3,z4,z5]),(0,[z97,z0,z1,z232,z3,z4,z5]),(0,[z0,z1,z7,z3,z623,z4,z5])],[(0,[z0,z1,z7,z3,z4,z624,z5]),(0,[z0,z1,z7,z3,z4,z625,z5])],[(0,[z0,z626,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z627,z4,z5]),(0,[z0,z421,z1,z7,z3,z4,z5])],[(0,[z0,z1,z95,z7,z120,z3,z5]),(0,[z0,z1,z7,z3,z4,z133,z5]),(0,[z181,z0,z1,z7,z3,z4,z18])]],
   [[(0,[z0,z1,z7,z628,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z76,z18]),(0,[z0,z1,z7,z3,z629,z4,z5]),(0,[z0,z630,z1,z7,z3,z4,z5])],[(0,[z0,z631,z1,z7,z3,z4,z5]),(0,[z0,z360,z1,z7,z3,z4,z68]),(0,[z0,z207,z1,z7,z3,z108,z5]),(0,[z0,z1,z632,z7,z3,z4,z5])],[(0,[z633,z0,z1,z7,z3,z4,z5]),(0,[z158,z0,z1,z7,z17,z3,z4]),(0,[z0,z1,z7,z3,z634,z4,z5]),(0,[z1,z7,z28,z3,z168,z4,z5])],[(0,[z635,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z437,z5])],[(0,[z0,z1,z7,z636,z3,z4,z5]),(0,[z0,z1,z7,z3,z637,z4,z5]),(0,[z0,z1,z638,z7,z3,z4,z5]),(0,[z0,z1,z7,z639,z3,z4,z5])],[(0,[z0,z25,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z640,z3,z4,z5]),(0,[z0,z360,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z641,z4,z5]),(0,[z0,z1,z12,z7,z3,z4,z41])],[(0,[z642,z0,z1,z7,z3,z4,z5]),(0,[z55,z0,z1,z120,z3,z4,z5]),(0,[z243,z0,z1,z7,z3,z4,z54]),(0,[z119,z0,z1,z7,z3,z214,z5])],[(0,[z0,z1,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z159,z5]),(0,[z643,z0,z1,z7,z3,z4,z5]),(1,[z273,z0,z1,z7,z3,z5]),(0,[z0,z1,z232,z3,z4,z5,z392]),(0,[z644,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z645,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z412,z3,z4,z5]),(0,[z0,z1,z7,z3,z646,z4,z5]),(0,[z0,z1,z7,z3,z4,z647,z5]),(0,[z0,z1,z12,z7,z3,z214,z4])],[(0,[z0,z1,z7,z3,z648,z4,z5]),(0,[z649,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z650,z7,z3,z4,z5]),(0,[z0,z1,z579,z12,z7,z3,z4])],[(0,[z651,z0,z1,z7,z3,z4,z5]),(0,[z652,z0,z1,z7,z3,z4,z5]),(0,[z107,z93,z1,z7,z3,z4,z5]),(0,[z0,z1,z232,z7,z3,z88,z4])],[(0,[z653,z0,z1,z7,z3,z4,z5]),(0,[z98,z0,z1,z7,z3,z43,z5]),(0,[z98,z1,z7,z3,z4,z5,z86]),(0,[z0,z1,z7,z654,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z5,z655])],[(0,[z0,z1,z656,z7,z3,z4,z5]),(1,[z32,z1,z7,z3,z4,z144]),(0,[z0,z34,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z120,z3,z4,z5]),(1,[z0,z1,z7,z187,z3,z4])],[(0,[z657,z0,z1,z7,z3,z4,z5]),(0,[z56,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z658,z5])],[(0,[z0,z1,z7,z3,z4,z5,z659]),(0,[z660,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z661,z7,z3,z4,z5]),(0,[z0,z1,z662,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z18,z392]),(0,[z0,z1,z7,z3,z214,z5,z18])],[(0,[z663,z0,z1,z7,z3,z4,z5]),(0,[z0,z664,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z665,z5]),(1,[z0,z1,z7,z42,z4,z54])]],
   [[(0,[z0,z1,z7,z3,z666,z4,z5]),(0,[z0,z1,z667,z7,z3,z4,z5]),(0,[z0,z1,z668,z7,z3,z4,z5]),(0,[z669,z0,z1,z7,z3,z4,z5]),(1,[z0,z1,z7,z3,z458,z4])],[(1,[z0,z188,z7,z3,z4,z5]),(0,[z670,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z49,z3,z4,z31]),(0,[z0,z1,z12,z240,z7,z3,z4]),(0,[z97,z0,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z96,z3,z458,z4])],[(0,[z0,z14,z1,z7,z3,z4,z5])],[(0,[z671,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z672,z4,z5]),(0,[z0,z1,z7,z3,z4,z178,z5]),(0,[z673,z0,z1,z7,z3,z4,z5])],[(0,[z674,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z240,z7,z3,z4,z18])],[(0,[z0,z1,z7,z3,z675,z4,z5]),(0,[z37,z0,z1,z7,z3,z4,z18]),(0,[z0,z101,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z676,z5])],[(0,[z0,z1,z7,z3,z677,z4,z5]),(0,[z0,z1,z7,z678,z3,z4,z5]),(0,[z0,z1,z7,z3,z679,z4,z5]),(0,[z105,z0,z1,z7,z3,z219,z5]),(0,[z0,z680,z1,z7,z3,z4,z5]),(0,[z98,z0,z1,z7,z3,z4,z144]),(0,[z681,z0,z1,z7,z3,z4,z5])]],
   [[(0,[z85,z0,z1,z7,z3,z4,z5]),(0,[z0,z360,z1,z7,z3,z4,z390]),(0,[z0,z1,z7,z3,z682,z4,z5]),(0,[z243,z0,z1,z7,z49,z3,z4])],[(0,[z0,z1,z7,z3,z4,z5,z683]),(0,[z0,z1,z7,z3,z4,z684,z5]),(0,[z685,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z241,z3,z4,z5]),(0,[z112,z0,z1,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z4,z686,z5]),(0,[z0,z1,z12,z571,z7,z3,z4])],[(0,[z687,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z52,z64,z3,z4,z5]),(0,[z0,z1,z7,z3,z688,z4,z5]),(1,[z0,z1,z7,z3,z4,z18])],[(0,[z126,z0,z1,z15,z3,z4,z5]),(0,[z0,z1,z7,z689,z3,z4,z5]),(0,[z55,z0,z1,z15,z3,z4,z5]),(0,[z0,z690,z1,z7,z3,z4,z5])],[(0,[z0,z1,z15,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z691,z4,z5]),(0,[z0,z1,z7,z3,z4,z692,z5]),(0,[z0,z1,z7,z3,z505,z4,z5])],[(0,[z137,z0,z1,z7,z3,z4,z18])],[(0,[z0,z1,z7,z3,z4,z5,z390]),(0,[z0,z1,z7,z3,z4,z5,z226])]],
   [[(0,[z0,z693,z1,z7,z3,z4,z5]),(0,[z338,z0,z1,z7,z3,z4,z5]),(1,[z0,z101,z7,z3,z4,z31])],[(0,[z0,z1,z7,z694,z3,z4,z5]),(0,[z98,z0,z1,z7,z3,z143,z5]),(0,[z30,z0,z101,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z288,z4,z5])],[(0,[z0,z1,z7,z3,z219,z4,z164]),(0,[z0,z1,z7,z695,z3,z4,z5])],[(0,[z0,z1,z7,z141,z3,z4,z5]),(0,[z0,z1,z696,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z697,z4,z5]),(0,[z0,z1,z7,z698,z3,z4,z5]),(0,[z699,z0,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z700,z4,z5]),(0,[z0,z1,z26,z7,z3,z4,z18]),(0,[z701,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z702,z5]),(1,[z0,z1,z232,z3,z4,z392])],[(0,[z165,z0,z1,z7,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z108,z4]),(0,[z55,z0,z1,z7,z3,z41,z5]),(0,[z0,z1,z7,z703,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z704,z5]),(0,[z0,z1,z7,z3,z108,z4,z18]),(0,[z0,z705,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z61,z3,z133,z5]),(0,[z0,z1,z7,z3,z4,z706,z5]),(0,[z0,z1,z7,z3,z4,z18,z441])],[(0,[z0,z1,z12,z15,z7,z3,z4])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z7,z3,z4,z707]),(0,[z311,z0,z1,z7,z3,z18])],[(0,[z708,z0,z1,z7,z3,z5]),(0,[z0,z1,z7,z709,z4,z5]),(0,[z0,z1,z7,z3,z219,z104]),(0,[z0,z1,z7,z3,z4,z710])],[(0,[z0,z711,z7,z3,z4,z5]),(0,[z0,z1,z7,z712,z4,z5]),(0,[z93,z1,z12,z7,z3,z4]),(0,[z0,z1,z713,z7,z3,z4]),(0,[z273,z0,z1,z12,z7,z3])],[(0,[z0,z1,z7,z3,z4,z714]),(0,[z0,z1,z7,z3,z4,z715]),(0,[z0,z60,z1,z7,z96,z18]),(0,[z0,z716,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z717,z5]),(0,[z107,z0,z7,z3,z178,z18]),(0,[z0,z1,z7,z718,z3,z4])],[(0,[z158,z0,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z719,z4]),(0,[z10,z1,z7,z28,z4,z18]),(0,[z119,z527,z1,z7,z3,z5])],[(0,[z107,z0,z1,z7,z251,z18]),(0,[z273,z0,z1,z7,z3,z5])],[(0,[z0,z1,z7,z3,z720,z5]),(0,[z199,z0,z1,z7,z3,z18]),(0,[z721,z0,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z722])]],
   [[(0,[z0,z1,z7,z723,z42,z4])],[(0,[z0,z1,z7,z3,z724,z5]),(0,[z119,z0,z1,z272,z7,z3])],[(0,[z158,z0,z1,z7,z464,z4]),(0,[z107,z0,z1,z74,z3,z18]),(0,[z137,z0,z1,z4,z138,z18]),(0,[z55,z0,z1,z725,z3,z5]),(0,[z0,z1,z215,z3,z88,z4])],[(0,[z0,z1,z726,z7,z3,z4]),(0,[z0,z1,z217,z7,z3,z43]),(0,[z727,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z187,z3,z4])],[(0,[z107,z93,z1,z7,z3,z18]),(0,[z0,z1,z412,z3,z5,z18]),(0,[z0,z207,z7,z3,z437,z5]),(0,[z0,z1,z12,z7,z3,z432])],[(0,[z0,z1,z7,z728,z3,z5]),(0,[z107,z0,z1,z7,z3,z729]),(0,[z0,z1,z12,z393,z7,z3])],[(0,[z57,z25,z7,z3,z4,z18]),(0,[z0,z207,z7,z3,z108,z191]),(0,[z0,z1,z7,z730,z3,z5]),(0,[z0,z1,z7,z42,z4,z54]),(0,[z0,z1,z7,z71,z4,z54])],[(0,[z0,z1,z7,z731,z4,z5]),(0,[z0,z1,z7,z3,z732,z5]),(0,[z0,z1,z7,z3,z4,z733]),(0,[z0,z1,z7,z3,z4,z734]),(0,[z55,z0,z1,z120,z3,z5]),(0,[z0,z1,z7,z3,z458,z4])]],
   [[(0,[z0,z188,z7,z3,z4,z5]),(0,[z0,z1,z7,z735,z3,z5]),(0,[z1,z7,z3,z4,z144,z736]),(0,[z737,z1,z7,z3,z4,z5])],[(0,[z670,z26,z7,z3,z4,z5]),(0,[z107,z0,z7,z16,z178,z5]),(0,[z0,z1,z7,z3,z47,z18])],[(0,[z0,z1,z7,z3,z738,z5]),(0,[z32,z1,z7,z3,z4,z736]),(0,[z0,z1,z225,z7,z3,z18]),(0,[z527,z1,z412,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z739]),(0,[z51,z1,z17,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z740]),(0,[z0,z1,z7,z3,z281,z18]),(1,[z0,z1,z3,z741,z4])],[(0,[z0,z207,z1,z7,z3,z18]),(0,[z0,z1,z412,z3,z4,z18])],[(0,[z0,z1,z7,z3,z4,z742]),(0,[z0,z743,z1,z7,z4,z5]),(0,[z0,z744,z7,z3,z4,z5]),(0,[z0,z1,z7,z745,z4,z5]),(0,[z0,z360,z7,z169,z4,z18]),(0,[z107,z93,z7,z3,z178,z5]),(0,[z0,z1,z12,z7,z16,z4]),(0,[z0,z1,z240,z241,z4,z18])],[],[(1,[z26,z141,z3,z4,z5]),(1,[z746,z7,z3,z4,z5]),(0,[z119,z0,z1,z12,z7,z3])]],
   [[(0,[z0,z1,z7,z3,z677,z18]),(0,[z0,z1,z7,z747,z4,z5]),(0,[z0,z1,z748,z3,z4,z5]),(0,[z0,z1,z7,z3,z87,z392]),(0,[z0,z1,z749,z7,z3,z4])],[(0,[z0,z1,z7,z3,z750,z5]),(0,[z0,z1,z7,z3,z299,z18]),(0,[z0,z1,z12,z95,z3,z41]),(0,[z0,z1,z7,z3,z575,z18]),(0,[z0,z1,z7,z751,z4,z18])],[(0,[z0,z1,z7,z3,z752,z5]),(0,[z0,z1,z7,z3,z4,z753]),(0,[z0,z1,z7,z3,z300,z18]),(0,[z107,z0,z7,z3,z178,z47]),(0,[z0,z1,z7,z754,z3,z4]),(0,[z0,z1,z7,z187,z267,z3])],[(0,[z0,z1,z7,z3,z4,z755]),(0,[z9,z1,z7,z168,z4,z18]),(0,[z0,z1,z272,z7,z3,z18])],[(0,[z382,z26,z7,z3,z4,z5]),(0,[z0,z1,z7,z756,z4,z5]),(0,[z0,z1,z7,z757,z3,z4]),(0,[z0,z1,z7,z3,z758,z5]),(0,[z527,z1,z7,z3,z4,z77]),(0,[z107,z0,z74,z3,z178,z5]),(0,[z0,z1,z7,z61,z133,z257]),(0,[z0,z60,z1,z7,z730,z5])],[(0,[z0,z1,z7,z3,z4,z759])],[],[(0,[z0,z1,z7,z3,z564,z18]),(0,[z51,z82,z17,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z760]),(0,[z0,z1,z7,z3,z761,z4]),(0,[z126,z127,z64,z3,z4,z5]),(0,[z0,z7,z3,z108,z762,z5])]],
   [[(0,[z0,z1,z7,z3,z4,z763]),(0,[z0,z1,z764,z7,z3,z4]),(0,[z0,z1,z7,z483,z4,z54]),(0,[z93,z1,z412,z3,z4,z5])],[(0,[z85,z1,z765,z3,z4,z5]),(0,[z1,z7,z3,z766,z4,z5]),(0,[z0,z1,z767,z3,z4,z5]),(0,[z0,z1,z768,z7,z3,z5]),(0,[z0,z1,z769,z3,z4,z5])],[(0,[z0,z1,z7,z3,z770,z5])],[(0,[z0,z1,z771,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z772]),(0,[z1,z7,z3,z76,z362,z18]),(0,[z0,z1,z7,z3,z773,z5]),(0,[z774,z1,z7,z3,z4,z5]),(0,[z0,z1,z232,z3,z4,z392])],[(0,[z0,z1,z7,z251,z4,z5]),(0,[z0,z1,z232,z267,z3,z392])],[(0,[z0,z1,z7,z3,z775,z5]),(0,[z0,z1,z776,z7,z3,z4])],[(0,[z0,z1,z777,z3,z4,z5]),(0,[z1,z7,z3,z4,z736,z5]),(0,[z778,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z146,z4,z18])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z7,z779,z4,z5]),(0,[z105,z1,z7,z3,z732,z5]),(0,[z32,z1,z7,z3,z4,z362]),(0,[z0,z1,z780,z7,z3,z4])]],
   [[(0,[z0,z1,z7,z3,z4,z781]),(0,[z0,z1,z7,z782,z4,z5]),(0,[z0,z1,z7,z783,z3,z4]),(0,[z0,z1,z7,z3,z87,z5])],[(0,[z0,z1,z7,z3,z4,z5]),(0,[z10,z1,z7,z766,z4,z5])],[(0,[z784,z0,z1,z7,z4,z5]),(0,[z0,z313,z7,z169,z4,z5]),(0,[z93,z1,z7,z3,z4,z77])],[(0,[z0,z1,z7,z16,z4,z77]),(0,[z0,z101,z7,z146,z4,z31]),(0,[z0,z1,z579,z7,z3,z18])],[(0,[z0,z1,z7,z3,z4,z785]),(0,[z32,z0,z1,z7,z3,z87]),(0,[z0,z7,z786,z3,z4,z5]),(0,[z0,z1,z7,z787,z4,z5]),(0,[z0,z1,z7,z725,z3,z5])],[(0,[z0,z1,z7,z3,z43,z5]),(0,[z0,z1,z95,z3,z41,z18]),(0,[z0,z231,z1,z7,z3,z18])],[],[(0,[z0,z1,z141,z3,z4,z18]),(0,[z280,z0,z64,z3,z4,z5]),(0,[z0,z188,z12,z7,z3,z4]),(0,[z0,z1,z788,z3,z4,z5])]],
   [[(0,[z56,z26,z141,z3,z4,z5]),(0,[z56,z746,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z350,z18]),(0,[z0,z60,z1,z12,z7,z96])],[(0,[z9,z1,z7,z766,z4,z5]),(0,[z0,z1,z7,z3,z4,z789]),(0,[z0,z1,z7,z96,z730,z5])],[(0,[z0,z1,z790,z7,z3,z5]),(0,[z0,z1,z7,z3,z4,z791]),(0,[z792,z0,z1,z7,z3,z4]),(1,[z127,z64,z3,z4,z5]),(0,[z237,z0,z1,z24,z3,z4])],[(0,[z0,z26,z141,z3,z4,z5]),(0,[z0,z1,z793,z3,z4,z5]),(0,[z0,z1,z7,z3,z794,z5])],[(0,[z1,z26,z7,z3,z76,z18]),(0,[z795,z0,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z76,z18]),(0,[z0,z1,z7,z3,z4,z796]),(0,[z0,z1,z797,z7,z3,z4]),(0,[z0,z60,z1,z7,z96,z458])],[(0,[z0,z82,z7,z3,z4,z5]),(0,[z91,z1,z7,z3,z564,z5]),(0,[z91,z1,z12,z7,z3,z219]),(0,[z0,z1,z7,z3,z798,z5]),(0,[z0,z1,z302,z7,z3,z18])],[(0,[z799,z0,z1,z3,z4,z5]),(0,[z0,z1,z7,z3,z800,z5]),(0,[z0,z1,z74,z3,z4,z77])],[(0,[z0,z1,z801,z3,z4,z5]),(0,[z0,z802,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z44,z18]),(0,[z107,z527,z1,z7,z3,z18]),(0,[z0,z1,z7,z3,z41,z18]),(0,[z0,z1,z12,z7,z61,z133])]],
   [[(0,[z0,z1,z7,z3,z4,z803]),(0,[z527,z1,z7,z3,z5,z18]),(0,[z0,z1,z7,z3,z375,z18]),(0,[z0,z1,z7,z3,z377,z18])],[(0,[z0,z1,z7,z3,z804,z5]),(0,[z0,z1,z272,z7,z3,z143]),(0,[z530,z1,z7,z3,z219,z5]),(0,[z197,z1,z7,z3,z4,z86]),(0,[z0,z1,z7,z805,z3,z4]),(0,[z0,z1,z7,z3,z4,z806]),(0,[z0,z1,z81,z3,z41,z5])],[(0,[z0,z1,z807,z7,z3,z4]),(0,[z127,z14,z7,z3,z4,z5]),(0,[z0,z1,z94,z7,z3,z4]),(0,[z0,z34,z1,z7,z3,z89]),(0,[z0,z1,z12,z7,z3,z87])],[(0,[z0,z1,z7,z3,z4,z808]),(0,[z0,z1,z7,z315,z4,z5]),(0,[z107,z0,z12,z7,z3,z178])],[(0,[z0,z1,z7,z3,z809,z5])],[],[(0,[z810,z0,z1,z7,z3,z5]),(0,[z0,z1,z7,z3,z4,z811]),(0,[z0,z1,z7,z3,z629,z18]),(0,[z137,z0,z1,z12,z4,z138]),(0,[z0,z1,z7,z3,z812,z4]),(0,[z0,z403,z1,z7,z3,z18]),(0,[z0,z1,z7,z3,z813,z4])],[(0,[z0,z1,z7,z814,z3,z5]),(0,[z0,z397,z15,z3,z4,z5]),(0,[z0,z1,z7,z3,z562,z18]),(0,[z0,z1,z7,z3,z4,z148]),(0,[z0,z815,z7,z3,z4,z5]),(0,[z0,z1,z3,z816,z4,z5]),(0,[z0,z1,z579,z215,z3,z4])]],
   [[(0,[z0,z1,z7,z3,z4,z736]),(0,[z0,z14,z786,z3,z4,z5]),(0,[z527,z1,z7,z3,z4,z18]),(0,[z107,z527,z7,z3,z178,z5]),(0,[z0,z1,z7,z71,z4,z270])],[(0,[z602,z26,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z817])],[(0,[z1,z188,z17,z3,z4,z5]),(0,[z126,z0,z786,z3,z4,z5]),(0,[z0,z1,z818,z7,z3,z4]),(0,[z484,z0,z7,z3,z4,z50]),(0,[z0,z1,z7,z3,z4,z819])],[(0,[z56,z26,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z143,z5]),(0,[z0,z1,z232,z424,z3,z4]),(0,[z98,z1,z7,z287,z3,z4]),(0,[z0,z1,z820,z3,z4,z5]),(0,[z821,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z822]),(0,[z65,z0,z1,z7,z121,z4]),(1,[z0,z1,z7,z3,z750]),(0,[z0,z1,z7,z3,z4,z68]),(0,[z0,z170,z7,z38,z4,z5]),(0,[z823,z1,z7,z3,z4,z5]),(0,[z0,z7,z3,z4,z824,z5])],[(0,[z0,z1,z7,z825,z4,z5])],[(0,[z0,z1,z7,z3,z4,z826]),(0,[z9,z374,z1,z7,z4,z5]),(0,[z0,z1,z7,z3,z452,z18]),(0,[z335,z0,z1,z7,z3,z18])],[(0,[z0,z1,z7,z120,z3,z148]),(0,[z0,z1,z7,z730,z61,z5])]],
   [[(0,[z0,z1,z12,z7,z3,z4]),(0,[z827,z0,z1,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z828])],[(0,[z105,z1,z12,z7,z3,z76]),(0,[z107,z0,z1,z7,z3,z191]),(0,[z0,z1,z7,z3,z4,z829])],[(0,[z359,z1,z7,z3,z76,z5]),(0,[z0,z1,z7,z3,z4,z830]),(0,[z37,z0,z7,z38,z4,z18]),(0,[z0,z1,z7,z4,z831,z5])],[(0,[z0,z1,z765,z3,z4,z5]),(0,[z0,z1,z7,z560,z3,z18])],[(0,[z0,z508,z15,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z832]),(0,[z105,z1,z7,z3,z76,z18]),(0,[z197,z1,z7,z3,z76,z5]),(0,[z833,z1,z7,z3,z4,z5]),(0,[z0,z101,z1,z7,z3,z89]),(0,[z97,z0,z1,z3,z88,z4])],[(0,[z0,z1,z12,z7,z464,z4]),(0,[z598,z0,z64,z3,z4,z5]),(0,[z527,z1,z7,z16,z4,z5]),(0,[z55,z0,z1,z12,z120,z3]),(0,[z97,z0,z1,z3,z505,z4])],[(0,[z746,z26,z7,z3,z4,z5]),(0,[z0,z127,z64,z3,z4,z5]),(0,[z0,z1,z7,z38,z4,z390]),(0,[z834,z1,z7,z3,z4,z5]),(0,[z93,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z61,z133,z18])],[(0,[z0,z1,z142,z7,z3,z18]),(0,[z0,z1,z7,z3,z835,z5]),(0,[z1,z7,z3,z4,z836,z5]),(0,[z0,z1,z7,z42,z288,z4])]],
   [[(0,[z670,z0,z64,z3,z4,z5])],[(0,[z127,z7,z64,z3,z4,z5]),(0,[z107,z0,z7,z251,z178,z5]),(0,[z0,z1,z7,z3,z837,z4]),(0,[z0,z1,z7,z3,z444,z18])],[(0,[z1,z7,z3,z732,z4,z5]),(0,[z0,z603,z7,z169,z4,z5]),(0,[z0,z1,z12,z7,z315,z4]),(0,[z0,z838,z7,z3,z4,z5]),(0,[z484,z112,z0,z7,z3,z4])],[(0,[z127,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z450,z18])],[(0,[z57,z396,z7,z3,z4,z5]),(0,[z0,z82,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z729]),(0,[z0,z1,z7,z3,z4,z839])],[(0,[z0,z387,z1,z7,z3,z18]),(1,[z0,z786,z3,z4,z5]),(0,[z119,z0,z1,z412,z3,z5]),(0,[z0,z207,z7,z3,z108,z18]),(0,[z0,z60,z1,z7,z96,z5])],[(0,[z0,z1,z7,z840,z4,z5]),(0,[z126,z0,z64,z3,z4,z18]),(0,[z841,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z842]),(0,[z107,z0,z7,z3,z178,z5])],[(0,[z10,z1,z7,z28,z4,z5]),(0,[z0,z1,z7,z169,z4,z390]),(0,[z30,z0,z7,z3,z4,z50])]],
   [[(0,[z0,z1,z7,z843,z3,z4]),(0,[z0,z1,z7,z3,z844,z5]),(0,[z0,z1,z3,z845,z4,z5]),(0,[z97,z0,z1,z151,z3,z4]),(0,[z0,z14,z15,z3,z4,z5]),(0,[z527,z1,z74,z3,z4,z5]),(1,[z0,z7,z3,z762,z5]),(0,[z0,z101,z7,z3,z4,z715]),(0,[z0,z1,z7,z3,z4,z846])],[(0,[z0,z1,z7,z3,z289,z18]),(0,[z0,z847,z7,z3,z4,z5]),(0,[z105,z1,z7,z3,z76,z159]),(0,[z0,z7,z3,z4,z715,z31])],[(0,[z0,z14,z189,z3,z4,z5]),(0,[z0,z1,z7,z3,z648,z18]),(0,[z0,z1,z12,z7,z3,z89]),(0,[z0,z1,z725,z3,z41,z5])],[(0,[z0,z1,z848,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z390]),(0,[z0,z1,z7,z614,z133,z5]),(0,[z0,z1,z849,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z226])],[(0,[z0,z1,z7,z3,z4,z850]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z1,z7,z3,z219,z732,z5]),(0,[z137,z0,z1,z4,z138,z5]),(0,[z0,z421,z7,z3,z4,z441])],[(0,[z0,z852,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z853]),(0,[z0,z1,z7,z3,z4,z854]),(0,[z0,z1,z7,z266,z4,z54]),(0,[z107,z0,z1,z7,z16,z18]),(0,[z0,z1,z855,z3,z4,z5])],[(0,[z10,z1,z7,z196,z4,z5]),(0,[z165,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z614,z3,z18]),(0,[z0,z1,z7,z856,z3,z5]),(0,[z0,z1,z7,z718,z3,z18])],[(0,[z857,z0,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z308,z18]),(0,[z0,z1,z7,z328,z61,z133])]],
   [[(0,[z57,z25,z7,z3,z4,z5]),(0,[z57,z1,z141,z3,z4,z5]),(0,[z0,z1,z7,z3,z219,z18])],[(0,[z0,z1,z7,z858,z3,z4]),(0,[z0,z1,z7,z859,z4,z18])],[(0,[z0,z1,z64,z3,z41,z18]),(0,[z273,z30,z0,z7,z3,z50])],[(0,[z0,z1,z7,z3,z440,z18]),(0,[z0,z1,z36,z7,z3,z18]),(0,[z97,z0,z1,z3,z741,z4]),(0,[z1,z7,z3,z4,z860,z18])],[(0,[z98,z0,z1,z7,z3,z87]),(0,[z0,z1,z412,z16,z4,z5]),(0,[z0,z1,z7,z861,z4,z5]),(0,[z0,z1,z7,z3,z623,z18])],[(0,[z0,z1,z7,z332,z3,z18]),(0,[z0,z1,z7,z412,z3,z18]),(0,[z0,z1,z7,z187,z3,z18])],[(0,[z0,z1,z7,z464,z4,z18]),(0,[z862,z1,z7,z3,z4,z5]),(0,[z93,z1,z74,z3,z4,z5]),(0,[z0,z1,z7,z3,z185,z18]),(0,[z1,z7,z3,z4,z863,z5]),(0,[z0,z1,z7,z646,z4,z54])],[(0,[z0,z1,z7,z3,z499,z18]),(1,[z1,z7,z3,z4,z736]),(0,[z0,z7,z3,z4,z50,z715]),(0,[z0,z1,z7,z3,z4,z864])]],
   [[(0,[z0,z1,z7,z3,z865,z5]),(0,[z0,z1,z7,z866,z3,z4]),(0,[z867,z1,z7,z3,z4,z5]),(0,[z0,z1,z868,z3,z4,z5])],[],[(0,[z0,z1,z869,z3,z4,z5]),(0,[z0,z1,z7,z298,z4,z54]),(0,[z0,z1,z749,z7,z3,z214])],[(0,[z602,z0,z1,z7,z3,z18]),(0,[z91,z1,z272,z7,z3,z219]),(0,[z0,z1,z7,z251,z4,z77]),(1,[z0,z1,z7,z730,z5]),(0,[z338,z1,z7,z3,z4,z362])],[(0,[z0,z1,z7,z3,z870,z5]),(0,[z0,z1,z7,z871,z4,z5]),(0,[z0,z1,z7,z3,z4,z872])],[(0,[z0,z873,z7,z3,z4,z5]),(0,[z51,z158,z1,z17,z3,z4]),(0,[z9,z1,z7,z168,z4,z5]),(0,[z32,z128,z1,z7,z3,z4]),(0,[z0,z1,z412,z3,z4,z47]),(0,[z0,z874,z7,z3,z4,z5]),(0,[z0,z1,z7,z267,z3,z5]),(0,[z0,z1,z120,z725,z3,z5]),(0,[z0,z1,z12,z7,z3,z123]),(0,[z0,z1,z12,z7,z875,z4]),(0,[z0,z325,z1,z7,z288,z4])],[(0,[z0,z1,z876,z3,z4,z5])],[(0,[z0,z1,z7,z3,z634,z18])]],
   [[(0,[z1,z7,z3,z4,z736,z86]),(0,[z0,z1,z7,z3,z4,z77]),(0,[z0,z1,z7,z328,z3,z4])],[(0,[z0,z1,z7,z3,z4,z877]),(0,[z0,z1,z7,z166,z3,z18]),(0,[z273,z0,z1,z7,z3,z18])],[(1,[z1,z765,z3,z4,z5]),(0,[z51,z1,z12,z17,z3,z4]),(0,[z0,z1,z7,z3,z4,z878]),(0,[z0,z1,z7,z879,z4,z5]),(0,[z880,z1,z7,z3,z4,z5]),(0,[z0,z1,z749,z7,z3,z18])],[(0,[z0,z1,z12,z2,z3,z4]),(0,[z0,z1,z7,z3,z524,z18]),(0,[z0,z881,z7,z3,z4,z5]),(0,[z882,z0,z1,z7,z3,z4]),(0,[z0,z1,z7,z3,z88,z87])],[(0,[z0,z1,z7,z883,z4,z5]),(0,[z30,z0,z7,z3,z50,z89]),(0,[z277,z0,z7,z3,z4,z437])],[(0,[z0,z1,z7,z3,z4,z750]),(0,[z0,z1,z7,z3,z884,z5])],[(0,[z0,z1,z7,z885,z3,z4]),(0,[z0,z886,z7,z3,z4,z5]),(0,[z91,z1,z7,z3,z219,z5]),(0,[z887,z1,z7,z3,z4,z5]),(0,[z888,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z889,z5]),(0,[z0,z1,z7,z3,z43,z86]),(0,[z0,z207,z7,z3,z437,z18]),(0,[z0,z1,z232,z24,z3,z4])]],
   [[(0,[z0,z1,z7,z3,z4,z890]),(0,[z9,z1,z12,z7,z168,z4]),(0,[z0,z1,z7,z3,z4,z104])],[(0,[z0,z1,z7,z3,z4,z891]),(0,[z0,z1,z7,z3,z543,z18])],[(0,[z0,z1,z7,z892,z3,z4]),(0,[z0,z1,z7,z3,z4,z893]),(0,[z0,z1,z7,z3,z4,z894])],[(0,[z0,z188,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z895,z5]),(0,[z0,z1,z7,z3,z4,z896])],[(0,[z0,z1,z3,z741,z4,z392])],[(0,[z0,z1,z7,z897,z3,z4]),(0,[z0,z1,z7,z3,z465,z18])],[(0,[z0,z1,z898,z7,z3,z4])],[(0,[z57,z25,z12,z7,z3,z4]),(0,[z0,z7,z3,z4,z899,z5]),(0,[z0,z1,z95,z3,z41,z5])]],
   [[(0,[z85,z1,z52,z3,z4,z5]),(0,[z900,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z173,z4])],[(0,[z1,z7,z3,z219,z76,z18]),(0,[z98,z1,z7,z3,z43,z86])],[(0,[z85,z1,z563,z3,z4,z5]),(0,[z0,z1,z901,z3,z4,z5]),(0,[z0,z1,z12,z412,z3,z4]),(0,[z0,z34,z1,z7,z3,z18]),(0,[z0,z1,z7,z155,z3,z18])],[(0,[z0,z207,z7,z3,z762,z5]),(0,[z0,z1,z4,z831,z138,z5])],[(0,[z0,z1,z7,z3,z568,z18]),(0,[z0,z1,z902,z7,z3,z4]),(0,[z0,z1,z903,z3,z4,z5]),(0,[z904,z1,z7,z3,z4,z5]),(0,[z126,z0,z12,z64,z3,z4])],[(0,[z65,z0,z1,z12,z7,z4]),(0,[z0,z1,z7,z121,z735,z3]),(0,[z0,z1,z7,z3,z572,z18]),(0,[z55,z0,z1,z187,z120,z3])],[(0,[z56,z12,z26,z7,z3,z4]),(0,[z905,z0,z1,z7,z3,z4]),(0,[z359,z0,z1,z7,z3,z18]),(0,[z0,z1,z7,z3,z574,z18]),(0,[z0,z1,z906,z7,z3,z4]),(0,[z0,z1,z232,z7,z3,z43]),(0,[z0,z1,z7,z3,z907,z4]),(0,[z0,z1,z7,z3,z4,z908]),(0,[z0,z1,z81,z3,z4,z392]),(0,[z0,z1,z12,z7,z550,z3]),(0,[z0,z1,z7,z723,z4,z5])],[(0,[z0,z1,z7,z3,z401,z18]),(0,[z0,z1,z7,z3,z4,z909]),(0,[z910,z1,z7,z3,z4,z5]),(0,[z0,z60,z1,z7,z96,z226])]],
   [[(0,[z0,z1,z7,z3,z4,z164]),(0,[z0,z1,z7,z3,z4,z911])],[(0,[z463,z26,z7,z3,z4,z5]),(0,[z0,z1,z912,z7,z3,z4])],[(0,[z137,z0,z1,z103,z4,z5]),(0,[z97,z0,z1,z7,z3,z43]),(0,[z98,z1,z111,z7,z3,z4])],[(0,[z0,z1,z913,z7,z3,z4]),(0,[z0,z1,z7,z914,z3,z4]),(0,[z227,z1,z7,z3,z4,z144]),(0,[z0,z1,z240,z4,z831,z5]),(0,[z0,z1,z367,z7,z3,z18]),(0,[z915,z1,z7,z3,z4,z18])],[(0,[z0,z1,z916,z3,z4,z5]),(0,[z0,z1,z7,z121,z3,z750]),(0,[z0,z207,z94,z7,z3,z108])],[(0,[z65,z0,z1,z7,z4,z5]),(0,[z98,z1,z7,z3,z4,z736]),(0,[z0,z1,z512,z7,z3,z18]),(0,[z0,z1,z12,z7,z146,z4])],[(0,[z0,z1,z15,z3,z41,z18]),(0,[z0,z1,z7,z3,z89,z5])],[(0,[z519,z1,z17,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z917]),(0,[z0,z1,z7,z3,z4,z918])]],
   [[(0,[z91,z1,z7,z3,z732,z5]),(0,[z0,z1,z7,z3,z4,z919]),(1,[z527,z1,z7,z3,z18]),(0,[z107,z0,z1,z7,z3,z18]),(0,[z0,z1,z7,z3,z4,z191]),(0,[z0,z1,z12,z7,z3,z118])],[(0,[z0,z188,z52,z3,z4,z5]),(0,[z0,z1,z7,z200,z3,z18])],[(0,[z0,z1,z2,z3,z4,z18]),(0,[z91,z1,z7,z3,z219,z164]),(0,[z0,z1,z7,z3,z920,z5]),(0,[z0,z1,z7,z16,z4,z18])],[(0,[z56,z26,z2,z3,z4,z5]),(0,[z0,z786,z64,z3,z4,z5]),(0,[z107,z0,z412,z3,z178,z5]),(0,[z0,z1,z7,z723,z4,z54])],[(0,[z0,z921,z7,z3,z4,z5]),(0,[z51,z1,z765,z3,z4,z5])],[(0,[z0,z1,z7,z922,z4,z5]),(1,[z188,z17,z3,z4,z5]),(0,[z0,z1,z923,z3,z4,z5]),(0,[z924,z1,z7,z3,z4,z5]),(0,[z55,z0,z1,z332,z3,z5]),(0,[z0,z1,z7,z3,z4,z925])],[],[(0,[z0,z926,z7,z3,z4,z5]),(0,[z98,z1,z7,z3,z143,z86])]],
   [[(0,[z0,z1,z7,z927,z4,z5]),(0,[z0,z1,z7,z928,z4,z5]),(0,[z0,z1,z7,z3,z4,z929]),(0,[z0,z1,z7,z3,z4,z930]),(0,[z0,z1,z7,z3,z43,z18]),(0,[z931,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z741,z4]),(0,[z197,z1,z7,z3,z4,z366])],[(0,[z0,z932,z7,z3,z4,z5]),(0,[z0,z1,z7,z121,z464,z4]),(0,[z527,z1,z7,z3,z4,z47]),(0,[z0,z1,z7,z315,z4,z31]),(0,[z933,z1,z7,z3,z4,z5]),(0,[z0,z1,z3,z88,z741,z4]),(0,[z484,z0,z1,z7,z3,z18])],[(0,[z228,z1,z17,z3,z4,z5]),(0,[z0,z1,z7,z3,z934,z5]),(0,[z0,z935,z7,z3,z4,z5]),(0,[z0,z1,z3,z4,z831,z5]),(0,[z0,z1,z12,z7,z267,z3])],[(0,[z0,z1,z936,z3,z4,z5]),(0,[z937,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z938,z5]),(0,[z0,z1,z7,z3,z89,z54])],[(0,[z519,z0,z64,z3,z4,z5]),(0,[z10,z1,z12,z7,z28,z4]),(0,[z0,z1,z7,z939,z4,z5])],[(0,[z0,z360,z7,z747,z4,z5]),(0,[z0,z1,z74,z3,z4,z18]),(0,[z107,z0,z7,z3,z178,z77]),(0,[z0,z1,z7,z49,z3,z89])],[(0,[z105,z1,z7,z3,z76,z5]),(0,[z93,z1,z7,z16,z4,z5])],[(0,[z0,z1,z7,z3,z4,z940]),(0,[z0,z1,z7,z941,z4,z5]),(0,[z0,z1,z942,z3,z4,z5]),(0,[z0,z1,z7,z3,z532,z18])]],
   [[(0,[z0,z1,z7,z943,z3,z5]),(0,[z1,z7,z765,z3,z4,z5]),(0,[z0,z1,z7,z61,z133,z5])],[(0,[z57,z268,z7,z3,z4,z5]),(0,[z0,z1,z99,z7,z3,z18]),(0,[z0,z34,z571,z7,z3,z4])],[(0,[z944,z0,z1,z7,z3,z4]),(0,[z0,z1,z7,z945,z3,z4]),(0,[z0,z1,z232,z3,z741,z4]),(0,[z0,z1,z12,z7,z3,z18])],[(0,[z25,z746,z7,z3,z4,z5]),(0,[z85,z188,z7,z3,z4,z5]),(1,[z1,z7,z766,z4,z5])],[(0,[z0,z1,z7,z3,z946,z5]),(0,[z947,z1,z7,z3,z4,z5]),(0,[z0,z1,z412,z251,z4,z5]),(0,[z948,z1,z7,z3,z4,z5]),(0,[z0,z1,z81,z3,z41,z18]),(0,[z119,z0,z1,z749,z7,z3])],[(0,[z127,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z486,z18]),(0,[z0,z1,z7,z3,z4,z257])],[(0,[z949,z1,z7,z3,z4,z5]),(0,[z0,z1,z950,z7,z3,z5]),(0,[z0,z1,z7,z3,z214,z18])],[(0,[z93,z1,z7,z3,z4,z47]),(0,[z107,z0,z531,z7,z3,z5]),(1,[z0,z1,z725,z3,z5]),(0,[z55,z0,z1,z120,z3,z323])]],
   [[(0,[z126,z0,z64,z3,z4,z5]),(0,[z0,z1,z7,z16,z4,z47]),(0,[z0,z1,z7,z3,z90,z18])],[(0,[z51,z65,z1,z17,z4,z5]),(0,[z0,z1,z412,z3,z4,z5]),(0,[z0,z1,z7,z3,z729,z18]),(0,[z30,z0,z1,z7,z3,z89]),(0,[z0,z1,z12,z7,z951,z4])],[(0,[z0,z1,z7,z3,z4,z952]),(0,[z0,z1,z7,z17,z3,z750]),(0,[z0,z360,z7,z169,z4,z5]),(0,[z0,z1,z74,z16,z4,z5]),(0,[z0,z1,z240,z241,z4,z5])],[(0,[z0,z1,z7,z3,z4,z953]),(0,[z0,z1,z786,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z954]),(0,[z0,z527,z1,z7,z3,z18]),(0,[z0,z1,z7,z3,z658,z18])],[(0,[z0,z1,z7,z3,z4,z955]),(0,[z0,z305,z1,z7,z3,z18]),(1,[z0,z7,z3,z4,z715])],[(0,[z85,z1,z12,z52,z3,z4]),(0,[z0,z1,z7,z3,z762,z5]),(0,[z0,z1,z7,z3,z956,z5]),(0,[z119,z0,z1,z7,z187,z3]),(0,[z0,z1,z7,z751,z4,z5])],[(0,[z1,z7,z3,z732,z76,z5]),(0,[z0,z1,z906,z7,z3,z219]),(0,[z957,z0,z1,z7,z3,z4]),(0,[z0,z7,z3,z4,z824,z18])]],
   [[(0,[z165,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z455,z3,z18]),(0,[z0,z1,z7,z3,z4,z958]),(0,[z0,z7,z747,z169,z4,z5]),(0,[z0,z1,z7,z959,z3,z4])],[(0,[z0,z188,z17,z3,z4,z5]),(0,[z0,z1,z7,z960,z4,z5]),(0,[z0,z1,z7,z3,z961,z4]),(0,[z0,z1,z962,z3,z4,z5]),(0,[z527,z1,z12,z7,z3,z4])],[(0,[z963,z1,z7,z3,z4,z5])],[(0,[z0,z1,z74,z3,z4,z47]),(0,[z0,z101,z571,z7,z3,z4]),(0,[z0,z1,z7,z859,z4,z5])],[(0,[z0,z1,z7,z3,z4,z964]),(0,[z126,z165,z64,z3,z4,z5]),(0,[z0,z7,z747,z3,z4,z5]),(0,[z0,z1,z7,z965,z4,z5]),(0,[z0,z603,z7,z3,z4,z31])],[(0,[z30,z0,z7,z3,z4,z715])],[(0,[z0,z1,z966,z3,z4,z5]),(0,[z0,z1,z967,z7,z3,z5]),(0,[z968,z1,z7,z3,z4,z5]),(0,[z969,z0,z7,z3,z4,z5])],[(0,[z51,z188,z17,z3,z4,z5]),(0,[z0,z1,z7,z315,z4,z50]),(0,[z0,z1,z725,z3,z4,z5])]],
   [[(0,[z0,z1,z7,z3,z970,z4]),(0,[z0,z1,z7,z464,z4,z5]),(0,[z0,z1,z7,z3,z4,z971]),(0,[z0,z1,z7,z951,z4,z5])],[(0,[z51,z1,z464,z17,z4,z5]),(0,[z0,z1,z7,z730,z133,z5])],[(0,[z0,z1,z972,z3,z4,z5]),(0,[z0,z1,z217,z7,z3,z18]),(0,[z0,z1,z7,z3,z637,z18])],[(0,[z0,z1,z7,z973,z4,z5]),(0,[z463,z1,z17,z3,z4,z5]),(0,[z0,z1,z7,z146,z4,z5]),(0,[z0,z1,z974,z3,z4,z5]),(0,[z0,z1,z120,z3,z41,z18])],[(0,[z0,z14,z12,z15,z3,z4])],[(0,[z0,z1,z975,z3,z4,z5]),(0,[z55,z0,z1,z120,z3,z18])],[(0,[z0,z1,z7,z3,z4,z976]),(0,[z0,z1,z12,z7,z251,z4]),(0,[z30,z0,z7,z3,z4,z437]),(0,[z0,z1,z7,z529,z3,z18])],[(0,[z0,z1,z7,z977,z3,z5]),(0,[z0,z1,z7,z766,z4,z5]),(0,[z0,z7,z3,z762,z178,z5])]],
   [[(0,[z0,z1,z12,z141,z3,z4]),(0,[z98,z1,z7,z3,z4,z86]),(0,[z0,z1,z12,z7,z3,z143]),(0,[z0,z1,z12,z7,z3,z676]),(0,[z0,z1,z12,z749,z7,z3])],[(0,[z51,z1,z17,z3,z4,z18]),(0,[z0,z1,z272,z7,z3,z4]),(0,[z0,z1,z7,z978,z3,z4]),(0,[z0,z15,z786,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z323])],[(1,[z0,z7,z747,z4,z5]),(0,[z0,z1,z12,z74,z3,z4]),(0,[z979,z1,z7,z3,z4,z5])],[(0,[z1,z765,z17,z3,z4,z5]),(0,[z0,z14,z15,z3,z4,z18]),(0,[z0,z1,z579,z7,z3,z87])],[(0,[z0,z1,z141,z3,z4,z5]),(0,[z1,z26,z141,z3,z4,z5]),(0,[z0,z1,z980,z3,z4,z5]),(0,[z1,z746,z7,z3,z4,z5]),(0,[z127,z1,z12,z7,z3,z4]),(1,[z0,z1,z749,z7,z3]),(0,[z0,z1,z749,z7,z3,z5])],[(0,[z0,z1,z7,z3,z4,z981]),(0,[z0,z982,z7,z3,z4,z5]),(0,[z1,z52,z765,z3,z4,z5]),(0,[z1,z7,z766,z168,z4,z5]),(0,[z1,z7,z28,z766,z4,z5]),(0,[z0,z360,z7,z169,z4,z68]),(1,[z0,z1,z4,z831,z5])],[(0,[z0,z1,z7,z983,z3,z5]),(0,[z0,z1,z7,z3,z984,z5])],[(0,[z0,z1,z985,z3,z4,z5]),(0,[z0,z986,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z987]),(0,[z0,z1,z7,z24,z3,z18]),(0,[z333,z1,z111,z7,z3,z4])]],
   [[(0,[z0,z1,z7,z3,z988,z5]),(0,[z0,z1,z7,z3,z615,z18]),(0,[z32,z1,z7,z3,z4,z144]),(0,[z0,z1,z7,z3,z989,z4]),(0,[z0,z1,z7,z3,z4,z990]),(0,[z0,z1,z7,z3,z21,z18])],[(0,[z0,z1,z7,z3,z991,z5])],[(0,[z0,z992,z7,z3,z4,z5]),(0,[z65,z158,z0,z1,z7,z4]),(0,[z107,z0,z1,z412,z3,z18]),(0,[z273,z0,z1,z7,z3,z47])],[(0,[z0,z1,z7,z3,z4,z993]),(0,[z235,z0,z1,z3,z505,z4])],[(0,[z0,z994,z7,z3,z4,z5]),(0,[z995,z0,z1,z7,z3,z5]),(0,[z0,z1,z3,z505,z41,z18])],[(0,[z0,z207,z1,z7,z3,z191])],[(0,[z0,z1,z7,z996,z3,z4]),(0,[z0,z1,z7,z997,z4,z5]),(0,[z0,z1,z156,z120,z3,z5])],[(0,[z0,z998,z1,z7,z4,z5]),(0,[z57,z746,z7,z3,z4,z5]),(0,[z0,z1,z999,z7,z3,z4]),(0,[z165,z1,z12,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z1000]),(0,[z0,z1,z3,z741,z4,z5])]],
   [[(0,[z57,z1,z7,z3,z76,z18]),(0,[z188,z7,z17,z3,z4,z5]),(0,[z127,z1,z64,z3,z4,z5]),(0,[z527,z1,z7,z251,z4,z5]),(0,[z0,z1001,z7,z3,z4,z5])],[(0,[z0,z1,z7,z3,z4,z1002]),(0,[z1003,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z251,z4,z18])],[(0,[z0,z431,z1,z7,z3,z18])],[(0,[z0,z1,z7,z3,z4,z1004])],[(0,[z527,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z76,z104]),(0,[z0,z1,z12,z240,z241,z4]),(0,[z0,z1,z7,z3,z418,z18]),(0,[z969,z0,z12,z7,z3,z4])],[(0,[z0,z1,z7,z3,z1005,z4]),(0,[z107,z0,z207,z7,z3,z18]),(0,[z0,z1,z7,z3,z87,z18])],[(0,[z0,z1,z7,z3,z4,z18]),(0,[z0,z1,z7,z121,z3,z4])]],
   [[(0,[z56,z26,z7,z3,z4,z5]),(0,[z0,z1,z95,z3,z41,z148]),(0,[z0,z1,z7,z267,z3,z18])],[(0,[z0,z25,z141,z3,z4,z5]),(0,[z26,z7,z141,z3,z4,z5]),(0,[z29,z25,z7,z3,z4,z5]),(0,[z0,z1,z7,z1006,z4,z5]),(0,[z0,z1,z7,z286,z3,z18])],[(0,[z681,z0,z1,z12,z7,z3]),(0,[z0,z1,z111,z7,z3,z18])],[(0,[z1007,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z1008,z4,z5]),(0,[z37,z0,z7,z747,z4,z5]),(0,[z0,z1,z241,z4,z831,z5]),(0,[z0,z1,z81,z3,z4,z70])],[(0,[z1009,z0,z1,z7,z3,z4]),(0,[z0,z1010,z7,z3,z4,z5]),(0,[z0,z360,z7,z169,z4,z390]),(0,[z0,z7,z38,z747,z4,z5]),(0,[z0,z101,z7,z3,z4,z31]),(0,[z0,z1,z7,z3,z1011,z5]),(0,[z0,z1,z7,z3,z4,z1012])],[(0,[z0,z1,z7,z3,z4,z1013]),(0,[z0,z1,z7,z3,z595,z18]),(0,[z915,z1,z7,z3,z4,z5]),(0,[z0,z1,z788,z3,z4,z18])],[(0,[z93,z1,z7,z251,z4,z5])],[(0,[z0,z1,z656,z7,z3,z18]),(0,[z37,z0,z7,z38,z4,z5]),(0,[z0,z60,z1,z7,z166,z5]),(0,[z119,z0,z1,z7,z3,z47]),(0,[z0,z7,z3,z4,z762,z5]),(0,[z0,z1,z7,z120,z3,z18]),(0,[z0,z1,z95,z725,z3,z5]),(0,[z0,z1,z232,z3,z87,z392])]],
   [[(0,[z0,z1,z906,z7,z3,z18]),(1,[z0,z1,z412,z3,z18])],[(0,[z91,z1,z7,z3,z219,z18])],[(0,[z0,z1,z1014,z3,z4,z5]),(0,[z0,z1,z7,z434,z3,z18]),(0,[z0,z1,z7,z1015,z4,z5]),(0,[z0,z1,z7,z3,z41,z148])],[(0,[z93,z1,z7,z3,z4,z5]),(0,[z0,z82,z7,z3,z4,z18]),(0,[z0,z1,z7,z3,z4,z1016]),(0,[z0,z1,z7,z718,z120,z3])],[(0,[z0,z1,z7,z3,z4,z159]),(0,[z0,z1,z7,z16,z4,z5]),(0,[z0,z716,z7,z3,z4,z5])],[(0,[z0,z1,z7,z1017,z4,z5]),(0,[z0,z1,z7,z3,z4,z1018]),(0,[z0,z1,z7,z3,z4,z1019])],[(0,[z0,z1,z7,z3,z1020,z5]),(0,[z0,z1,z7,z1021,z4,z5]),(0,[z0,z1,z7,z3,z4,z1022]),(0,[z0,z1,z12,z7,z314,z3])],[(0,[z51,z1,z121,z17,z3,z4]),(0,[z0,z1,z7,z3,z4,z1023]),(0,[z1024,z0,z1,z7,z3,z4])]],
   [[(0,[z26,z17,z64,z3,z4,z5]),(0,[z0,z1,z1025,z3,z4,z5]),(0,[z0,z1,z7,z251,z4,z47])],[(0,[z0,z1,z7,z315,z4,z18])],[(0,[z0,z207,z7,z3,z108,z5]),(0,[z0,z1,z74,z251,z4,z5])],[(0,[z85,z1,z52,z3,z4,z18]),(0,[z1026,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z4,z1027])],[(0,[z137,z0,z1,z4,z831,z5])],[(0,[z0,z1,z7,z3,z4,z1028]),(0,[z105,z1,z7,z3,z76,z104]),(0,[z0,z1,z7,z3,z4,z1029]),(0,[z0,z1,z7,z3,z4,z1030]),(0,[z0,z1,z7,z3,z4,z47]),(0,[z1031,z1,z7,z3,z4,z5]),(0,[z1032,z1,z7,z3,z4,z5]),(0,[z0,z815,z7,z3,z4,z18]),(0,[z0,z1,z3,z816,z4,z18])],[(0,[z0,z1,z7,z3,z4,z1033]),(0,[z1034,z1,z7,z3,z4,z5]),(0,[z0,z101,z7,z315,z4,z31])],[(0,[z0,z1,z1035,z3,z4,z5]),(0,[z0,z1,z74,z3,z4,z5])]],
   [[(0,[z0,z746,z7,z3,z4,z5]),(0,[z0,z1,z412,z3,z4,z77]),(0,[z1036,z0,z1,z7,z3,z4])],[(0,[z0,z1,z7,z3,z143,z18])],[(0,[z0,z1,z7,z3,z1037,z5]),(0,[z0,z1,z7,z730,z4,z5])],[(1,[z1,z7,z3,z732,z5]),(0,[z0,z1,z1038,z3,z4,z5]),(0,[z0,z1,z12,z7,z3,z43]),(0,[z1039,z1,z7,z3,z4,z5]),(0,[z0,z1,z7,z3,z1040,z4]),(0,[z0,z1,z7,z875,z4,z5]),(0,[z0,z421,z207,z7,z3,z18]),(0,[z0,z1,z12,z7,z3,z236])],[(0,[z0,z1,z7,z3,z194,z18]),(0,[z0,z360,z12,z7,z169,z4])],[(0,[z0,z1,z1041,z3,z4,z5]),(0,[z0,z1,z7,z1042,z4,z5]),(0,[z0,z421,z7,z3,z4,z31]),(0,[z598,z0,z1,z7,z3,z18]),(0,[z1043,z0,z1,z7,z3,z4]),(0,[z227,z1,z217,z7,z3,z4])],[(0,[z433,z0,z7,z38,z4,z5]),(0,[z0,z1,z7,z723,z3,z4])],[(0,[z0,z1,z12,z7,z3,z224])]],
   [[(0,[z0,z1,z7,z1044,z4,z5]),(0,[z0,z1,z7,z3,z209,z18]),(0,[z65,z0,z1,z7,z4,z18]),(0,[z0,z1,z7,z1045,z4,z5]),(0,[z1,z7,z3,z4,z860,z5])],[(0,[z254,z1,z52,z3,z4,z5]),(0,[z0,z1,z1046,z7,z3,z4]),(0,[z0,z1,z7,z3,z4,z1047]),(0,[z0,z1,z7,z3,z89,z18])],[(0,[z0,z1,z7,z3,z4,z1048]),(0,[z0,z1,z7,z1049,z4,z5]),(0,[z197,z1,z7,z3,z76,z18]),(0,[z0,z1,z7,z3,z43,z144])],[(0,[z0,z7,z3,z4,z715,z5]),(0,[z0,z1,z7,z3,z1050,z4])],[(0,[z0,z1,z240,z462,z4,z5]),(0,[z127,z1,z15,z3,z4,z5])],[(0,[z0,z1,z3,z1051,z4,z5]),(0,[z0,z1,z1052,z7,z3,z4]),(0,[z0,z1,z7,z1053,z4,z5]),(0,[z0,z1,z7,z3,z4,z1054]),(0,[z0,z109,z7,z3,z4,z50]),(0,[z0,z1,z7,z1055,z3,z4])],[(0,[z0,z1,z1056,z7,z3,z4]),(0,[z0,z1,z7,z1057,z3,z5]),(0,[z0,z1,z469,z7,z3,z18])],[(0,[z0,z1,z7,z3,z4,z1058]),(0,[z0,z1,z7,z3,z1059,z4]),(0,[z0,z1,z99,z3,z41,z5]),(0,[z37,z0,z12,z7,z38,z4]),(0,[z107,z0,z7,z3,z762,z5]),(0,[z0,z1,z7,z1060,z3,z4]),(0,[z0,z1,z95,z3,z173,z41])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1069).take 84) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1153)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 536, 84] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 245).take 11).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 128, 11] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_42584

theorem PEqualNP.Outside.L_meta_42584 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276807680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276807680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42584.solve