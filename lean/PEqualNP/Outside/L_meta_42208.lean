import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42208

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
  Nat.testBit (4276808424 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0026263780e38f29#64 ++ 0x04009898de038e3c#64 ++ 0x027e7e7f81e79f3e#64 ++ 0x9409f9f9fe079e7c#64 : BitVec 256),
   (0x0c90908a060d3542#64 ++ 0x00324242281834d5#64 ++ 0x1d91918e0e3ffffd#64 ++ 0xfc7646463838ffff#64 : BitVec 256),
   (0x61616151b030c28c#64 ++ 0x0185858546c0c30a#64 ++ 0xe1e1e1f1f038e3fb#64 ++ 0xdb878787c7c0e38f#64 : BitVec 256),
   (0xb601fa00db40f830#64 ++ 0x0ad807e8036d03e0#64 ++ 0xfe01fe01ffc0fc37#64 ++ 0xeff807f807ff03f0#64 : BitVec 256),
   (0xdbfa00016dbe0000#64 ++ 0x236fe80005b6f800#64 ++ 0xfffe0001ffff002f#64 ++ 0xaffff80007fffc00#64 : BitVec 256),
   (0xffddddec00000000#64 ++ 0x13ff7777b0000000#64 ++ 0xfffffffe0000001f#64 ++ 0xf3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81e79f3e 0x9409f9f9fe079e7c

def z1 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91918e0e3ffffd 0xfc7646463838ffff

def z2 : W := mkw 0x49f00001243c0000 0x0127c0000490f000 0xfdf00001fe3f002f 0xaff7c00007f8fc00

def z3 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f038e3fb 0xdb878787c7c0e38f

def z4 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01ffc0fc37 0xeff807f807ff03f0

def z5 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffff002f 0xaffff80007fffc00

def z6 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z7 : W := mkw 0x0890000000000000 0x0022400000000000 0x1d9000000000000d 0xa076400000000000

def z8 : W := mkw 0x002200016dbe0000 0x2000880005b6f800 0x00000001ffff0020 0x0c00000007fffc00

def z9 : W := mkw 0x0026263580e28a29 0x04009898d6038a28 0x026e6e7181c00002 0x0009b9b9c6070000

def z10 : W := mkw 0x08900000040c0000 0x0022400000103000 0x1c1000000e070004 0x2470400000381c00

def z11 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000181e79f20 0x0400000006079e7c

def z12 : W := mkw 0x0400900002003000 0x00100240000800c0 0x1c0190000e00fc35 0xec700640003803f0

def z13 : W := mkw 0x00202011b030c28c 0x0000808046c0c30a 0x00606071f038e3fa 0x98018181c7c0e38f

def z14 : W := mkw 0x0890008a040d0542 0x0022400228103415 0x0190018e003f03c8 0x100640063800fc0f

def z15 : W := mkw 0xffddddec040c0000 0x13ff7777b0103000 0xfffffffe0e3f003f 0xfffffffff838fc00

def z16 : W := mkw 0x200161509000c28c 0x008005854240030a 0x0001e1f00000e3d0 0x50000787c000038f

def z17 : W := mkw 0x96009a004b403830 0x0a580268012d00e0 0xfe001e01ffc01c27 0xaff8007807ff0070

def z18 : W := mkw 0x61616351b070caac 0x0185858d46c1c32a 0xe3e1fff1f1f8ffff 0xdf8f87ffc7c7e3ff

def z19 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e7e7e0000001e 0x9009f9f9f8000000

def z20 : W := mkw 0xf3616b51f970cabc 0x0bcd85ad47e5c32a 0xe3e1eff1f1f8e3fb 0xdb8f87bfc7c7e38f

def z21 : W := mkw 0x49dc05ec00000000 0x11277017b0000000 0x01fe01fe00000008 0x1007f807f8000000

def z22 : W := mkw 0xffddddee060d3542 0x13ff7777b81834d5 0xfffffffe0e3fffff 0xfffffffff838ffff

def z23 : W := mkw 0xb627fe37dbe3ff39 0x0ed89ff8df6f8ffc 0xfe7ffe7fffe7ff3f 0xfff9fff9ffff9ffc

def z24 : W := mkw 0x9222000149a20000 0x0248880005268800 0xfe7e0001ffe7002f 0xaff9f80007ff9c00

def z25 : W := mkw 0x92002200c9408820 0x0248008803250220 0xfe007e01ffc09c37 0xaff801f807ff0270

def z26 : W := mkw 0x2401fa009240f830 0x089007e8024903e0 0x0001fe000000fc10 0x400007f8000003f0

def z27 : W := mkw 0x200161509000c28c 0x008005854240030a 0x0181e1f00038e3f9 0xd8060787c000e38f

def z28 : W := mkw 0xfffdddfd2030028c 0x13fff777f480c00a 0xfffffffe003803df 0xf3fffffff800e00f

def z29 : W := mkw 0x000002004b403830 0x08000008012d00e0 0x000000000fc01c00 0x04000000003f0070

def z30 : W := mkw 0x49fa015124be028c 0x2127e8054492f80a 0x01fe01f0003f03c8 0x1007f807c000fc0f

def z31 : W := mkw 0x6141414030104084 0x0185050500c04102 0xe18181807038e3f9 0xdb86060601c0e38f

def z32 : W := mkw 0x61676777b0f3cfad 0x05859d9ddec3cf3e 0xe3fffffff1ffffff 0xdf8fffffffc7ffff

def z33 : W := mkw 0x200567769041cfad 0x0480159dda41073e 0x0001fffe0000ffd0 0x500007fff80003ff

def z34 : W := mkw 0xdbd8000000000000 0x036f600000000000 0xfffe00000000000f 0xa3fff80000000000

def z35 : W := mkw 0xb2016a00d940c830 0x0ac805a803650320 0xe2006e01f1c00002 0x038801b807c70000

def z36 : W := mkw 0x0006062600c30d21 0x0400181898030c34 0x021e1e0e01c71c04 0x0408787838071c70

def z37 : W := mkw 0x0026043700a30709 0x04009810dc028c1c 0x007e007e00270308 0x1001f801f8009c0c

def z38 : W := mkw 0xdbfa01516dbe028c 0x236fe80545b6f80a 0xfffe01f1ffff03ef 0xbffff807c7fffc0f

def z39 : W := mkw 0x0400908a02013542 0x00100242280804d5 0x0181918e0038fff9 0xd80606463800e3ff

def z40 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81c71c06 0x0409f9f9fe071c70

def z41 : W := mkw 0x0000000002003000 0x00000000000800c0 0x000000000e00fc20 0x0c000000003803f0

def z42 : W := mkw 0xffffdded69b20000 0x33ffff77b5a6c800 0xfffffffff1c0001f 0xf3ffffffffc70000

def z43 : W := mkw 0x9200000049000000 0x0248000001240000 0xfe000001ffc00027 0xaff8000007ff0000

def z44 : W := mkw 0xfffbfa01fffef830 0x2bffefe807fffbe0 0xfffffe01fffffc3f 0xeffffff807fffff0

def z45 : W := mkw 0xffffffedfffef830 0x3bffffffb7fffbe0 0xfffffffffffffc3f 0xfffffffffffffff0

def z46 : W := mkw 0x0400908a060d3542 0x00100242281834d5 0x0001918e0e3ffff0 0x5c0006463838ffff

def z47 : W := mkw 0x0026042500a20000 0x0000981094028800 0x027e7e7f81e7003e 0x9409f9f9fe079c00

def z48 : W := mkw 0x0000000200010500 0x0000000008000414 0x0010100e00279f3c 0x9400404038009e7c

def z49 : W := mkw 0xfbfb41417dbe4084 0x23efed0505f6f902 0xffff8181ffff60ef 0xeffffe0607fffd83

def z50 : W := mkw 0x00222213edff8f29 0x240088884fb7fe3c 0x00000001ffff9f20 0x0c00000007fffe7c

def z51 : W := mkw 0xdfd8908a6f1d3542 0x237f624229bc74d5 0xfd91918e7e3ffffd 0xfff6464639f8ffff

def z52 : W := mkw 0x0400908a02013542 0x00100242280804d5 0x0001918e0000ffd0 0x50000646380003ff

def z53 : W := mkw 0x0006062600c30d21 0x0400181898030c34 0x021e1e0e01e79f3c 0x9408787838079e7c

def z54 : W := mkw 0x9e9a908a4f8f3542 0x227a6a42293e3cd5 0x1e1e100e0fc71c04 0x24787840383f1c70

def z55 : W := mkw 0xdfd8908800000000 0x037f624220000000 0xffff918e0000001f 0xf3fffe4638000000

def z56 : W := mkw 0x4160000120300000 0x010580000480c000 0xe1e00001f038002b 0x8b87800007c0e000

def z57 : W := mkw 0xfbfb6151fdbec28c 0x23efed8547f6fb0a 0xffffe1f1ffffe3ff 0xffffff87c7ffff8f

def z58 : W := mkw 0xffd9d9c830104084 0x13ff676720c04102 0xfd818180701860c1 0x6bf6060601c06183

def z59 : W := mkw 0x0002020200c30d21 0x0400080808030c34 0x0000000001c71c00 0x0400000000071c70

def z60 : W := mkw 0x9aba00014dae0000 0x226ae8000536b800 0x1e7e00018fe7002e 0xa479f800063f9c00

def z61 : W := mkw 0x416001512030028c 0x010580054480c00a 0x01e001f0003803c8 0x10078007c000e00f

def z62 : W := mkw 0x08900002040d0500 0x0022400008103414 0x1d90100e0e3f9f3d 0xbc7640403838fe7c

def z63 : W := mkw 0x9e9e9eae00c30d21 0x167a7a7ab8030c34 0x1e1e1e0e01c71c04 0x2478787838071c70

def z64 : W := mkw 0x920a000049820000 0x2248280001260800 0x020e000001c00000 0x0008380000070000

def z65 : W := mkw 0x08900000040c0000 0x0022400000103000 0x01900000003f0008 0x000640000000fc00

def z66 : W := mkw 0xf36b6151f9b2c28c 0x23cdad8547e6cb0a 0xe3efe1f1f1f8e3fb 0xdb8fbf87c7c7e38f

def z67 : W := mkw 0x41662637a0f38f29 0x05059898de83ce3c 0xe3fe7e7ff1ff9f3f 0x9f8ff9f9ffc7fe7c

def z68 : W := mkw 0x0022000100a20000 0x0000880004028800 0x027e000181e7002e 0x8409f80006079c00

def z69 : W := mkw 0xfbdd4dec00000000 0x13ef7537b0000000 0xe3fe6ffe0000000a 0x138ff9bff8000000

def z70 : W := mkw 0x00000000040c0000 0x0000000000103000 0x000000000e3f0020 0x0c0000000038fc00

def z71 : W := mkw 0x2001414000000000 0x0080050500000000 0x0001e1f000000010 0x50000787c0000000

def z72 : W := mkw 0x0000200080008000 0x0000008002000200 0x0000600180008032 0x8000018006000200

def z73 : W := mkw 0x0cb694bf06af374b 0x0432da52fc1abcdd 0x1dff91fe0e3ffffd 0xfc77fe47f838ffff

def z74 : W := mkw 0x61416150b010c28c 0x0185058542c0430a 0xe181e1f07018e3d1 0x5b860787c1c0638f

def z75 : W := mkw 0x0026263580e28a29 0x04009898d6038a28 0x027e6e7181e7002e 0x8409f9b9c6079c00

def z76 : W := mkw 0x0000000200010500 0x0000000008000414 0x0000000000279f20 0x0400000000009e7c

def z77 : W := mkw 0x0022000100a20000 0x0000880004028800 0x026e000181c00002 0x0009b80006070000

def z78 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfd800001ffff0021 0x2ff6000007fffc00

def z79 : W := mkw 0xffffddff00a30709 0x17ffff77fc028c1c 0xfffffffe0027031f 0xf3fffffff8009c0c

def z80 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d8181800e3fffe1 0x6c7606060038ffff

def z81 : W := mkw 0xfbfb6001fdbec000 0x23efed8007f6fb00 0xffffe001ffffe03f 0xefffff8007ffff80

def z82 : W := mkw 0xf767ff77fbf3ffbd 0x0fdd9ffddfefcffe 0xffffffffffffffff 0xffffffffffffffff

def z83 : W := mkw 0x6df1f1dbb63df7ce 0x01b7c7c76ed8f7df 0xfdf1f1fffe3fffff 0xfff7c7c7fff8ffff

def z84 : W := mkw 0x416001512030028c 0x010580054480c00a 0xe1e001f1f03803eb 0x9b878007c7c0e00f

def z85 : W := mkw 0xdbfa000124be0000 0x236fe8000492f800 0xfffe0000003f000f 0xa3fff8000000fc00

def z86 : W := mkw 0x0c9696ae06cf3d63 0x04325a5ab81b3cf5 0x1f9f9f8e0ffffffd 0xfc7e7e7e383fffff

def z87 : W := mkw 0x0000220080408820 0x0000008802010220 0x02007e0181c09c36 0x840801f806070270

def z88 : W := mkw 0x49fe05ff00a30709 0x1527f817fc028c1c 0x01fe01fe00270308 0x1007f807f8009c0c

def z89 : W := mkw 0x0022000100a20000 0x0000880004028800 0x0000000181e70020 0x0400000006079c00

def z90 : W := mkw 0xd36a00016dbe0000 0x234da80005b6f800 0xe26e0001ffff0022 0x0f89b80007fffc00

def z91 : W := mkw 0x0c90908800000000 0x0032424220000000 0x1d91918e0000001d 0xf076464638000000

def z92 : W := mkw 0x2001400000000000 0x0080050000000000 0xe001e00000000013 0xc380078000000000

def z93 : W := mkw 0x9e9a908a4f8f3542 0x227a6a42293e3cd5 0x1f9f918e0ffffffd 0xfc7e7e46383fffff

def z94 : W := mkw 0xbe91d88a060d3542 0x02fa4762281834d5 0xff91ff8e0e3fffff 0xfffe47fe3838ffff

def z95 : W := mkw 0x9e9c9eac4b403830 0x1a7a727ab12d00e0 0x1e1e1e0e0fc01c04 0x24787878383f0070

def z96 : W := mkw 0x6141414000000000 0x0185050500000000 0xe1e1e1f00000001b 0xd3878787c0000000

def z97 : W := mkw 0xdbfe263780e38f29 0x076ff898de038e3c 0xfffe7e7f81e79f3f 0xb7fff9f9fe079e7c

def z98 : W := mkw 0xbeb7febfdfefff7b 0x0efadffaff7fbffd 0xffffffffffffffff 0xffffffffffffffff

def z99 : W := mkw 0x0004042400000000 0x0000101090000000 0x026e6e7000000002 0x0009b9b9c0000000

def z100 : W := mkw 0x61416140b010c084 0x0185058502c04302 0xe181e181f018e0f3 0xcb86078607c06383

def z101 : W := mkw 0x0004042400000000 0x0000101090000000 0x021e1e0e00000004 0x0008787838000000

def z102 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d90100e0e3f1c2d 0xac7640403838fc70

def z103 : W := mkw 0x00002200db40f830 0x08000088036d03e0 0x00000001ffc0fc20 0x0c00000007ff03f0

def z104 : W := mkw 0x92002200db40f830 0x0a480088036d03e0 0xfe000001ffc0fc27 0xaff8000007ff03f0

def z105 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xffee0001ffd80003 0x2bffb80007ff6000

def z106 : W := mkw 0xf349494000000000 0x13cd252500000000 0xe000000000000000 0x0380000000000000

def z107 : W := mkw 0x0000220080408820 0x0000008802010220 0x00007e0000009c10 0x000001f800000270

def z108 : W := mkw 0xfbd9414000000000 0x03ef650500000000 0xffffe1f00000001f 0xf3ffff87c0000000

def z109 : W := mkw 0xfffffdfdfdbec28c 0x33fffff7f7f6fb0a 0xffffffffffffe3ff 0xffffffffffffff8f

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x018181800038e3f9 0xd80606060000e38f

def z111 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfe7e0001ffc70006 0x27f9f80007ff1c00

def z112 : W := mkw 0xf761fb51fb70fabc 0x0bdd87ed47edc3ea 0xffe1fff1fff8ffff 0xffff87ffc7ffe3ff

def z113 : W := mkw 0xb605ffecdb40f830 0x1ad817ffb36d03e0 0xfe01ffffffc0fc37 0xfff807ffffff03f0

def z114 : W := mkw 0x0c90908800000000 0x0032424220000000 0x1d81818000000001 0x6076060600000000

def z115 : W := mkw 0xb601d8005b007010 0x0ad80760016c01c0 0xfc0180007e006001 0x6bf0060001f80180

def z116 : W := mkw 0x2c95ddec00000000 0x10b25777b0000000 0x1d91fffe0000001d 0xf07647fff8000000

def z117 : W := mkw 0x9e9c9cac00000000 0x127a7272b0000000 0x1e1e1e0e00000004 0x2078787838000000

def z118 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe26e6e7000000002 0x0389b9b9c0000000

def z119 : W := mkw 0x9a9a00004d8e0000 0x226a680001363800 0xfe1e0001ffc70027 0xaff8780007ff1c00

def z120 : W := mkw 0x6141414030104084 0x0185050500c04102 0xe1818180701860c1 0x4b86060601c06183

def z121 : W := mkw 0xffffdded6dbe0000 0x33ffff77b5b6f800 0xffffffffffff003f 0xfffffffffffffc00

def z122 : W := mkw 0xdbd800006d1c0000 0x236f600001b47000 0xfffe00007e18000f 0xabfff80001f86000

def z123 : W := mkw 0x04009002060d3542 0x00100240081834d5 0x1c0190000e3ffff5 0xec7006400038ffff

def z124 : W := mkw 0xdbfe05ed6dbe0000 0x336ff817b5b6f800 0xfffe01ffffff002f 0xbffff807fffffc00

def z125 : W := mkw 0x0020201180208208 0x0000808046008208 0x006060718020833a 0x90018181c600820c

def z126 : W := mkw 0xd36a000169b20000 0x234da80005a6c800 0xe26e0001f1c00002 0x0389b80007c70000

def z127 : W := mkw 0xdbf8000120300000 0x036fe0000480c000 0xfffe0001f038002f 0xabfff80007c0e000

def z128 : W := mkw 0x0004062600410d21 0x0400101898010434 0x00001e0e00001c00 0x0000007838000070

def z129 : W := mkw 0x61676577b0b3c78d 0x05859d95dec2cf1e 0xe1ffe1fff03fe3fb 0xdb87ff87ffc0ff8f

def z130 : W := mkw 0x9200000049000000 0x0248000001240000 0x1e0000000fc00004 0x24780000003f0000

def z131 : W := mkw 0x00202011b030c28c 0x0000808046c0c30a 0x00000001f038e3e0 0x0800000007c0e38f

def z132 : W := mkw 0x0004263680418f29 0x04001098da01063c 0x00007e7e00009f10 0x100001f9f800027c

def z133 : W := mkw 0x0400908a02013542 0x00100242280804d5 0x0011918e0027fffc 0xd400464638009fff

def z134 : W := mkw 0x0c9494ae060d3542 0x00325252b81834d5 0x1ffffffe0e3fffff 0xfc7ffffff838ffff

def z135 : W := mkw 0xdffa908b6fbf3542 0x237fea422dbefcd5 0xffff918fffffffff 0xfffffe463fffffff

def z136 : W := mkw 0x04009a0002403830 0x08100268000900e0 0x00001e0000001c00 0x0000007800000070

def z137 : W := mkw 0x96009a004b403830 0x0a580268012d00e0 0x1e001e000fc01c04 0x24780078003f0070

def z138 : W := mkw 0xb607fe26dbc3fd31 0x0ed81ff89b6f0ff4 0xfe1ffe0fffc7fc37 0xeff87ff83fff1ff0

def z139 : W := mkw 0xd36a000169b20000 0x234da80005a6c800 0xe3ee0001f1f8002b 0x8b8fb80007c7e000

def z140 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1c10100e0e071c04 0x2470404038381c70

def z141 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe0606071f0000002 0x03818181c7c00000

def z142 : W := mkw 0x9200000000000000 0x0248000000000000 0xfe00000000000007 0xa3f8000000000000

def z143 : W := mkw 0x49dc05ec00000000 0x11277017b0000000 0x03fe7ffe0000001e 0x900ff9fff8000000

def z144 : W := mkw 0xbe91fa8adf4dfd72 0x0afa47ea2b7d37f5 0xff91ff8fffffffff 0xfffe47fe3fffffff

def z145 : W := mkw 0x4140014000000000 0x0105000500000000 0x01e001f000000008 0x10078007c0000000

def z146 : W := mkw 0x0000000200010500 0x0000000008000414 0x0010000e00270308 0x1000400038009c0c

def z147 : W := mkw 0x0022221386efbf6b 0x040088884e1bbefd 0x000000018fffffe0 0x0c000000063fffff

def z148 : W := mkw 0x616141513030428c 0x0185850544c0c10a 0xe1e181f0703863c9 0x5b878607c1c0e18f

def z149 : W := mkw 0xffffffff80e38f29 0x17fffffffe038e3c 0xffffffff81e79f3f 0xf7fffffffe079e7c

def z150 : W := mkw 0x49fa000124be0000 0x2127e8000492f800 0x1dfe00000e3f002d 0xac77f8000038fc00

def z151 : W := mkw 0x200161509000c28c 0x008005854240030a 0xe001e1f1f000e3f3 0xdb800787c7c0038f

def z152 : W := mkw 0x0c909088060c3042 0x00324242201830c1 0x1d8181800e1860c1 0x6876060600386183

def z153 : W := mkw 0x0cb6b6bf86efbf6b 0x0432dadafe1bbefd 0x1fffffff8fffffff 0xfc7ffffffe3fffff

def z154 : W := mkw 0x0000201080008208 0x0000008042000208 0x0000607000008310 0x10000181c000020c

def z155 : W := mkw 0x0022000100a20000 0x0000880004028800 0x007e000000270008 0x0001f80000009c00

def z156 : W := mkw 0x0020201380218708 0x000080804e00861c 0x0070707f80279f3e 0x9401c1c1fe009e7c

def z157 : W := mkw 0x9a9000004d0c0000 0x026a400001343000 0xff900001ffff002f 0xaffe400007fffc00

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000208338 0x900000000000820c

def z159 : W := mkw 0xffddddec060c3042 0x13ff7777b01830c1 0xfffffffe0e1860df 0xfbfffffff8386183

def z160 : W := mkw 0x6161615180208208 0x0185858546008208 0xe1e1e1f18020833b 0xd3878787c600820c

def z161 : W := mkw 0x2c91f1da960df7ce 0x00b247c76a5837df 0x1d91f1fe0e3ffffd 0xfc7647c7f838ffff

def z162 : W := mkw 0xf36d6d75b030c28c 0x13cdb5b5d6c0c30a 0xe26e6e71f0000002 0x0389b9b9c7c00000

def z163 : W := mkw 0xb601d80000000000 0x02d8076000000000 0xfe01fe0000000017 0xe3f807f800000000

def z164 : W := mkw 0x00222213dbe3ff39 0x0c0088884f6f8ffc 0x00000001ffe7ff20 0x0c00000007ff9ffc

def z165 : W := mkw 0xfffbfa8bfffffd72 0x2bffefea2ffffff5 0xffffff8fffffffff 0xfffffffe3fffffff

def z166 : W := mkw 0x4140000000000000 0x0105000000000000 0xe1e000000000000b 0x8387800000000000

def z167 : W := mkw 0x0022001300a30709 0x040088004c028c1c 0x0000000000270300 0x0000000000009c0c

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x027e00000000000e 0x8009f80000000000

def z169 : W := mkw 0x6dd1d1c800000000 0x01b7474720000000 0xfdf1f1fe0000001f 0xf3f7c7c7f8000000

def z170 : W := mkw 0xf36b6a01f9f2c830 0x2bcdada807e7cb20 0xe26e6e01f1c00002 0x0389b9b807c70000

def z171 : W := mkw 0xffd9fa00db40f830 0x0bff67e8036d03e0 0xfffffe01ffc0fc3f 0xeffffff807ff03f0

def z172 : W := mkw 0x0004043600010709 0x04001010d800041c 0x0000007e00000300 0x10000001f800000c

def z173 : W := mkw 0x0890008a040d0542 0x0022400228103415 0x0010000e00070000 0x0000400038001c00

def z174 : W := mkw 0x002200036fbf3542 0x200088000dbefcd5 0x00000001ffffffe0 0x0c00000007ffffff

def z175 : W := mkw 0x00000002060d3542 0x00000000081834d5 0x000000000e3fffe0 0x0c0000000038ffff

def z176 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x027e000181e79f2e 0x8409f80006079e7c

def z177 : W := mkw 0x0400900002003000 0x00100240000800c0 0x000190000000fc10 0x40000640000003f0

def z178 : W := mkw 0xbe9dddec00000000 0x12fa7777b0000000 0x1e1ffffe00000014 0x70787ffff8000000

def z179 : W := mkw 0x4160000120300000 0x010580000480c000 0xe1e18181f038e3fb 0xdb87860607c0e38f

def z180 : W := mkw 0xdffa90896dbe0000 0x237fea4225b6f800 0xffff918fffff003f 0xfffffe463ffffc00

def z181 : W := mkw 0x2405ddec00000000 0x10901777b0000000 0x0001fffe00000010 0x500007fff8000000

def z182 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x00007e7f81e79f30 0x140001f9fe079e7c

def z183 : W := mkw 0x2c95ddee060d3542 0x10b25777b81834d5 0x1d91fffe0e3ffffd 0xfc7647fff838ffff

def z184 : W := mkw 0x4140000020100000 0x0105000000804000 0xe180000070180001 0x0b86000001c06000

def z185 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91818e0e3f63c9 0x787646063838fd8f

def z186 : W := mkw 0xffd9d9c800000000 0x13ff676720000000 0xff81ff8000000017 0xe3fe07fe00000000

def z187 : W := mkw 0x49fe043724bf0709 0x2527f810dc92fc1c 0x01fe007e003f0308 0x1007f801f800fc0c

def z188 : W := mkw 0xdbd800006d1c0000 0x236f600001b47000 0xfd8000007e180001 0x2bf6000001f86000

def z189 : W := mkw 0xffddddec6d1c0000 0x33ff7777b1b47000 0xfffffffe7e18001f 0xfbfffffff9f86000

def z190 : W := mkw 0x002200016dbe0000 0x2000880005b6f800 0x027e0001ffff002e 0x8c09f80007fffc00

def z191 : W := mkw 0x08b6263784ef8f29 0x0422d898de13be3c 0x1ffe7e7f8fff9f3f 0xbc7ff9f9fe3ffe7c

def z192 : W := mkw 0xbe9ddcac00000000 0x12fa7772b0000000 0xfe1ffe0e00000017 0xe3f87ff838000000

def z193 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe0606071f020833a 0x93818181c7c0820c

def z194 : W := mkw 0x00222213b0f3cfad 0x040088884ec3cf3e 0x00000001f1ffffe0 0x0c00000007c7ffff

def z195 : W := mkw 0x0c90908a040d0542 0x0032424228103415 0x1d91918e003f03dd 0xf07646463800fc0f

def z196 : W := mkw 0x00262637dbe3ff39 0x0c009898df6f8ffc 0x027e7e7fffe7ff3e 0x9c09f9f9ffff9ffc

def z197 : W := mkw 0xb623fa13dbe3ff39 0x0ed88fe84f6f8ffc 0xfe01fe01ffe7ff37 0xeff807f807ff9ffc

def z198 : W := mkw 0xdbfa2213edff8f29 0x276fe8884fb7fe3c 0xfffe0001ffff9f2f 0xaffff80007fffe7c

def z199 : W := mkw 0x08900000040c0000 0x0022400000103000 0x1d9000000e3f002d 0xac7640000038fc00

def z200 : W := mkw 0x0020221180608a28 0x0000808846018228 0x02607e7181e09f3e 0x940981f9c607827c

def z201 : W := mkw 0x6167677780e38f29 0x05859d9dde038e3c 0xe3ffffff81e79f3f 0xd78ffffffe079e7c

def z202 : W := mkw 0x6dd1d1ca060d3542 0x01b74747281834d5 0xfdf1f1fe0e3fffff 0xfff7c7c7f838ffff

def z203 : W := mkw 0x49fe27ff80e38f29 0x1527f89ffe038e3c 0x03fe7fff81e79f3e 0x940ff9fffe079e7c

def z204 : W := mkw 0x4ddc95ee060d3542 0x11377257b81834d5 0x1dff91fe0e3ffffd 0xfc77fe47f838ffff

def z205 : W := mkw 0x4162000120b20000 0x010588000482c800 0xe3fe0001f1ff002f 0x8f8ff80007c7fc00

def z206 : W := mkw 0xfbd941407d1c4084 0x23ef650501f47102 0xfd8181807e1860c1 0x6bf6060601f86183

def z207 : W := mkw 0xdbfa2201fffef830 0x2b6fe88807fffbe0 0xfffe0001fffffc2f 0xaffff80007fffff0

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000000380029 0x880600000000e000

def z209 : W := mkw 0xfbfb6a01fdfec830 0x2befeda807f7fb20 0xfffe6e01ffff002f 0xaffff9b807fffc00

def z210 : W := mkw 0xfffbd8016dbe0000 0x23ffef6005b6f800 0xfffffe01ffff003f 0xeffffff807fffc00

def z211 : W := mkw 0xb605fe36db41ff39 0x0ed817f8db6d07fc 0xfe01fe7fffc0ff37 0xfff807f9ffff03fc

def z212 : W := mkw 0xdffa908b6fbf3542 0x237fea422dbefcd5 0xfffe100fffff1c2f 0xaffff8403ffffc70

def z213 : W := mkw 0x416a000120b20000 0x2105a8000482c800 0x006e000000000000 0x0001b80000000000

def z214 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1c11900e0e07fc35 0xec70464038381ff0

def z215 : W := mkw 0xfffdfdfdb030c28c 0x13fff7f7f6c0c30a 0xfffffffff038e3ff 0xfbffffffffc0e38f

def z216 : W := mkw 0xb601fa009240f830 0x0ad807e8024903e0 0xfe01fe000000fc17 0xe3f807f8000003f0

def z217 : W := mkw 0xffffdded00a20000 0x13ffff77b4028800 0xffffffff81e7003f 0xf7fffffffe079c00

def z218 : W := mkw 0xb2276e37d9e3cf39 0x0ec89db8df678f3c 0xe27e7e7ff1e79f3e 0x9789f9f9ffc79e7c

def z219 : W := mkw 0x2401fa009240f830 0x089007e8024903e0 0xe001fe01f000fc33 0xcb8007f807c003f0

def z220 : W := mkw 0x00262637b0f3cfad 0x04009898dec3cf3e 0x027e7e7ff1fffffe 0x9c09f9f9ffc7ffff

def z221 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfdfe00007e3f0009 0x2bf7f80001f8fc00

def z222 : W := mkw 0x2427ffff80e38f29 0x14909ffffe038e3c 0x027fffff81e79f3e 0xd409fffffe079e7c

def z223 : W := mkw 0x0400900202013500 0x00100240080804d4 0x1c11900e0e27ff3d 0xfc70464038389ffc

def z224 : W := mkw 0x49fa000124be0000 0x2127e8000492f800 0x01fe0000003f0008 0x0007f8000000fc00

def z225 : W := mkw 0x0890008a060d3542 0x00224002281834d5 0x0190018e0e3fffe8 0x1c0640063838ffff

def z226 : W := mkw 0x2405fe369241ff39 0x0c9017f8da4907fc 0x0001fe7e0000ff10 0x500007f9f80003fc

def z227 : W := mkw 0x0890008a040d0542 0x0022400228103415 0x0190118e003f9ffc 0x940640463800fe7f

def z228 : W := mkw 0xdbfe2637edff8f29 0x276ff898dfb7fe3c 0xfffe7e7fffff9f3f 0xbffff9f9fffffe7c

def z229 : W := mkw 0xffddddee040d0542 0x13ff7777b8103415 0xfffffffe003f03df 0xf3fffffff800fc0f

def z230 : W := mkw 0xffddfdec9000c000 0x13ff77f7b2400300 0xfffffffff000e03f 0xfbffffffffc00380

def z231 : W := mkw 0xfbfb41416dbe0000 0x23efed0505b6f800 0xffffe1f1ffff003f 0xffffff87c7fffc00

def z232 : W := mkw 0xfffbd9c96dbe0000 0x33ffef6725b6f800 0xffff8181ffff002f 0xeffffe0607fffc00

def z233 : W := mkw 0x6565fdfdb030c28c 0x119597f7f6c0c30a 0xe1e1fffff038e3fb 0xdb8787ffffc0e38f

def z234 : W := mkw 0x0c90908a00010500 0x0032424228000414 0x1d91918e00279f3d 0xf476464638009e7c

def z235 : W := mkw 0x4166057720b3078d 0x05059815dc82cc1e 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000100000009c34 0x8400004000000270

def z237 : W := mkw 0xb627fe35dbe2fa39 0x0ed89ff8d76f8be8 0xfe6ffe71ffc0fc37 0xeff9bff9c7ff03f0

def z238 : W := mkw 0xffd9d9c800000000 0x13ff676720000000 0xfd91918e0000001d 0xf3f6464638000000

def z239 : W := mkw 0x0426b6bf82e3bf6b 0x04109adafe0b8efd 0x027fffff81e7fffe 0xd409fffffe079fff

def z240 : W := mkw 0xffddddec49000000 0x13ff7777b1240000 0xffffffffffc0003f 0xffffffffffff0000

def z241 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000181c00026 0x8408000006070000

def z242 : W := mkw 0x000000005b007010 0x08000000016c01c0 0x000000007e006000 0x0800000001f80180

def z243 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1c10100e0e3fffe4 0x2c7040403838ffff

def z244 : W := mkw 0x9e9c9cac00000000 0x127a7272b0000000 0x1e7e7e7e0000001e 0xb079f9f9f8000000

def z245 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xffff8181ffffe3ff 0xfffffe0607ffff8f

def z246 : W := mkw 0x416001512030028c 0x010580054480c00a 0x0060007000000000 0x00018001c0000000

def z247 : W := mkw 0xf74dddec00000000 0x13dd3777b0000000 0xe26ffffe00000012 0x5389bffff8000000

def z248 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e06071f038002b 0x8b878181c7c0e000

def z249 : W := mkw 0xdbf800016d3c0000 0x236fe00005b4f000 0xfde00001fe38002b 0xabf7800007f8e000

def z250 : W := mkw 0x00002202df4dfd72 0x080000880b7d37f5 0x00000001ffffffe0 0x0c00000007ffffff

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x01800180003803c8 0x100600060000e00f

def z252 : W := mkw 0x0400900002003000 0x00100240000800c0 0x1c0010000e001c04 0x2470004000380070

def z253 : W := mkw 0x2401d80000000000 0x0090076000000000 0x0001fe0000000010 0x400007f800000000

def z254 : W := mkw 0x0000020000400820 0x0000000800010020 0x02001e0001c01c04 0x0408007800070070

def z255 : W := mkw 0x61636151b0b2c28c 0x01858d8546c2cb0a 0xe3ffe1f1f1ffe3ff 0xdf8fff87c7c7ff8f

def z256 : W := mkw 0x0cb0b09b862db74a 0x0032c2c26e18b6dd 0x1df1f1ff8e3fffff 0xfc77c7c7fe38ffff

def z257 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1818181f038e3e1 0x4b86060607c0e38f

def z258 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f000001b 0xd3878787c7c00000

def z259 : W := mkw 0xffddddec02003000 0x13ff7777b00800c0 0xfffffffe0e00fc3f 0xfffffffff83803f0

def z260 : W := mkw 0x4df0908b263d3542 0x0137c2422c98f4d5 0xfdf1918ffe3fffff 0xfff7c6463ff8ffff

def z261 : W := mkw 0x49fe2637a4ff8f29 0x2527f898de93fe3c 0x03fe7e7f81ff9f3e 0x940ff9f9fe07fe7c

def z262 : W := mkw 0x08900002060d3542 0x00224000081834d5 0x1d9000000e3fffed 0xac7640000038ffff

def z263 : W := mkw 0xffffffffb0f3cfad 0x17fffffffec3cf3e 0xfffffffff1ffffff 0xffffffffffc7ffff

def z264 : W := mkw 0xdbfe04256dbe0000 0x236ff81095b6f800 0xfffe7e7fffff003f 0xbffff9f9fffffc00

def z265 : W := mkw 0xffd9d9c800000000 0x13ff676720000000 0xfd81818000000001 0x63f6060600000000

def z266 : W := mkw 0x00202211fb70fabc 0x0800808847edc3ea 0x00000001fff8ffe0 0x0c00000007ffe3ff

def z267 : W := mkw 0x0024263780618f29 0x04009098de01863c 0x00607e7f80209f3a 0x900181f9fe00827c

def z268 : W := mkw 0x9a98000000000000 0x026a600000000000 0x1e1e000000000004 0x2078780000000000

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010100e0000001c 0x9000404038000000

def z270 : W := mkw 0x0c90b28a864dbd62 0x003242ca2a1936f5 0x1f91ff8f8fffffff 0xfc7e47fe3e3fffff

def z271 : W := mkw 0xbe91d8885f0c7052 0x0afa4762217c31c1 0xfd8181807e1860c1 0x6bf6060601f86183

def z272 : W := mkw 0xffddddec30104084 0x13ff7777b0c04102 0xfffffffe701860df 0xfbfffffff9c06183

def z273 : W := mkw 0x6561fb51b270fabc 0x099587ed46c9c3ea 0xe1e1fff1f038fffb 0xdb8787ffc7c0e3ff

def z274 : W := mkw 0x00262637edff8f29 0x24009898dfb7fe3c 0x027e7e7fffff9f3e 0x9c09f9f9fffffe7c

def z275 : W := mkw 0x61676775b0f2caad 0x05859d9dd6c3cb2a 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z276 : W := mkw 0xffd9d9c800000000 0x13ff676720000000 0xffff81800000000f 0xe3fffe0600000000

def z277 : W := mkw 0x0404b6be8241bf6b 0x041012dafa0906fd 0x0001fffe0000ffd0 0x500007fff80003ff

def z278 : W := mkw 0x0cb0b09bb63df7ce 0x0032c2c26ed8f7df 0x1d91918ffe3ffffd 0xfc7646463ff8ffff

def z279 : W := mkw 0x000405ec00000000 0x10001017b0000000 0x000001fe00000000 0x10000007f8000000

def z280 : W := mkw 0x49d801c800000000 0x1127600720000000 0x0180018000000000 0x0006000600000000

def z281 : W := mkw 0x2027677790e3cfad 0x04809d9dde438f3e 0x027fffff81e7fffe 0xd409fffffe079fff

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000000027002c 0x8400400000009c00

def z283 : W := mkw 0xb2016a00db40f830 0x0ac805a8036d03e0 0xe2006e01ffc0fc22 0x0f8801b807ff03f0

def z284 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91918e0e071c1d 0xf476464638381c70

def z285 : W := mkw 0xb601d8005b007010 0x0ad80760016c01c0 0xfe018001ffc06027 0xeff8060007ff0180

def z286 : W := mkw 0xfbf96151fd3cc28c 0x23efe58547f4f30a 0xfde1e1f1fe38e3fb 0xfbf78787c7f8e38f

def z287 : W := mkw 0xb601fb50db40fabc 0x0ad807ed436d03ea 0xfe01fff1ffc0fff7 0xfff807ffc7ff03ff

def z288 : W := mkw 0xf741fb40db40f830 0x0bdd07ed036d03e0 0xffe1fff1ffc0fc3f 0xffff87ffc7ff03f0

def z289 : W := mkw 0xffddffecdb40f830 0x1bff77ffb36d03e0 0xffffffffffc0fc3f 0xffffffffffff03f0

def z290 : W := mkw 0x6dddddec00000000 0x11b77777b0000000 0x01fffffe00000018 0x5007fffff8000000

def z291 : W := mkw 0xdbfa2011edbe8208 0x236fe88047b6fa08 0xfffe6071ffff833f 0xbffff981c7fffe0c

def z292 : W := mkw 0x0026263786efbf6b 0x04009898de1bbefd 0x027e7e7f8ffffffe 0x9c09f9f9fe3fffff

def z293 : W := mkw 0xb601d80049000000 0x02d8076001240000 0xfe01fe01ffc00037 0xeff807f807ff0000

def z294 : W := mkw 0xd36e2635e9f28a29 0x274db898d7a7ca28 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z295 : W := mkw 0x2401d9c800000000 0x1090076720000000 0x0001818000000000 0x4000060600000000

def z296 : W := mkw 0xffddfffe80418f29 0x17ff77fffa01063c 0xfffffffe00009f1f 0xf3fffffff800027c

def z297 : W := mkw 0x49dc05ee040d0542 0x11277017b8103415 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z298 : W := mkw 0xf74dff64db40f830 0x1bdd37fd936d03e0 0xfe6ffe71ffc0fc37 0xeff9bff9c7ff03f0

def z299 : W := mkw 0x2401fb509240fabc 0x089007ed424903ea 0x0001fff00000ffd0 0x500007ffc00003ff

def z300 : W := mkw 0x9a9a00004d8e0000 0x226a680001363800 0x1e1e00000fc70004 0x24787800003f1c00

def z301 : W := mkw 0x0426b63782e3bf29 0x04109ad8de0b8efc 0x1e7ffe7f8fe7ff3f 0xfc79fff9fe3f9ffc

def z302 : W := mkw 0x200160009000c000 0x0080058002400300 0xe001e001f000e033 0xcb80078007c00380

def z303 : W := mkw 0x41662777a0f38fad 0x0505989dde83ce3e 0x03fe7fff81ff9ffe 0x940ff9fffe07fe7f

def z304 : W := mkw 0xdbdc042400000000 0x036f701090000000 0xfffe7e7e0000001f 0xb3fff9f9f8000000

def z305 : W := mkw 0x08b626bf84ef8f6b 0x0422d89afe13be3d 0x03fe7fff81ff9ffe 0x940ff9fffe07fe7f

def z306 : W := mkw 0x96069e264bc33d31 0x0e581a78992f0cf4 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z307 : W := mkw 0x0cb2b29b86efbf6b 0x0432caca6e1bbefd 0x1d91918f8ffffffd 0xfc7646463e3fffff

def z308 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0038e3ff 0xfbfffffff800e38f

def z309 : W := mkw 0x61616001b030c000 0x0185858006c0c300 0xe1e1e001f038e03b 0xcb87878007c0e380

def z310 : W := mkw 0x08b200016dbe0000 0x2022c80005b6f800 0x1d900001ffff002d 0xac76400007fffc00

def z311 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x007e7e7e00279f18 0x1001f9f9f8009e7c

def z312 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d90118e0e3f1fcc 0x347640463838fc7f

def z313 : W := mkw 0xffddddee00010500 0x13ff7777b8000414 0xfffffffe00279f3f 0xf7fffffff8009e7c

def z314 : W := mkw 0xffd9fa00ff5cf830 0x2bff67e803fd73e0 0xff81fe01ffd8fc37 0xeffe07f807ff63f0

def z315 : W := mkw 0x2401f0009200f000 0x009007c0024803c0 0xfc01f001fe00fc37 0xeff007c007f803f0

def z316 : W := mkw 0x69f161dbb43dc7ce 0x01a7c5876ed0f71f 0xe1f1e1fff03fe3fb 0xdb87c787ffc0ff8f

def z317 : W := mkw 0xb2016a00d940c830 0x0ac805a803650320 0xe2007e01f1c09c36 0x878801f807c70270

def z318 : W := mkw 0x0000220080408820 0x0000008802010220 0x0000000181c09c20 0x0400000006070270

def z319 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x021e1e0f81e79f24 0x040878783e079e7c

def z320 : W := mkw 0x0000220080408820 0x0000008802010220 0x02006e0181c00002 0x000801b806070000

def z321 : W := mkw 0xdfdc9cac00000000 0x137f7272b0000000 0xfffe1e0e0000000f 0xa3fff87838000000

def z322 : W := mkw 0x00222201fffef830 0x2800888807fffbe0 0x00000001fffffc20 0x0c00000007fffff0

def z323 : W := mkw 0x9ebebebf80e38f29 0x167afafafe038e3c 0x1e7e7e7f81e79f3e 0xb479f9f9fe079e7c

def z324 : W := mkw 0x9e98988800000000 0x127a626220000000 0x1c00000000000000 0x2070000000000000

def z325 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xff81ff81fff8ffff 0xfffe07fe07ffe3ff

def z326 : W := mkw 0xffddddee060d3542 0x13ff7777b81834d5 0xfffffffe0e071c1f 0xf7fffffff8381c70

def z327 : W := mkw 0xf741d9407b107094 0x0bdd076501ec41c2 0xfd8181807e1860c1 0x6bf6060601f86183

def z328 : W := mkw 0xd36a000169b20000 0x234da80005a6c800 0xe27e0001f1e7002e 0x8789f80007c79c00

def z329 : W := mkw 0x6561f1dbb231f7ce 0x019587c76ec8c7df 0xe1e1f1fff038fffb 0xdb8787c7ffc0e3ff

def z330 : W := mkw 0xffd9d8007f1c7010 0x2bff676001fc71c0 0xfd8180007e186001 0x6bf6060001f86180

def z331 : W := mkw 0x202160119020c208 0x0080858046408308 0xe061e071f020e33b 0xdb818781c7c0838c

def z332 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d81918e0e18ffd1 0x78760646383863ff

def z333 : W := mkw 0xbe9dfeacdb40f830 0x1afa77fab36d03e0 0xfe1ffe0fffc0fc37 0xeff87ff83fff03f0

def z334 : W := mkw 0x0022000300a30500 0x000088000c028c14 0x027e100f81e79f3e 0x9409f8403e079e7c

def z335 : W := mkw 0xfffddded20300000 0x13fff777b480c000 0xfffffffff038003f 0xfbffffffffc0e000

def z336 : W := mkw 0x0006062600c30d21 0x0400181898030c34 0x027e7e7e01c71c1e 0x9409f9f9f8071c70

def z337 : W := mkw 0xffdfddec4d8e0000 0x33ff7f77b1363800 0xfffffffe0fc7001f 0xf7fffffff83f1c00

def z338 : W := mkw 0x49d80000241c0000 0x2127600000907000 0x0180000000180000 0x0006000000006000

def z339 : W := mkw 0x6141414030104084 0x0185050500c04102 0xe1e1e1f0701860db 0xdb878787c1c06183

def z340 : W := mkw 0xdbfe06276dff0d21 0x276ff8189db7fc34 0xfffe1e0fffff1c2f 0xaffff8783ffffc70

def z341 : W := mkw 0x0004042400000000 0x0000101090000000 0x007e007e00000008 0x1001f801f8000000

def z342 : W := mkw 0x49fc05fd2030028c 0x1127f017f480c00a 0x01fe01fe003803c8 0x1007f807f800e00f

def z343 : W := mkw 0x4dfa908b26bf3542 0x2137ea422c9afcd5 0x1dff918e0e3ffffd 0xfc77fe463838ffff

def z344 : W := mkw 0xf34d6f64d940c830 0x1bcd35bd93650320 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z345 : W := mkw 0x0000000202013542 0x00000000080804d5 0x000000000000ffc0 0x00000000000003ff

def z346 : W := mkw 0x0004042600010500 0x0000101098000414 0x027e7e7e00279f3e 0x9409f9f9f8009e7c

def z347 : W := mkw 0x49fa000124be0000 0x2127e8000492f800 0x03fe000181ff002e 0x840ff8000607fc00

def z348 : W := mkw 0x0400908a02013542 0x00100242280804d5 0x0000100e00001c00 0x0000004038000070

def z349 : W := mkw 0x6545ddec00000000 0x11951777b0000000 0xe1e1fffe0000001b 0xd38787fff8000000

def z350 : W := mkw 0x0c909088060c3042 0x00324242201830c1 0x1d8181800e38e3f9 0xf87606060038e38f

def z351 : W := mkw 0xdbda00004d8e0000 0x236f680001363800 0xfffe00000fc7000f 0xa7fff800003f1c00

def z352 : W := mkw 0x0026043500a20209 0x04009810d4028808 0x006e007000000000 0x0001b801c0000000

def z353 : W := mkw 0xdbfa000100a20000 0x036fe80004028800 0xfffe000181e7002f 0xa7fff80006079c00

def z354 : W := mkw 0xb601fa02df4dfd72 0x0ad807e80b7d37f5 0xfe01fe01fffffff7 0xeff807f807ffffff

def z355 : W := mkw 0x0cb2908b6fbf3542 0x2032ca422dbefcd5 0x1d91918ffffffffd 0xfc7646463fffffff

def z356 : W := mkw 0x2001414010004084 0x0080050500400102 0x00018180000060c0 0x4000060600000183

def z357 : W := mkw 0x61656575b030c28c 0x01859595d6c0c30a 0xe3fffffff038e3ff 0xdb8fffffffc0e38f

def z358 : W := mkw 0x0000220280418d20 0x000000880a010634 0x02107e0f81e79f3e 0x940841f83e079e7c

def z359 : W := mkw 0x00000002040d0542 0x0000000008103415 0x00000000003f03c0 0x000000000000fc0f

def z360 : W := mkw 0xb601fa02db41fd30 0x0ad807e80b6d07f4 0xfe11fe0fffe7ff3f 0xfff847f83fff9ffc

def z361 : W := mkw 0xb601d8005b007010 0x0ad80760016c01c0 0xfc0190007e00fc35 0xeff0064001f803f0

def z362 : W := mkw 0x089a0000048e0000 0x2022680000123800 0x001e000000070000 0x0000780000001c00

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x02007e0000000016 0x800801f800000000

def z364 : W := mkw 0xfff1fbdbff7dfffe 0x0bffc7ef6ffdf7ff 0xfff1ffffffffffff 0xffffc7ffffffffff

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000000e000025 0xac70000000380000

def z366 : W := mkw 0x2401fa009240f830 0x089007e8024903e0 0x1c01fe000e00fc35 0xec7007f8003803f0

def z367 : W := mkw 0x0022220180e28820 0x0000888806038a20 0x027e7e0181e79c3e 0x8409f9f806079e70

def z368 : W := mkw 0x0022221180e28a29 0x0400888846038a28 0x0000000181c00000 0x0000000006070000

def z369 : W := mkw 0xf761fb51fb70fabc 0x0bdd87ed47edc3ea 0xfe61fe71ffc0fc37 0xeff987f9c7ff03f0

def z370 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xe201fe01f1c0fc12 0x438807f807c703f0

def z371 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x02007e0181e79f36 0x840801f806079e7c

def z372 : W := mkw 0xbe91fa8adf4dfd72 0x0afa47ea2b7d37f5 0xfe11fe0fffc7fc37 0xeff847f83fff1ff0

def z373 : W := mkw 0xdbd8000049000000 0x036f600001240000 0xfffe0001ffc0002f 0xaffff80007ff0000

def z374 : W := mkw 0x4140014020100084 0x0105000500804002 0x01800180001800c0 0x0006000600006003

def z375 : W := mkw 0xbe91d88800000000 0x02fa476220000000 0xff91ff8e0000001f 0xf3fe47fe38000000

def z376 : W := mkw 0x0004263480408a29 0x04001098d2010228 0x00006e7000000000 0x000001b9c0000000

def z377 : W := mkw 0x0020201180208208 0x0000808046008208 0x0000000180208320 0x000000000600820c

def z378 : W := mkw 0xffddffec80408820 0x13ff77ffb2010220 0xffffffff81c09c3f 0xf7fffffffe070270

def z379 : W := mkw 0xb623fa01dbe2f830 0x0ad88fe8076f8be0 0xfe7ffe01ffe7fc3f 0xeff9fff807ff9ff0

def z380 : W := mkw 0x0c90908a02013542 0x00324242280804d5 0x1d91918e0000ffdd 0xf0764646380003ff

def z381 : W := mkw 0x0022000169b20000 0x2000880005a6c800 0x00000001f1c00000 0x0000000007c70000

def z382 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1c11918e0e07ffd4 0x7470464638381fff

def z383 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0x01e1e1f00038e3d8 0x50078787c000e38f

def z384 : W := mkw 0x00202011b030c28c 0x0000808046c0c30a 0x00000001f0000000 0x0000000007c00000

def z385 : W := mkw 0xd36e2637e9f38f29 0x274db898dfa7ce3c 0xe27e7e7ff1e79f3e 0x9789f9f9ffc79e7c

def z386 : W := mkw 0x0400b200db40f830 0x081002c8036d03e0 0x1c019001ffc0fc35 0xec70064007ff03f0

def z387 : W := mkw 0xb201480059004010 0x0ac8052001640100 0xe000000070000000 0x0380000001c00000

def z388 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfd81fffe00000011 0x73f607fff8000000

def z389 : W := mkw 0xfffbd8017fbe7010 0x2bffef6005fef9c0 0xffff8001ffff602f 0xeffffe0007fffd80

def z390 : W := mkw 0x0c94b6be864dbf6b 0x043252dafa1936fd 0x1d91fffe0e3ffffd 0xfc7647fff838ffff

def z391 : W := mkw 0x00202011b030c28c 0x0000808046c0c30a 0x01818181f038e3f9 0xd806060607c0e38f

def z392 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe007e01ffc01c06 0x27f801f807ff0070

def z393 : W := mkw 0x0026043700a30709 0x04009810dc028c1c 0x007e107e00279f3c 0x9401f841f8009e7c

def z394 : W := mkw 0x61616351fb70fabc 0x0985858d47edc3ea 0xe1e1e1f1fff8fffb 0xdf878787c7ffe3ff

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x006060700000001a 0x90018181c0000000

def z396 : W := mkw 0x0cb6b6bf86efbf6b 0x0432dadafe1bbefd 0x1e7e7e7f8fe79f3e 0xb479f9f9fe3f9e7c

def z397 : W := mkw 0xfffdfffdfb70fabc 0x1bfff7fff7edc3ea 0xfffffffffff8ffff 0xffffffffffffe3ff

def z398 : W := mkw 0xdffe9cad6dbe0000 0x337ffa72b5b6f800 0xfffe1e0fffff002f 0xaffff8783ffffc00

def z399 : W := mkw 0x0026043700a30709 0x04009810dc028c1c 0x027e7e7e0027031e 0x9009f9f9f8009c0c

def z400 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xff9f9f8e00000005 0x63fe7e7e38000000

def z401 : W := mkw 0x2427fe3792e3ff39 0x0c909ff8de4b8ffc 0x027ffe7f81e7ff3e 0xd409fff9fe079ffc

def z402 : W := mkw 0x49fe05ed24be0000 0x3127f817b492f800 0x01fe01fe003f0008 0x1007f807f800fc00

def z403 : W := mkw 0x6145456400000000 0x0185151590000000 0xe3fffffe0000001f 0xd38ffffff8000000

def z404 : W := mkw 0x200160009000c000 0x0080058002400300 0xe0006001f0000002 0x0380018007c00000

def z405 : W := mkw 0xf761fa01fb70f830 0x0bdd87e807edc3e0 0xffe1fe01fff8fc3f 0xefff87f807ffe3f0

def z406 : W := mkw 0x000020109000c28c 0x000000804240030a 0x000000000000e3c0 0x000000000000038f

def z407 : W := mkw 0xffddddec5b007010 0x1bff7777b16c01c0 0xfffffffe7e00601f 0xfbfffffff9f80180

def z408 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x0191918e003fffd8 0x500646463800ffff

def z409 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe27e7e7e0000001e 0x9389f9f9f8000000

def z410 : W := mkw 0xb601d8005b007010 0x0ad80760016c01c0 0xfe01fe007e006017 0xebf807f801f80180

def z411 : W := mkw 0xf3616b51f970cabc 0x0bcd85ad47e5c32a 0xe2606e71f1c00002 0x038981b9c7c70000

def z412 : W := mkw 0xdfd8908a060d3542 0x037f6242281834d5 0xffff918e0e3fffff 0xfffffe463838ffff

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z414 : W := mkw 0x9a9e06264dcf0d21 0x266a781899373c34 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z415 : W := mkw 0x69f16151b43cc28c 0x01a7c58546d0f30a 0xfdf1e1f1fe3fe3ff 0xfff7c787c7f8ff8f

def z416 : W := mkw 0x0004263680418f29 0x04001098da01063c 0x00107e7e00279f3c 0x940041f9f8009e7c

def z417 : W := mkw 0x0026063700e30f29 0x04009818dc038c3c 0x027e1e7e01e71f0c 0x1409f879f8079c7c

def z418 : W := mkw 0xb2016a00d940c830 0x0ac805a803650320 0xe201ee01f1c0e033 0xcb8807b807c70380

def z419 : W := mkw 0xb605fe24db40f830 0x0ad817f8936d03e0 0xfe7ffe7fffc0fc3f 0xfff9fff9ffff03f0

def z420 : W := mkw 0xb601fa8adb41fd72 0x0ad807ea2b6d07f5 0xfe01ff8fffc0fff7 0xfff807fe3fff03ff

def z421 : W := mkw 0xffddffec9240f830 0x1bff77ffb24903e0 0xfffffffe0000fc1f 0xf3fffffff80003f0

def z422 : W := mkw 0x0022000124be0000 0x200088000492f800 0x00000000003f0000 0x000000000000fc00

def z423 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xffefeff000000003 0x63ffbfbfc0000000

def z424 : W := mkw 0xffffffffdbe3ff39 0x1fffffffff6f8ffc 0xffffffffffe7ff3f 0xffffffffffff9ffc

def z425 : W := mkw 0xf761f951b030c28c 0x03dd87e546c0c30a 0xffe1fff1f038e3ff 0xfbff87ffc7c0e38f

def z426 : W := mkw 0x0c909088060c3042 0x00324242201830c1 0x1c0000000e000000 0x2070000000380000

def z427 : W := mkw 0xffd9d9c800000000 0x13ff676720000000 0xfde1e1f00000001b 0xf3f78787c0000000

def z428 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x026e7e7f81c09f12 0x1009b9f9fe07027c

def z429 : W := mkw 0x08b604bf04af074b 0x0422d812fc12bc1d 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z430 : W := mkw 0xb621fa11db60fa38 0x0ad887e8476d83e8 0xfe61fe71ffe0ff3f 0xfff987f9c7ff83fc

def z431 : W := mkw 0x9e9c9cac00000000 0x127a7272b0000000 0x1f9f9f8e0000001d 0xf07e7e7e38000000

def z432 : W := mkw 0x9e9c9cae060d3542 0x127a7272b81834d5 0x1e1e1e0e0e071c04 0x2478787838381c70

def z433 : W := mkw 0xdbfa00036fbf3542 0x236fe8000dbefcd5 0xfffe0001ffffffef 0xaffff80007ffffff

def z434 : W := mkw 0x2405ddec00000000 0x10901777b0000000 0x027ffffe0000001e 0xd009fffff8000000

def z435 : W := mkw 0x49fa008b24bf0542 0x2127e8022c92fc15 0x01fe018e003f03c8 0x1007f8063800fc0f

def z436 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe0606071f038e3e2 0x0b818181c7c0e38f

def z437 : W := mkw 0x61636151fdbec28c 0x21858d8547f6fb0a 0xe1e1e1f1ffffe3fb 0xdf878787c7ffff8f

def z438 : W := mkw 0x0000221280418f29 0x040000884a01063c 0x0000000000009f00 0x000000000000027c

def z439 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x03ffffff81ffffff 0xdc0ffffffe07ffff

def z440 : W := mkw 0x920c0c2400000000 0x1248303090000000 0x020e0e0000000000 0x0008383800000000

def z441 : W := mkw 0xbe91fa00df4cf830 0x0afa47e8037d33e0 0xff91fe01fffffc3f 0xeffe47f807fffff0

def z442 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x026e6e7181e79f22 0x0409b9b9c6079e7c

def z443 : W := mkw 0xb601d80002003000 0x02d80760000800c0 0xfe01fe000e00fc37 0xeff807f8003803f0

def z444 : W := mkw 0x0002000000820000 0x0000080000020800 0x021e000001c70004 0x0408780000071c00

def z445 : W := mkw 0xdffeb6bfefffbf6b 0x277ffadaffbffefd 0xffffffffffffffff 0xffffffffffffffff

def z446 : W := mkw 0xdbfa2201edfe8820 0x236fe88807b7fa20 0xfffe7e01ffff9c3f 0xaffff9f807fffe70

def z447 : W := mkw 0x000000006d1c0000 0x2000000001b47000 0x000000007e180000 0x0800000001f86000

def z448 : W := mkw 0x00002200d940c830 0x0800008803650320 0x00000001f1c00000 0x0000000007c70000

def z449 : W := mkw 0xb2016a00d940c830 0x0ac805a803650320 0xfe006e01ffc00027 0xaff801b807ff0000

def z450 : W := mkw 0xffffffffedff8f29 0x37ffffffffb7fe3c 0xffffffffffff9f3f 0xfffffffffffffe7c

def z451 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfc018001ffc0fc21 0x6ff0060007ff03f0

def z452 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe061e1f1f000e3d2 0x53818787c7c0038f

def z453 : W := mkw 0xffffdded24be0000 0x33ffff77b492f800 0xfffffffe003f001f 0xf3fffffff800fc00

def z454 : W := mkw 0xffd9d9c86d1c0000 0x33ff676721b47000 0xfd8181807e180001 0x6bf6060601f86000

def z455 : W := mkw 0x20016a009040c830 0x088005a802410320 0x00006e0000000000 0x000001b800000000

def z456 : W := mkw 0x000020009000c000 0x0000008002400300 0x00000001f000e020 0x0800000007c00380

def z457 : W := mkw 0x0026243780a38709 0x04009890de028e1c 0x007e607f8027833a 0x9001f981fe009e0c

def z458 : W := mkw 0x960090004b003000 0x02580240012c00c0 0xfe019001ffc0fc37 0xeff8064007ff03f0

def z459 : W := mkw 0x9e9c9cae060d3542 0x127a7272b81834d5 0x1f9f9f8e0e3ffffd 0xfc7e7e7e3838ffff

def z460 : W := mkw 0x6df7f7ffb6ffffef 0x05b7dfdffedbffff 0xffffffffffffffff 0xffffffffffffffff

def z461 : W := mkw 0xffdfdfee00c30d21 0x17ff7f7fb8030c34 0xfffffffe01c71c1f 0xf7fffffff8071c70

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x000181800000e3d0 0x500006060000038f

def z463 : W := mkw 0x9e909a8a4f4d3d72 0x0a7a426a293d34f5 0x1e101e0e0fc71c04 0x24784078383f1c70

def z464 : W := mkw 0xffddfdfc9000c28c 0x13ff77f7f240030a 0xfffffffe0000e3df 0xf3fffffff800038f

def z465 : W := mkw 0xb601f8009000c000 0x02d807e002400300 0xfe01fe01f000e037 0xebf807f807c00380

def z466 : W := mkw 0x69fd65fdb030c28c 0x11a7f597f6c0c30a 0xe1ffe1fff038e3fb 0xdb87ff87ffc0e38f

def z467 : W := mkw 0xfff9f9d9b030c28c 0x13ffe7e766c0c30a 0xfde1e1f1f038e3fb 0xfbf78787c7c0e38f

def z468 : W := mkw 0x200160009000c000 0x0080058002400300 0xe181e181f038e3fb 0xdb86078607c0e38f

def z469 : W := mkw 0x2401fa8a9241fd72 0x089007ea2a4907f5 0x0001ff8e0000ffd0 0x500007fe380003ff

def z470 : W := mkw 0xb601f800db00f010 0x0ad807e0036c03c0 0xfc01e001fe00e033 0xebf0078007f80380

def z471 : W := mkw 0x6dd1d1c8361c70c6 0x01b7474720d871c3 0xfd8181807e1860c1 0x6bf6060601f86183

def z472 : W := mkw 0x61676775b0f2caad 0x05859d9dd6c3cb2a 0xe3efeff1f1f8e3fb 0xdb8fbfbfc7c7e38f

def z473 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfdff81fe00000009 0x73f7fe07f8000000

def z474 : W := mkw 0x92000a0049400830 0x0a48002801250020 0x02000e0001c00000 0x0008003800070000

def z475 : W := mkw 0x416001512030028c 0x010580054480c00a 0x01e181f00038e3f9 0xd8078607c000e38f

def z476 : W := mkw 0xb627fe3780e38f29 0x06d89ff8de038e3c 0xfe7ffe7f81e79f3f 0xf7f9fff9fe079e7c

def z477 : W := mkw 0xb601d80000000000 0x02d8076000000000 0xfc01800000000001 0x63f0060000000000

def z478 : W := mkw 0xb201480000000000 0x02c8052000000000 0xe2006e0000000002 0x038801b800000000

def z479 : W := mkw 0x0cb6b6bf80e38f29 0x0432dadafe038e3c 0x1fffffff81e79f3f 0xf47ffffffe079e7c

def z480 : W := mkw 0xf741fb40fb50f8b4 0x0bdd07ed03ed43e2 0xff81ff81ffd8fcf7 0xeffe07fe07ff63f3

def z481 : W := mkw 0x2401d80012007010 0x08900760004801c0 0x0001800000006000 0x4000060000000180

def z482 : W := mkw 0x0400b2008240b820 0x001002c8020902e0 0x1e01fe018fc0fc37 0xec7807f8063f03f0

def z483 : W := mkw 0xf36f6f7580e28a29 0x17cdbdbdd6038a28 0xe26e6e7181c00002 0x0389b9b9c6070000

def z484 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e6e7f81e7030a 0x1009f9b9fe079c0c

def z485 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91918e0e1f7cc5 0x6c76464638387df3

def z486 : W := mkw 0xb605dc2400000000 0x02d8177090000000 0xfe7ffe7e0000001f 0xf3f9fff9f8000000

def z487 : W := mkw 0x9200000049000000 0x0248000001240000 0xe2000001f1c00002 0x0388000007c70000

def z488 : W := mkw 0x9e909a8a4f4d3d72 0x0a7a426a293d34f5 0x1f919f8e0ffffffd 0xfc7e467e383fffff

def z489 : W := mkw 0x08900000040c0000 0x0022400000103000 0x1d9181800e3fe3fd 0xfc7646060038ff8f

def z490 : W := mkw 0x9600ba00db40f830 0x0a5802e8036d03e0 0x1e001e01ffc0fc24 0x2c78007807ff03f0

def z491 : W := mkw 0xfbff6777fdffcfad 0x27effd9ddff7ff3e 0xffffffffffffffff 0xffffffffffffffff

def z492 : W := mkw 0xfffbf1dbffbff7ce 0x23ffefc76ffeffdf 0xfffff1ffffffffff 0xffffffc7ffffffff

def z493 : W := mkw 0x0026263580e28a29 0x04009898d6038a28 0x026e6e7181e0833a 0x9009b9b9c607820c

def z494 : W := mkw 0xfffbfb51fffefabc 0x2bffefed47fffbea 0xfffffff1ffffffff 0xffffffffc7ffffff

def z495 : W := mkw 0x6141414000000000 0x0185050500000000 0xe181818000000001 0x4386060600000000

def z496 : W := mkw 0x00000002060d3542 0x00000000081834d5 0x000000000e071c00 0x0400000000381c70

def z497 : W := mkw 0xd360000169300000 0x034d800005a4c000 0xffe00001fff8002f 0xafff800007ffe000

def z498 : W := mkw 0x49fa00016dbe0000 0x2127e80005b6f800 0x01fe0001ffff0028 0x0c07f80007fffc00

def z499 : W := mkw 0x6161414120300000 0x018585050480c000 0xe1e1e1f1f038003b 0xdb878787c7c0e000

def z500 : W := mkw 0xf36d6d75b030c28c 0x13cdb5b5d6c0c30a 0xe3efeff1f038e3fb 0xdb8fbfbfc7c0e38f

def z501 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f01860c3 0x4b878787c7c06183

def z502 : W := mkw 0xf741d94000000000 0x03dd076500000000 0xffe1fff00000001f 0xf3ff87ffc0000000

def z503 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfe7e7e7e00000006 0x23f9f9f9f8000000

def z504 : W := mkw 0x00000002060d3542 0x00000000081834d5 0x018181800e3ffff9 0xdc0606060038ffff

def z505 : W := mkw 0xdbfa000169b20000 0x236fe80005a6c800 0xfffe0001f1c0000f 0xa3fff80007c70000

def z506 : W := mkw 0x9e90908a4f0d3542 0x027a4242293c34d5 0xff91918fffffffff 0xfffe46463fffffff

def z507 : W := mkw 0xbe91fa88df4cf872 0x0afa47ea237d33e1 0xff81ff81ffd8fcf7 0xeffe07fe07ff63f3

def z508 : W := mkw 0x00000000060c3042 0x00000000001830c1 0x000000000e1860c0 0x0800000000386183

def z509 : W := mkw 0xf74ddd6400000000 0x13dd377590000000 0xfe6ffe7000000017 0xe3f9bff9c0000000

def z510 : W := mkw 0x9626be37cbe3bf39 0x0e589af8df2f8efc 0x1e7e7e7f8fe79f3e 0xb479f9f9fe3f9e7c

def z511 : W := mkw 0x9600980000000000 0x0258026000000000 0x1e001e0000000004 0x2078007800000000

def z512 : W := mkw 0x0c909088060c3042 0x00324242201830c1 0x1d9181800e3f60ed 0xec7646060038fd83

def z513 : W := mkw 0x922200016dbe0000 0x2248880005b6f800 0xfe000001ffff0027 0xaff8000007fffc00

def z514 : W := mkw 0x960098004b003010 0x0a580260012c00c0 0x1c0000000e000000 0x2070000000380000

def z515 : W := mkw 0x0006042600830501 0x0400181098020c14 0x001e000e00070000 0x0000780038001c00

def z516 : W := mkw 0x202161519020c28c 0x008085854640830a 0x0061e1f18020e3fa 0xd0018787c600838f

def z517 : W := mkw 0xbe91fa88db40f830 0x0afa47ea236d03e0 0xff91ff8fffc0fc3f 0xfffe47fe3fff03f0

def z518 : W := mkw 0x04049cac00000000 0x10101272b0000000 0x00001e0e00000000 0x0000007838000000

def z519 : W := mkw 0x41602011a0308208 0x010580804680c208 0xe1e06071f038833b 0x9b878181c7c0e20c

def z520 : W := mkw 0x6141414030104084 0x0185050500c04102 0xe000000070000000 0x0380000001c00000

def z521 : W := mkw 0xfbdd4d6400000000 0x13ef753590000000 0xfffe6e700000000f 0xa3fff9b9c0000000

def z522 : W := mkw 0x92262637c9e38f29 0x06489898df278e3c 0xfe7e7e7fffe79f3f 0xbff9f9f9ffff9e7c

def z523 : W := mkw 0xffddffeedf4dfd72 0x1bff77ffbb7d37f5 0xffffffffffffffff 0xffffffffffffffff

def z524 : W := mkw 0xfffdfdfd80208208 0x13fff7f7f6008208 0xffffffff8020833f 0xf3fffffffe00820c

def z525 : W := mkw 0xbe91d88a5f0d7552 0x0afa4762297c35d5 0xfd91918e7e3ffffd 0xfff6464639f8ffff

def z526 : W := mkw 0x0004042400000000 0x0000101090000000 0x00007e7e00000010 0x100001f9f8000000

def z527 : W := mkw 0x20216151b030c28c 0x0080858546c0c30a 0x0001e1f1f038e3f0 0x58000787c7c0e38f

def z528 : W := mkw 0x0c909088040c0000 0x0032424220103000 0x1d91918e0e3f003d 0xfc7646463838fc00

def z529 : W := mkw 0xb601fa00d940c830 0x0ad807e803650320 0xfe01fe01f1c00017 0xe3f807f807c70000

def z530 : W := mkw 0x2c91f08a960df542 0x00b247c22a5837d5 0xfd91f18ffe3fffff 0xfff647c63ff8ffff

def z531 : W := mkw 0x0004262480408820 0x0000109892010220 0x027e7e7f81c09c3e 0x9409f9f9fe070270

def z532 : W := mkw 0x4160000120300000 0x010580000480c000 0x01e0000000380008 0x000780000000e000

def z533 : W := mkw 0x4df091db263d37ce 0x0137c2476c98f4df 0x1df191fe0e3ffffd 0xfc77c647f838ffff

def z534 : W := mkw 0x0006062400c20821 0x0400181890030820 0x020e0e0001c00000 0x0008383800070000

def z535 : W := mkw 0xdffa90896fbe3042 0x237fea4225bef8c1 0xffff8181ffff60ef 0xeffffe0607fffd83

def z536 : W := mkw 0xdbd8000000000000 0x036f600000000000 0xfd80000000000001 0x23f6000000000000

def z537 : W := mkw 0x002000112030028c 0x000080004480c00a 0x00000000003803c0 0x000000000000e00f

def z538 : W := mkw 0x0026062700e30d21 0x040098189c038c34 0x027e1e0f81e71c2e 0x8409f8783e079c70

def z539 : W := mkw 0x0004263680418f29 0x04001098da01063c 0x02007e7f81c09f36 0x940801f9fe07027c

def z540 : W := mkw 0x20216011b030c28c 0x0080858046c0c30a 0xe001e001f038e3f3 0xcb80078007c0e38f

def z541 : W := mkw 0x2401fa009240f830 0x089007e8024903e0 0x0201fe0181c0fc36 0xc40807f8060703f0

def z542 : W := mkw 0x61636353b0f3cfad 0x05858d8d4ec3cf3e 0xe1e1e1f1f1fffffb 0xdf878787c7c7ffff

def z543 : W := mkw 0x00000002060d3542 0x00000000081834d5 0x0010100e0e3ffffc 0x9c0040403838ffff

def z544 : W := mkw 0x414c056400000000 0x1105301590000000 0x006e007000000000 0x0001b801c0000000

def z545 : W := mkw 0x0026263580e28a29 0x04009898d6038a28 0x026e7e7181c09c36 0x8409b9f9c6070270

def z546 : W := mkw 0xdffa9a016ffe3830 0x2b7fea6805bff8e0 0xfffe1e01ffff1c2f 0xaffff87807fffc70

def z547 : W := mkw 0x69fb6151b4bec28c 0x21a7ed8546d2fb0a 0xe1ffe1f1f03fe3fb 0xdb87ff87c7c0ff8f

def z548 : W := mkw 0xd348000000000000 0x034d200000000000 0xe26e000000000002 0x0389b80000000000

def z549 : W := mkw 0x000200004d8e0000 0x2000080001363800 0x000000000fc70000 0x04000000003f1c00

def z550 : W := mkw 0xdbfa00036dbf0500 0x236fe8000db6fc14 0xfffe100fffff9f3f 0xbffff8403ffffe7c

def z551 : W := mkw 0xffddffecd940c830 0x1bff77ffb3650320 0xfffffffff1c0001f 0xf3ffffffffc70000

def z552 : W := mkw 0xdbfe2635edfe8a29 0x276ff898d7b7fa28 0xfffe6e71ffff002f 0xaffff9b9c7fffc00

def z553 : W := mkw 0x0022201180a28208 0x0000888046028a08 0x027e607181e7833e 0x9409f981c6079e0c

def z554 : W := mkw 0xffd9d80000000000 0x03ff676000000000 0xfffffe000000001f 0xe3fffff800000000

def z555 : W := mkw 0x6161414130304084 0x0185850504c0c102 0xe1e18181f03860eb 0xcb87860607c0e183

def z556 : W := mkw 0xffddddee02013542 0x13ff7777b80804d5 0xfffffffe0000ffdf 0xf3fffffff80003ff

def z557 : W := mkw 0xdfdc9dec00000000 0x137f7277b0000000 0x1ffe1ffe0000000c 0x307ff87ff8000000

def z558 : W := mkw 0xb601da005b407830 0x0ad80768016d01e0 0xfe019e007fc07c05 0x6ff8067801ff01f0

def z559 : W := mkw 0xb601fa0080408820 0x02d807e802010220 0xfe01fe0181c09c37 0xe7f807f806070270

def z560 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe3efeff00000001b 0xd38fbfbfc0000000

def z561 : W := mkw 0x20016200db40f830 0x08800588036d03e0 0xe001e001ffc0fc33 0xcf80078007ff03f0

def z562 : W := mkw 0x614161409000c000 0x0185058502400300 0xe1e1e1f1f000e03b 0xdb878787c7c00380

def z563 : W := mkw 0xf36f4d6569b20000 0x33cdbd3595a6c800 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z564 : W := mkw 0x0026043700a30709 0x04009810dc028c1c 0x027e007f81e7032e 0x9409f801fe079c0c

def z565 : W := mkw 0x41602151b030c28c 0x0105808546c0c30a 0x01e001f1f038e3e8 0x18078007c7c0e38f

def z566 : W := mkw 0xf761f951fb30f29c 0x0bdd87e547ecc3ca 0xfde1e1f1fe38e3fb 0xfbf78787c7f8e38f

def z567 : W := mkw 0x0400908800000000 0x0010024220000000 0x0001918e00000010 0x5000064638000000

def z568 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0010100f81e79f3c 0x940040403e079e7c

def z569 : W := mkw 0x2027663790e3cf29 0x04809d98de438f3c 0xe27ffe7ff1e7ff3f 0xdf89fff9ffc79ffc

def z570 : W := mkw 0x200160009000c000 0x0080058002400300 0x0001e0000000e010 0x4000078000000380

def z571 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfc01fe007e00fc11 0x6bf007f801f803f0

def z572 : W := mkw 0x0890008a040d0542 0x0022400228103415 0x0191818e003fe3f9 0xd80646063800ff8f

def z573 : W := mkw 0x0006263680c38f29 0x04001898da030e3c 0x021e7e7e01c79f14 0x140879f9f8071e7c

def z574 : W := mkw 0xb2016000d900c000 0x02c8058003640300 0xfe01e001ffc0e037 0xeff8078007ff0380

def z575 : W := mkw 0x41602011b030c28c 0x0105808046c0c30a 0xe1e00001f038e3eb 0x8b87800007c0e38f

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x000180000000e031 0xc800060000000380

def z577 : W := mkw 0x0026263580e28a29 0x04009898d6038a28 0x027e7e7f81c0001e 0x9009f9f9fe070000

def z578 : W := mkw 0x69dd45ec00000000 0x11a77517b0000000 0xe1ffe1fe0000001b 0xd387ff87f8000000

def z579 : W := mkw 0x2c91fa8a964dfd72 0x08b247ea2a5937f5 0x1d91ff8e0e3ffffd 0xfc7647fe3838ffff

def z580 : W := mkw 0x616141512030028c 0x018585054480c00a 0xe1e1e1f0003803db 0xd3878787c000e00f

def z581 : W := mkw 0x0000000200010500 0x0000000008000414 0x0000100e00009f10 0x100000403800027c

def z582 : W := mkw 0xbe9bfa00dfcef830 0x2afa6fe8037f3be0 0xfe1ffe01ffc7fc37 0xeff87ff807ff1ff0

def z583 : W := mkw 0xf36f6f7780e38f29 0x17cdbdbdde038e3c 0xe27e7e7f81e79f3e 0x9789f9f9fe079e7c

def z584 : W := mkw 0xffdddfec4b403830 0x1bff777fb12d00e0 0xfffffffe0fc01c1f 0xf7fffffff83f0070

def z585 : W := mkw 0x0020000120300000 0x000080000480c000 0x00000001f0380020 0x0800000007c0e000

def z586 : W := mkw 0xb621fa11fb70fabc 0x0ad887e847edc3ea 0xfe01fe01fff8fff7 0xeff807f807ffe3ff

def z587 : W := mkw 0xffd9d9c8060c3042 0x13ff6767201830c1 0xfd8181800e1860c1 0x6bf6060600386183

def z588 : W := mkw 0xfbff4d656dbe0000 0x33effd3595b6f800 0xfffe6e71ffff002f 0xaffff9b9c7fffc00

def z589 : W := mkw 0x0024243580208208 0x00009090d6008208 0x027e7e7f8020833e 0x9009f9f9fe00820c

def z590 : W := mkw 0x2405ffec9240f830 0x189017ffb24903e0 0x0001fffe0000fc10 0x500007fff80003f0

def z591 : W := mkw 0x00002200db40f830 0x08000088036d03e0 0x02007e01ffc0fc36 0x8c0801f807ff03f0

def z592 : W := mkw 0x6561f151b230f28c 0x019587c546c8c3ca 0xfde1f1f1fe38ffff 0xfff787c7c7f8e3ff

def z593 : W := mkw 0x0020201180208208 0x0000808046008208 0x0060607180000002 0x00018181c6000000

def z594 : W := mkw 0xfffdfdffb63df7ce 0x13fff7f7fed8f7df 0xfffffffffe3fffff 0xfffffffffff8ffff

def z595 : W := mkw 0xf36b6151f9b2c28c 0x23cdad8547e6cb0a 0xe26e6071f1c00002 0x0389b981c7c70000

def z596 : W := mkw 0xf3616151f930c28c 0x03cd858547e4c30a 0xffe1e1f1fff8e3ff 0xffff8787c7ffe38f

def z597 : W := mkw 0x0020000100200000 0x0000800004008000 0x006000018020002a 0x8001800006008000

def z598 : W := mkw 0x9600ba00cb40b830 0x0a5802e8032d02e0 0x1e007e018fc09c36 0xa47801f8063f0270

def z599 : W := mkw 0x4160000120300000 0x010580000480c000 0xe0600001f0000002 0x0381800007c00000

def z600 : W := mkw 0xf76bfa01fbf2f830 0x2bddafe807efcbe0 0xfe6ffe01ffc0fc37 0xeff9bff807ff03f0

def z601 : W := mkw 0xdbd800006d1c0000 0x236f600001b47000 0xfd9000007e3f002d 0xaff6400001f8fc00

def z602 : W := mkw 0x96009a004b403830 0x0a580268012d00e0 0x1e019e000fc0fc35 0xec780678003f03f0

def z603 : W := mkw 0x0c90b28adf4dfd72 0x083242ca2b7d37f5 0x1d91918ffffffffd 0xfc7646463fffffff

def z604 : W := mkw 0x0020201180208208 0x0000808046008208 0x01e1e1f18038e3fb 0xd8078787c600e38f

def z605 : W := mkw 0x9a9a00004d8e0000 0x226a680001363800 0x1f9e00000fff002d 0xac7e7800003ffc00

def z606 : W := mkw 0x089c04ac00000000 0x10227012b0000000 0x001e000e00000000 0x0000780038000000

def z607 : W := mkw 0x0400900002003000 0x00100240000800c0 0x1c0180000e006001 0x6870060000380180

def z608 : W := mkw 0x0c909088060c3042 0x00324242201830c1 0x1d91918e0e1860dd 0xf876464638386183

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000038e3e0 0x080000000000e38f

def z610 : W := mkw 0x08900088040c0042 0x0022400220103001 0x01800180001800c0 0x0006000600006003

def z611 : W := mkw 0x0400900000000000 0x0010024000000000 0x1c01900000000015 0xe070064000000000

def z612 : W := mkw 0x9aba00016dbe0000 0x226ae80005b6f800 0x1e1e0001ffff0024 0x2c78780007fffc00

def z613 : W := mkw 0xfffffe37ffffff39 0x2ffffff8dffffffc 0xfffffe7fffffff3f 0xfffffff9fffffffc

def z614 : W := mkw 0x9abe2637cdef8f29 0x266af898df37be3c 0x1e7e7e7f8fe79f3e 0xb479f9f9fe3f9e7c

def z615 : W := mkw 0x0c909000060c3000 0x00324240001830c0 0x1d9190000e3ffc3d 0xec7646400038fff0

def z616 : W := mkw 0x0000000030104084 0x0000000000c04102 0x00000000701860c0 0x0800000001c06183

def z617 : W := mkw 0x0c9494ac00000000 0x00325252b0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z618 : W := mkw 0x9a9800004d0c0000 0x226a600001343000 0x1c0000000e000000 0x2070000000380000

def z619 : W := mkw 0xffd9fbc8db40f830 0x1bff67ef236d03e0 0xff81ff81ffc0fc37 0xeffe07fe07ff03f0

def z620 : W := mkw 0xdbfa008b6dbf0542 0x236fe8022db6fc15 0xfffe018fffff03ef 0xbffff8063ffffc0f

def z621 : W := mkw 0x0c90908800000000 0x0032424220000000 0x1d91918e0038e3fd 0xf87646463800e38f

def z622 : W := mkw 0x4ddc95ec00000000 0x11377257b0000000 0x1dff91fe0000001d 0xf077fe47f8000000

def z623 : W := mkw 0x49d8000000000000 0x0127600000000000 0x01fe000000000008 0x0007f80000000000

def z624 : W := mkw 0x61656777b071cfad 0x0585959ddec1c73e 0xe1e1fffff038fffb 0xdb8787ffffc0e3ff

def z625 : W := mkw 0x49f001db243d07ce 0x0127c0076c90f41f 0x01f001fe003f03c8 0x1007c007f800fc0f

def z626 : W := mkw 0xfbfb6151fdbec28c 0x23efed8547f6fb0a 0xfffe6071ffff002f 0xaffff981c7fffc00

def z627 : W := mkw 0x08b2000104ae0000 0x0022c8000412b800 0x1ffe00018fff002f 0xac7ff800063ffc00

def z628 : W := mkw 0xfffdfdfdb030c28c 0x13fff7f7f6c0c30a 0xfffffffff000001f 0xf3ffffffffc00000

def z629 : W := mkw 0xdffa90016fbe3000 0x237fea4005bef8c0 0xffff9001fffffc3f 0xeffffe4007fffff0

def z630 : W := mkw 0xffffffff86efbf6b 0x17fffffffe1bbefd 0xffffffff8fffffff 0xfffffffffe3fffff

def z631 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xe3fe0001f1ff000a 0x038ff80007c7fc00

def z632 : W := mkw 0xd36a000169b20000 0x234da80005a6c800 0xfe6e0001ffc00027 0xaff9b80007ff0000

def z633 : W := mkw 0xdfd890886f1c3042 0x237f624221bc70c1 0xfd8181807e1860c1 0x6bf6060601f86183

def z634 : W := mkw 0xffd9d9c85b007010 0x1bff6767216c01c0 0xfd8181807e006001 0x6bf6060601f80180

def z635 : W := mkw 0xb2276e35d9e2ca39 0x0ec89db8d7678b28 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z636 : W := mkw 0x0c909088060c3042 0x00324242201830c1 0x1d8191800e18fcf5 0xec760646003863f3

def z637 : W := mkw 0x0cb2908b06af3542 0x0032ca422c1abcd5 0x1fff918f8fffffff 0xfc7ffe463e3fffff

def z638 : W := mkw 0xdbd80000040c0000 0x036f600000103000 0xfffe00000e3f002f 0xaffff8000038fc00

def z639 : W := mkw 0x000022009240f830 0x08000088024903e0 0x000000000000fc00 0x00000000000003f0

def z640 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x007e007f81e79f28 0x1401f801fe079e7c

def z641 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe061e071f000e033 0xcb818781c7c00380

def z642 : W := mkw 0x0890008a040d0542 0x0022400228103415 0x1d90018e0e3f03ed 0xbc7640063838fc0f

def z643 : W := mkw 0x9e9e9cac4d8e0000 0x327a7a72b1363800 0x1e1e1e0e0fc70004 0x24787878383f1c00

def z644 : W := mkw 0x0020001100200208 0x0000800044008008 0x0060007000200308 0x10018001c000800c

def z645 : W := mkw 0x2001400010004000 0x0080050000400100 0xe001800070006001 0x4b80060001c00180

def z646 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0x1ffe00000fff000c 0x247ff800003ffc00

def z647 : W := mkw 0x0400900002003000 0x00100240000800c0 0x1d8191800e38fffd 0xfc7606460038e3ff

def z648 : W := mkw 0xb605ddec00000000 0x12d81777b0000000 0xfe01fffe00000017 0xf3f807fff8000000

def z649 : W := mkw 0x0000008a00010542 0x0000000228000415 0x0000018e000003c0 0x100000063800000f

def z650 : W := mkw 0xdbfa2011fdbec28c 0x236fe88047f6fb0a 0xfffe0001ffffe3ef 0xaffff80007ffff8f

def z651 : W := mkw 0x61676777b0f3cfad 0x05859d9ddec3cf3e 0xe27e7e7ff1e79f3e 0x9789f9f9ffc79e7c

def z652 : W := mkw 0x0004263680418f29 0x04001098da01063c 0x027e7e7e00009f1e 0x9009f9f9f800027c

def z653 : W := mkw 0xdbfe04376dbf0709 0x276ff810ddb6fc1c 0xfffe007fffff032f 0xbffff801fffffc0c

def z654 : W := mkw 0x00202013b63df7ce 0x000080804ed8f7df 0x00000001fe3fffe0 0x0c00000007f8ffff

def z655 : W := mkw 0x49fa000124be0000 0x2127e8000492f800 0xe1fe0001f03f002b 0x8b87f80007c0fc00

def z656 : W := mkw 0x614161509000c28c 0x018505854240030a 0xe1e1e1f00000e3db 0xd3878787c000038f

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x01818180001860c1 0x4806060600006183

def z658 : W := mkw 0x6df1f1d9b63cf2ce 0x01b7c7c766d8f3cb 0xfde1e1f1fe38e3fb 0xfbf78787c7f8e38f

def z659 : W := mkw 0xdbda00006d9e0000 0x236f680001b67800 0xff9e00007fdf0005 0x2ffe780001ff7c00

def z660 : W := mkw 0x6141414000000000 0x0185050500000000 0xe060607000000002 0x03818181c0000000

def z661 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01ee01ffc06003 0x6bf807b807ff0180

def z662 : W := mkw 0xfffffffd80e28a29 0x17fffffff6038a28 0xffffffff81c0001f 0xf3fffffffe070000

def z663 : W := mkw 0x08900000040c0000 0x0022400000103000 0x1d8000000e180001 0x2876000000386000

def z664 : W := mkw 0x6dd1d1ca361d75c6 0x01b7474728d875d7 0xfd91918e7e3ffffd 0xfff6464639f8ffff

def z665 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1c10100e0e279f3c 0xb470404038389e7c

def z666 : W := mkw 0x416200016dbe0000 0x2105880005b6f800 0xe1e00001ffff002b 0x8f87800007fffc00

def z667 : W := mkw 0x2405fffe80418f29 0x149017fffa01063c 0x0001fffe00009f10 0x500007fff800027c

def z668 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0x1e01fe000fc0fc14 0x647807f8003f03f0

def z669 : W := mkw 0xd348000069100000 0x234d200001a44000 0xe000000070000000 0x0380000001c00000

def z670 : W := mkw 0x200161509000c28c 0x008005854240030a 0x0000607000000000 0x00000181c0000000

def z671 : W := mkw 0x2405fdfc9000c28c 0x109017f7f240030a 0x0001fffe0000e3d0 0x500007fff800038f

def z672 : W := mkw 0xdbdc05ec00000000 0x136f7017b0000000 0xfffe01fe0000000f 0xb3fff807f8000000

def z673 : W := mkw 0x0890008800000000 0x0022400220000000 0x0190018e00000008 0x1006400638000000

def z674 : W := mkw 0xb601da004b403830 0x0ad80768012d00e0 0xfe01fe000fc01c17 0xe7f807f8003f0070

def z675 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e061f1f03803ca 0x13878187c7c0e00f

def z676 : W := mkw 0x2401fa00db40f830 0x089007e8036d03e0 0x0001fe01ffc0fc30 0x4c0007f807ff03f0

def z677 : W := mkw 0x9200000049000000 0x0248000001240000 0xfc0000007e000001 0x2bf0000001f80000

def z678 : W := mkw 0x2401f1da9201f7ce 0x009007c76a4807df 0x0001f1fe0000ffd0 0x500007c7f80003ff

def z679 : W := mkw 0x6df1f1d9b030c28c 0x01b7c7c766c0c30a 0xfdf1f1fff038e3ff 0xfbf7c7c7ffc0e38f

def z680 : W := mkw 0x61616153b63df7ce 0x018585854ed8f7df 0xe1e1e1f1fe3ffffb 0xdf878787c7f8ffff

def z681 : W := mkw 0x41602151a030828c 0x010580854680c20a 0x01e061f1803883fa 0x90078187c600e20f

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000001f0000023 0x8b80000007c00000

def z683 : W := mkw 0x9e9a9a004fce3830 0x2a7a6a68013f38e0 0x1e1e1e000fc71c04 0x24787878003f1c70

def z684 : W := mkw 0x0000000200010500 0x0000000008000414 0x0010100e00071c04 0x0400404038001c70

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x0181818000000019 0xd006060600000000

def z686 : W := mkw 0xdbd800006d1c0000 0x236f600001b47000 0xff800001ffd80027 0xaffe000007ff6000

def z687 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0060607181e79f3a 0x94018181c6079e7c

def z688 : W := mkw 0x20054d6400000000 0x1080153590000000 0x00006e7000000000 0x000001b9c0000000

def z689 : W := mkw 0x0006262680c38d21 0x040018989a030e34 0x021e7e0f81c79c36 0x840879f83e071e70

def z690 : W := mkw 0x0000000200010500 0x0000000008000414 0x0191918e003ffffd 0xdc0646463800ffff

def z691 : W := mkw 0xffd9d9ca060d3542 0x13ff6767281834d5 0xfd91918e0e3ffffd 0xfff646463838ffff

def z692 : W := mkw 0x0c90908800000000 0x0032424220000000 0x1c10100e00000004 0x2070404038000000

def z693 : W := mkw 0x000001500000028c 0x000000054000000a 0x000001f0000003c0 0x10000007c000000f

def z694 : W := mkw 0xb623fa01fffef830 0x2ad88fe807fffbe0 0xfe01fe01fffffc37 0xeff807f807fffff0

def z695 : W := mkw 0x2405ddee02013542 0x10901777b80804d5 0x0001fffe0000ffd0 0x500007fff80003ff

def z696 : W := mkw 0x0c90908802003000 0x00324242200800c0 0x1d91918e0e00fc3d 0xfc764646383803f0

def z697 : W := mkw 0xfbf96151b030c28c 0x03efe58546c0c30a 0xffffe1f1f038e3ff 0xfbffff87c7c0e38f

def z698 : W := mkw 0xffffddef6fbf3542 0x33ffff77bdbefcd5 0xffffffffffffffff 0xffffffffffffffff

def z699 : W := mkw 0x61616153b031c78c 0x018585854ec0c71e 0xe1f1f1fff03fffff 0xdf87c7c7ffc0ffff

def z700 : W := mkw 0x0c9696ae06cf3d63 0x04325a5ab81b3cf5 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z701 : W := mkw 0x0400908802003042 0x00100242200800c1 0x00018180000060c0 0x4000060600000183

def z702 : W := mkw 0x200162009040c820 0x0080058802410320 0xe201fe01f1c0fc37 0xcf8807f807c703f0

def z703 : W := mkw 0x00222011fdbec28c 0x2000888047f6fb0a 0x00000001ffffe3e0 0x0c00000007ffff8f

def z704 : W := mkw 0x0000000049000000 0x0000000001240000 0x00000001ffc00020 0x0c00000007ff0000

def z705 : W := mkw 0x0400908a02013542 0x00100242280804d5 0x1c01918e0e00fff5 0xfc700646383803ff

def z706 : W := mkw 0x6141414000000000 0x0185050500000000 0xe1e1e1f00038e3fb 0xdb878787c000e38f

def z707 : W := mkw 0xb2016a00d940c830 0x0ac805a803650320 0xfe007e01ffc09c37 0xaff801f807ff0270

def z708 : W := mkw 0xdbdc2636ed5d8f29 0x276f7098dbb5763c 0xfd807e7e7e189f11 0x3bf601f9f9f8627c

def z709 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe6071ffff003f 0xbffff981c7fffc00

def z710 : W := mkw 0xd76a908b6bb33542 0x235daa422daeccd5 0xe26f918ff1c0ffd2 0x5389be463fc703ff

def z711 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x1e7e7e7f8fe79f3f 0xbc79f9f9fe3f9e7c

def z712 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e181f1f038e3e9 0x5b878607c7c0e38f

def z713 : W := mkw 0x61416150b010c28c 0x0185058542c0430a 0xe1e1e1f07018e3db 0xdb878787c1c0638f

def z714 : W := mkw 0x6dfbfa01b6fef830 0x29b7efe806dbfbe0 0x01fffe00003ffc18 0x4007fff80000fff0

def z715 : W := mkw 0x49dc27ecdb40f830 0x1927709fb36d03e0 0x01fe01ffffc0fc28 0x1c07f807ffff03f0

def z716 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0181ffff03ef 0xbffff80607fffc0f

def z717 : W := mkw 0x654dddec00000000 0x11953777b0000000 0x006ffffe00000010 0x5001bffff8000000

def z718 : W := mkw 0x20054d6400000000 0x1080153590000000 0x027e7e7e0000001e 0x9009f9f9f8000000

def z719 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91918e0e3fffd9 0x787646463838ffff

def z720 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d81918e0e3ffff1 0x7c7606463838ffff

def z721 : W := mkw 0x9a9a00004d8e0000 0x226a680001363800 0xfe1e0001ffc70006 0x27f8780007ff1c00

def z722 : W := mkw 0xf34d4d66060d3542 0x13cd3535981834d5 0xe26e6e700e3fffe2 0x0f89b9b9c038ffff

def z723 : W := mkw 0x0006062600c30d21 0x0400181898030c34 0x027e7e7e01c71c06 0x0409f9f9f8071c70

def z724 : W := mkw 0xb601da005b407830 0x0ad80768016d01e0 0xfe019e01ffc07c27 0xeff8067807ff01f0

def z725 : W := mkw 0xfffbfbdb80e38f29 0x17ffefef6e038e3c 0xfd81818181e79f21 0x67f6060606079e7c

def z726 : W := mkw 0x61416150b010c28c 0x0185058542c0430a 0xe181e1f07038e3f9 0xdb860787c1c0e38f

def z727 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xff9e0001ffff0025 0x2ffe780007fffc00

def z728 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01ff81ffc0fff7 0xfff807fe07ff03ff

def z729 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe61fe71ffc0fc3f 0xfff987f9c7ff03f0

def z730 : W := mkw 0xb627dc375ba37719 0x0ed89f70dd6e8ddc 0xfc7f807e7e276309 0x7bf1fe01f9f89d8c

def z731 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0200000181e79f26 0x8408000006079e7c

def z732 : W := mkw 0x9e9c9cac00000000 0x127a7272b0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z733 : W := mkw 0xdfdc94ac00000000 0x037f7252b0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z734 : W := mkw 0xfbdd456400000000 0x03ef751590000000 0xfffffffe0000001f 0xf3fffffff8000000

def z735 : W := mkw 0x9ebcbcbdb030c28c 0x127af2f2f6c0c30a 0x1e1e1e0ff038e3e4 0x287878783fc0e38f

def z736 : W := mkw 0x202160119020c208 0x0080858046408308 0xe1e1e1f1f038e3fb 0xdb878787c7c0e38f

def z737 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfe7e0001ffff0026 0x2ff9f80007fffc00

def z738 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0xe27e7e7ff1e79f3f 0x9f89f9f9ffc79e7c

def z739 : W := mkw 0x61636151b0b2c28c 0x01858d8546c2cb0a 0xe1e1e1f1f1ffe3fb 0xdf878787c7c7ff8f

def z740 : W := mkw 0xb601fb50db40fabc 0x0ad807ed436d03ea 0xfe01fe71ffc0fc37 0xeff807f9c7ff03f0

def z741 : W := mkw 0x0894042400000000 0x0022501090000000 0x1ffe7e7e0000001f 0xb07ff9f9f8000000

def z742 : W := mkw 0x2405ddec00000000 0x10901777b0000000 0x026ffffe00000012 0x5009bffff8000000

def z743 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e7e7e00000006 0x0009f9f9f8000000

def z744 : W := mkw 0x00222213a0f38f29 0x040088884e83ce3c 0x00000001f1ff9f20 0x0c00000007c7fe7c

def z745 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe7ffe01ffc0fc3f 0xeff9fff807ff03f0

def z746 : W := mkw 0x9aba00016dbe0000 0x226ae80005b6f800 0xfe1e0001ffff0027 0xaff8780007fffc00

def z747 : W := mkw 0x04049cac00000000 0x10101272b0000000 0x027e7e7e0000001e 0x9009f9f9f8000000

def z748 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe181e1f1f038e3f1 0x5b860787c7c0e38f

def z749 : W := mkw 0x6df1f1dbb63df7ce 0x01b7c7c76ed8f7df 0xfc70707ffe071c06 0x27f1c1c1fff81c70

def z750 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01ffc0fc13 0x6bf807f807ff03f0

def z751 : W := mkw 0xffddddec4b003010 0x1bff7777b12c00c0 0xfffffffe0e00001f 0xf3fffffff8380000

def z752 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe26e7e7e00000012 0x1389b9f9f8000000

def z753 : W := mkw 0x41602011a0308208 0x010580804680c208 0xe1e1e1f1f038e3fb 0xdb878787c7c0e38f

def z754 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xffff8001ffffe03f 0xeffffe0007ffff80

def z755 : W := mkw 0xffddddec040c0000 0x13ff7777b0103000 0xfffffffe0e18001f 0xfbfffffff8386000

def z756 : W := mkw 0x0026063700e30f29 0x04009818dc038c3c 0x027e7e7e01e71f1e 0x9409f9f9f8079c7c

def z757 : W := mkw 0x49dc042400000000 0x0127701090000000 0x03fe7e7e0000001e 0x900ff9f9f8000000

def z758 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xff81ff81ffc0fc3f 0xfffe07fe07ff03f0

def z759 : W := mkw 0xffddddec10004000 0x13ff7777b0400100 0xfffffffe7000601f 0xfbfffffff9c00180

def z760 : W := mkw 0xffddddec02003000 0x13ff7777b00800c0 0xfffffffe0000fc1f 0xf3fffffff80003f0

def z761 : W := mkw 0xffddddec060c3042 0x13ff7777b01830c1 0xfffffffe0e18fcff 0xfffffffff83863f3

def z762 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0x1ffffffe0000001c 0x707ffffff8000000

def z763 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe00009c3f 0xf7fffffff8000270

def z764 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91818e0e3fffe9 0x7c7646063838ffff

def z765 : W := mkw 0xfbdd4dec00000000 0x13ef7537b0000000 0xfffe6ffe0000000f 0xb3fff9bff8000000

def z766 : W := mkw 0x0006262680c38d21 0x040018989a030e34 0x027e7e7f81c79c3e 0x9409f9f9fe071e70

def z767 : W := mkw 0xffddddec6d1c0000 0x33ff7777b1b47000 0xffffffffffd8003f 0xffffffffffff6000

def z768 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xff81fe01fff8fc3f 0xeffe07f807ffe3f0

def z769 : W := mkw 0x6dddddec00000000 0x11b77777b0000000 0x1dfffffe0000001d 0xf077fffff8000000

def z770 : W := mkw 0xffddddec6f1c3042 0x33ff7777b1bc70c1 0xfffffffe7e1860df 0xfbfffffff9f86183

def z771 : W := mkw 0xb601fb40db40f830 0x0ad807ed036d03e0 0xfe01fff1ffc0fc37 0xfff807ffc7ff03f0

def z772 : W := mkw 0x61636351b0f2caac 0x01858d8d46c3cb2a 0xe3fffff1f1ffffff 0xdf8fffffc7c7ffff

def z773 : W := mkw 0x2427dded6dbe0000 0x30909f77b5b6f800 0x0001ffffffff0030 0x5c0007fffffffc00

def z774 : W := mkw 0xfbdd4dec00000000 0x13ef7537b0000000 0xe3fe7ffe0000001e 0x938ff9fff8000000

def z775 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe007e01ffc0fc26 0x2ff801f807ff03f0

def z776 : W := mkw 0x6147476630d34da5 0x05851d1d98c34d36 0xe39f9f8e71df7cc5 0x4f8e7e7e39c77df3

def z777 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffff000b 0x2bfff80007fffc00

def z778 : W := mkw 0x0022221384ef8f6b 0x040088884e13be3d 0x0000000181ff9fe0 0x040000000607fe7f

def z779 : W := mkw 0xba9b6150dd8ec28c 0x22ea6d8543763b0a 0x1e1fe1f00fc7e3d4 0x74787f87c03f1f8f

def z780 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfc01fe01ffc0fc31 0x6ff007f807ff03f0

def z781 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000100181e79f34 0x8400004006079e7c

def z782 : W := mkw 0xba916a8add4dcd72 0x0aea45aa2b753735 0xe3906f8ff1ff03ca 0x138e41be3fc7fc0f

def z783 : W := mkw 0xb2016a00db40f830 0x0ac805a8036d03e0 0xfe006e01ffc0fc27 0xaff801b807ff03f0

def z784 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1f91918f8fffffff 0xfc7e46463e3fffff

def z785 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01ffe0ff3f 0xfff807f807ff83fc

def z786 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe11fe01ffe7fc3f 0xeff847f807ff9ff0

def z787 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81c79c36 0x8409f9f9fe071e70

def z788 : W := mkw 0xf36f6775f9f2caad 0x27cdbd9dd7e7cb2a 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z789 : W := mkw 0xb623fa13dbe3ff39 0x0ed88fe84f6f8ffc 0xfc018001ffe7ff21 0x6ff0060007ff9ffc

def z790 : W := mkw 0xb601da004b403830 0x0ad80768012d00e0 0xfe01fe01ffc01c37 0xeff807f807ff0070

def z791 : W := mkw 0xdbfa01416dbe0084 0x236fe80505b6f802 0xfffe0181ffff00ef 0xaffff80607fffc03

def z792 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x03fe7fff81ff9ffe 0x940ff9fffe07fe7f

def z793 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81c79f16 0x1409f9f9fe071e7c

def z794 : W := mkw 0xdbfa00116dbe028c 0x236fe80045b6f80a 0xfffe0001ffff03ef 0xaffff80007fffc0f

def z795 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f038e3da 0x53878787c7c0e38f

def z796 : W := mkw 0xffddddec7f1c7010 0x3bff7777b1fc71c0 0xfffffffe7e18601f 0xfbfffffff9f86180

def z797 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xffeffffe00000013 0x73ffbffff8000000

def z798 : W := mkw 0xfbdd4d6400000000 0x13ef753590000000 0xfffe7e7e0000001f 0xb3fff9f9f8000000

def z799 : W := mkw 0xdfdc9cac00000000 0x137f7272b0000000 0xfffe7e7e0000001f 0xb3fff9f9f8000000

def z800 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfe7e7e7e0000001e 0xb3f9f9f9f8000000

def z801 : W := mkw 0x000405ec00000000 0x10001017b0000000 0x027e7ffe0000001e 0x9009f9fff8000000

def z802 : W := mkw 0xd36a000169b20000 0x234da80005a6c800 0xfe7e0001ffe7002f 0xaff9f80007ff9c00

def z803 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe3e1e1f1f1f8e3ff 0xdf8f8787c7c7e38f

def z804 : W := mkw 0x9204042449000000 0x0248101091240000 0xfe7e7e7fffc0003f 0xbff9f9f9ffff0000

def z805 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f038e3e3 0x4b878787c7c0e38f

def z806 : W := mkw 0xdfdc9dec00000000 0x137f7277b0000000 0x1ffe7ffe0000001e 0xb07ff9fff8000000

def z807 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe001860df 0xfbfffffff8006183

def z808 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000181c71c00 0x0400000006071c70

def z809 : W := mkw 0xdbfa00896dbe0042 0x236fe80225b6f801 0xfffe0181ffff00ef 0xaffff80607fffc03

def z810 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfe7ffe7e00000017 0xe3f9fff9f8000000

def z811 : W := mkw 0x0022221390e3cf29 0x040088884e438f3c 0x00000001f1e7ff20 0x0c00000007c79ffc

def z812 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0xfd91918ffe3fffff 0xfff646463ff8ffff

def z813 : W := mkw 0xffddddec040c0042 0x13ff7777b0103001 0xfffffffe001800df 0xf3fffffff8006003

def z814 : W := mkw 0xffddddec7b107094 0x1bff7777b1ec41c2 0xfffffffe7e1860df 0xfbfffffff9f86183

def z815 : W := mkw 0x9e969eae4fcf3d73 0x0e7a5a7ab93f3cf5 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z816 : W := mkw 0x61636351b0f2caad 0x05858d8d46c3cb2a 0xe1e1e1f1f1f8e3fb 0xdb878787c7c7e38f

def z817 : W := mkw 0x9600ba00cb40b830 0x0a5802e8032d02e0 0xfe007e01ffc09c37 0xaff801f807ff0270

def z818 : W := mkw 0x089404ac00000000 0x00225012b0000000 0x03fe7ffe0000001e 0x900ff9fff8000000

def z819 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e7e7f81c0003e 0x9409f9f9fe070000

def z820 : W := mkw 0x49f2000124be0000 0x0127c8000492f800 0xfffe0001ffff002f 0xaffff80007fffc00

def z821 : W := mkw 0xb601fa10db40fabc 0x0ad807e8436d03ea 0xfe01fe01ffc0fff7 0xeff807f807ff03ff

def z822 : W := mkw 0x414c056400000000 0x1105301590000000 0x027e7e7e0000001e 0x9009f9f9f8000000

def z823 : W := mkw 0x614141503010428c 0x0185050540c0410a 0xe18181f0701863c1 0x5b860607c1c0618f

def z824 : W := mkw 0x616141513030428c 0x0185850544c0c10a 0xe1e181f07038e3f9 0xdb878607c1c0e38f

def z825 : W := mkw 0x00222213d9e3cf39 0x0c0088884f678f3c 0x00000001f1e79f20 0x0400000007c79e7c

def z826 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfe7e0001ffe7002e 0xa7f9f80007ff9c00

def z827 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e7e7e00009c3e 0x9409f9f9f8000270

def z828 : W := mkw 0xd36a00016dbe0000 0x234da80005b6f800 0xfe6e0001ffff0027 0xaff9b80007fffc00

def z829 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe019e01ffc0fc25 0x6ff8067807ff03f0

def z830 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81e71c2e 0x8409f9f9fe079c70

def z831 : W := mkw 0x6145456400000000 0x0185151590000000 0xe27e7e7e0000001e 0x9389f9f9f8000000

def z832 : W := mkw 0xb601fa88db40f872 0x0ad807ea236d03e1 0xfe01ff81ffc0fcf7 0xeff807fe07ff03f3

def z833 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe3e1fff1f038e3ff 0xdb8f87ffc7c0e38f

def z834 : W := mkw 0x49f605ff24bf07cf 0x0527d817fc92fc1f 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z835 : W := mkw 0x49fe04bf24bf074b 0x2527f812fc92fc1d 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z836 : W := mkw 0x9aba00014dae0000 0x226ae8000536b800 0xfe7e0001ffe7002f 0xaff9f80007ff9c00

def z837 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81e71f0e 0x1409f9f9fe079c7c

def z838 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f03863cb 0x5b878787c7c0e18f

def z839 : W := mkw 0x2c95ddec00000000 0x10b25777b0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z840 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1df1f1fe0e3fffff 0xfc77c7c7f838ffff

def z841 : W := mkw 0xf74dddec00000000 0x13dd3777b0000000 0xe3effffe0000001b 0xd38fbffff8000000

def z842 : W := mkw 0x49fe042724bf0501 0x2527f8109c92fc14 0x01fe000e003f0008 0x0007f8003800fc00

def z843 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfdfffffe00000019 0x73f7fffff8000000

def z844 : W := mkw 0xffddddec060c3042 0x13ff7777b01830c1 0xfffffffe0e3f60ff 0xfffffffff838fd83

def z845 : W := mkw 0x2405ddec00000000 0x10901777b0000000 0x007ffffe00000018 0x5001fffff8000000

def z846 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01ffc0fc16 0x67f807f807ff03f0

def z847 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffffe3ef 0xaffff80007ffff8f

def z848 : W := mkw 0xffddddec49000000 0x13ff7777b1240000 0xfffffffff1c0001f 0xf3ffffffffc70000

def z849 : W := mkw 0xf74dddec00000000 0x13dd3777b0000000 0xfe6ffffe00000017 0xf3f9bffff8000000

def z850 : W := mkw 0xdbfa01c96dbe0000 0x336fe80725b6f800 0xfffe0181ffff002f 0xaffff80607fffc00

def z851 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81e79f1a 0x1009f9f9fe079e7c

def z852 : W := mkw 0x61636353b0f3cfad 0x05858d8d4ec3cf3e 0xe1818181f1ffffe1 0x4f86060607c7ffff

def z853 : W := mkw 0x0cb6b6bd86eeba6b 0x0432dadaf61bbae9 0x1fefeff18fd860c3 0x687fbfbfc63f6183

def z854 : W := mkw 0xdbdc05ec00000000 0x136f7017b0000000 0xfffe7ffe0000001f 0xb3fff9fff8000000

def z855 : W := mkw 0xffddddec49000000 0x13ff7777b1240000 0xfffffffe0fc0001f 0xf7fffffff83f0000

def z856 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01fff8fff7 0xeff807f807ffe3ff

def z857 : W := mkw 0xffd9d9c85f0c7052 0x1bff6767217c31c1 0xfd8181807e1860c1 0x6bf6060601f86183

def z858 : W := mkw 0xdbd800004d0c0000 0x036f600001343000 0xfffe0001ffff002f 0xaffff80007fffc00

def z859 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xffffeffe0000000b 0x73ffffbff8000000

def z860 : W := mkw 0xb601d8004b003000 0x02d80760012c00c0 0xfe01fe01ffc0fc37 0xeff807f807ff03f0

def z861 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01ffc07c07 0x6ff807f807ff01f0

def z862 : W := mkw 0x0404942402003000 0x00101250900800c0 0x1e7ffe7e0e00fc3f 0xfc79fff9f83803f0

def z863 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xe3fffffe0000001a 0x538ffffff8000000

def z864 : W := mkw 0xffd9d9c87f1c7010 0x3bff676721fc71c0 0xfd8181807e186001 0x6bf6060601f86180

def z865 : W := mkw 0x00262637a0f38fad 0x04009898de83ce3e 0x027e7e7f81ff9ffe 0x9409f9f9fe07fe7f

def z866 : W := mkw 0xf3676f75f9f2cabd 0x0fcd9dbdd7e7cb2a 0xe26e6e71f1c00002 0x0389b9b9c7c70000

def z867 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000181e70300 0x0000000006079c0c

def z868 : W := mkw 0x0006062600c30d21 0x0400181898030c34 0x027e7e7e01e79f3e 0x9409f9f9f8079e7c

def z869 : W := mkw 0x9600ba00db40f830 0x0a5802e8036d03e0 0xfe001e01ffc0fc27 0xaff8007807ff03f0

def z870 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfe7e0001ffc70027 0xaff9f80007ff1c00

def z871 : W := mkw 0x08b2221384ef8f29 0x0422c8884e13be3c 0x1d9000018fff9f2d 0xac764000063ffe7c

def z872 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfe7ffffe00000016 0x73f9fffff8000000

def z873 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe1001ffff9c3f 0xaffff84007fffe70

def z874 : W := mkw 0xffddddec5f0c7052 0x1bff7777b17c31c1 0xfffffffe7e1860df 0xfbfffffff9f86183

def z875 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000000279f00 0x0000000000009e7c

def z876 : W := mkw 0xffddddec69100000 0x33ff7777b1a44000 0xfffffffe7000001f 0xf3fffffff9c00000

def z877 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1fff918e0e3fffff 0xfc7ffe463838ffff

def z878 : W := mkw 0x922200016dbe0000 0x2248880005b6f800 0xfe7e0001ffff002f 0xaff9f80007fffc00

def z879 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xffee0001ffff0023 0x2fffb80007fffc00

def z880 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027fffff81e7fffe 0xd409fffffe079fff

def z881 : W := mkw 0x0022221382e3bf29 0x040088884e0b8efc 0x000000018fe7ff20 0x0c000000063f9ffc

def z882 : W := mkw 0xdbda00004d8e0000 0x236f680001363800 0xfffe0001ffc7002f 0xaffff80007ff1c00

def z883 : W := mkw 0x0022221386efbf6b 0x040088884e1bbefd 0x000000018fe79f20 0x04000000063f9e7c

def z884 : W := mkw 0x0cb2b29b86efbf6b 0x0432caca6e1bbefd 0x1d8181818fffffe1 0x6c760606063fffff

def z885 : W := mkw 0x0c9494ac060c3042 0x00325252b01830c1 0x1ffffffe0e1860df 0xf87ffffff8386183

def z886 : W := mkw 0x00222213cbe3bf39 0x0c0088884f2f8efc 0x000000018fe79f20 0x04000000063f9e7c

def z887 : W := mkw 0xffddddec10004084 0x13ff7777b0400102 0xfffffffe000060df 0xf3fffffff8000183

def z888 : W := mkw 0xffddddec49000000 0x13ff7777b1240000 0xfffffffe7e00001f 0xfbfffffff9f80000

def z889 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0000e03f 0xfbfffffff8000380

def z890 : W := mkw 0x9e9c9eae4f4d3d72 0x1a7a727ab93d34f5 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z891 : W := mkw 0xffddddec4b003000 0x13ff7777b12c00c0 0xffffffffffc0fc3f 0xffffffffffff03f0

def z892 : W := mkw 0x00222213cdef8f29 0x240088884f37be3c 0x000000018fe79f20 0x04000000063f9e7c

def z893 : W := mkw 0x92002200db40f830 0x0a480088036d03e0 0xfe007e01ffc0fc37 0xaff801f807ff03f0

def z894 : W := mkw 0x2405febe9241ff7b 0x0c9017fafa4907fd 0x0001fffe0000ffd0 0x500007fff80003ff

def z895 : W := mkw 0xdbfa00116dbe0208 0x236fe80045b6f808 0xfffe0071ffff032f 0xbffff801c7fffc0c

def z896 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe3ffe1f1f038e3ff 0xdb8fff87c7c0e38f

def z897 : W := mkw 0xdbfa01416dbe0000 0x236fe80505b6f800 0xfffe01f1ffff002f 0xbffff807c7fffc00

def z898 : W := mkw 0xb601fb50db40fabc 0x0ad807ed436d03ea 0xff81fff1fff8ffff 0xfffe07ffc7ffe3ff

def z899 : W := mkw 0xffddddec02003000 0x13ff7777b00800c0 0xfffffffe0e38ffff 0xfffffffff838e3ff

def z900 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe100fffff003f 0xbffff8403ffffc00

def z901 : W := mkw 0xb2016200d940c820 0x02c8058803650320 0xfe01fe01ffc0fc37 0xeff807f807ff03f0

def z902 : W := mkw 0x00262637b0f3cfad 0x04009898dec3cf3e 0x027e7e7ff1e79f3e 0x9409f9f9ffc79e7c

def z903 : W := mkw 0x2405fe269241fd31 0x0c9017f89a4907f4 0x0001fe0e0000fc10 0x400007f8380003f0

def z904 : W := mkw 0x6141414030104084 0x0185050500c04102 0xe1e1e1f07038e3fb 0xdb878787c1c0e38f

def z905 : W := mkw 0x0400900202013500 0x00100240080804d4 0x1d91918e0e3ffffd 0xfc7646463838ffff

def z906 : W := mkw 0x0004262680418d20 0x000010989a010634 0x027e7e7f81e79f3e 0x9409f9f9fe079e7c

def z907 : W := mkw 0x61636151b0b2c28c 0x01858d8546c2cb0a 0xe1ffe1f1f03fe3fb 0xdb87ff87c7c0ff8f

def z908 : W := mkw 0x0022221384ef8f29 0x040088884e13be3c 0x000000018fff9f20 0x0c000000063ffe7c

def z909 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01ee01ffc0fc23 0x6ff807b807ff03f0

def z910 : W := mkw 0x61616b51b070cabc 0x098585ad46c1c32a 0xe1e1eff1f038e3fb 0xdb8787bfc7c0e38f

def z911 : W := mkw 0x61616351b070caac 0x0185858d46c1c32a 0xe1e1fff1f038fffb 0xdb8787ffc7c0e3ff

def z912 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e6e7e0000000a 0x1009f9b9f8000000

def z913 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe7e01ffff003f 0xaffff9f807fffc00

def z914 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe27e6e7e0000000a 0x1389f9b9f8000000

def z915 : W := mkw 0x49fe057724bf078d 0x2527f815dc92fc1e 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z916 : W := mkw 0x089c04ac00000000 0x10227012b0000000 0x027e7e7e0000001e 0x9009f9f9f8000000

def z917 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffff000e 0x27fff80007fffc00

def z918 : W := mkw 0xbe9ddcac00000000 0x12fa7772b0000000 0xfe7ffe7e0000001f 0xf3f9fff9f8000000

def z919 : W := mkw 0xfbdd4dec00000000 0x13ef7537b0000000 0xe3ffeffe0000001b 0xd38fffbff8000000

def z920 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1f1f1fff038e3ff 0xdb87c7c7ffc0e38f

def z921 : W := mkw 0x4ddc95ec00000000 0x11377257b0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z922 : W := mkw 0xffd9d9c86f1c3042 0x33ff676721bc70c1 0xfd8181807e1860c1 0x6bf6060601f86183

def z923 : W := mkw 0xbe95dcac00000000 0x02fa5772b0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z924 : W := mkw 0xffddddec5b007010 0x1bff7777b16c01c0 0xfffffffe7e00fc3f 0xfffffffff9f803f0

def z925 : W := mkw 0x0026263790e3cfad 0x04009898de438f3e 0x027e7e7f81e7fffe 0x9409f9f9fe079fff

def z926 : W := mkw 0xffddddec060c3042 0x13ff7777b01830c1 0xfffffffe0e38e3ff 0xfbfffffff838e38f

def z927 : W := mkw 0x616141513030428c 0x0185850544c0c10a 0xe1e1e1f0703863db 0xdb878787c1c0e18f

def z928 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0020833f 0xf3fffffff800820c

def z929 : W := mkw 0x4144056400000000 0x0105101590000000 0x03fe7ffe0000001e 0x900ff9fff8000000

def z930 : W := mkw 0x96009a004b403830 0x0a580268012d00e0 0xfe001e01ffc01c06 0x27f8007807ff0070

def z931 : W := mkw 0x0404942400000000 0x0010125090000000 0x1e7ffe7e0000001f 0xf079fff9f8000000

def z932 : W := mkw 0xffddddec060c3042 0x13ff7777b01830c1 0xfffffffe0e00001f 0xf3fffffff8380000

def z933 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffc7000f 0xa7fff80007ff1c00

def z934 : W := mkw 0xb2054c2400000000 0x02c8153090000000 0xe27e7e7e0000001e 0x9389f9f9f8000000

def z935 : W := mkw 0x0026062700e30d21 0x040098189c038c34 0x027e7e7f81e71c3e 0x9409f9f9fe079c70

def z936 : W := mkw 0xffdddc2400000000 0x03ff777090000000 0xfffffe7e0000001f 0xf3fffff9f8000000

def z937 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000181e79f38 0x9400000006079e7c

def z938 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0027003f 0xf7fffffff8009c00

def z939 : W := mkw 0x4144042400000000 0x0105101090000000 0xe3fe7e7e0000001f 0x938ff9f9f8000000

def z940 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1f91ff8e0e3fffff 0xfc7e47fe3838ffff

def z941 : W := mkw 0x2005456400000000 0x0080151590000000 0x027ffffe0000001e 0xd009fffff8000000

def z942 : W := mkw 0xb605ddec00000000 0x12d81777b0000000 0xfe7ffffe0000001f 0xf3f9fffff8000000

def z943 : W := mkw 0x0004042400000000 0x0000101090000000 0x007e7e7e00000018 0x1001f9f9f8000000

def z944 : W := mkw 0x200161509000c28c 0x008005854240030a 0xe181e1f1f038e3fb 0xdb860787c7c0e38f

def z945 : W := mkw 0xffddddec040c0000 0x13ff7777b0103000 0xfffffffe0e3fe3ff 0xfffffffff838ff8f

def z946 : W := mkw 0x0422b21382e3bf29 0x04108ac84e0b8efc 0x1c0190018fe7ff35 0xec700640063f9ffc

def z947 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe003803df 0xf3fffffff800e00f

def z948 : W := mkw 0xb601fb40db40f8b4 0x0ad807ed036d03e2 0xfe01ff81ffc0fcf7 0xeff807fe07ff03f3

def z949 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x03ffffff81e79f3f 0xd40ffffffe079e7c

def z950 : W := mkw 0x96009a004b403830 0x0a580268012d00e0 0xfe019e01ffc0fc37 0xeff8067807ff03f0

def z951 : W := mkw 0x0026262580e28820 0x0000989896038a20 0x027e7e7f81e79c3e 0x9409f9f9fe079e70

def z952 : W := mkw 0x9ab200014dae0000 0x026ac8000536b800 0xfffe0001ffff002f 0xaffff80007fffc00

def z953 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7e01e79f1c 0x1409f9f9f8079e7c

def z954 : W := mkw 0x614161409000c000 0x0185058502400300 0xe1e1e1f1f038e3fb 0xdb878787c7c0e38f

def z955 : W := mkw 0x2005442400000000 0x0080151090000000 0xe27ffe7e0000001f 0xd389fff9f8000000

def z956 : W := mkw 0xffddddec040c0000 0x13ff7777b0103000 0xfffffffe0e07001f 0xf7fffffff8381c00

def z957 : W := mkw 0xd7609b516b703abc 0x0b5d826d45adc0ea 0x1fe01ff00ff81fcc 0x347f807fc03fe07f

def z958 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffdf0007 0x2ffff80007ff7c00

def z959 : W := mkw 0x920c0c2400000000 0x1248303090000000 0x027e7e7e0000001e 0x9009f9f9f8000000

def z960 : W := mkw 0x0c9494ac00000000 0x00325252b0000000 0x1e7e7e7e0000001e 0xb079f9f9f8000000

def z961 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81e79f26 0x0409f9f9fe079e7c

def z962 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91918e0e3fffdc 0x747646463838ffff

def z963 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1f1f1f038ffff 0xdf8787c7c7c0e3ff

def z964 : W := mkw 0x49fe05ef24bf0542 0x3127f817bc92fc15 0x01fe01fe003f03c8 0x1007f807f800fc0f

def z965 : W := mkw 0xb601fa88db40f830 0x0ad807ea236d03e0 0xfe01ff8fffc0fc37 0xfff807fe3fff03f0

def z966 : W := mkw 0x9202000049820000 0x0248080001260800 0xfe1e0001ffc70027 0xaff8780007ff1c00

def z967 : W := mkw 0xffddddec59004010 0x1bff7777b1640100 0xfffffffe7000001f 0xf3fffffff9c00000

def z968 : W := mkw 0xf745dd6400000000 0x03dd177590000000 0xfffffffe0000001f 0xf3fffffff8000000

def z969 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e7e7e0027003e 0x9409f9f9f8009c00

def z970 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe007e01ffc09c36 0xa7f801f807ff0270

def z971 : W := mkw 0x0006263680c38f29 0x04001898da030e3c 0x027e7e7e01c79f1e 0x9409f9f9f8071e7c

def z972 : W := mkw 0x2405ff769241ffbd 0x0c9017fdda4907fe 0x0001fffe0000ffd0 0x500007fff80003ff

def z973 : W := mkw 0x0004042400000000 0x0000101090000000 0x027e7e7e0020833e 0x9009f9f9f800820c

def z974 : W := mkw 0x0026042700a30500 0x000098109c028c14 0x027e7e7f81e79f3e 0x9409f9f9fe079e7c

def z975 : W := mkw 0xb601fbc8db40f830 0x1ad807ef236d03e0 0xfe01ff81ffc0fc37 0xeff807fe07ff03f0

def z976 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xffffffff81c0003f 0xf7fffffffe070000

def z977 : W := mkw 0xffddddec30104084 0x13ff7777b0c04102 0xfffffffe7038e3ff 0xfbfffffff9c0e38f

def z978 : W := mkw 0x49fe05ff24bf0709 0x3527f817fc92fc1c 0x01fe01fe003f0308 0x1007f807f800fc0c

def z979 : W := mkw 0xdbfa01516dbe028c 0x236fe80545b6f80a 0xffff81f1ffffe3ff 0xfffffe07c7ffff8f

def z980 : W := mkw 0x2405dc2400000000 0x0090177090000000 0x027ffe7e0000001e 0xd009fff9f8000000

def z981 : W := mkw 0xffddddec02003042 0x13ff7777b00800c1 0xfffffffe000060df 0xf3fffffff8000183

def z982 : W := mkw 0x00262637a0f38f29 0x04009898de83ce3c 0x027e7e7ff1ff9f3e 0x9c09f9f9ffc7fe7c

def z983 : W := mkw 0x0004042400000000 0x0000101090000000 0x03fffffe0038e3ff 0xd80ffffff800e38f

def z984 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f1f018e3d3 0x5b878787c7c0638f

def z985 : W := mkw 0x9600b200cb40b820 0x025802c8032d02e0 0xfe01fe01ffc0fc37 0xeff807f807ff03f0

def z986 : W := mkw 0x0004042400000000 0x0000101090000000 0x03fffffe0000001f 0xd00ffffff8000000

def z987 : W := mkw 0xdbfa2213edff8f29 0x276fe8884fb7fe3c 0xfd800001ffff9f21 0x2ff6000007fffe7c

def z988 : W := mkw 0x9200020049400820 0x0248000801250020 0xfe001e01ffc01c27 0xaff8007807ff0070

def z989 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe007e01ffc01c27 0xaff801f807ff0070

def z990 : W := mkw 0xffddddec361c70c6 0x13ff7777b0d871c3 0xfffffffe7e1860df 0xfbfffffff9f86183

def z991 : W := mkw 0xffddddec30104084 0x13ff7777b0c04102 0xfffffffe7000001f 0xf3fffffff9c00000

def z992 : W := mkw 0x49dc05ec00000000 0x11277017b0000000 0x01fe7ffe00000018 0x1007f9fff8000000

def z993 : W := mkw 0xf74dddec00000000 0x13dd3777b0000000 0xe26e7e7e00000002 0x0389b9f9f8000000

def z994 : W := mkw 0xffddddec060c3000 0x13ff7777b01830c0 0xfffffffe0e3ffc3f 0xfffffffff838fff0

def z995 : W := mkw 0x040494ac00000000 0x00101252b0000000 0x027ffffe0000001e 0xd009fffff8000000

def z996 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe3fffffe0000001f 0xd38ffffff8000000

def z997 : W := mkw 0xffddddec4d0c0000 0x33ff7777b1343000 0xfffffffe0e00001f 0xf3fffffff8380000

def z998 : W := mkw 0xf74dddec00000000 0x13dd3777b0000000 0xe27ffffe0000001e 0xd389fffff8000000

def z999 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe11fe0fffc0fc3f 0xfff847f83fff03f0

def z1000 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xfde1e1f1fe38e3ff 0xfff78787c7f8e38f

def z1001 : W := mkw 0x00222213a4ff8f29 0x240088884e93fe3c 0x0000000181ff9f20 0x040000000607fe7c

def z1002 : W := mkw 0x0c90908a060d3542 0x00324242281834d5 0x1d91918e0e3fffe5 0x6c7646463838ffff

def z1003 : W := mkw 0xdbdc04246d1c0000 0x236f701091b47000 0xfffe7e7e7e18001f 0xbbfff9f9f9f86000

def z1004 : W := mkw 0xffddddec02003000 0x13ff7777b00800c0 0xfffffffe0e001c1f 0xf7fffffff8380070

def z1005 : W := mkw 0x6dddddec00000000 0x11b77777b0000000 0x03fffffe0000001e 0xd00ffffff8000000

def z1006 : W := mkw 0x9e9e96ae4fcf3d63 0x267a7a5ab93f3cf5 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z1007 : W := mkw 0x61416150b010c28c 0x0185058542c0430a 0xe181e1f1f018e3f3 0xdb860787c7c0638f

def z1008 : W := mkw 0xffddddec12007010 0x1bff7777b04801c0 0xfffffffe0000601f 0xf3fffffff8000180

def z1009 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81fffffe 0x9c09f9f9fe07ffff

def z1010 : W := mkw 0xdbfa00896dbe0000 0x236fe80225b6f800 0xfffe018fffff002f 0xbffff8063ffffc00

def z1011 : W := mkw 0x00262637b0f3cfad 0x04009898dec3cf3e 0x03fffffff1ffffff 0xdc0fffffffc7ffff

def z1012 : W := mkw 0x00222213a0f38fad 0x040088884e83ce3e 0x0000000181ff9fe0 0x040000000607fe7f

def z1013 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfdfe0001ffff0029 0x2ff7f80007fffc00

def z1014 : W := mkw 0x61636151b0b2c28c 0x01858d8546c2cb0a 0xe3efe1f1f1f8e3fb 0xdb8fbf87c7c7e38f

def z1015 : W := mkw 0x69dd45ec00000000 0x11a77517b0000000 0xe3fffffe0000001f 0xd38ffffff8000000

def z1016 : W := mkw 0xffddddec20100000 0x13ff7777b0804000 0xfffffffe7018001f 0xfbfffffff9c06000

def z1017 : W := mkw 0xb605dc245b007010 0x0ad81770916c01c0 0xfe7ffe7e7e00601f 0xfbf9fff9f9f80180

def z1018 : W := mkw 0x00222213efffbf6b 0x240088884fbffefd 0x00000001ffffffe0 0x0c00000007ffffff

def z1019 : W := mkw 0x6161414120300000 0x018585050480c000 0xe1e1e1f1f038e3fb 0xdb878787c7c0e38f

def z1020 : W := mkw 0x6545ddec00000000 0x11951777b0000000 0xe3fffffe0000001f 0xd38ffffff8000000

def z1021 : W := mkw 0x00222213e9f38f29 0x240088884fa7ce3c 0x00000001f1e79f20 0x0400000007c79e7c

def z1022 : W := mkw 0xffddddec241c0000 0x33ff7777b0907000 0xfffffffe0018001f 0xf3fffffff8006000

def z1023 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000181ffffe0 0x0c0000000607ffff

def z1024 : W := mkw 0xd34c042400000000 0x034d301090000000 0xe27e7e7e0000001e 0x9389f9f9f8000000

def z1025 : W := mkw 0x00222213c9e38f29 0x040088884f278e3c 0x00000001ffe79f20 0x0c00000007ff9e7c

def z1026 : W := mkw 0xb601fa10db40fa38 0x0ad807e8436d03e8 0xfe01fe71ffc0ff37 0xfff807f9c7ff03fc

def z1027 : W := mkw 0x08900002040d0500 0x0022400008103414 0x1d91918e0e3ffffd 0xfc7646463838ffff

def z1028 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0038003f 0xfbfffffff800e000

def z1029 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffff000003f 0xfbffffffffc00000

def z1030 : W := mkw 0xf74ddd6400000000 0x13dd377590000000 0xfe7ffe7e0000001f 0xf3f9fff9f8000000

def z1031 : W := mkw 0xffddddec02003000 0x13ff7777b00800c0 0xfffffffe0e00601f 0xfbfffffff8380180

def z1032 : W := mkw 0x2405ffee9241fd72 0x189017ffba4907f5 0x0001fffe0000ffd0 0x500007fff80003ff

def z1033 : W := mkw 0x0022221382e3bf6b 0x040088884e0b8efd 0x0000000181e7ffe0 0x0400000006079fff

def z1034 : W := mkw 0x61616351b070caac 0x0185858d46c1c32a 0xe3e1eff1f1f8e3fb 0xdb8f87bfc7c7e38f

def z1035 : W := mkw 0x616141513030428c 0x0185850544c0c10a 0xe1e181f1f03863eb 0xdb878607c7c0e18f

def z1036 : W := mkw 0x0004042400000000 0x0000101090000000 0x026e7e7e00000012 0x1009b9f9f8000000

def z1037 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xffff8181ffff003f 0xfffffe0607fffc00

def z1038 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0e00003f 0xfffffffff8380000

def z1039 : W := mkw 0x416001512030028c 0x010580054480c00a 0xe1e181f1f038e3fb 0xdb878607c7c0e38f

def z1040 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0010000181e79f2c 0x8400400006079e7c

def z1041 : W := mkw 0x9a9c042400000000 0x026a701090000000 0x1e7e7e7e0000001e 0xb079f9f9f8000000

def z1042 : W := mkw 0xffddddec5b007010 0x1bff7777b16c01c0 0xffffffffffc0603f 0xffffffffffff0180

def z1043 : W := mkw 0x9e9c9cac00000000 0x127a7272b0000000 0x1e7e7e7e00000006 0x2079f9f9f8000000

def z1044 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffe7e7e0000000f 0xa3fff9f9f8000000

def z1045 : W := mkw 0x9e9e9cae4f8f3542 0x327a7a72b93e3cd5 0x1e1e1e0e0fc71c04 0x24787878383f1c70

def z1046 : W := mkw 0xffddddec20100084 0x13ff7777b0804002 0xfffffffe001800df 0xf3fffffff8006003

def z1047 : W := mkw 0xbe9dddec00000000 0x12fa7777b0000000 0x1e7ffffe0000001e 0xf079fffff8000000

def z1048 : W := mkw 0x96049c2400000000 0x0258127090000000 0x1e7e7e7e0000001e 0xb079f9f9f8000000

def z1049 : W := mkw 0x00222213b6ffffef 0x040088884edbffff 0x00000001ffffffe0 0x0c00000007ffffff

def z1050 : W := mkw 0x49dc05ec00000000 0x11277017b0000000 0x03fe6ffe0000000a 0x100ff9bff8000000

def z1051 : W := mkw 0x00222213ffffff39 0x2c0088884ffffffc 0x00000001ffffff20 0x0c00000007fffffc

def z1052 : W := mkw 0xffddddec040c0000 0x13ff7777b0103000 0xfffffffe003f001f 0xf3fffffff800fc00

def z1053 : W := mkw 0x2401f2009240f820 0x009007c8024903e0 0xfe01fe01ffc0fc37 0xeff807f807ff03f0

def z1054 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027e7e7f81c71c1e 0x9409f9f9fe071c70

def z1055 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0181818181fffff9 0xdc0606060607ffff

def z1056 : W := mkw 0x00222213b0f3cfad 0x040088884ec3cf3e 0x00000001f1e79f20 0x0400000007c79e7c

def z1057 : W := mkw 0x0026263790e3cf29 0x04009898de438f3c 0x027e7e7ff1e7ff3e 0x9c09f9f9ffc79ffc

def z1058 : W := mkw 0x2405fffe9241ff39 0x1c9017fffa4907fc 0x0001fffe0000ff10 0x500007fff80003fc

def z1059 : W := mkw 0x92222213c9e38f29 0x064888884f278e3c 0xfe000001ffe79f27 0xaff8000007ff9e7c

def z1060 : W := mkw 0x9204042400000000 0x0248101090000000 0xfe7e7e7e0000001f 0xb3f9f9f9f8000000

def z1061 : W := mkw 0xd362000169b20000 0x034d880005a6c800 0xfffe0001ffff002f 0xaffff80007fffc00

def z1062 : W := mkw 0x00222213fbf3ffbd 0x0c0088884fefcffe 0x00000001ffffffe0 0x0c00000007ffffff

def z1063 : W := mkw 0x9a9a00004d8e0000 0x226a680001363800 0xff9e0001ffff002f 0xaffe780007fffc00

def z1064 : W := mkw 0x00222213fdffcfad 0x240088884ff7ff3e 0x00000001ffffffe0 0x0c00000007ffffff

def z1065 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xfe01fe01ffc01c17 0xe7f807f807ff0070

def z1066 : W := mkw 0xdbfa01516dbe028c 0x236fe80545b6f80a 0xfffe0071ffff002f 0xaffff801c7fffc00

def z1067 : W := mkw 0xffddddec7d1c4084 0x33ff7777b1f47102 0xfffffffe7e1860df 0xfbfffffff9f86183

def z1068 : W := mkw 0x0022221392e3ff39 0x0c0088884e4b8ffc 0x0000000181e7ff20 0x0400000006079ffc

def z1069 : W := mkw 0xf34d4d6400000000 0x13cd353590000000 0xe27e7e7e00000006 0x0389f9f9f8000000

def z1070 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x027ffe7f81e7ff3f 0xdc09fff9fe079ffc

def z1071 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xfffe0001ffff833f 0xbffff80007fffe0c

def z1072 : W := mkw 0x08940424040c0000 0x0022501090103000 0x1ffe7e7e0e3f003f 0xbc7ff9f9f838fc00

def z1073 : W := mkw 0x0022221390e3cfad 0x040088884e438f3e 0x0000000181e7ffe0 0x0400000006079fff

def z1074 : W := mkw 0xffddddec4d0c0000 0x13ff7777b1343000 0xffffffffffff003f 0xfffffffffffffc00

def z1075 : W := mkw 0xfbdd4dec00000000 0x13ef7537b0000000 0xe27e6e7e00000002 0x0389f9b9f8000000

def z1076 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1f1e1f1f03fe3ff 0xdf87c787c7c0ff8f

def z1077 : W := mkw 0x616b6151b0b2c28c 0x2185ad8546c2cb0a 0xe1efe1f1f038e3fb 0xdb87bf87c7c0e38f

def z1078 : W := mkw 0x0026263780e38f29 0x04009898de038e3c 0x03fe7e7f81ff9f3f 0x9c0ff9f9fe07fe7c

def z1079 : W := mkw 0xdbfa00016dbe0000 0x236fe80005b6f800 0xffff8181ffff60ef 0xeffffe0607fffd83

def z1080 : W := mkw 0x6dddddec00000000 0x11b77777b0000000 0xe1fffffe0000001b 0xd387fffff8000000

def z1081 : W := mkw 0x2405f7fe9241ffef 0x049017dffa4907ff 0x0001fffe0000ffd0 0x500007fff80003ff

def z1082 : W := mkw 0xdbfa000149a20000 0x036fe80005268800 0xfffe0001ffe7002f 0xaffff80007ff9c00

def z1083 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffe7ffe0000000e 0x33fff9fff8000000

def z1084 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe0000e3df 0xf3fffffff800038f

def z1085 : W := mkw 0x69dd4dec00000000 0x11a77537b0000000 0x01fe6ffe00000008 0x1007f9bff8000000

def z1086 : W := mkw 0xdbda00006d9e0000 0x236f680001b67800 0xff9e0001ffdf0027 0xaffe780007ff7c00

def z1087 : W := mkw 0x6145456430104084 0x0185151590c04102 0xe3fffffe701860df 0xdb8ffffff9c06183

def z1088 : W := mkw 0x0022221380e38f29 0x040088884e038e3c 0x0000000181c09f00 0x000000000607027c

def z1089 : W := mkw 0x6dd5d5ec00000000 0x01b75757b0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z1090 : W := mkw 0x00222213dfefff7b 0x0c0088884f7fbffd 0x00000001ffffffe0 0x0c00000007ffffff

def z1091 : W := mkw 0xffddddec00000000 0x13ff7777b0000000 0xfffffffe00000007 0x63fffffff8000000

def z1092 : W := mkw 0x61616151b030c28c 0x0185858546c0c30a 0xe1e1e1f07038e3d9 0x5b878787c1c0e38f

def z1093 : W := mkw 0xb601fa00c9408820 0x02d807e803250220 0xfe01fe01ffc09c37 0xeff807f807ff0270

def z1094 : W := mkw 0x61616351b070caac 0x0185858d46c1c32a 0xe1e1e1f1f1f8fffb 0xdf878787c7c7e3ff

def z1095 : W := mkw 0xf34d4dec00000000 0x13cd3537b0000000 0xe26e6ffe00000002 0x1389b9bff8000000

def z1096 : W := mkw 0xffddddec6d1c0000 0x33ff7777b1b47000 0xfffffffe7e3f003f 0xfffffffff9f8fc00

def z1097 : W := mkw 0xb601fa00db40f830 0x0ad807e8036d03e0 0xff81ff81ffd8fcf7 0xeffe07fe07ff63f3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z6])],[(0,[z9,z0,z1,z3,z4,z5,z6]),(0,[z0,z10,z1,z3,z4,z5,z6])],[(0,[z11,z0,z12,z1,z3,z4,z5]),(0,[z13,z0,z1,z3,z4,z5,z6]),(0,[z0,z12,z14,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z15]),(0,[z0,z1,z16,z3,z17,z5,z6])],[(1,[z0,z1,z18,z4,z5,z6]),(0,[z19,z0,z1,z16,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z20,z6])],[(0,[z0,z1,z21,z3,z4,z5,z22])],[(0,[z19,z0,z1,z3,z4,z23,z5]),(0,[z0,z1,z3,z24,z4,z23,z6]),(1,[z0,z1,z3,z25,z5,z6]),(0,[z19,z0,z1,z26,z3,z4,z5]),(0,[z0,z1,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z28]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z30,z3,z4,z5,z6])],[(0,[z0,z1,z31,z3,z4,z5,z6]),(0,[z19,z1,z3,z32,z4,z5,z6]),(0,[z0,z1,z33,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z34,z5]),(0,[z0,z1,z3,z35,z4,z5,z6])],[(0,[z36,z9,z1,z3,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z38,z6]),(0,[z0,z39,z1,z3,z4,z5,z6])]],
   [[(0,[z11,z0,z0,z1,z3,z4,z5]),(1,[z40,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z42]),(1,[z0,z1,z3,z43,z6,z44]),(0,[z0,z1,z3,z4,z5,z6,z45]),(0,[z0,z46,z1,z3,z4,z5,z6]),(0,[z47,z0,z1,z3,z4,z5,z6])],[(0,[z48,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z49,z6]),(0,[z50,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z51,z6]),(0,[z19,z0,z52,z1,z3,z4,z5]),(0,[z53,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z54,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z55,z6]),(1,[z0,z1,z56,z4,z57,z6])],[(0,[z19,z0,z1,z3,z4,z5,z44]),(0,[z0,z1,z3,z4,z5,z58,z6])],[(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z60,z4,z5,z6]),(0,[z0,z1,z61,z3,z4,z38,z6])],[(0,[z0,z62,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z63,z4,z5,z6]),(0,[z0,z1,z3,z64,z4,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z66,z6]),(0,[z0,z1,z67,z3,z4,z5,z6])],[(0,[z68,z0,z1,z3,z43,z4,z6]),(1,[z0,z1,z3,z4,z5,z69]),(0,[z70,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z71,z3,z4,z5,z6])],[(0,[z72,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z73,z3,z4,z5,z6]),(1,[z0,z1,z74,z4,z5,z6]),(0,[z75,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z76,z0,z1,z3,z4,z5,z6]),(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z78,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z79]),(0,[z19,z0,z80,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z81,z6]),(0,[z0,z1,z26,z3,z4,z57,z6]),(0,[z0,z1,z21,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z11,z0,z1,z56,z3,z4,z5]),(0,[z11,z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z83,z4,z5,z6]),(0,[z0,z1,z84,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z85,z5,z6])],[(0,[z0,z1,z86,z3,z4,z5,z6]),(1,[z87,z1,z3,z23,z5,z6]),(0,[z0,z1,z88,z3,z4,z5,z6]),(0,[z89,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z90,z5,z6]),(0,[z0,z91,z3,z4,z5,z6,z22]),(0,[z0,z1,z92,z3,z4,z5,z6]),(0,[z0,z1,z3,z93,z4,z5,z6]),(0,[z0,z1,z3,z4,z94,z5,z6]),(0,[z0,z1,z3,z95,z4,z5,z6])],[(0,[z11,z0,z1,z96,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z97,z6])],[(0,[z0,z1,z3,z4,z98,z5,z6]),(0,[z99,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z100,z3,z4,z5,z6]),(0,[z101,z19,z0,z1,z3,z4,z5]),(0,[z19,z0,z1,z3,z43,z4,z5]),(0,[z0,z102,z1,z3,z4,z5,z6]),(0,[z103,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z34,z5,z6]),(0,[z0,z1,z3,z104,z4,z5,z6])],[(0,[z0,z1,z3,z4,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z106,z6]),(0,[z107,z0,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z61,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z108,z6]),(0,[z0,z1,z3,z4,z5,z6,z109])],[(0,[z19,z0,z1,z21,z3,z4,z5]),(0,[z110,z0,z1,z3,z4,z111,z6]),(0,[z0,z1,z3,z4,z5,z112,z6]),(0,[z0,z1,z3,z4,z113,z5,z6])]],
   [[(0,[z0,z114,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z115,z4,z5,z6]),(0,[z0,z1,z116,z3,z4,z5,z6]),(0,[z0,z1,z3,z117,z4,z5,z118]),(1,[z0,z1,z3,z119,z4,z6])],[(0,[z36,z0,z1,z120,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z5,z121]),(0,[z11,z0,z1,z3,z4,z122,z5]),(0,[z0,z1,z3,z4,z122,z5,z6]),(0,[z0,z123,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z124,z6])],[(0,[z125,z0,z1,z32,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z126,z5]),(0,[z11,z0,z1,z3,z117,z4,z5]),(0,[z0,z1,z3,z4,z127,z5,z6]),(0,[z0,z1,z26,z3,z43,z5,z6])],[(0,[z128,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z5,z6]),(0,[z0,z80,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z130,z4,z5,z6]),(0,[z131,z0,z1,z117,z4,z5,z6])],[(0,[z132,z11,z0,z1,z3,z4,z5]),(0,[z0,z133,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z134,z3,z4,z5]),(0,[z11,z11,z0,z1,z3,z4,z5]),(0,[z0,z52,z1,z3,z4,z135,z6]),(0,[z0,z136,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z43,z137,z5,z6])],[(0,[z0,z1,z3,z4,z138,z5,z6]),(1,[z36,z1,z120,z4,z5,z6]),(0,[z0,z1,z3,z4,z139,z5,z6]),(0,[z0,z140,z141,z3,z4,z5,z6]),(0,[z0,z1,z3,z142,z4,z5,z6])],[(0,[z0,z1,z143,z3,z115,z4,z5]),(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z35,z4,z144,z5,z6]),(0,[z0,z1,z145,z3,z4,z5,z6]),(1,[z131,z0,z1,z117,z4,z5])],[(0,[z146,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z147,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z61,z32,z4,z5,z6]),(1,[z0,z1,z148,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z149]),(0,[z0,z1,z150,z3,z4,z5,z6]),(0,[z0,z1,z151,z3,z4,z5,z6])],[(0,[z152,z1,z153,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6]),(0,[z155,z0,z1,z3,z4,z5,z6]),(0,[z156,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z6])],[(0,[z158,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z159]),(0,[z0,z1,z61,z120,z4,z5,z6]),(0,[z0,z1,z160,z3,z4,z5,z6]),(0,[z0,z1,z3,z35,z5,z112,z6]),(0,[z0,z1,z161,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z162,z6]),(0,[z103,z0,z1,z3,z163,z5,z6])],[(0,[z164,z0,z1,z3,z4,z23,z5]),(0,[z19,z0,z140,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z165]),(0,[z0,z3,z4,z126,z5,z135,z6]),(0,[z0,z1,z166,z3,z4,z5,z6])],[(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z168,z19,z0,z1,z3,z4,z5]),(0,[z11,z0,z1,z16,z3,z4,z5]),(0,[z0,z1,z3,z169,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z170,z6]),(0,[z0,z1,z3,z4,z5,z171,z6])],[(0,[z11,z0,z1,z3,z4,z23,z5]),(0,[z172,z0,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z26,z3,z4,z5])],[(0,[z36,z0,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z34,z5]),(0,[z0,z173,z1,z3,z4,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z22]),(0,[z176,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z87,z1,z3,z4,z23,z5,z6]),(0,[z19,z0,z91,z1,z3,z4,z5]),(0,[z0,z177,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z178,z5,z6])],[(0,[z131,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z144,z5,z112,z6]),(0,[z0,z1,z179,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z180,z6]),(0,[z0,z1,z181,z3,z4,z5,z118]),(0,[z0,z1,z3,z43,z4,z5,z6]),(0,[z182,z0,z1,z3,z4,z5,z6])],[(0,[z11,z0,z52,z1,z3,z4,z5]),(0,[z0,z1,z56,z4,z5,z57,z6]),(0,[z0,z1,z183,z3,z4,z5,z6])],[(0,[z0,z1,z184,z3,z4,z5,z6]),(0,[z0,z185,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z6]),(0,[z0,z1,z187,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z188,z5,z189]),(0,[z59,z11,z0,z1,z3,z4,z5]),(0,[z11,z0,z1,z3,z4,z5,z44]),(0,[z190,z0,z1,z3,z4,z5,z6]),(0,[z0,z14,z1,z3,z4,z5,z6]),(0,[z0,z191,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z192,z5,z6])],[(0,[z0,z1,z193,z3,z4,z5,z6]),(1,[z194,z0,z1,z3,z4,z5]),(0,[z11,z0,z1,z3,z83,z4,z5]),(0,[z110,z0,z140,z3,z4,z5,z6]),(0,[z0,z195,z1,z3,z4,z5,z6])],[(0,[z0,z196,z1,z3,z4,z5,z6])],[(0,[z0,z1,z16,z32,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z197,z5]),(0,[z0,z1,z3,z4,z5,z198,z6]),(1,[z0,z199,z3,z4,z135,z6]),(0,[z200,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z201,z4,z5,z6]),(0,[z0,z1,z3,z202,z4,z5,z6]),(0,[z0,z1,z203,z3,z4,z5,z6]),(0,[z0,z1,z204,z3,z4,z5,z6])],[(0,[z0,z1,z205,z3,z4,z5,z6]),(0,[z0,z1,z61,z3,z119,z4,z6])]],
   [[(0,[z9,z0,z153,z3,z4,z5,z6]),(0,[z76,z11,z0,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z111,z6]),(0,[z0,z1,z3,z4,z5,z206,z6]),(0,[z0,z1,z3,z4,z5,z207,z6])],[(0,[z208,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z209,z6]),(0,[z0,z1,z3,z4,z5,z6,z210])],[(0,[z0,z1,z3,z4,z211,z5,z6]),(0,[z19,z11,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z212,z6]),(0,[z0,z1,z213,z3,z4,z5,z6]),(0,[z0,z214,z1,z3,z4,z5,z6]),(0,[z0,z1,z96,z4,z5,z6,z215]),(0,[z0,z1,z3,z216,z4,z5,z6])],[(0,[z87,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z217]),(0,[z0,z1,z3,z218,z4,z5,z6]),(0,[z0,z1,z219,z3,z4,z5,z6]),(0,[z131,z220,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z221,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z198]),(0,[z0,z1,z222,z3,z4,z5,z6])],[(0,[z0,z223,z1,z3,z4,z5,z6]),(0,[z0,z1,z224,z3,z43,z4,z6]),(0,[z0,z225,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z226,z3,z4,z5,z6]),(0,[z0,z227,z1,z3,z4,z5,z6]),(0,[z0,z1,z187,z3,z5,z228,z6]),(0,[z11,z0,z1,z3,z43,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z229]),(0,[z0,z1,z3,z4,z5,z6,z230]),(0,[z0,z1,z3,z4,z5,z231,z6])],[(0,[z19,z0,z199,z1,z3,z4,z5]),(0,[z11,z0,z1,z61,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z232]),(1,[z0,z1,z3,z4,z38,z6]),(0,[z0,z1,z3,z233,z4,z5,z6])]],
   [[(0,[z36,z1,z153,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z78,z5]),(0,[z0,z234,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z21,z3,z4,z5])],[(0,[z0,z1,z235,z3,z4,z5,z6]),(0,[z110,z0,z1,z141,z4,z5,z6]),(0,[z0,z1,z224,z3,z137,z5,z6])],[(0,[z236,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z237,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z121])],[(0,[z0,z1,z3,z4,z5,z238,z6]),(0,[z11,z0,z1,z3,z4,z126,z5]),(1,[z0,z140,z141,z4,z5,z6]),(0,[z0,z239,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z43,z4,z5,z240])],[(0,[z241,z0,z1,z3,z4,z5,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z135,z57,z6]),(1,[z0,z91,z3,z4,z5,z22]),(0,[z0,z243,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z244,z4,z5,z6]),(0,[z87,z0,z1,z3,z23,z5,z6]),(0,[z68,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z245,z6]),(0,[z0,z1,z246,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z247]),(0,[z8,z0,z1,z3,z4,z5,z121])],[(0,[z0,z1,z248,z3,z4,z5,z6])]],
   [[(1,[z0,z1,z96,z4,z5,z215])],[(0,[z0,z1,z3,z4,z249,z5,z6]),(0,[z250,z0,z1,z3,z4,z5,z6])],[(0,[z251,z0,z1,z3,z4,z5,z6]),(0,[z0,z12,z1,z3,z35,z5,z6])],[(0,[z0,z252,z1,z3,z4,z5,z6]),(0,[z0,z1,z253,z3,z4,z5,z6]),(1,[z103,z0,z1,z21,z3,z5])],[(0,[z254,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z255,z4,z5,z6]),(0,[z167,z11,z0,z1,z3,z4,z5]),(0,[z11,z0,z140,z1,z3,z4,z5]),(0,[z0,z52,z199,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z135,z6])],[(0,[z0,z1,z256,z3,z4,z5,z6]),(1,[z0,z1,z143,z3,z4,z5]),(0,[z68,z0,z1,z3,z4,z188,z6]),(0,[z0,z1,z134,z3,z4,z5,z6]),(0,[z0,z1,z257,z3,z4,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z0,z1,z3,z43,z5,z112,z6])],[(0,[z19,z0,z1,z3,z32,z4,z5]),(0,[z87,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z259]),(0,[z0,z1,z260,z3,z4,z5,z6]),(0,[z0,z1,z224,z3,z4,z5,z6]),(0,[z0,z1,z261,z3,z4,z5,z6]),(0,[z0,z1,z3,z163,z4,z5,z6]),(0,[z8,z0,z1,z181,z3,z4,z6]),(0,[z0,z262,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z263]),(0,[z0,z1,z3,z4,z5,z264,z6]),(0,[z0,z52,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z118,z6,z22])]],
   [[(0,[z87,z37,z1,z3,z4,z5,z6]),(0,[z11,z1,z3,z4,z5,z265,z6]),(0,[z266,z0,z1,z3,z4,z5,z6]),(0,[z267,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z268,z4,z5,z6])],[(0,[z269,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z270,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z228,z6]),(0,[z11,z0,z91,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z271,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z272]),(0,[z37,z0,z1,z3,z43,z5,z6]),(0,[z19,z0,z1,z3,z4,z5,z215]),(0,[z0,z1,z3,z4,z126,z5,z6]),(0,[z0,z1,z3,z273,z4,z5,z6]),(0,[z0,z1,z3,z4,z34,z6,z121]),(0,[z0,z274,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z275,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z276,z6]),(0,[z0,z140,z1,z141,z4,z5,z6])],[(0,[z0,z277,z1,z3,z4,z5,z6]),(0,[z0,z1,z278,z3,z4,z5,z6]),(0,[z279,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z32,z4,z5,z57,z6]),(0,[z0,z1,z280,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z188,z5]),(0,[z0,z14,z1,z3,z35,z5,z6]),(0,[z0,z1,z281,z3,z4,z5,z6]),(0,[z0,z1,z96,z3,z117,z4,z5])],[(0,[z282,z0,z1,z3,z4,z5,z6]),(0,[z194,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z283,z4,z5,z6]),(0,[z0,z284,z1,z3,z4,z5,z6])],[(0,[z9,z0,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z43,z4,z6,z44])]],
   [[(0,[z0,z1,z3,z285,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z286,z6]),(0,[z19,z0,z1,z3,z4,z5,z264]),(0,[z0,z1,z3,z137,z4,z5,z6]),(0,[z0,z1,z3,z4,z287,z5,z6]),(0,[z0,z1,z3,z4,z5,z288,z6]),(0,[z0,z1,z3,z4,z5,z289,z121])],[(0,[z19,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z290,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z291,z6]),(1,[z19,z36,z1,z3,z4,z5]),(0,[z19,z0,z1,z3,z4,z5,z289]),(0,[z0,z140,z1,z83,z4,z5,z6]),(0,[z0,z292,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z5,z6])],[(0,[z0,z1,z3,z4,z294,z5,z6]),(0,[z0,z1,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z296]),(0,[z0,z1,z297,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z298,z6]),(0,[z0,z1,z299,z3,z4,z5,z6]),(0,[z0,z1,z56,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z34,z5,z121])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z300,z4,z5]),(0,[z1,z3,z4,z5,z265,z6,z149]),(0,[z175,z11,z0,z1,z3,z4,z5]),(0,[z0,z301,z1,z3,z4,z5,z6]),(0,[z0,z1,z302,z3,z137,z5,z6]),(0,[z0,z1,z303,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z304,z5,z6]),(0,[z0,z140,z1,z3,z4,z5,z6]),(0,[z110,z0,z1,z3,z4,z245,z6]),(0,[z0,z305,z1,z3,z4,z5,z6])],[(0,[z87,z0,z1,z3,z43,z5,z6]),(0,[z0,z1,z3,z306,z4,z5,z6]),(0,[z0,z1,z307,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z308]),(0,[z0,z1,z3,z4,z5,z22,z289]),(0,[z0,z1,z309,z3,z4,z5,z6])],[(0,[z0,z310,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z43,z300,z4,z6]),(0,[z311,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z226,z3,z4,z23,z6]),(0,[z11,z0,z199,z1,z3,z4,z5])],[(0,[z19,z0,z1,z3,z163,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z22]),(0,[z0,z312,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z313]),(0,[z0,z1,z3,z4,z5,z314,z6]),(0,[z0,z1,z315,z3,z4,z5,z6]),(0,[z0,z1,z3,z316,z4,z5,z6])],[(0,[z0,z1,z3,z317,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z159]),(0,[z318,z0,z1,z3,z4,z5,z6]),(0,[z319,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z320,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z321,z6]),(0,[z322,z0,z1,z3,z4,z5,z6])],[(0,[z0,z199,z1,z3,z4,z5,z15]),(0,[z0,z1,z3,z117,z4,z5,z22]),(0,[z0,z1,z3,z323,z4,z5,z6])],[(0,[z1,z120,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z17,z4,z5,z6])],[(0,[z125,z0,z1,z120,z4,z5,z6]),(0,[z0,z1,z3,z324,z4,z5,z6]),(0,[z19,z37,z0,z1,z3,z4,z5]),(0,[z19,z0,z14,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z325,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z326]),(0,[z0,z1,z3,z4,z5,z327,z6])]],
   [[(0,[z0,z1,z3,z4,z328,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z308]),(0,[z0,z1,z3,z329,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z22,z121]),(0,[z0,z1,z3,z4,z5,z330,z6])],[(0,[z0,z1,z331,z3,z4,z5,z6]),(0,[z0,z332,z1,z3,z4,z5,z6]),(0,[z0,z1,z302,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z333,z5,z6])],[(0,[z132,z1,z3,z4,z188,z5,z6]),(0,[z110,z0,z3,z83,z4,z5,z6]),(1,[z0,z52,z3,z4,z126,z6]),(0,[z0,z1,z224,z3,z5,z112,z6])],[(0,[z8,z11,z0,z1,z3,z4,z5]),(0,[z334,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z335]),(0,[z336,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z337])],[(0,[z0,z1,z153,z3,z4,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z19,z131,z0,z1,z3,z4,z5]),(0,[z0,z1,z339,z3,z4,z5,z6]),(1,[z110,z0,z83,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z340,z6]),(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z61,z3,z137,z5,z6]),(0,[z0,z1,z342,z3,z4,z5,z6]),(0,[z0,z1,z343,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z344,z6])],[(0,[z11,z0,z1,z3,z32,z4,z5]),(0,[z175,z19,z0,z1,z3,z4,z5]),(0,[z345,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z36,z1,z120,z3,z4,z5,z6]),(0,[z346,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z347,z3,z4,z5,z6]),(0,[z132,z68,z1,z3,z4,z5,z6]),(0,[z0,z348,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z349,z4,z5,z6])],[(0,[z0,z350,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z351,z5,z6])],[(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z353,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z215]),(0,[z0,z1,z3,z4,z354,z5,z6]),(0,[z0,z1,z355,z3,z4,z5,z6])],[(1,[z48,z153,z3,z4,z5,z6]),(0,[z0,z1,z356,z3,z4,z5,z6]),(0,[z0,z1,z120,z4,z5,z57,z6]),(0,[z19,z0,z1,z3,z357,z4,z5]),(0,[z19,z0,z1,z181,z3,z4,z5]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z359,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z360,z5,z6]),(0,[z0,z1,z3,z361,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z362,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z300,z4,z5,z6]),(1,[z0,z1,z3,z290,z4,z5])],[(0,[z11,z0,z1,z3,z4,z188,z5]),(0,[z363,z19,z0,z1,z3,z4,z5]),(1,[z0,z1,z3,z4,z245,z6]),(0,[z0,z1,z3,z4,z5,z6,z364]),(0,[z365,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z366,z3,z4,z5,z6]),(0,[z0,z1,z181,z3,z4,z5,z22]),(0,[z367,z0,z1,z3,z4,z5,z6])],[(0,[z368,z0,z1,z3,z4,z5,z6]),(0,[z9,z1,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z5,z369,z6]),(0,[z0,z1,z117,z4,z5,z6,z215])]],
   [[(0,[z19,z0,z1,z120,z3,z4,z5])],[(1,[z0,z1,z187,z3,z5,z6]),(0,[z0,z1,z3,z370,z4,z5,z6]),(0,[z371,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z372,z5,z6]),(0,[z0,z1,z3,z137,z35,z5,z6]),(0,[z0,z1,z96,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z373,z5,z6])],[(0,[z48,z9,z1,z3,z4,z5,z6]),(0,[z36,z1,z3,z4,z5,z265,z6]),(0,[z0,z1,z374,z3,z4,z5,z6]),(0,[z0,z1,z16,z120,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z289]),(0,[z0,z1,z3,z4,z375,z5,z6]),(0,[z0,z1,z61,z3,z4,z5,z6])],[(0,[z376,z0,z1,z3,z4,z5,z6]),(0,[z377,z0,z1,z3,z4,z5,z6]),(1,[z19,z1,z3,z32,z4,z5]),(0,[z19,z0,z1,z3,z115,z4,z5])],[(0,[z0,z1,z3,z4,z5,z6,z378]),(0,[z37,z0,z1,z3,z23,z5,z6]),(0,[z0,z1,z3,z4,z379,z5,z6]),(0,[z11,z0,z1,z3,z300,z4,z5]),(0,[z0,z1,z3,z4,z5,z118,z289]),(0,[z0,z380,z1,z3,z4,z5,z6])],[(0,[z381,z0,z1,z3,z4,z5,z6]),(0,[z0,z382,z1,z3,z4,z5,z6]),(0,[z0,z1,z383,z3,z4,z5,z6])],[(0,[z87,z0,z1,z18,z4,z5,z6]),(0,[z384,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z385,z5,z6]),(0,[z0,z386,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z387,z4,z5,z6]),(0,[z0,z1,z32,z4,z5,z112,z6]),(0,[z0,z1,z3,z4,z5,z388,z6]),(0,[z103,z11,z0,z1,z3,z4,z5]),(0,[z131,z0,z1,z3,z4,z5,z215])],[(0,[z0,z1,z3,z18,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z240])],[(0,[z0,z1,z3,z4,z5,z6,z389]),(0,[z0,z1,z390,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z163,z4,z5]),(0,[z391,z0,z1,z3,z4,z5,z6])],[(0,[z110,z0,z1,z3,z392,z5,z6]),(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z394,z4,z5,z6]),(0,[z0,z1,z181,z3,z4,z5,z6])],[(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z269,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z397]),(0,[z0,z1,z3,z4,z5,z398,z6]),(0,[z399,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z400,z6]),(0,[z0,z12,z3,z4,z144,z5,z6]),(0,[z0,z1,z302,z3,z5,z112,z6]),(0,[z0,z1,z401,z3,z4,z5,z6])],[(1,[z11,z1,z3,z4,z5,z265]),(0,[z0,z52,z1,z3,z4,z126,z6]),(0,[z0,z1,z402,z3,z4,z5,z6])],[(1,[z0,z1,z403,z3,z4,z5]),(0,[z0,z1,z404,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z259]),(0,[z0,z1,z3,z4,z5,z118,z121]),(0,[z0,z1,z3,z4,z5,z405,z6]),(0,[z406,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z115,z4,z23,z5,z6]),(0,[z11,z37,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z115,z4,z5,z407]),(0,[z19,z0,z1,z3,z4,z5,z228]),(0,[z11,z0,z14,z1,z3,z4,z5]),(0,[z110,z0,z1,z3,z4,z5,z308]),(0,[z0,z1,z3,z43,z5,z6,z44])],[(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z0,z1,z56,z3,z300,z4,z6]),(0,[z0,z408,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z409]),(0,[z19,z0,z1,z3,z137,z4,z5]),(0,[z0,z1,z3,z410,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z411,z6]),(0,[z0,z1,z3,z4,z5,z412,z6])],[(0,[z413,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z272]),(0,[z0,z1,z3,z414,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z144,z5]),(0,[z110,z0,z1,z83,z4,z5,z6])],[(0,[z19,z9,z0,z1,z3,z4,z5]),(0,[z1,z3,z4,z188,z5,z228,z6]),(0,[z0,z1,z3,z415,z4,z5,z6]),(0,[z416,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z143,z3,z4,z5,z6]),(0,[z417,z0,z1,z3,z4,z5,z6])],[(0,[z19,z0,z1,z224,z3,z4,z5]),(0,[z110,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z418,z4,z5,z6])],[(0,[z19,z0,z1,z3,z4,z419,z5]),(0,[z0,z1,z3,z4,z420,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z421]),(0,[z422,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z423,z6]),(0,[z19,z0,z152,z1,z3,z4,z5]),(0,[z0,z1,z403,z3,z32,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z424]),(0,[z0,z1,z3,z4,z5,z425,z6])],[(0,[z0,z426,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z427,z6]),(0,[z19,z0,z1,z3,z4,z5,z118]),(0,[z428,z0,z1,z3,z4,z5,z6])],[(0,[z0,z429,z1,z3,z4,z5,z6]),(1,[z9,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z430,z5,z6]),(0,[z36,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z431,z4,z5,z6]),(0,[z0,z1,z3,z432,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z433,z6])],[(0,[z0,z1,z3,z4,z5,z6,z407]),(0,[z0,z1,z434,z3,z4,z5,z6]),(0,[z99,z19,z0,z1,z3,z4,z5]),(0,[z103,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z435,z3,z4,z5,z6]),(0,[z0,z1,z436,z3,z4,z5,z6]),(0,[z0,z1,z3,z290,z43,z4,z5]),(0,[z0,z1,z26,z224,z3,z5,z6]),(0,[z0,z1,z3,z437,z4,z5,z6])],[(0,[z438,z0,z1,z3,z4,z5,z6]),(0,[z103,z0,z1,z3,z4,z5,z289])],[(0,[z11,z0,z1,z181,z3,z4,z5]),(0,[z110,z439,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z440,z4,z5,z6]),(0,[z0,z1,z3,z4,z441,z5,z6])],[(0,[z68,z0,z1,z74,z4,z5,z6]),(0,[z11,z0,z1,z3,z410,z4,z5]),(0,[z0,z12,z1,z3,z4,z5,z69]),(0,[z442,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z443,z4,z5,z6])],[(0,[z444,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z61,z3,z5,z112,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z445,z6]),(0,[z0,z1,z3,z4,z5,z446,z6]),(0,[z447,z0,z1,z3,z4,z5,z6]),(0,[z448,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z449,z4,z5,z6])],[(0,[z11,z0,z1,z120,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z450]),(0,[z0,z1,z3,z451,z4,z5,z6]),(0,[z0,z1,z452,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z22,z215]),(0,[z0,z1,z3,z4,z5,z6,z453]),(0,[z8,z0,z1,z181,z3,z4,z5])],[(0,[z0,z1,z21,z3,z4,z5,z121]),(0,[z0,z1,z3,z4,z5,z454,z6])],[(0,[z48,z0,z1,z3,z4,z5,z6]),(0,[z132,z0,z1,z3,z4,z228,z6]),(0,[z0,z1,z455,z3,z4,z5,z6]),(0,[z0,z1,z3,z300,z4,z135,z6]),(0,[z456,z0,z1,z3,z4,z5,z6]),(0,[z457,z0,z1,z3,z4,z5,z6])],[(0,[z87,z0,z1,z148,z4,z5,z6]),(1,[z132,z1,z3,z4,z188,z6]),(1,[z0,z1,z3,z392,z5,z6]),(0,[z0,z1,z3,z458,z4,z5,z6]),(0,[z0,z1,z3,z459,z4,z5,z6]),(0,[z0,z1,z26,z3,z4,z5,z6]),(0,[z103,z0,z1,z21,z3,z4,z5])],[(0,[z0,z1,z3,z460,z4,z5,z6]),(0,[z0,z1,z120,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z461]),(0,[z0,z1,z148,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z115,z4,z5]),(0,[z19,z0,z1,z3,z4,z5,z149]),(0,[z462,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z463,z4,z5,z6]),(1,[z0,z1,z302,z5,z112,z6]),(0,[z0,z1,z3,z4,z5,z6,z464]),(0,[z0,z1,z3,z465,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z44]),(0,[z0,z1,z3,z466,z4,z5,z6])],[(0,[z19,z125,z0,z1,z3,z4,z5]),(0,[z19,z0,z1,z3,z451,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z467]),(0,[z0,z1,z468,z3,z4,z5,z6]),(0,[z0,z1,z469,z3,z4,z5,z6]),(0,[z0,z199,z1,z3,z4,z135,z6])],[(0,[z0,z1,z3,z470,z4,z5,z6]),(0,[z0,z1,z120,z4,z5,z112,z6]),(0,[z19,z68,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z471,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z472,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z473,z6]),(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z0,z1,z475,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z476,z5,z6])],[(0,[z0,z1,z3,z477,z4,z5,z6]),(0,[z341,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z478,z4,z5,z6]),(0,[z0,z1,z479,z3,z4,z5,z6])],[(1,[z19,z11,z1,z3,z4,z5])],[],[(0,[z0,z1,z3,z4,z5,z480,z6]),(1,[z0,z1,z226,z3,z4,z6]),(0,[z0,z1,z481,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z111,z5,z6])],[(0,[z0,z482,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z483,z6]),(0,[z484,z0,z1,z3,z4,z5,z6])],[(0,[z0,z439,z1,z3,z4,z5,z6]),(0,[z0,z52,z3,z4,z126,z5,z6]),(0,[z0,z91,z1,z3,z4,z5,z118])],[(0,[z0,z485,z1,z3,z4,z5,z6]),(0,[z101,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z486,z5]),(0,[z0,z1,z3,z487,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z118]),(0,[z0,z1,z3,z488,z4,z5,z6]),(0,[z0,z489,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z490,z4,z5,z6])]],
   [[(0,[z19,z0,z1,z153,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z491,z6]),(0,[z0,z1,z3,z4,z5,z265,z6]),(0,[z0,z1,z3,z4,z5,z6,z492]),(0,[z493,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z494])],[(0,[z11,z0,z1,z3,z4,z5,z228])],[(0,[z0,z1,z495,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z304,z5]),(0,[z496,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z497,z5,z6]),(0,[z0,z1,z498,z3,z4,z5,z6]),(0,[z0,z1,z499,z3,z4,z5,z6])],[(0,[z413,z11,z0,z1,z3,z4,z5]),(0,[z11,z0,z1,z3,z137,z4,z5]),(0,[z0,z199,z1,z3,z4,z5,z247]),(0,[z0,z1,z3,z4,z5,z500,z6])],[(0,[z0,z1,z501,z3,z4,z5,z6]),(0,[z48,z1,z153,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z144,z5]),(0,[z0,z1,z3,z4,z5,z502,z6]),(1,[z0,z1,z61,z137,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z121])],[(0,[z11,z9,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z503,z6]),(0,[z504,z0,z1,z3,z4,z5,z6])],[(0,[z19,z0,z1,z3,z4,z5,z265]),(0,[z110,z11,z0,z1,z3,z4,z5]),(1,[z439,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z505,z5,z6]),(0,[z0,z1,z302,z4,z5,z112,z6]),(0,[z0,z1,z3,z43,z4,z57,z6]),(0,[z0,z1,z3,z506,z4,z5,z6]),(0,[z0,z1,z181,z3,z4,z34,z5])],[(0,[z0,z1,z3,z4,z507,z5,z6]),(0,[z508,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z120,z3,z244,z4,z5]),(0,[z19,z1,z3,z4,z5,z6,z149]),(0,[z11,z0,z1,z224,z3,z4,z5]),(0,[z110,z0,z1,z3,z325,z5,z6]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z0,z1,z3,z510,z4,z5,z6]),(0,[z0,z1,z3,z511,z4,z5,z6])]],
   [[(0,[z0,z512,z1,z3,z4,z5,z6]),(0,[z132,z0,z1,z3,z43,z4,z6]),(0,[z11,z0,z1,z339,z3,z4,z5]),(0,[z0,z1,z3,z513,z4,z5,z6])],[(0,[z11,z0,z152,z1,z3,z4,z5]),(0,[z0,z1,z3,z514,z4,z5,z6]),(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z37,z0,z1,z3,z115,z5,z6]),(0,[z0,z1,z516,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z517,z5,z6])],[(0,[z11,z0,z1,z3,z4,z5,z118]),(0,[z0,z518,z1,z3,z4,z5,z6])],[(0,[z0,z1,z519,z3,z4,z5,z6])],[(0,[z0,z1,z520,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z23,z5,z6]),(0,[z19,z0,z1,z3,z4,z5,z112]),(0,[z0,z1,z3,z4,z5,z521,z6]),(0,[z0,z1,z3,z522,z4,z5,z6])],[(0,[z1,z153,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z523])],[(0,[z0,z1,z3,z4,z5,z6,z524]),(0,[z0,z1,z3,z4,z486,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6]),(0,[z50,z0,z1,z3,z4,z5,z228]),(0,[z19,z0,z1,z3,z4,z5,z57]),(0,[z110,z0,z1,z3,z4,z5,z503]),(0,[z0,z1,z61,z137,z4,z5,z6])],[(0,[z0,z1,z16,z3,z300,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z525,z5,z6]),(0,[z89,z0,z1,z3,z4,z5,z6]),(0,[z526,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z118,z215]),(0,[z0,z1,z21,z3,z5,z6,z289]),(0,[z0,z1,z181,z3,z4,z6,z121])],[(1,[z0,z1,z3,z244,z4,z5]),(0,[z19,z0,z1,z3,z35,z4,z5]),(0,[z19,z0,z1,z3,z4,z5,z135]),(0,[z0,z1,z16,z56,z4,z5,z6]),(1,[z0,z1,z3,z287,z5,z6]),(0,[z0,z1,z527,z3,z4,z5,z6]),(0,[z0,z528,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z300,z4,z126,z6]),(0,[z0,z1,z300,z4,z5,z57,z6]),(1,[z0,z1,z3,z4,z5,z240])],[(0,[z0,z1,z3,z529,z4,z5,z6]),(0,[z0,z1,z530,z3,z4,z5,z6]),(0,[z531,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z532,z3,z4,z5,z6])],[(0,[z87,z0,z1,z3,z115,z5,z6]),(0,[z68,z0,z1,z3,z4,z228,z6]),(1,[z50,z0,z1,z3,z4,z5]),(0,[z19,z132,z0,z1,z3,z4,z5]),(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z0,z199,z1,z3,z4,z126,z6]),(0,[z0,z1,z533,z3,z4,z5,z6])],[(0,[z534,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z535,z6]),(0,[z164,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z536,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z149]),(0,[z0,z1,z302,z61,z4,z5,z6]),(0,[z537,z0,z1,z3,z4,z5,z6]),(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z539,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z540,z3,z4,z5,z6])],[(0,[z0,z1,z541,z3,z4,z5,z6]),(0,[z19,z0,z1,z141,z3,z4,z5]),(0,[z0,z1,z3,z542,z4,z5,z6]),(0,[z543,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z544,z3,z4,z5,z6]),(0,[z0,z1,z181,z21,z3,z4,z5])]],
   [[(1,[z125,z1,z32,z4,z5,z6]),(0,[z0,z12,z1,z3,z144,z5,z6]),(0,[z545,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z247,z6]),(0,[z0,z1,z3,z4,z5,z546,z6]),(0,[z0,z1,z3,z547,z4,z5,z6])],[(0,[z194,z0,z1,z3,z32,z4,z5]),(1,[z37,z1,z3,z115,z5,z6]),(0,[z132,z0,z1,z3,z4,z5,z6]),(0,[z110,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z548,z5,z6]),(0,[z549,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z550,z6]),(0,[z0,z1,z3,z255,z4,z5,z6]),(0,[z0,z1,z3,z4,z188,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z551]),(0,[z0,z1,z26,z3,z4,z6,z44])],[(0,[z0,z1,z3,z4,z5,z552,z6]),(0,[z37,z0,z1,z224,z3,z5,z6]),(0,[z0,z1,z141,z3,z4,z5,z6])],[(0,[z0,z1,z120,z3,z4,z5,z272]),(0,[z19,z8,z0,z1,z3,z4,z5]),(0,[z553,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z554,z6])],[(1,[z147,z0,z1,z3,z4,z5]),(0,[z0,z1,z555,z3,z4,z5,z6]),(0,[z0,z12,z1,z3,z4,z5,z259]),(0,[z0,z1,z3,z4,z5,z69,z6]),(0,[z0,z1,z3,z4,z5,z6,z556]),(0,[z0,z1,z3,z163,z4,z5,z289]),(1,[z0,z1,z3,z4,z34,z121])],[(0,[z318,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z392,z4,z5,z6]),(1,[z175,z0,z3,z4,z5,z118]),(0,[z0,z1,z3,z4,z5,z557,z6]),(0,[z0,z1,z3,z300,z4,z5,z6])],[(0,[z0,z1,z3,z558,z4,z5,z6]),(1,[z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z559,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z560,z6]),(0,[z0,z1,z21,z3,z4,z5,z118])]],
   [[(1,[z0,z1,z3,z325,z5,z6]),(0,[z0,z1,z561,z3,z4,z5,z6]),(0,[z0,z1,z562,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z563,z6])],[(0,[z11,z0,z1,z153,z3,z4,z5]),(0,[z0,z199,z1,z3,z4,z5,z6]),(0,[z0,z220,z1,z3,z4,z5,z6]),(0,[z564,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z565,z3,z4,z5,z6]),(1,[z8,z0,z1,z181,z3,z4])],[(0,[z48,z0,z153,z3,z4,z5,z6]),(0,[z0,z1,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z566,z6]),(0,[z0,z567,z1,z3,z4,z5,z6]),(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z569,z3,z4,z5,z6]),(0,[z0,z1,z570,z3,z4,z5,z6]),(0,[z0,z1,z26,z3,z300,z4,z6])],[(0,[z9,z152,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z255,z4,z5,z6]),(0,[z0,z1,z3,z571,z4,z5,z6]),(1,[z19,z1,z3,z4,z5,z149]),(0,[z0,z1,z3,z4,z197,z5,z6]),(0,[z0,z14,z1,z3,z144,z5,z6])],[(1,[z0,z1,z3,z4,z5,z407])],[(1,[z0,z1,z3,z24,z4,z6]),(0,[z0,z572,z1,z3,z4,z5,z6]),(0,[z573,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z574,z4,z5,z6]),(0,[z131,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z575,z3,z4,z5,z6])],[(0,[z87,z0,z1,z224,z3,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z265]),(0,[z576,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z503]),(0,[z0,z1,z3,z4,z126,z57,z6]),(0,[z577,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z578,z4,z5,z6]),(0,[z0,z1,z579,z3,z4,z5,z6]),(0,[z0,z1,z580,z3,z4,z5,z6])]],
   [[(0,[z581,z0,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z83,z4,z5]),(0,[z0,z1,z3,z4,z582,z5,z6])],[(0,[z0,z1,z3,z4,z5,z583,z6]),(1,[z220,z1,z3,z4,z5,z6]),(1,[z336,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z584]),(0,[z585,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z586,z5,z6])],[(0,[z37,z1,z3,z115,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z587,z6])],[(0,[z0,z1,z3,z4,z5,z588,z6]),(0,[z0,z1,z3,z119,z4,z5,z6]),(1,[z0,z1,z16,z300,z4,z6]),(0,[z589,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z590,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z189]),(0,[z11,z0,z1,z3,z4,z5,z112]),(0,[z591,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z592,z4,z5,z6])],[(0,[z593,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z32,z4,z5,z265,z6]),(0,[z19,z0,z1,z3,z4,z5,z22]),(0,[z0,z1,z3,z4,z5,z6,z594]),(0,[z0,z1,z3,z4,z5,z595,z6]),(0,[z0,z1,z3,z4,z5,z596,z6])],[(0,[z597,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z598,z4,z5,z6]),(0,[z0,z1,z599,z3,z4,z5,z6]),(0,[z0,z199,z3,z4,z5,z135,z6]),(0,[z0,z1,z3,z4,z5,z600,z6])]],
   [[(0,[z0,z1,z3,z4,z601,z5,z6]),(0,[z125,z11,z0,z1,z3,z4,z5]),(0,[z87,z0,z1,z3,z4,z5,z6]),(0,[z68,z1,z3,z4,z5,z228,z6]),(0,[z0,z1,z3,z602,z4,z5,z6]),(0,[z0,z1,z56,z3,z4,z57,z6]),(0,[z0,z1,z603,z3,z4,z5,z6])],[(0,[z604,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z605,z4,z5,z6]),(0,[z0,z606,z1,z3,z4,z5,z6])],[(0,[z0,z607,z1,z3,z4,z5,z6]),(0,[z0,z152,z1,z3,z4,z5,z159]),(1,[z19,z0,z1,z3,z4,z5]),(0,[z368,z11,z0,z1,z3,z4,z5]),(0,[z11,z0,z608,z1,z3,z4,z5]),(0,[z11,z0,z1,z3,z35,z4,z5]),(0,[z11,z0,z1,z3,z4,z5,z135]),(0,[z609,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z21,z3,z163,z4,z5])],[(0,[z0,z152,z1,z3,z4,z5,z6]),(0,[z0,z610,z1,z3,z4,z5,z6]),(0,[z0,z611,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z612,z4,z5,z6])],[(0,[z36,z0,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z613]),(0,[z0,z1,z3,z25,z4,z5,z6]),(0,[z0,z1,z3,z614,z4,z5,z6]),(0,[z0,z615,z1,z3,z4,z5,z6])],[(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z215]),(1,[z0,z1,z26,z224,z3,z6])],[(1,[z0,z1,z617,z3,z4,z5]),(0,[z36,z125,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z618,z4,z5,z6]),(0,[z0,z1,z3,z4,z144,z5,z6]),(0,[z0,z1,z16,z3,z287,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z189]),(0,[z377,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z619,z6])]],
   [[(0,[z0,z1,z3,z4,z486,z23,z5]),(0,[z11,z0,z1,z141,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z620,z6]),(0,[z0,z621,z1,z3,z4,z5,z6])],[(0,[z0,z1,z622,z3,z4,z5,z6]),(0,[z0,z1,z623,z3,z4,z5,z6])],[(0,[z0,z1,z403,z3,z4,z5,z6]),(0,[z0,z1,z3,z624,z4,z5,z6]),(0,[z0,z1,z625,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z626,z6]),(0,[z0,z1,z137,z4,z5,z112,z6])],[(0,[z0,z627,z1,z3,z4,z5,z6]),(0,[z125,z1,z3,z32,z4,z5,z6]),(1,[z164,z0,z1,z3,z4,z5]),(0,[z132,z0,z1,z26,z3,z4,z6]),(0,[z19,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z628]),(0,[z0,z1,z3,z4,z5,z629,z6])],[(0,[z0,z1,z3,z4,z5,z6,z630]),(0,[z0,z1,z3,z4,z5,z409,z6]),(1,[z0,z1,z434,z3,z4,z5]),(0,[z0,z1,z3,z4,z631,z5,z6])],[(0,[z0,z1,z3,z357,z4,z5,z6]),(0,[z0,z12,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z632,z5,z6]),(0,[z0,z1,z3,z4,z5,z633,z6]),(1,[z0,z1,z3,z17,z5,z6]),(0,[z0,z1,z3,z4,z5,z634,z6]),(0,[z0,z1,z3,z4,z5,z6,z289])],[(0,[z0,z1,z3,z635,z4,z5,z6]),(0,[z0,z636,z1,z3,z4,z5,z6]),(0,[z0,z1,z637,z3,z4,z5,z6]),(0,[z19,z0,z1,z302,z3,z4,z5]),(1,[z0,z12,z3,z144,z5,z6]),(0,[z0,z1,z3,z4,z638,z5,z6])],[(0,[z0,z1,z3,z25,z5,z228,z6]),(0,[z11,z0,z1,z307,z3,z4,z5]),(0,[z175,z0,z91,z3,z4,z5,z6]),(0,[z639,z0,z1,z3,z4,z5,z6]),(0,[z640,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z132,z0,z1,z3,z4,z188,z6]),(0,[z0,z1,z641,z3,z4,z5,z6]),(0,[z0,z1,z224,z3,z5,z6,z44]),(0,[z0,z642,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z163,z5,z289]),(0,[z103,z0,z1,z21,z3,z5,z6]),(0,[z8,z0,z1,z3,z4,z34,z6]),(0,[z0,z1,z3,z643,z4,z5,z6])],[(0,[z48,z0,z152,z3,z4,z5,z6]),(0,[z644,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z645,z3,z4,z5,z6]),(0,[z19,z0,z12,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z646,z5,z6]),(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z0,z1,z96,z3,z4,z5,z215]),(0,[z336,z131,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z648,z5,z6])],[(0,[z649,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z650,z6])],[(0,[z0,z1,z3,z24,z4,z5,z6]),(0,[z526,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z651,z4,z5,z6]),(0,[z0,z91,z1,z3,z4,z5,z22])],[(0,[z0,z1,z3,z4,z419,z5,z6]),(0,[z131,z0,z1,z3,z117,z4,z5]),(0,[z652,z0,z1,z3,z4,z5,z6])],[(0,[z147,z0,z1,z153,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z653,z6]),(0,[z654,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z655,z3,z4,z5,z6]),(0,[z0,z1,z3,z163,z5,z6,z289]),(0,[z0,z1,z656,z3,z4,z5,z6])],[(1,[z68,z1,z3,z4,z228,z6]),(1,[z0,z14,z3,z35,z5,z6])],[(0,[z657,z0,z1,z3,z4,z5,z6]),(0,[z19,z0,z0,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z658,z4,z5,z6]),(0,[z0,z1,z3,z4,z659,z5,z6]),(0,[z0,z1,z660,z3,z4,z5,z6]),(0,[z0,z1,z3,z137,z144,z5,z6])],[(0,[z0,z1,z3,z661,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z662])],[],[],[(0,[z0,z663,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z664,z4,z5,z6]),(0,[z0,z665,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z57,z6]),(0,[z0,z1,z666,z3,z4,z5,z6])],[(0,[z19,z36,z1,z3,z4,z5,z6]),(0,[z0,z1,z74,z3,z4,z5,z6]),(0,[z19,z0,z1,z257,z3,z4,z5]),(0,[z0,z1,z667,z3,z4,z5,z6]),(0,[z0,z1,z3,z668,z4,z5,z6])],[(0,[z0,z1,z3,z4,z669,z5,z6]),(0,[z0,z608,z1,z3,z4,z5,z6]),(0,[z0,z1,z670,z3,z4,z5,z6]),(0,[z0,z1,z671,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z672,z5,z6])],[(0,[z438,z11,z0,z1,z3,z4,z5]),(0,[z11,z0,z1,z3,z4,z5,z22]),(0,[z110,z40,z1,z3,z4,z5,z6]),(0,[z0,z141,z3,z83,z4,z5,z6]),(0,[z0,z673,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z674,z4,z5,z6])]],
   [[(0,[z0,z1,z617,z3,z4,z5,z6]),(0,[z0,z1,z675,z3,z4,z5,z6]),(0,[z0,z91,z1,z3,z4,z5,z6]),(0,[z0,z1,z676,z3,z4,z5,z6])],[(0,[z0,z1,z3,z677,z4,z5,z6]),(0,[z19,z0,z1,z56,z3,z4,z5]),(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z6])],[(0,[z395,z19,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z679,z4,z5,z6]),(0,[z0,z1,z3,z680,z4,z5,z6]),(0,[z0,z1,z181,z3,z4,z5,z289])],[(0,[z0,z1,z681,z3,z4,z5,z6]),(0,[z19,z0,z1,z96,z3,z4,z5]),(0,[z682,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z683,z4,z5,z6])],[(0,[z684,z0,z1,z3,z4,z5,z6]),(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z26,z224,z3,z4,z6])],[(0,[z0,z1,z3,z4,z686,z5,z6]),(0,[z687,z0,z1,z3,z4,z5,z6])],[(0,[z48,z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z688,z3,z4,z5,z6]),(0,[z689,z0,z1,z3,z4,z5,z6])],[(0,[z690,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z691,z6]),(0,[z0,z692,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z617,z153,z3,z4,z5]),(0,[z363,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z15]),(0,[z693,z0,z1,z3,z4,z5,z6]),(0,[z131,z0,z1,z96,z4,z5,z6]),(0,[z0,z1,z3,z4,z694,z5,z6])],[(0,[z0,z152,z1,z3,z4,z5,z409]),(0,[z19,z36,z0,z1,z3,z4,z5]),(0,[z413,z19,z0,z1,z3,z4,z5]),(0,[z19,z0,z1,z3,z117,z4,z5]),(0,[z0,z1,z695,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z304,z5,z228]),(0,[z0,z696,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z697,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z19,z11,z0,z1,z3,z4,z5]),(0,[z0,z14,z3,z35,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z698])],[(0,[z0,z1,z3,z699,z4,z5,z6]),(0,[z0,z1,z700,z3,z4,z5,z6]),(0,[z0,z701,z1,z3,z4,z5,z6]),(0,[z0,z1,z702,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z6]),(0,[z175,z0,z3,z4,z5,z118,z6]),(0,[z703,z0,z1,z3,z4,z5,z6]),(0,[z704,z0,z1,z3,z4,z5,z6]),(0,[z0,z705,z1,z3,z4,z5,z6])],[(0,[z68,z0,z1,z26,z3,z4,z6]),(0,[z0,z1,z434,z3,z4,z188,z5])],[(0,[z0,z1,z3,z4,z5,z118,z6]),(0,[z0,z1,z16,z3,z4,z57,z6])],[(0,[z11,z0,z1,z3,z542,z4,z5]),(0,[z11,z0,z1,z302,z3,z4,z5]),(0,[z0,z1,z706,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z707,z5,z6]),(0,[z1,z3,z4,z708,z5,z6]),(0,[z19,z0,z1,z3,z4,z709]),(0,[z0,z3,z4,z710,z135,z6])],[(0,[z11,z0,z1,z3,z17,z5])],[(0,[z711,z1,z3,z4,z5,z6])],[(0,[z1,z3,z32,z244,z4,z5]),(0,[z194,z220,z1,z3,z4,z5]),(0,[z0,z1,z712,z4,z5,z6]),(0,[z0,z1,z434,z3,z4,z5]),(0,[z368,z0,z608,z3,z4,z5]),(0,[z11,z0,z1,z713,z4,z5]),(0,[z0,z1,z3,z714,z4,z6]),(0,[z0,z1,z715,z3,z5,z6])],[(0,[z0,z1,z148,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z38]),(0,[z19,z0,z1,z3,z119,z4]),(0,[z0,z1,z3,z4,z716,z6]),(0,[z0,z1,z3,z717,z4,z5]),(0,[z0,z1,z718,z3,z4,z5])],[(0,[z0,z719,z3,z4,z5,z6]),(0,[z37,z1,z3,z115,z5,z407]),(0,[z363,z0,z1,z3,z419,z5])],[(0,[z0,z1,z3,z4,z709,z6]),(0,[z19,z0,z720,z3,z4,z5]),(0,[z0,z1,z3,z721,z4,z6]),(0,[z0,z1,z27,z300,z4,z6])],[(0,[z19,z0,z1,z712,z4,z5]),(0,[z0,z3,z4,z5,z722,z6]),(0,[z723,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z724,z5,z6]),(0,[z0,z80,z3,z4,z5,z118]),(0,[z0,z1,z3,z4,z5,z725]),(0,[z0,z1,z475,z137,z5,z6])],[(0,[z13,z1,z32,z4,z5,z6]),(0,[z0,z1,z181,z3,z4,z78]),(0,[z346,z11,z1,z3,z4,z5]),(0,[z0,z1,z3,z392,z111,z6])],[(0,[z0,z1,z726,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z727]),(0,[z11,z0,z1,z3,z4,z245]),(0,[z0,z1,z3,z728,z5,z6])],[(0,[z0,z1,z3,z729,z5,z6]),(0,[z37,z1,z3,z730,z5,z6]),(0,[z731,z0,z1,z3,z4,z5]),(0,[z0,z1,z715,z3,z163,z5])],[(0,[z0,z1,z3,z732,z4,z5]),(0,[z0,z1,z3,z4,z5,z733]),(0,[z0,z1,z3,z4,z5,z734]),(0,[z0,z1,z117,z735,z4,z5])],[(0,[z0,z1,z736,z4,z5,z6]),(0,[z0,z1,z120,z4,z38,z6]),(0,[z68,z1,z3,z4,z228,z6]),(0,[z11,z0,z1,z3,z392,z5]),(0,[z0,z1,z3,z4,z737,z6]),(0,[z738,z1,z3,z4,z5,z6])],[(0,[z0,z1,z739,z4,z5,z6]),(0,[z0,z1,z3,z4,z111,z308]),(0,[z0,z1,z3,z740,z5,z6]),(0,[z0,z1,z706,z4,z5,z215]),(0,[z0,z1,z26,z30,z3,z6]),(0,[z0,z1,z3,z43,z683,z6])],[(0,[z0,z720,z3,z4,z5,z6]),(0,[z19,z1,z281,z3,z4,z5]),(0,[z19,z1,z3,z201,z4,z5]),(0,[z0,z1,z3,z325,z5,z503]),(0,[z0,z741,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z742,z3,z4,z5]),(0,[z194,z0,z1,z3,z4,z5]),(0,[z743,z0,z1,z3,z4,z5]),(0,[z744,z0,z1,z3,z4,z5])],[(0,[z19,z0,z1,z3,z745,z5]),(0,[z19,z1,z303,z3,z4,z5]),(0,[z0,z1,z3,z746,z4,z6]),(0,[z0,z747,z1,z3,z4,z5])],[(0,[z19,z0,z1,z748,z4,z5]),(0,[z0,z3,z749,z4,z5,z6]),(0,[z0,z91,z3,z4,z5,z722])],[(0,[z0,z1,z3,z750,z5,z6]),(0,[z0,z1,z3,z4,z5,z751]),(0,[z0,z1,z3,z4,z5,z752]),(0,[z395,z0,z1,z357,z4,z5])],[(0,[z0,z1,z753,z4,z5,z6]),(0,[z19,z0,z1,z3,z17,z5]),(0,[z19,z367,z1,z3,z4,z5]),(0,[z11,z0,z1,z61,z137,z5]),(0,[z0,z1,z3,z4,z111,z6]),(0,[z0,z1,z3,z4,z754,z6])],[(0,[z0,z1,z3,z4,z5,z755]),(0,[z756,z1,z3,z4,z5,z6]),(0,[z0,z1,z735,z4,z5,z215]),(0,[z0,z1,z757,z3,z4,z5])],[(0,[z87,z11,z1,z3,z23,z5])],[(0,[z0,z1,z255,z43,z4,z6]),(0,[z0,z1,z3,z758,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z759]),(0,[z0,z1,z3,z4,z5,z760])],[],[(0,[z0,z1,z3,z4,z5,z761]),(0,[z1,z3,z4,z5,z6,z725]),(0,[z175,z0,z307,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z762])],[(0,[z0,z1,z3,z4,z5,z763]),(0,[z0,z764,z3,z4,z5,z6]),(0,[z11,z0,z1,z226,z3,z4]),(0,[z0,z1,z26,z3,z211,z6]),(0,[z0,z1,z3,z4,z34,z264]),(0,[z110,z40,z83,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z765]),(0,[z0,z52,z3,z4,z710,z6]),(0,[z0,z1,z3,z4,z38,z6]),(0,[z766,z1,z3,z4,z5,z6])],[(0,[z19,z1,z3,z4,z5,z461]),(0,[z538,z1,z120,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z767]),(0,[z76,z0,z307,z3,z4,z5]),(0,[z0,z140,z749,z4,z5,z6])],[(0,[z0,z1,z3,z4,z727,z6]),(0,[z19,z125,z1,z32,z4,z5]),(0,[z526,z0,z1,z3,z4,z78]),(0,[z19,z0,z1,z3,z4,z245]),(0,[z0,z1,z3,z768,z5,z6]),(0,[z110,z0,z83,z4,z111,z6]),(0,[z0,z1,z3,z769,z4,z5])],[(0,[z68,z11,z1,z3,z4,z228]),(0,[z0,z1,z3,z4,z5,z770]),(0,[z0,z1,z3,z771,z5,z6]),(0,[z0,z1,z772,z4,z5,z6]),(0,[z0,z1,z773,z3,z4,z34])],[(0,[z0,z1,z3,z4,z5,z774]),(0,[z0,z140,z141,z4,z5,z6]),(0,[z0,z1,z3,z775,z5,z6]),(0,[z0,z1,z3,z4,z5,z15])]],
   [[(0,[z0,z1,z702,z5,z112,z6]),(0,[z1,z120,z776,z4,z5,z6]),(0,[z19,z0,z1,z3,z392,z5])],[(0,[z0,z1,z3,z4,z777,z6]),(0,[z0,z1,z3,z293,z5,z289])],[(0,[z36,z11,z1,z120,z4,z5]),(0,[z778,z0,z1,z3,z4,z5]),(0,[z0,z1,z300,z4,z779,z6])],[(0,[z19,z0,z1,z3,z780,z5]),(0,[z781,z0,z1,z3,z4,z5])],[(0,[z40,z1,z3,z392,z5,z6]),(0,[z0,z1,z3,z4,z5,z722])],[(0,[z1,z776,z3,z4,z5,z6]),(0,[z0,z1,z383,z137,z5,z6])],[(0,[z48,z617,z153,z3,z4,z5])],[(0,[z48,z147,z153,z3,z4,z5]),(0,[z19,z0,z1,z61,z137,z5]),(0,[z0,z12,z3,z782,z5,z6]),(0,[z0,z1,z179,z4,z57,z6]),(0,[z0,z1,z3,z783,z5,z6]),(0,[z103,z0,z1,z21,z3,z5])]],
   [[(0,[z19,z1,z32,z4,z5,z112]),(0,[z0,z1,z255,z4,z5,z6]),(0,[z0,z784,z3,z4,z5,z6]),(0,[z0,z1,z3,z24,z4,z486]),(0,[z0,z1,z21,z715,z3,z5])],[(0,[z0,z1,z3,z785,z5,z6]),(0,[z0,z1,z3,z786,z5,z6]),(0,[z19,z319,z1,z3,z4,z5]),(0,[z19,z1,z3,z4,z5,z330]),(0,[z787,z1,z3,z4,z5,z6])],[(0,[z0,z1,z18,z4,z5,z6]),(0,[z0,z3,z4,z5,z788,z6]),(0,[z0,z1,z3,z43,z446,z6]),(0,[z0,z1,z3,z4,z789,z5]),(0,[z68,z0,z1,z3,z25,z6]),(0,[z131,z0,z1,z542,z4,z5])],[(0,[z19,z0,z1,z3,z729,z5]),(0,[z0,z3,z4,z710,z5,z6]),(0,[z0,z489,z3,z4,z135,z6])],[(0,[z0,z1,z3,z25,z5,z6]),(0,[z132,z1,z3,z4,z188,z189]),(0,[z0,z1,z3,z790,z5,z6])],[(0,[z48,z19,z153,z3,z4,z5]),(0,[z0,z1,z3,z4,z791,z6]),(0,[z792,z1,z3,z4,z5,z6]),(0,[z793,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z794,z6])],[(0,[z11,z0,z1,z148,z4,z5]),(0,[z19,z0,z1,z226,z3,z4]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z796])],[(0,[z0,z1,z3,z25,z304,z5]),(0,[z0,z3,z4,z5,z118,z722]),(0,[z0,z1,z3,z43,z6,z44])]],
   [[(0,[z0,z1,z3,z4,z5,z797]),(0,[z0,z1,z56,z4,z57,z6])],[(0,[z0,z1,z3,z4,z5,z798]),(0,[z0,z1,z3,z4,z5,z799]),(0,[z11,z47,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z800]),(0,[z110,z439,z83,z4,z5,z6]),(0,[z801,z0,z1,z3,z4,z5])],[(0,[z0,z1,z749,z4,z5,z6])],[(0,[z0,z1,z3,z4,z802,z6]),(0,[z0,z1,z803,z4,z5,z6]),(0,[z68,z1,z3,z4,z708,z6]),(0,[z0,z1,z3,z804,z4,z5]),(0,[z0,z1,z21,z3,z451,z5]),(0,[z0,z1,z3,z4,z5,z69])],[(0,[z19,z0,z1,z805,z4,z5])],[(0,[z0,z1,z74,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z806])],[(0,[z0,z199,z3,z4,z135,z247]),(0,[z0,z1,z3,z443,z5,z289])]],
   [[(0,[z0,z1,z3,z4,z5,z807]),(0,[z808,z0,z1,z3,z4,z5]),(0,[z131,z220,z1,z117,z4,z5])],[(0,[z0,z1,z3,z4,z809,z6]),(0,[z0,z1,z3,z4,z5,z810]),(0,[z811,z0,z1,z3,z4,z5]),(0,[z0,z812,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z813]),(0,[z87,z1,z3,z23,z5,z6]),(0,[z0,z1,z3,z4,z5,z814]),(0,[z0,z1,z3,z43,z6,z494])],[(0,[z0,z1,z815,z4,z5,z6]),(0,[z125,z194,z1,z32,z4,z5])],[(0,[z0,z1,z816,z4,z5,z6]),(0,[z0,z1,z3,z817,z5,z6]),(0,[z0,z1,z3,z163,z419,z5]),(0,[z0,z818,z1,z3,z4,z5]),(0,[z819,z0,z1,z3,z4,z5])],[(0,[z0,z1,z820,z3,z4,z6]),(0,[z0,z1,z3,z821,z5,z6]),(0,[z0,z1,z26,z3,z714,z6])],[(0,[z0,z1,z822,z3,z4,z5]),(0,[z0,z1,z3,z17,z57,z6]),(0,[z0,z1,z823,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z159]),(0,[z87,z1,z226,z3,z23,z6]),(0,[z110,z0,z749,z4,z5,z6])]],
   [[(0,[z0,z1,z824,z4,z5,z6]),(0,[z0,z1,z61,z598,z5,z6]),(0,[z825,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z826,z6]),(0,[z19,z0,z1,z148,z4,z5]),(0,[z827,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z828,z6])],[(0,[z0,z1,z32,z287,z5,z6]),(0,[z19,z36,z1,z257,z4,z5]),(0,[z19,z0,z1,z3,z829,z5]),(0,[z830,z1,z3,z4,z5,z6]),(0,[z0,z1,z831,z3,z4,z5]),(0,[z0,z1,z3,z4,z638,z121])],[(0,[z0,z1,z3,z832,z5,z6]),(0,[z19,z0,z1,z833,z4,z5]),(0,[z110,z19,z0,z83,z4,z5]),(0,[z19,z1,z479,z3,z4,z5]),(0,[z59,z0,z1,z339,z4,z5]),(0,[z110,z0,z83,z4,z5,z308])],[(0,[z0,z1,z834,z3,z5,z6]),(0,[z36,z1,z120,z4,z5,z6]),(0,[z19,z0,z1,z187,z3,z5])],[(0,[z0,z1,z4,z779,z5,z6]),(0,[z131,z0,z1,z117,z4,z5])],[(0,[z0,z1,z835,z3,z5,z6]),(0,[z0,z1,z3,z836,z4,z6]),(0,[z0,z1,z96,z357,z4,z5]),(0,[z837,z1,z3,z4,z5,z6]),(0,[z0,z1,z468,z5,z112,z6]),(0,[z0,z52,z3,z4,z126,z6])],[(0,[z0,z1,z838,z4,z5,z6]),(0,[z0,z1,z839,z3,z4,z5]),(0,[z0,z840,z3,z4,z5,z6])]],
   [[(0,[z125,z11,z1,z32,z4,z5]),(0,[z132,z0,z1,z3,z25,z6]),(0,[z0,z1,z3,z4,z5,z841])],[(0,[z0,z1,z842,z3,z5,z6]),(0,[z19,z336,z1,z3,z4,z5]),(0,[z11,z0,z1,z18,z4,z5]),(0,[z0,z1,z3,z4,z5,z843]),(0,[z0,z1,z3,z4,z5,z844]),(0,[z19,z1,z222,z3,z4,z5]),(0,[z531,z11,z1,z3,z4,z5]),(0,[z110,z0,z83,z4,z5,z6]),(0,[z0,z199,z3,z4,z710,z6])],[(0,[z172,z0,z1,z3,z43,z6]),(0,[z0,z1,z845,z3,z4,z5]),(0,[z11,z0,z1,z302,z5,z112]),(0,[z0,z1,z3,z846,z5,z6]),(0,[z0,z1,z3,z4,z847,z6]),(0,[z0,z1,z3,z290,z43,z44])],[(0,[z168,z0,z1,z3,z4,z264]),(0,[z0,z1,z3,z4,z5,z848])],[(0,[z0,z1,z3,z4,z5,z849]),(0,[z0,z1,z3,z4,z710,z6])],[(0,[z0,z1,z3,z4,z850,z6]),(1,[z1,z3,z4,z708,z6]),(0,[z132,z11,z1,z3,z4,z188]),(0,[z851,z1,z3,z4,z5,z6])],[(0,[z19,z687,z1,z3,z4,z5])],[(0,[z0,z1,z3,z852,z4,z5])]],
   [[(0,[z853,z153,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z854,z5]),(0,[z40,z1,z3,z325,z5,z6]),(0,[z0,z3,z35,z782,z5,z6])],[(0,[z8,z0,z1,z3,z4,z198]),(0,[z0,z1,z3,z4,z5,z855])],[(0,[z132,z1,z3,z4,z708,z6]),(0,[z0,z1,z3,z43,z546,z6]),(0,[z0,z1,z21,z3,z104,z5])],[(0,[z0,z1,z3,z856,z5,z6])],[(0,[z1,z3,z4,z5,z265,z725]),(0,[z1,z3,z4,z5,z857,z6]),(0,[z0,z1,z3,z4,z858,z6]),(0,[z0,z1,z773,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z859]),(0,[z0,z199,z3,z4,z135,z6]),(0,[z0,z310,z1,z181,z3,z4])],[(0,[z36,z1,z120,z244,z4,z5]),(0,[z318,z0,z1,z3,z197,z5]),(0,[z0,z1,z3,z860,z5,z6]),(0,[z0,z386,z1,z21,z3,z5])],[(0,[z0,z1,z3,z861,z5,z6]),(0,[z40,z1,z3,z4,z5,z503])]],
   [[(0,[z19,z1,z3,z32,z4,z5])],[(0,[z0,z862,z1,z3,z4,z5]),(0,[z11,z0,z1,z739,z4,z5]),(0,[z0,z1,z3,z4,z5,z863]),(0,[z1,z3,z4,z5,z864,z6])],[(0,[z865,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z866,z6]),(0,[z0,z1,z3,z780,z5,z6]),(0,[z89,z0,z1,z3,z4,z198]),(0,[z867,z0,z1,z3,z4,z5]),(0,[z110,z0,z83,z4,z245,z6]),(0,[z868,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z869,z5,z6]),(0,[z131,z0,z1,z735,z4,z5])],[(0,[z19,z0,z1,z18,z4,z5]),(1,[z1,z3,z730,z5,z6]),(0,[z0,z1,z3,z4,z870,z6])],[(0,[z11,z577,z1,z3,z4,z5]),(0,[z0,z871,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z872]),(0,[z103,z0,z1,z715,z3,z5])],[(0,[z0,z1,z3,z4,z873,z6]),(0,[z439,z1,z3,z4,z111,z6])],[(0,[z87,z0,z1,z3,z24,z6]),(0,[z11,z0,z1,z74,z4,z5]),(0,[z11,z1,z3,z4,z5,z725]),(0,[z0,z1,z3,z4,z5,z874]),(0,[z336,z1,z3,z4,z5,z215])]],
   [[(0,[z875,z0,z1,z3,z4,z5]),(0,[z0,z1,z383,z300,z4,z6]),(0,[z59,z336,z1,z3,z4,z5])],[(0,[z19,z0,z764,z3,z4,z5]),(0,[z11,z1,z3,z4,z5,z587])],[(0,[z0,z1,z3,z4,z5,z876]),(0,[z0,z877,z3,z4,z5,z6]),(0,[z11,z1,z3,z4,z5,z265])],[(0,[z0,z1,z3,z878,z4,z6]),(0,[z19,z0,z1,z3,z4,z879]),(0,[z880,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z259]),(0,[z0,z1,z61,z137,z38,z6]),(0,[z0,z1,z84,z4,z57,z6])],[(0,[z0,z91,z3,z4,z5,z22])],[(0,[z0,z749,z83,z4,z5,z6]),(0,[z881,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z247])],[(0,[z0,z1,z3,z4,z5,z409]),(0,[z0,z1,z3,z4,z882,z6])],[(0,[z59,z19,z1,z3,z4,z5]),(0,[z101,z0,z1,z257,z4,z5]),(0,[z11,z0,z52,z3,z4,z126]),(0,[z883,z0,z1,z3,z4,z5]),(0,[z0,z1,z96,z4,z5,z215])]],
   [[(1,[z0,z1,z4,z779,z6])],[(0,[z0,z1,z884,z3,z4,z5])],[],[(0,[z36,z1,z120,z4,z5,z272])],[(0,[z0,z1,z885,z3,z4,z5]),(0,[z0,z1,z143,z3,z4,z5]),(0,[z886,z0,z1,z3,z4,z5])],[(0,[z9,z152,z3,z4,z5,z159]),(0,[z19,z1,z32,z4,z5,z57]),(0,[z0,z1,z3,z4,z5,z887]),(0,[z0,z1,z18,z43,z5,z6]),(0,[z0,z1,z833,z4,z5,z6]),(0,[z11,z0,z140,z141,z4,z5])],[(0,[z9,z152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z888]),(0,[z341,z0,z1,z3,z451,z5]),(0,[z0,z1,z3,z4,z5,z889]),(0,[z0,z1,z890,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z891])],[(0,[z36,z1,z31,z4,z5,z6]),(0,[z19,z1,z569,z3,z4,z5]),(0,[z11,z292,z1,z3,z4,z5]),(0,[z892,z0,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z893,z5,z6])],[(0,[z0,z1,z894,z3,z4,z6]),(0,[z0,z1,z3,z4,z895,z6]),(0,[z19,z194,z1,z3,z4,z5]),(0,[z19,z0,z1,z896,z4,z5]),(0,[z19,z1,z67,z3,z4,z5]),(0,[z110,z11,z0,z83,z4,z5]),(0,[z0,z1,z3,z4,z897,z6])],[(0,[z19,z0,z1,z74,z4,z5]),(0,[z0,z1,z3,z43,z379,z6]),(0,[z19,z1,z3,z4,z5,z725]),(0,[z103,z0,z1,z3,z197,z5]),(0,[z0,z1,z3,z392,z5,z308]),(0,[z0,z1,z3,z898,z5,z6]),(0,[z0,z1,z3,z4,z5,z899])],[(0,[z0,z1,z3,z4,z900,z6]),(0,[z0,z1,z3,z901,z5,z6]),(0,[z68,z1,z3,z25,z228,z6]),(0,[z902,z1,z3,z4,z5,z6]),(0,[z0,z12,z3,z144,z5,z69])],[(0,[z0,z1,z903,z3,z4,z6])],[(0,[z0,z1,z904,z4,z5,z6]),(0,[z0,z905,z3,z4,z5,z6]),(0,[z19,z36,z1,z120,z4,z5]),(0,[z438,z0,z1,z3,z4,z122]),(0,[z11,z40,z1,z3,z4,z5]),(0,[z906,z1,z3,z4,z5,z6])],[(0,[z19,z68,z1,z3,z4,z228]),(0,[z1,z3,z4,z5,z725,z149])],[(0,[z0,z1,z907,z4,z5,z6]),(0,[z0,z1,z3,z745,z5,z6]),(0,[z908,z0,z1,z3,z4,z5]),(0,[z0,z696,z3,z4,z5,z22])]],
   [[(0,[z0,z1,z3,z909,z5,z6]),(0,[z11,z274,z1,z3,z4,z5]),(0,[z0,z1,z3,z392,z5,z6]),(0,[z0,z1,z3,z325,z111,z6]),(0,[z0,z1,z910,z4,z5,z6])],[(0,[z19,z36,z1,z3,z4,z5]),(0,[z0,z1,z911,z4,z5,z6]),(0,[z912,z0,z1,z3,z4,z5]),(0,[z19,z417,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z779,z6]),(0,[z0,z1,z181,z3,z513,z4])],[(0,[z0,z1,z16,z60,z4,z6]),(0,[z19,z0,z52,z3,z4,z126]),(0,[z0,z1,z715,z3,z5,z289])],[(0,[z0,z1,z3,z4,z913,z6]),(0,[z0,z1,z3,z4,z5,z914]),(0,[z11,z0,z1,z3,z4,z111])],[(0,[z0,z1,z915,z3,z5,z6])],[(0,[z1,z3,z852,z32,z4,z5]),(0,[z1,z3,z4,z730,z5,z6]),(0,[z68,z1,z74,z4,z228,z6]),(0,[z0,z1,z3,z4,z5,z308]),(0,[z0,z916,z1,z3,z4,z5]),(0,[z0,z1,z3,z17,z300,z6])],[(0,[z36,z1,z257,z4,z5,z6]),(0,[z19,z11,z1,z3,z4,z5]),(0,[z11,z0,z1,z3,z287,z5]),(0,[z0,z1,z3,z4,z917,z6]),(0,[z0,z1,z3,z119,z112,z6])],[(0,[z152,z853,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z918,z5]),(0,[z0,z1,z3,z4,z111,z503]),(0,[z0,z1,z3,z4,z5,z919])]],
   [[(0,[z0,z1,z226,z3,z4,z6]),(0,[z19,z0,z140,z141,z4,z5]),(0,[z0,z1,z3,z782,z5,z6])],[(0,[z0,z1,z920,z4,z5,z6]),(0,[z0,z1,z921,z3,z4,z5]),(0,[z336,z11,z1,z3,z4,z5]),(0,[z110,z0,z83,z392,z5,z6]),(0,[z1,z3,z4,z5,z922,z6])],[],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z923,z5]),(0,[z0,z1,z3,z4,z5,z924]),(0,[z132,z1,z401,z3,z4,z6]),(0,[z925,z1,z3,z4,z5,z6])],[(0,[z0,z1,z805,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z926]),(0,[z0,z1,z927,z4,z5,z6]),(0,[z0,z1,z3,z4,z708,z6])],[(0,[z0,z1,z3,z4,z5,z928]),(0,[z19,z640,z1,z3,z4,z5])],[(1,[z853,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z304,z5])],[(0,[z0,z1,z120,z287,z5,z6]),(0,[z358,z19,z1,z3,z4,z5]),(0,[z0,z39,z3,z4,z126,z6]),(0,[z0,z1,z929,z3,z4,z5])]],
   [[(0,[z19,z40,z1,z3,z4,z5]),(0,[z0,z3,z4,z782,z5,z6]),(0,[z0,z1,z3,z930,z5,z6]),(0,[z0,z1,z61,z137,z5,z6])],[(0,[z11,z1,z3,z4,z5,z58]),(0,[z0,z931,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z932]),(0,[z0,z1,z257,z117,z4,z5]),(0,[z0,z1,z3,z392,z245,z6]),(0,[z0,z1,z3,z4,z933,z6]),(0,[z0,z1,z3,z934,z4,z5]),(0,[z935,z1,z3,z4,z5,z6])],[(0,[z0,z1,z16,z300,z287,z6])],[(0,[z0,z1,z3,z4,z5,z936]),(0,[z11,z439,z1,z3,z4,z5]),(0,[z937,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z373,z121])],[(0,[z0,z1,z3,z4,z5,z938]),(0,[z19,z442,z1,z3,z4,z5])],[(0,[z125,z1,z776,z4,z5,z6]),(0,[z37,z0,z1,z3,z24,z6]),(0,[z11,z37,z1,z3,z115,z5]),(0,[z19,z0,z1,z3,z4,z111]),(0,[z11,z0,z1,z3,z325,z5]),(0,[z0,z1,z939,z3,z4,z5])],[(0,[z0,z940,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z245,z308]),(0,[z0,z1,z941,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z942,z5]),(0,[z0,z1,z26,z255,z4,z6]),(0,[z68,z1,z3,z4,z304,z228]),(0,[z0,z1,z3,z43,z582,z6])],[(0,[z19,z0,z1,z3,z287,z5]),(0,[z943,z0,z1,z3,z4,z5]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z945])],[(0,[z0,z946,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z947]),(0,[z0,z1,z773,z3,z4,z121])],[(0,[z48,z153,z3,z4,z5,z6]),(0,[z0,z1,z3,z948,z5,z6]),(0,[z949,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z950,z5,z6]),(0,[z951,z1,z3,z4,z5,z6])],[(0,[z9,z152,z3,z4,z5,z409]),(0,[z0,z1,z3,z290,z4,z5])],[(0,[z0,z1,z3,z4,z879,z6]),(0,[z0,z1,z3,z952,z4,z6]),(0,[z0,z1,z3,z244,z4,z5]),(0,[z0,z1,z3,z4,z245,z6]),(0,[z175,z0,z3,z4,z5,z722]),(0,[z953,z1,z3,z4,z5,z6])],[(0,[z11,z220,z1,z3,z4,z5]),(0,[z0,z1,z954,z4,z5,z6]),(0,[z0,z1,z955,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z240])],[(0,[z0,z1,z3,z4,z5,z956])]],
   [[(0,[z0,z1,z187,z3,z5,z6]),(0,[z19,z0,z1,z920,z4,z5]),(1,[z0,z1,z957,z5,z6])],[(0,[z0,z1,z3,z4,z958,z6]),(0,[z0,z1,z3,z959,z4,z5]),(0,[z0,z1,z960,z3,z4,z5])],[(0,[z690,z153,z3,z4,z5,z6]),(0,[z19,z1,z16,z32,z4,z5]),(0,[z1,z3,z115,z730,z5,z6]),(0,[z11,z0,z1,z56,z4,z57]),(0,[z961,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z722]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z0,z1,z3,z714,z5,z6])],[(0,[z0,z1,z187,z3,z304,z5]),(0,[z504,z0,z3,z4,z5,z118])],[(0,[z0,z1,z963,z4,z5,z6]),(0,[z11,z9,z152,z3,z4,z5]),(0,[z125,z1,z32,z4,z5,z6]),(0,[z11,z0,z1,z3,z43,z44]),(0,[z439,z1,z3,z4,z245,z6])],[(0,[z9,z853,z3,z4,z5,z6]),(0,[z37,z1,z3,z115,z5,z6]),(0,[z0,z1,z896,z4,z5,z6])],[(0,[z48,z853,z3,z4,z5,z6]),(0,[z48,z11,z153,z3,z4,z5]),(0,[z87,z1,z18,z23,z5,z6])],[(0,[z1,z853,z3,z4,z5,z6]),(0,[z19,z439,z1,z3,z4,z5]),(0,[z743,z40,z1,z3,z4,z5]),(0,[z0,z1,z773,z3,z4,z5])]],
   [[(0,[z87,z1,z3,z522,z5,z6]),(0,[z19,z0,z1,z302,z5,z112]),(0,[z0,z1,z964,z3,z5,z6])],[(0,[z147,z0,z1,z3,z4,z5]),(0,[z19,z37,z1,z3,z115,z5]),(0,[z19,z0,z1,z3,z325,z5]),(0,[z19,z538,z1,z3,z4,z5]),(0,[z0,z1,z3,z965,z5,z6]),(0,[z0,z1,z3,z4,z34,z121])],[(0,[z0,z1,z3,z966,z4,z6]),(0,[z175,z0,z3,z4,z5,z118])],[(0,[z11,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z967]),(0,[z0,z1,z3,z4,z5,z968]),(0,[z969,z0,z1,z3,z4,z5]),(0,[z0,z3,z4,z126,z710,z6]),(0,[z367,z0,z1,z3,z43,z6])],[(0,[z0,z1,z3,z970,z5,z6])],[(0,[z87,z19,z1,z3,z23,z5]),(0,[z11,z0,z1,z16,z300,z4]),(0,[z0,z14,z3,z782,z5,z6])],[(0,[z0,z1,z403,z3,z4,z5]),(0,[z19,z182,z1,z3,z4,z5]),(0,[z971,z1,z3,z4,z5,z6]),(1,[z0,z1,z735,z4,z5]),(0,[z0,z1,z735,z4,z5,z6])],[(0,[z0,z1,z972,z3,z4,z6]),(0,[z36,z1,z3,z244,z4,z5]),(0,[z37,z1,z143,z3,z115,z5]),(0,[z19,z1,z3,z4,z5,z149]),(0,[z973,z0,z1,z3,z4,z5])]],
   [[(1,[z1,z776,z4,z5,z6])],[(0,[z87,z1,z3,z486,z23,z5]),(0,[z11,z196,z1,z3,z4,z5]),(1,[z0,z749,z4,z5,z6]),(0,[z974,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z957,z5,z6]),(0,[z0,z1,z56,z4,z779,z6])],[(0,[z0,z1,z3,z4,z5,z272]),(0,[z0,z1,z3,z975,z5,z6])],[(0,[z0,z1,z3,z4,z5,z976]),(0,[z87,z1,z3,z24,z23,z6]),(0,[z0,z1,z3,z4,z5,z503])],[(0,[z0,z1,z3,z4,z5,z977]),(0,[z0,z1,z978,z3,z5,z6]),(0,[z19,z1,z3,z4,z271,z5]),(0,[z167,z0,z1,z3,z410,z5]),(0,[z0,z1,z3,z4,z979,z6]),(0,[z0,z262,z3,z4,z5,z118]),(0,[z0,z1,z980,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z981]),(0,[z336,z1,z3,z4,z5,z6]),(0,[z19,z1,z61,z32,z4,z5]),(0,[z19,z0,z1,z56,z4,z57]),(0,[z110,z0,z83,z325,z5,z6]),(0,[z982,z1,z3,z4,z5,z6])],[(0,[z0,z1,z748,z4,z5,z6]),(0,[z983,z0,z1,z3,z4,z5])],[(0,[z0,z1,z984,z4,z5,z6]),(0,[z0,z1,z3,z985,z5,z6]),(0,[z19,z9,z152,z3,z4,z5]),(0,[z19,z0,z1,z3,z43,z44]),(0,[z986,z439,z1,z3,z4,z5]),(0,[z0,z1,z181,z773,z3,z4])]],
   [[(0,[z0,z1,z3,z4,z5,z987])],[(0,[z0,z1,z3,z988,z5,z6]),(0,[z0,z1,z3,z989,z5,z6]),(0,[z0,z1,z3,z4,z5,z990])],[(0,[z0,z1,z3,z4,z5,z991]),(0,[z68,z1,z255,z4,z228,z6]),(0,[z0,z91,z134,z3,z4,z5]),(0,[z19,z1,z203,z3,z4,z5])],[(0,[z553,z1,z32,z4,z5,z6]),(0,[z68,z1,z3,z522,z4,z6]),(0,[z0,z1,z992,z3,z4,z5]),(1,[z0,z3,z782,z5,z6]),(0,[z0,z1,z3,z4,z5,z993]),(0,[z336,z131,z1,z117,z4,z5])],[(0,[z110,z0,z83,z4,z5,z503]),(0,[z0,z1,z3,z4,z5,z994])],[(0,[z19,z334,z1,z3,z4,z5])],[(0,[z0,z1,z3,z325,z245,z6]),(0,[z0,z995,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z996]),(0,[z0,z1,z3,z4,z5,z997]),(0,[z0,z1,z3,z735,z4,z5]),(0,[z0,z1,z715,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z998]),(0,[z19,z0,z1,z3,z999,z5]),(0,[z19,z0,z1,z16,z300,z4]),(0,[z0,z1,z339,z4,z5,z215]),(0,[z0,z1,z1000,z4,z5,z6]),(0,[z1001,z0,z1,z3,z4,z5])],[(0,[z19,z1,z3,z852,z4,z5]),(0,[z0,z1,z26,z224,z3,z6])],[(0,[z0,z1,z617,z3,z4,z5]),(0,[z0,z1002,z3,z4,z5,z6])],[(0,[z87,z1,z148,z23,z5,z6]),(0,[z132,z1,z3,z4,z188,z6]),(0,[z0,z1,z3,z4,z1003,z5]),(0,[z0,z1,z3,z4,z5,z1004]),(0,[z0,z1,z16,z4,z779,z6])],[(0,[z0,z1,z226,z3,z4,z486]),(0,[z0,z1,z3,z1005,z4,z5]),(0,[z0,z1,z302,z5,z112,z6])],[(0,[z0,z853,z3,z4,z5,z6]),(0,[z0,z1,z1006,z4,z5,z6]),(0,[z0,z1,z1007,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1008]),(0,[z377,z0,z1,z542,z4,z5]),(0,[z0,z1,z3,z4,z245,z503]),(0,[z1009,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1010,z6]),(0,[z1011,z1,z3,z4,z5,z6]),(0,[z0,z1,z957,z5,z112,z6]),(0,[z1012,z0,z1,z3,z4,z5])],[(0,[z0,z1,z224,z3,z714,z6])],[(0,[z164,z0,z1,z3,z4,z5]),(0,[z19,z0,z1,z3,z4,z1013]),(0,[z0,z1,z16,z17,z300,z6])]],
   [[(0,[z0,z1,z1014,z4,z5,z6]),(0,[z0,z1,z3,z1015,z4,z5]),(0,[z0,z1,z3,z4,z5,z1016]),(0,[z0,z1,z3,z4,z1017,z5]),(0,[z40,z1,z3,z4,z111,z6]),(0,[z0,z1,z3,z714,z6,z44])],[(0,[z0,z1,z3,z17,z5,z6]),(1,[z0,z1,z715,z3,z5])],[(0,[z439,z1,z3,z392,z5,z6]),(0,[z0,z12,z3,z144,z5,z6]),(1,[z0,z3,z4,z710,z6]),(0,[z0,z1,z4,z779,z57,z6])],[(0,[z1018,z0,z1,z3,z4,z5]),(0,[z0,z1,z1019,z4,z5,z6])],[(0,[z689,z1,z120,z4,z5,z6]),(0,[z0,z1,z3,z163,z5,z289])],[(0,[z0,z1,z3,z1020,z4,z5]),(0,[z1021,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z486,z5]),(0,[z0,z1,z3,z4,z5,z1022]),(0,[z1023,z439,z1,z3,z4,z5]),(0,[z986,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1024,z5]),(0,[z0,z1,z302,z957,z5,z6])],[(0,[z269,z0,z134,z3,z4,z5]),(0,[z439,z1,z3,z4,z5,z308]),(0,[z808,z40,z1,z3,z4,z5]),(0,[z1025,z0,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z1026,z5,z6]),(0,[z0,z1,z32,z4,z38,z6]),(0,[z0,z1027,z3,z4,z5,z6]),(0,[z0,z1,z713,z4,z5,z6]),(0,[z11,z0,z12,z3,z144,z5]),(0,[z0,z1,z3,z4,z5,z1028]),(0,[z0,z1,z3,z4,z5,z1029])],[],[(0,[z0,z1,z3,z4,z5,z1030]),(0,[z11,z0,z1,z816,z4,z5]),(0,[z11,z1,z3,z4,z5,z634]),(0,[z0,z14,z3,z35,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1031]),(0,[z19,z0,z940,z3,z4,z5]),(0,[z0,z1,z1032,z3,z4,z6]),(0,[z336,z1,z3,z117,z4,z5])],[(0,[z36,z1,z617,z3,z4,z5])],[(0,[z439,z1,z3,z4,z5,z6]),(0,[z1,z617,z3,z32,z4,z5]),(0,[z19,z1,z3,z4,z5,z583]),(0,[z1033,z0,z1,z3,z4,z5])],[(0,[z0,z1,z1034,z4,z5,z6]),(0,[z19,z1,z3,z4,z5,z263]),(0,[z0,z1,z1035,z4,z5,z6]),(0,[z19,z0,z840,z3,z4,z5]),(0,[z1036,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1037,z6]),(0,[z0,z1,z3,z4,z5,z1038]),(0,[z0,z1,z1039,z4,z5,z6]),(0,[z1040,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z1041,z4,z5])],[(0,[z194,z1,z3,z4,z5,z265]),(0,[z50,z0,z1,z3,z25,z5]),(0,[z0,z1,z3,z137,z119,z6])]],
   [[(0,[z1,z3,z730,z23,z5,z6]),(0,[z0,z1,z3,z4,z5,z1042])],[(0,[z0,z1,z3,z1043,z4,z5]),(0,[z11,z0,z1,z255,z4,z5]),(0,[z19,z176,z1,z3,z4,z5]),(0,[z19,z573,z1,z3,z4,z5]),(1,[z1,z3,z4,z5,z725]),(0,[z0,z1,z3,z4,z5,z1044]),(0,[z0,z1,z1045,z4,z5,z6])],[(0,[z1,z776,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1046]),(0,[z0,z1,z3,z4,z1047,z5]),(0,[z0,z1,z4,z957,z5,z6])],[(0,[z11,z0,z1,z3,z24,z4]),(0,[z11,z1,z3,z4,z5,z454]),(0,[z0,z1,z3,z1048,z4,z5])],[(0,[z1049,z0,z1,z3,z4,z5]),(0,[z0,z1,z1050,z3,z4,z5]),(0,[z0,z1,z3,z829,z5,z6]),(0,[z1051,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1052])],[(0,[z0,z1,z1053,z3,z5,z6]),(0,[z0,z1,z205,z4,z57,z6]),(0,[z1054,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z714,z43,z6])],[(0,[z0,z1,z3,z730,z5,z6]),(0,[z1055,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z122,z121]),(0,[z1056,z0,z1,z3,z4,z5]),(0,[z1057,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1058,z3,z4,z6]),(0,[z0,z1,z3,z1059,z4,z5]),(0,[z0,z123,z3,z4,z5,z118]),(0,[z0,z1,z3,z1060,z4,z5]),(0,[z0,z1,z3,z43,z240,z44])]],
   [[(0,[z0,z1,z3,z4,z1061,z6]),(0,[z0,z1,z3,z410,z5,z289]),(0,[z0,z1,z3,z287,z5,z6])],[(0,[z1062,z0,z1,z3,z4,z5]),(0,[z87,z164,z1,z3,z23,z5]),(0,[z11,z0,z1,z3,z25,z5]),(0,[z11,z0,z1,z26,z224,z3]),(0,[z0,z1,z3,z1063,z4,z6])],[(0,[z125,z1,z403,z32,z4,z5]),(0,[z1,z3,z4,z708,z228,z6]),(0,[z19,z132,z1,z3,z4,z188]),(0,[z19,z0,z1,z3,z909,z5]),(0,[z19,z1,z3,z4,z476,z5])],[(0,[z0,z1,z3,z999,z5,z6]),(0,[z19,z0,z1,z3,z4,z900]),(0,[z19,z0,z12,z3,z144,z5])],[(0,[z1064,z0,z1,z3,z4,z5]),(0,[z87,z1,z3,z730,z5,z6]),(0,[z50,z0,z1,z3,z4,z5]),(0,[z19,z1,z3,z4,z5,z633]),(0,[z0,z1,z3,z1065,z5,z6])],[(0,[z0,z1,z224,z18,z5,z6]),(0,[z11,z0,z1,z927,z4,z5]),(0,[z1023,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1066,z6])],[(0,[z19,z1,z3,z4,z5,z97]),(0,[z0,z1,z3,z4,z5,z1067]),(0,[z1068,z0,z1,z3,z4,z5])],[(0,[z9,z350,z3,z4,z5,z6]),(0,[z0,z1,z776,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1069]),(0,[z68,z1,z187,z3,z228,z6])]],
   [[(0,[z1070,z1,z3,z4,z5,z6])],[(0,[z19,z36,z1,z357,z4,z5]),(0,[z99,z0,z80,z3,z4,z5]),(0,[z0,z1,z3,z325,z5,z308]),(0,[z0,z1,z61,z137,z119,z6])],[],[(0,[z0,z1,z3,z392,z5,z503])],[(0,[z19,z0,z1,z255,z4,z5]),(0,[z50,z0,z1,z187,z3,z5]),(0,[z11,z0,z1,z904,z4,z5]),(0,[z0,z1,z137,z957,z5,z6])],[(0,[z19,z1,z3,z63,z4,z5]),(0,[z0,z12,z3,z144,z5,z259])],[(0,[z0,z1,z3,z4,z1071,z6]),(0,[z604,z1,z32,z4,z5,z6]),(0,[z19,z0,z1,z3,z24,z4]),(0,[z0,z1072,z1,z3,z4,z5]),(0,[z40,z1,z3,z4,z5,z308]),(0,[z1073,z0,z1,z3,z4,z5])],[(0,[z200,z1,z32,z4,z5,z6]),(0,[z0,z1,z3,z325,z5,z6]),(0,[z0,z1,z3,z4,z5,z1074])]],
   [[(1,[z0,z1,z3,z714,z6]),(0,[z8,z0,z1,z181,z3,z4])],[(0,[z19,z1,z3,z323,z4,z5]),(0,[z0,z1,z96,z735,z4,z5])],[(0,[z1,z3,z4,z188,z708,z6]),(0,[z19,z568,z1,z3,z4,z5]),(0,[z19,z0,z1,z3,z4,z913]),(0,[z19,z53,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1075])],[(0,[z0,z1,z1076,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z407])],[(0,[z40,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z24,z4,z6]),(0,[z19,z0,z1,z3,z25,z5]),(0,[z19,z0,z1,z26,z224,z3]),(0,[z19,z220,z1,z3,z4,z5]),(0,[z11,z0,z199,z3,z4,z135]),(0,[z0,z1,z1077,z4,z5,z6]),(0,[z0,z1,z299,z224,z3,z6])],[(0,[z11,z589,z1,z3,z4,z5]),(0,[z0,z608,z3,z4,z5,z22]),(0,[z1078,z1,z3,z4,z5,z6])],[(0,[z11,z0,z1,z187,z3,z5]),(0,[z439,z1,z3,z325,z5,z6])],[(0,[z0,z1,z3,z4,z1079,z6]),(0,[z164,z0,z1,z3,z24,z4]),(0,[z0,z572,z3,z35,z5,z6]),(0,[z0,z1,z151,z5,z112,z6]),(0,[z0,z1,z3,z1080,z4,z5])]],
   [[(0,[z220,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1013,z6]),(0,[z0,z1,z224,z3,z653,z6]),(0,[z19,z1,z3,z542,z4,z5])],[(0,[z0,z1,z1081,z3,z4,z6]),(0,[z36,z1,z776,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z38]),(0,[z11,z0,z1,z3,z119,z4]),(0,[z0,z199,z3,z4,z135,z15]),(0,[z0,z621,z3,z4,z5,z22])],[(0,[z19,z371,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1082,z6]),(0,[z37,z1,z261,z3,z5,z6]),(0,[z68,z50,z1,z3,z4,z228]),(0,[z0,z1,z16,z300,z4,z6]),(1,[z0,z1,z773,z3,z4])],[(0,[z164,z0,z1,z226,z3,z4]),(0,[z0,z1,z3,z4,z5,z189])],[(0,[z19,z0,z877,z3,z4,z5]),(0,[z439,z1,z3,z4,z5,z503]),(0,[z0,z1,z3,z4,z5,z1083]),(0,[z0,z1,z3,z4,z5,z1084]),(0,[z0,z1,z3,z1085,z4,z5])],[(0,[z0,z1,z3,z4,z1086,z6]),(0,[z652,z11,z1,z3,z4,z5])],[(0,[z0,z1,z1087,z3,z4,z5]),(0,[z0,z647,z3,z144,z5,z6])]],
   [[(0,[z0,z528,z3,z4,z5,z22])],[(0,[z19,z0,z1,z3,z4,z5]),(0,[z132,z1,z434,z3,z4,z188]),(0,[z19,z689,z1,z3,z4,z5]),(0,[z1088,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z1089,z4,z5]),(0,[z19,z0,z1002,z3,z4,z5]),(0,[z0,z3,z4,z5,z722,z22])],[(0,[z1090,z0,z1,z3,z4,z5]),(0,[z0,z141,z749,z4,z5,z6]),(0,[z391,z0,z1,z117,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1091]),(0,[z0,z1,z1092,z4,z5,z6]),(0,[z0,z1,z3,z1093,z5,z6]),(0,[z11,z399,z1,z3,z4,z5]),(0,[z0,z1,z3,z119,z4,z6])],[(0,[z0,z1,z1094,z4,z5,z6]),(0,[z0,z3,z782,z144,z5,z6]),(0,[z0,z1,z3,z4,z5,z1095])],[(0,[z0,z1,z3,z4,z5,z1096]),(0,[z0,z1,z3,z1097,z5,z6]),(0,[z19,z36,z1,z32,z4,z5]),(0,[z19,z1,z3,z651,z4,z5]),(0,[z40,z1,z3,z4,z245,z6]),(0,[z0,z1,z61,z957,z5,z6])],[(0,[z19,z0,z199,z3,z4,z135]),(0,[z11,z0,z1,z1094,z4,z5]),(0,[z8,z0,z1,z773,z3,z4])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 543) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 543).take 541) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1084).take 74) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1158)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [543, 541, 74] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 148).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [148, 108] = true :=
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

end PEqualNP.Outside.L_meta_42208

theorem PEqualNP.Outside.L_meta_42208 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42208.solve