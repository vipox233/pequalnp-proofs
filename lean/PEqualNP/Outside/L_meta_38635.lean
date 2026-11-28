import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38635

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
  Nat.testBit (4276678376 * 2 ^ 32 + 4276136608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0045808584308aa0#64 ++ 0x40022c042c218455#64 ++ 0x80cf918f8471ffff#64 ++ 0xac067c8c7c238fff#64 : BitVec 256),
   (0x2112a632c5965992#64 ++ 0x81089531962cb2cc#64 ++ 0x6333ee73c79e599f#64 ++ 0x7b199f739e3cf2cc#64 : BitVec 256),
   (0x0c287058580b615b#64 ++ 0x00614382c2c05b0a#64 ++ 0x9c3c707c781fe1f6#64 ++ 0xfce1e383e3c0ff0f#64 : BitVec 256),
   (0x16807b006ac0741c#64 ++ 0x00b403d8035603a0#64 ++ 0xffc07f807fe07e1d#64 ++ 0xf7fe03fc03ff03f0#64 : BitVec 256),
   (0xdbff8000377d8000#64 ++ 0x06dffc0001bbec00#64 ++ 0xdfff80007fff8013#64 ++ 0xf6fffc0003fffc00#64 : BitVec 256),
   (0x5fff5def00000000#64 ++ 0x0afffaef78000000#64 ++ 0x7fffffff8000000f#64 ++ 0xebfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00c3818384601e09 0x00061c0c1c2300f0

def z1 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8471ffff 0xac067c8c7c238fff

def z2 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c781fe1f6 0xfce1e383e3c0ff0f

def z3 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f807fe07e1d 0xf7fe03fc03ff03f0

def z4 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c79e599f 0x7b199f739e3cf2cc

def z5 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff8000000f 0xebfffffffc000000

def z6 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff918fffffffff 0xfefffc8c7fffffff

def z7 : W := mkw 0x21122632c1865992 0x81089131960c32cc 0x63306e73c38e598c 0x5b1983739e1c72cc

def z8 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007fff8013 0xf6fffc0003fffc00

def z9 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80c3918384607e1d 0xa4061c8c1c2303f0

def z10 : W := mkw 0x0828000010090000 0x0041400000804800 0x9c3c0000781f8012 0xf4e1e00003c0fc00

def z11 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x003c007c001f81e2 0x0801e003e000fc0f

def z12 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee738000000f 0x6b199f739c000000

def z13 : W := mkw 0xdffff0587f7fe15b 0x06ffff82c3fbff0a 0xdffff07c7fffe1f7 0xfeffff83e3ffff0f

def z14 : W := mkw 0x5fff7fef6ac0741c 0x0afffbff7b5603a0 0xffffffffffe07e1f 0xffffffffffff03f0

def z15 : W := mkw 0xdfffddef377d8000 0x0efffeef79bbec00 0xffffffffffff801f 0xfffffffffffffc00

def z16 : W := mkw 0x0045008500208220 0x4002280428010411 0x80cf918f8061a66f 0xac067c8c7c030d33

def z17 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00000000479e5990 0x10000000023cf2cc

def z18 : W := mkw 0x5eed59cd00000000 0x0af76ace68000000 0x1ccc118c00000000 0x80e6608c60000000

def z19 : W := mkw 0x2157a6b7c5b6dbb2 0xc10abd35be2db6dd 0xe3ffffffc7ffffff 0xff1ffffffe3fffff

def z20 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5f3000007b8e0000 0x52f9800003dc7000

def z21 : W := mkw 0x0045008500000000 0x0002280428000000 0x00cf918f8000000f 0xa8067c8c7c000000

def z22 : W := mkw 0x04005def80000aa0 0x482002ef7c000055 0x20007fff80007fec 0x090003fffc0003ff

def z23 : W := mkw 0xc97f8085953d8aa0 0x464bfc042ca9ec55 0x003f800f801f81e2 0x0801fc007c00fc0f

def z24 : W := mkw 0x0000201040024112 0x0000010082001208 0x00306070401e4196 0x780183038200f20c

def z25 : W := mkw 0x16805b002ac0340c 0x00b402d8015601a0 0xffc01f803fe03e09 0x87fe00fc01ff01f0

def z26 : W := mkw 0x24007f32c8827d9e 0x812003f9964413ec 0x20007ff380007f8c 0x090003ff9c0003fc

def z27 : W := mkw 0x3792ff32efd67d9e 0x81bc97f9977eb3ec 0xfff3fff3fffe7f9f 0xffff9fff9ffff3fc

def z28 : W := mkw 0x040059000800240c 0x002002c800400120 0x0000118000002600 0x0000008c00000130

def z29 : W := mkw 0x04007b004880741c 0x002003d8024403a0 0x20007f8000007e0c 0x010003fc000003f0

def z30 : W := mkw 0x1280000022400000 0x0094000001120000 0xdfc000007fe00011 0xf6fe000003ff0000

def z31 : W := mkw 0x04005def00000000 0x082002ef78000000 0x20007fff8000000c 0x090003fffc000000

def z32 : W := mkw 0x5bff000000000000 0x02dff80000000000 0x5fff800000000003 0xe2fffc0000000000

def z33 : W := mkw 0x0000a200c4905890 0x00000510062482c4 0x6303ee03c790599f 0x7b181f701e3c82cc

def z34 : W := mkw 0x53d70da700000000 0x0a9eb86d38000000 0x63c38f8380000009 0x031e1c7c1c000000

def z35 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7f306e7000000000 0x43f9837380000000

def z36 : W := mkw 0x0000220040805010 0x0000011002040280 0x63006e004780581d 0x73180370023c02c0

def z37 : W := mkw 0x168059002a40240c 0x00b402c801520120 0x9cc0118038602600 0x84e6008c01c30130

def z38 : W := mkw 0x5eed79dd580b615b 0x0af76bceeac05b0a 0x9cfc71fc781fe1f6 0xfce7e38fe3c0ff0f

def z39 : W := mkw 0x2112062201841000 0x81089031100c2080 0x63000e0003800000 0x03180070001c0000

def z40 : W := mkw 0x16805b0022c01404 0x00b402d8011600a0 0x7fc07f8007e01e0d 0xe3fe03fc003f00f0

def z41 : W := mkw 0xd3d7800027748000 0x069ebc00013ba400 0x43c3800007e00001 0x021e1c00003f0000

def z42 : W := mkw 0x2112843285160982 0x810894219428b04c 0x6333ee73801e018f 0x6b199f739c00f00c

def z43 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cc118c0471fff0 0x8406608c60238fff

def z44 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7fc07f807b80000d 0xf3fe03fc03dc0000

def z45 : W := mkw 0x1680590000000000 0x00b402c800000000 0x7fc07f800000000d 0xe3fe03fc00000000

def z46 : W := mkw 0xdffffb007ffdf41c 0x06ffffd803ffefa0 0xffffff807ffffe1f 0xf7fffffc03fffff0

def z47 : W := mkw 0x37d7ffb7eff6ffbe 0xc1bebffdbf7fb7fd 0xffffffffffffffff 0xffffffffffffffff

def z48 : W := mkw 0xd3d7800027748000 0x069ebc00013ba400 0x43f3800047fe0013 0x721f9c00023ff000

def z49 : W := mkw 0xdfffd048377d8000 0x06fffe8241bbec00 0xdffff07c7fff8017 0xfeffff83e3fffc00

def z50 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x2033ee73801e598e 0x09019f739c00f2cc

def z51 : W := mkw 0x2112862285941880 0x81089431142ca0c4 0x63038e038790599f 0x2b181c701c3c82cc

def z52 : W := mkw 0x0000800084308aa0 0x4000040004218455 0x800000000471fff0 0x0400000000238fff

def z53 : W := mkw 0x0c285058180b214b 0x00614282c0c0590a 0x9c3c107c381fa1e2 0x8ce1e083e1c0fd0f

def z54 : W := mkw 0x0c28504800000000 0x0061428240000000 0x1c3c707c00000006 0xe8e1e383e0000000

def z55 : W := mkw 0x5fff7dff580b615b 0x0afffbeffac05b0a 0xfffffffff81fe1ff 0xffffffffffc0ff0f

def z56 : W := mkw 0x0045008500000000 0x0002280428000000 0x80cf918f84607e1f 0xac067c8c7c2303f0

def z57 : W := mkw 0xdaed8000377d8000 0x06d76c0001bbec00 0x9ccc00007fff8010 0x94e6600003fffc00

def z58 : W := mkw 0x697f84ff85160982 0x8b4bfc27fc28b04c 0x003f807f801e0182 0x0801fc03fc00f00c

def z59 : W := mkw 0x0000000080000880 0x0000000004000044 0x000000038000598c 0x080000001c0002cc

def z60 : W := mkw 0x2112863285961982 0x81089431942cb0cc 0x63338e73879e198b 0x0b199c739c3cf0cc

def z61 : W := mkw 0x5fff5def22400000 0x0afffaef79120000 0xffffffffffe0001f 0xffffffffffff0000

def z62 : W := mkw 0x0157808585348aa0 0x400abc042c29a455 0xc3ff918fc7ffffff 0xfe1ffc8c7e3fffff

def z63 : W := mkw 0x0000808584308aa0 0x400004042c218455 0x8000118f8471fffc 0x0c00008c7c238fff

def z64 : W := mkw 0x2d3af67add9f79db 0x8169d7b3d6ecfbce 0xff3ffe7fff9ff9ff 0xfff9fff3fffcffcf

def z65 : W := mkw 0x2512ff32cd967d9e 0x812897f9966cb3ec 0x6333fff3c79e7f9f 0x7b199fff9e3cf3fc

def z66 : W := mkw 0x7fffffffc5965992 0x8bfffffffe2cb2cc 0x7fffffffc79e599f 0xfbfffffffe3cf2cc

def z67 : W := mkw 0x0c28504818092049 0x0061428240c04902 0x9c3c707c3801a066 0xece1e383e1c00d03

def z68 : W := mkw 0x168059002a40240c 0x00b402c801520120 0xffc07f803860260d 0xe7fe03fc01c30130

def z69 : W := mkw 0x0045800084308aa0 0x40022c0004218455 0x80cf80000471fff3 0xa4067c0000238fff

def z70 : W := mkw 0xdfba70587b4f615b 0x06fdd382c3da7b0a 0xdf3c707c7b9fe1f6 0xfef9e383e3dcff0f

def z71 : W := mkw 0x04455def00000000 0x08222aef78000000 0x20cfffff8000000f 0xa9067ffffc000000

def z72 : W := mkw 0xdbff8da7377d8000 0x0edffc6d39bbec00 0xffff8f83ffff801b 0xf7fffc7c1ffffc00

def z73 : W := mkw 0x0000008580000aa0 0x400000042c000055 0x800c118f8011fffe 0xac00608c7c008fff

def z74 : W := mkw 0x040070104802611a 0x0020038082401308 0x9c307070781e6196 0xfce1838383c0f30c

def z75 : W := mkw 0x2d3af47add1f69db 0x8169d7a3d6e8fb4e 0x9c3ff07ff81fe1f6 0xfce1ff83ffc0ff0f

def z76 : W := mkw 0x2000a210c5b6dbb2 0xc1000510862db6dd 0x8000000047fffff0 0x14000000023fffff

def z77 : W := mkw 0xd3d78085a7748aa0 0x469ebc042d3ba455 0x43c3818387e01e09 0x021e1c0c1c3f00f0

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c100c0011e1f6 0xac00608060008f0f

def z80 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c78e1809 0x53199f739e3c70c0

def z81 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0x63c00f8007e01e09 0x031e007c003f00f0

def z82 : W := mkw 0x0d3a546a00000000 0x0069d2a350000000 0x7f3ffe7f8000000f 0xebf9fff3fc000000

def z83 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00cf918f801181ef 0xa8067c8c7c008c0f

def z84 : W := mkw 0x8c28f0587f7fe15b 0x04614782c3fbff0a 0x9c3c707c7fffe1f6 0xfce1e383e3ffff0f

def z85 : W := mkw 0x2112263241865112 0x81089131920c3288 0x6333ee73c38e000f 0x7b199f739e1c7000

def z86 : W := mkw 0xdaed000032698000 0x06d7680001934c00 0x9ccc000038618000 0x84e6600001c30c00

def z87 : W := mkw 0x1ea87b587acb755f 0x00f543dac3d65baa 0xfffc7ffc7fffffff 0xffffe3ffe3ffffff

def z88 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x000f800f801181e2 0x08007c007c008c0f

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0x000380038000000f 0x28001c001c000000

def z90 : W := mkw 0x1280000022400000 0x0094000001120000 0x43c0000007e00001 0x021e0000003f0000

def z91 : W := mkw 0x0c287258588b715b 0x00614392c2c45b8a 0xff3c7e7c7f9ff9ff 0xfff9e3f3e3fcffcf

def z92 : W := mkw 0x0000220040805010 0x0000011002040280 0x0000000047805810 0x10000000023c02c0

def z93 : W := mkw 0xdeed59003a69a40c 0x06f76ac801d34d20 0x9ccc11803861a600 0x84e6608c01c30d30

def z94 : W := mkw 0x0000800005140000 0x000004000028a000 0x00000000479e0010 0x10000000023cf000

def z95 : W := mkw 0x2512ffffc5965992 0x892897fffe2cb2cc 0x6333ffffc79e599f 0x7b199ffffe3cf2cc

def z96 : W := mkw 0x0c28504818092049 0x0061428240c04902 0x1c00000038000000 0x00e0000001c00000

def z97 : W := mkw 0x0000800084100880 0x0000040004208044 0x000380038410599f 0x28001c001c2082cc

def z98 : W := mkw 0x0045008500208220 0x4002280428010411 0x80cc118c0061a660 0x8406608c60030d33

def z99 : W := mkw 0x80008000377d8000 0x0400040001bbec00 0x800000007fff8010 0x1400000003fffc00

def z100 : W := mkw 0x0045a095dc3bebfb 0x40022d04aee1df5f 0x80cf918ffc7fffff 0xbc067c8c7fe3ffff

def z101 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00cf918f84601e0f 0xa8067c8c7c2300f0

def z102 : W := mkw 0x0000008580000aa0 0x400000042c000055 0x0000118f80007fec 0x0800008c7c0003ff

def z103 : W := mkw 0x52c5098500000000 0x0a96284c28000000 0x00c0018000000000 0x0006000c00000000

def z104 : W := mkw 0x0000220040805010 0x0000011002040280 0x20006e000000580c 0x01000370000002c0

def z105 : W := mkw 0x000000002a40240c 0x0000000001520120 0x8000000038602600 0x0400000001c30130

def z106 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff900c7fffe1f7 0xfefffc8063ffff0f

def z107 : W := mkw 0xfffff67afffff9db 0x87ffffb3d7ffffce 0xfffffe7ffffff9ff 0xfffffff3ffffffcf

def z108 : W := mkw 0x2000820085941880 0x81000410042ca0c4 0x0000000007801800 0x00000000003c00c0

def z109 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c3c607c781f81e2 0x58e1e303e3c0fc0f

def z110 : W := mkw 0x16807b106ac2751e 0x00b403d8835613a8 0xfff07ff07ffe7f9f 0xffff83ff83fff3fc

def z111 : W := mkw 0xc86d000010298000 0x0643680000814c00 0x000c000000018000 0x0000600000000c00

def z112 : W := mkw 0x81128000377d8000 0x0408940001bbec00 0xc33380007fff8013 0x76199c0003fffc00

def z113 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffcc7f8c7ff1ffff 0xfffe63fc63ff8fff

def z114 : W := mkw 0x2112263241865112 0x81089131920c3288 0x63306e70439e4196 0x7b198373821cf20c

def z115 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7f006e007b800000 0x53f8037003dc0000

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c0118004607e1d 0xa406008c002303f0

def z117 : W := mkw 0x12c5800026708000 0x00962c0001338400 0xdfcf80007ff18013 0xf6fe7c0003ff8c00

def z118 : W := mkw 0xdbba8000377d8000 0x06ddd40001bbec00 0xdf3000007fff8010 0x56f9800003fffc00

def z119 : W := mkw 0x040070584802615b 0x00200382c240130a 0x0000707c000061e4 0x08000383e000030f

def z120 : W := mkw 0x20002632c0825992 0x81000131960412cc 0x20006e738000598c 0x090003739c0002cc

def z121 : W := mkw 0x5fff7fef40805010 0x0afffbff7a040280 0x7fffffffc780581f 0xfbfffffffe3c02c0

def z122 : W := mkw 0x16c5d98584308aa0 0x40b62ecc2c218455 0xffcfff8f8471ffff 0xeffe7ffc7c238fff

def z123 : W := mkw 0x0045808584100880 0x00022c042c208044 0x00cf918f8410599f 0xa8067c8c7c2082cc

def z124 : W := mkw 0x168079006a40641c 0x00b403c803520320 0x9cc0718078606614 0xf4e6038c03c30330

def z125 : W := mkw 0x5bff04ef00000000 0x0adff82778000000 0x5fff807f80000003 0xeafffc03fc000000

def z126 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5f3f80007b9f8002 0x52f9fc0003dcfc00

def z127 : W := mkw 0x37927f326bc6751e 0x81bc93f9935e33a8 0xfff07ff07fee7e1d 0xf7ff83ff83ff73f0

def z128 : W := mkw 0x2512f632cd96799a 0x812897b1966cb3cc 0xff33fe73ff9e799f 0xfff99ff39ffcf3cc

def z129 : W := mkw 0x0000201040024112 0x0000010082001208 0x0000607000004184 0x080003038000020c

def z130 : W := mkw 0x2112a632efd67d9e 0x81089531977eb3ec 0xe333ee73fffe7f9f 0x7f199f739ffff3fc

def z131 : W := mkw 0x5fff5def10090000 0x0afffaef78804800 0xfffffffff81f801f 0xffffffffffc0fc00

def z132 : W := mkw 0x493a046a00000000 0x0a49d02350000000 0x0030007000000000 0x0001800380000000

def z133 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff800fffff81f3 0xfefffc007ffffc0f

def z134 : W := mkw 0x2112263241865112 0x81089131920c3288 0x63306e70438e0000 0x53198373821c7000

def z135 : W := mkw 0x5fffddef84308aa0 0x4afffeef7c218455 0xffffffff8471ffff 0xeffffffffc238fff

def z136 : W := mkw 0x16c5fb85eef0febc 0x40b62fdc2f7787f5 0xffc3ff83ffe07e1d 0xf7fe1ffc1fff03f0

def z137 : W := mkw 0x1280000022400000 0x0094000001120000 0x5f0000007b800000 0x52f8000003dc0000

def z138 : W := mkw 0xdbff0000334d0000 0x06dff800019a6800 0x5fff80007b8e0003 0xf2fffc0003dc7000

def z139 : W := mkw 0x0c28504818092049 0x0061428240c04902 0x9c0c100c3801a060 0x84e0608061c00d03

def z140 : W := mkw 0x093a8000151d0000 0x0049d40000a8e800 0xdf3f80007f9f8013 0xf6f9fc0003fcfc00

def z141 : W := mkw 0x17925d2200000000 0x00bc92e910000000 0x7ff3fff38000000f 0xebff9fff9c000000

def z142 : W := mkw 0x000022006ac0741c 0x00000110035603a0 0x800000007fe07e10 0x1400000003ff03f0

def z143 : W := mkw 0x0c285058100b0143 0x00614282c080580a 0x1c3c707c001f81e6 0xe8e1e383e000fc0f

def z144 : W := mkw 0x697fa6ffc5965992 0x8b4bfd37fe2cb2cc 0x633fee7fc79e599f 0x7b19ff73fe3cf2cc

def z145 : W := mkw 0x2d3a767a598f715b 0x8169d3b3d2cc7b8a 0x7f306e707b8e0000 0x53f9837383dc7000

def z146 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0x63000e0003800000 0x03180070001c0000

def z147 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff91807ffffe1f 0xf6fffc8c03fffff0

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000118000007e0c 0x0000008c000003f0

def z149 : W := mkw 0x168059002a40240c 0x00b402c801520120 0x9cc011803c607e1d 0xa4e6008c01e303f0

def z150 : W := mkw 0x2157a632c5b6d992 0x810abd31962db6cc 0xe3ffee73c7ffd99f 0xff1fff739e3ffecc

def z151 : W := mkw 0x2112a622c5945890 0x81089531162ca2c4 0x6303ee03c780581d 0x73181f701e3c02c0

def z152 : W := mkw 0x0c28504818092049 0x0061428240c04902 0x9c3c100c781fa072 0xf4e1e08063c0fd03

def z153 : W := mkw 0x5fff59cd00000000 0x0affface68000000 0x5fff918c00000003 0xe2fffc8c60000000

def z154 : W := mkw 0x57d75def00000000 0x0abebaef78000000 0x63c3ffff8000000d 0x0b1e1ffffc000000

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0x63006e000000000d 0x6318037000000000

def z156 : W := mkw 0x0045000000208000 0x0002280000010400 0x80cc000000618000 0x8406600000030c00

def z157 : W := mkw 0x1ea87b587acb755f 0x00f543dac3d65baa 0x7f306e707b8e0000 0x53f9837383dc7000

def z158 : W := mkw 0xffffff32fffffd9e 0x87fffff997ffffec 0xfffffff3ffffff9f 0xffffffff9ffffffc

def z159 : W := mkw 0xdfffd9cd377d8000 0x0efffece69bbec00 0xdfff918c7fff8013 0xf6fffc8c63fffc00

def z160 : W := mkw 0x16c5fb85eef0febc 0x40b62fdc2f7787f5 0xffcfff8ffff1ffff 0xfffe7ffc7fff8fff

def z161 : W := mkw 0x5fff5def80000aa0 0x4afffaef7c000055 0x7fffffff80007fef 0xebfffffffc0003ff

def z162 : W := mkw 0x497f84ef84308aa0 0x4a4bfc277c218455 0x80ff91ff8471ffff 0xac07fc8ffc238fff

def z163 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x000f918f8011ffee 0x08007c8c7c008fff

def z164 : W := mkw 0x0157800005348000 0x000abc000029a400 0xc3ff800047ff8013 0xf61ffc00023ffc00

def z165 : W := mkw 0x5bba000000000000 0x02ddd00000000000 0x5f30000000000000 0x42f9800000000000

def z166 : W := mkw 0x2112862285941880 0x81089431142ca0c4 0x63038e0387801809 0x03181c701c3c00c0

def z167 : W := mkw 0xc97f8000153d8000 0x064bfc0000a9ec00 0x003f8000001f8002 0x0001fc000000fc00

def z168 : W := mkw 0xfbffa632f7ffd992 0x87dffd3197bffecc 0xffffee73ffffd99f 0xffffff739ffffecc

def z169 : W := mkw 0x2c28f258dd9f79db 0x81614792c6ecfbce 0x9c3c707c7f9ff9f6 0xfce1e383e3fcffcf

def z170 : W := mkw 0x2112a210c5965992 0x81089510862cb2cc 0x43338000479e5993 0x72199c00023cf2cc

def z171 : W := mkw 0x497f04ef00000000 0x0a4bf82778000000 0x003f807f80000002 0x0801fc03fc000000

def z172 : W := mkw 0x0400700048006018 0x0020038002400300 0x9c00700078006014 0xf4e0038003c00300

def z173 : W := mkw 0x2512f67acd9679db 0x812897b3d66cb3ce 0x6333fe7fc79e79ff 0x7b199ff3fe3cf3cf

def z174 : W := mkw 0x2d7ff6ffddbffbfb 0xc16bffb7feedffdf 0xffffffffffffffff 0xffffffffffffffff

def z175 : W := mkw 0x0000a200eef0febc 0x40000510077787f5 0x800000007ff1fff0 0x1400000003ff8fff

def z176 : W := mkw 0x215786a785b49aa0 0xc10abc353c2da4d5 0xe3cf9f8f87f1ffff 0xaf1e7cfc7c3f8fff

def z177 : W := mkw 0xdbff8422377d8000 0x06dffc2111bbec00 0xffffee73ffff801f 0xffffff739ffffc00

def z178 : W := mkw 0x5ea8594800000000 0x0af542ca40000000 0x1c00000000000000 0x00e0000000000000

def z179 : W := mkw 0x1ea87b486ac0741c 0x00f543da435603a0 0xfffc7ffc7fe07e1f 0xffffe3ffe3ff03f0

def z180 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x9cc011807fe07e10 0x94e6008c03ff03f0

def z181 : W := mkw 0x0c6df0dddc3bebfb 0x40636f86eee1df5f 0x9cfff1fffc7fffff 0xfce7ff8fffe3ffff

def z182 : W := mkw 0xc97f8000153d8000 0x064bfc0000a9ec00 0x9c3f8000781f8012 0xf4e1fc0003c0fc00

def z183 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80c381838471fff9 0x04061c0c1c238fff

def z184 : W := mkw 0x12c58b85a6f09ea4 0x40962c5c2d3784f5 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z185 : W := mkw 0x015704a700000000 0x000ab82538000000 0x63ffffff8000000f 0xeb1ffffffc000000

def z186 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x63306e70479e5990 0x53198373823cf2cc

def z187 : W := mkw 0x0c6d50cd00000000 0x00636a8668000000 0x1cfff1ff8000000f 0xe8e7ff8ffc000000

def z188 : W := mkw 0x1280000022400000 0x0094000001120000 0xdfc011807fe07e1d 0xf6fe008c03ff03f0

def z189 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0xffc00f807fe01e19 0xf7fe007c03ff00f0

def z190 : W := mkw 0xa000a210f7ffd992 0x8500051087bffecc 0x800000007fffd990 0x1400000003fffecc

def z191 : W := mkw 0x2c28767ad88b79db 0x816143b3d6c45bce 0xbc3c7e7ff81ff9fe 0xfde1e3f3ffc0ffcf

def z192 : W := mkw 0x0045800004308000 0x00022c0000218400 0x80cf800004718013 0xa4067c0000238c00

def z193 : W := mkw 0x0112800005140000 0x000894000028a000 0x43338000479e0013 0x72199c00023cf000

def z194 : W := mkw 0x04007b004880741c 0x002003d8024403a0 0x63007f8047807e1d 0x731803fc023c03f0

def z195 : W := mkw 0x0000201040024112 0x0000010082001208 0x00306070400e0000 0x5001830382007000

def z196 : W := mkw 0x0045800004308000 0x00022c0000218400 0x80cf900c0471e1f7 0xac067c8060238f0f

def z197 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x9cff8000387f8002 0x84e7fc0001c3fc00

def z198 : W := mkw 0x1680fb00eed07c9c 0x00b407d8077683e4 0xffc3ff83fff07f9f 0xfffe1ffc1fff83fc

def z199 : W := mkw 0x5bff008500000000 0x02dff80428000000 0x5fff918f8000000f 0xeafffc8c7c000000

def z200 : W := mkw 0x0000200048006018 0x0000010002400300 0x8000000078006010 0x1400000003c00300

def z201 : W := mkw 0x92808000377d8000 0x0494040001bbec00 0xdfc000007fff8011 0xf6fe000003fffc00

def z202 : W := mkw 0x05125def00000000 0x082892ef78000000 0x6333ffff8000000f 0x6b199ffffc000000

def z203 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff84607e1f 0xeffffffffc2303f0

def z204 : W := mkw 0x5eedd9cd84308aa0 0x4af76ece6c218455 0x9ccf918f8471ffff 0xace67c8c7c238fff

def z205 : W := mkw 0x0828004800000000 0x0041400240000000 0x003c007c00000002 0x0801e003e0000000

def z206 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x63c07f8007e07e0d 0x031e03fc003f03f0

def z207 : W := mkw 0x2112843285160982 0x810894219428b04c 0x00338073801e0182 0x08019c039c00f00c

def z208 : W := mkw 0x0c6df0dddc3bebfb 0x40636f86eee1df5f 0x9c3ff07ff81fe1f6 0xfce1ff83ffc0ff0f

def z209 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdff000007fee0011 0xf6ff800003ff7000

def z210 : W := mkw 0xdbff8085377d8000 0x06dffc0429bbec00 0xdfff918fffff801f 0xfefffc8c7ffffc00

def z211 : W := mkw 0x0000800004308000 0x0000040000218400 0x8000000004718010 0x0400000000238c00

def z212 : W := mkw 0xdffffb85fffdfebc 0x46ffffdc2fffeff5 0xffffff8fffffffff 0xfffffffc7fffffff

def z213 : W := mkw 0x4d7f54ef00000000 0x0a6bfaa778000000 0x1c3ff07f80000006 0xe8e1ff83fc000000

def z214 : W := mkw 0xdbffa20077fdd010 0x06dffd1003bfee80 0xffffee007fffd81f 0xf7ffff7003fffec0

def z215 : W := mkw 0xdfff5def334d0000 0x0efffaef799a6800 0x7ffffffffb8e000f 0xfbffffffffdc7000

def z216 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x1cff91ff80000002 0x88e7fc8ffc000000

def z217 : W := mkw 0x2045a6b7c4b2dbb2 0xc1022d35be2596dd 0xa0cfffff8471ffff 0xad067ffffc238fff

def z218 : W := mkw 0x0c2870584802615b 0x00614382c240130a 0x1c3c707c000061e6 0xe8e1e383e000030f

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c000000118012 0xa400600000008c00

def z220 : W := mkw 0x0c28f058dc1b69db 0x00614782c6e0db4e 0x9c3ff07ffc1ff9ff 0xfce1ff83ffe0ffcf

def z221 : W := mkw 0x2000a210dd9f79db 0x8100051086ecfbce 0x800000007f9ff9f0 0x1400000003fcffcf

def z222 : W := mkw 0x08282010500b4112 0x0041410082805a08 0x9c3c6070781fc196 0xfce1e30383c0fe0c

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0018004601e09 0x0006000c002300f0

def z224 : W := mkw 0x215786a785b49aa0 0xc10abc353c2da4d5 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z225 : W := mkw 0x00002010580b615b 0x0000010082c05b0a 0x80000000781fe1f0 0x1400000003c0ff0f

def z226 : W := mkw 0x0112042200000000 0x0008902110000000 0x63038e0380000009 0x03181c701c000000

def z227 : W := mkw 0x1680fb00eef0febc 0x40b407d8077787f5 0xffc07f807ff1fffd 0xf7fe03fc03ff8fff

def z228 : W := mkw 0x1aa8000032490000 0x00d5400001924800 0xdffc00007fff8013 0xf6ffe00003fffc00

def z229 : W := mkw 0xc97f8000377d8000 0x064bfc0001bbec00 0x803f80007fff8012 0x1401fc0003fffc00

def z230 : W := mkw 0xdeed7b007ae9f41c 0x06f76bd803d74fa0 0xffcc7f807fe1fe1d 0xf7fe63fc03ff0ff0

def z231 : W := mkw 0xdfff5def32698000 0x0efffaef79934c00 0xffffffffb861800f 0xeffffffffdc30c00

def z232 : W := mkw 0xd392000023440000 0x069c9000011a2000 0x4300000003800000 0x02180000001c0000

def z233 : W := mkw 0x0828000010090000 0x0041400000804800 0x1c300000780e0000 0x50e1800003c07000

def z234 : W := mkw 0x16807b107acb755f 0x00b403d883d65baa 0xffc07f807ffffffd 0xf7fe03fc03ffffff

def z235 : W := mkw 0x2157a6b7c5965992 0x810abd35be2cb2cc 0x63ffffffc79e599f 0xfb1ffffffe3cf2cc

def z236 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8011e1ff 0xeffffffffc008f0f

def z237 : W := mkw 0x2112842285140880 0x810894211428a044 0x0003800380000000 0x00001c001c000000

def z238 : W := mkw 0x88288000377d8000 0x0441440001bbec00 0x9c3c00007fff8012 0xf4e1e00003fffc00

def z239 : W := mkw 0x000022006ac0741c 0x00000110035603a0 0xe3006e007fe07e1d 0x7718037003ff03f0

def z240 : W := mkw 0xc97f84ef153d8000 0x0e4bfc2778a9ec00 0x003f807f801f8002 0x0801fc03fc00fc00

def z241 : W := mkw 0x5fff5d6a00000000 0x0afffaeb50000000 0x7fffee7000000003 0xe3ffff7380000000

def z242 : W := mkw 0x5eed7bcd6ac0741c 0x0af76bde6b5603a0 0xffcc7f8c7fe07e1d 0xf7fe63fc63ff03f0

def z243 : W := mkw 0x0112800085140880 0x000894000428a044 0x43338003c79e599f 0x7a199c001e3cf2cc

def z244 : W := mkw 0xdfba7b007bcd741c 0x06fdd3d803de6ba0 0x7f306e007b8e0000 0x53f9837003dc7000

def z245 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c306070780e0000 0x50e1830383c07000

def z246 : W := mkw 0x5fffddef04308000 0x0afffeef78218400 0xffffffff8471801f 0xeffffffffc238c00

def z247 : W := mkw 0x5eed59cd2a40240c 0x0af76ace69520120 0x9ccc118c38602600 0x84e6608c61c30130

def z248 : W := mkw 0x0045800084308880 0x00022c0004218444 0x80cf80038471d99f 0xac067c001c238ecc

def z249 : W := mkw 0x5bff042200000000 0x02dff82110000000 0x7fffee738000000f 0xebffff739c000000

def z250 : W := mkw 0x0000201040024112 0x0000010082001208 0x00000000401e4190 0x100000000200f20c

def z251 : W := mkw 0x04007b004880741c 0x002003d8024403a0 0xa0c07f8004607e1d 0xa50603fc002303f0

def z252 : W := mkw 0x0045008500208220 0x4002280428010411 0x80cc118c0071e7f6 0xac06608c60038f3f

def z253 : W := mkw 0x0c28704848006018 0x0061438242400300 0x9c3c707c78006016 0xfce1e383e3c00300

def z254 : W := mkw 0x1392800027540000 0x009c9400013aa000 0xdff380007ffe0013 0xf6ff9c0003fff000

def z255 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x63006e00479e599d 0x73180370023cf2cc

def z256 : W := mkw 0x04007b004880741c 0x002003d8024403a0 0x20006e0000000000 0x0100037000000000

def z257 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8461be69 0x84067c8c7c230df3

def z258 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x800f800f8471fff2 0x0c007c007c238fff

def z259 : W := mkw 0x53d70da700000000 0x0a9eb86d38000000 0x63cf9f8f8000000f 0xab1e7cfc7c000000

def z260 : W := mkw 0x16c5fb006ef0f41c 0x00b62fd8037787a0 0xffcfff807ff1fe1f 0xf7fe7ffc03ff8ff0

def z261 : W := mkw 0x5fff5dff100b0143 0x0afffaeff880580a 0x7fffffff801f81ef 0xebfffffffc00fc0f

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030607000000006 0x6801830380000000

def z263 : W := mkw 0x21122632c0825992 0x81089131960412cc 0x6333ee738000598f 0x6b199f739c0002cc

def z264 : W := mkw 0x0400700048006018 0x0020038002400300 0x9c0c700c7811e1f6 0xfce0638063c08f0f

def z265 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7f33ee738000000f 0x6bf99f739c000000

def z266 : W := mkw 0x00000010100b0143 0x000000008080580a 0x00000000001f81e0 0x000000000000fc0f

def z267 : W := mkw 0x1280090000000000 0x0094004800000000 0x63c00f8000000009 0x031e007c00000000

def z268 : W := mkw 0x0045a095c432cbb2 0x40022d04ae21965d 0x80fff1ffc47fffff 0xfc07ff8ffe23ffff

def z269 : W := mkw 0xfbff8432b77f8982 0x87dffc2195bbfc4c 0xdfff8073ffff8193 0xfefffc039ffffc0c

def z270 : W := mkw 0x0000a010c4124992 0x000005008620924c 0x0033e073c41e599f 0x78019f039e20f2cc

def z271 : W := mkw 0x5fff504800000000 0x02fffa8240000000 0x5ffff07c00000007 0xeaffff83e0000000

def z272 : W := mkw 0x5bff0da700000000 0x0adff86d38000000 0x7fff8f838000000b 0xe3fffc7c1c000000

def z273 : W := mkw 0x0000800084308aa0 0x4000040004218455 0x0000000004601e00 0x00000000002300f0

def z274 : W := mkw 0x1ea87b587acb755f 0x00f543dac3d65baa 0xfff07ff07fee7e1d 0xf7ff83ff83ff73f0

def z275 : W := mkw 0x00000b0000801404 0x00000058000400a0 0x20000f8000001e08 0x0100007c000000f0

def z276 : W := mkw 0x0045800004308000 0x00022c0000218400 0x000f800000118002 0x00007c0000008c00

def z277 : W := mkw 0xdbff8085377d8220 0x46dffc0429bbec11 0xdfff918c7fffa673 0xf6fffc8c63fffd33

def z278 : W := mkw 0x5fba7d7a580b615b 0x0afdd3ebd2c05b0a 0xff3c7e7c781fe1f6 0xfff9e3f3e3c0ff0f

def z279 : W := mkw 0x0000008580000aa0 0x400000042c000055 0x80c0118f84607ffd 0xac06008c7c2303ff

def z280 : W := mkw 0xfbba263273cf5112 0x87ddd131939e7a88 0x7f306e707b8e0000 0x53f9837383dc7000

def z281 : W := mkw 0x5bff0def00000000 0x0adff86f78000000 0x63ff8fff8000000b 0x0b1ffc7ffc000000

def z282 : W := mkw 0x0045008500000000 0x0002280428000000 0x80cf918f8011e1ff 0xac067c8c7c008f0f

def z283 : W := mkw 0x0000000022400000 0x0000000001120000 0x800000007fe00010 0x1400000003ff0000

def z284 : W := mkw 0x497f04ef00000000 0x0a4bf82778000000 0x00ff91ff8000000f 0xa807fc8ffc000000

def z285 : W := mkw 0x5fff5def2a40240c 0x0afffaef79520120 0xffffffffb860260f 0xeffffffffdc30130

def z286 : W := mkw 0x0400590000000000 0x002002c800000000 0x20007f800000000c 0x010003fc00000000

def z287 : W := mkw 0x1680590000000000 0x00b402c800000000 0x7f006e0000000000 0x43f8037000000000

def z288 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7ffc7ffc00000000 0xc3ffe3ffe0000000

def z289 : W := mkw 0x0c6d70dd580b615b 0x00636b86eac05b0a 0x9cfff1fff81fe1ff 0xfce7ff8fffc0ff0f

def z290 : W := mkw 0x497f84ef84308aa0 0x4a4bfc277c218455 0x003f807f801181e2 0x0801fc03fc008c0f

def z291 : W := mkw 0x2d3af67ac5965992 0x8169d7b3d62cb2cc 0x7f3ffe7fc79e599f 0xfbf9fff3fe3cf2cc

def z292 : W := mkw 0xdbffa0107f7fe15b 0x06dffd0083fbff0a 0xdfff80007fffe1f3 0xf6fffc0003ffff0f

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000104196 0x280000000000820c

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c011800000000d 0xa006008c00000000

def z295 : W := mkw 0x0112000001040000 0x0008900000082000 0x43300000438e0000 0x52198000021c7000

def z296 : W := mkw 0x53d70da700000000 0x0a9eb86d38000000 0x63f3eff38000000f 0x6b1f9f7f9c000000

def z297 : W := mkw 0x2112843285160982 0x810894219428b04c 0x43338073c79e0193 0x7a199c039e3cf00c

def z298 : W := mkw 0x5aed000000000000 0x02d7680000000000 0x1ccc000000000000 0x80e6600000000000

def z299 : W := mkw 0x04007b85c8807ebc 0x402003dc2e4403f5 0x20007f8f80007fec 0x090003fc7c0003ff

def z300 : W := mkw 0x497f04ff100b0143 0x0a4bf827f880580a 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z301 : W := mkw 0x0c285def00000000 0x086142ef78000000 0x3c3c7fff8000000e 0xe9e1e3fffc000000

def z302 : W := mkw 0x0000800084100880 0x0000040004208044 0x0003800384001809 0x00001c001c2000c0

def z303 : W := mkw 0x2400767ac88279db 0x812003b3d64413ce 0x20007e7f800079ec 0x090003f3fc0003cf

def z304 : W := mkw 0xd7d7fb006ff4f41c 0x06bebfd8037fa7a0 0xffc3ff807fe07e1d 0xf7fe1ffc03ff03f0

def z305 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x00338073c79e5992 0x18019c039e3cf2cc

def z306 : W := mkw 0x57d75da700000000 0x0abebaed38000000 0x7fc3ff838000000d 0xe3fe1ffc1c000000

def z307 : W := mkw 0x215784b785368ba2 0xc10abc25bc29b45d 0x80ff91ff847fffff 0xac07fc8ffc23ffff

def z308 : W := mkw 0x0c28705840024112 0x00614382c2001208 0x1c3c707c401e4196 0xf8e1e383e200f20c

def z309 : W := mkw 0x12802b006ac0741c 0x00940158035603a0 0xe3c00f807fe07e19 0x171e007c03ff03f0

def z310 : W := mkw 0x5fff5def00208220 0x4afffaef78010411 0xffffffff8061a66f 0xeffffffffc030d33

def z311 : W := mkw 0x0000008500000220 0x4000000428000011 0x0000118c00002660 0x0000008c60000133

def z312 : W := mkw 0x5bff000010090000 0x02dff80000804800 0xdfff8000781f8013 0xf6fffc0003c0fc00

def z313 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe33ffe7fc79ff9ff 0xff19fff3fe3cffcf

def z314 : W := mkw 0x5eed59cd00000000 0x0af76ace68000000 0x1ccf918f8000000f 0xa8e67c8c7c000000

def z315 : W := mkw 0x5fff5def18092049 0x0afffaef78c04902 0xffffffffb801a06f 0xeffffffffdc00d03

def z316 : W := mkw 0xdaed000032698000 0x06d7680001934c00 0xdfcc00007fe18011 0xf6fe600003ff0c00

def z317 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f807be02600 0xd7fe03fc03df0130

def z318 : W := mkw 0x5fba5def00000000 0x0afdd2ef78000000 0x7f307fff8000000c 0x4bf983fffc000000

def z319 : W := mkw 0x53920d2200000000 0x0a9c906910000000 0x63000e0000000000 0x0318007000000000

def z320 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff8183ffff9e1b 0xf6fffc0c1ffffcf0

def z321 : W := mkw 0xdbff8000b77d8880 0x06dffc0005bbec44 0xdfff8003ffffd99f 0xfefffc001ffffecc

def z322 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c306070781fe1f0 0x54e1830383c0ff0f

def z323 : W := mkw 0x5fba7d7a580b615b 0x0afdd3ebd2c05b0a 0x7f306e70780e0000 0x53f9837383c07000

def z324 : W := mkw 0x040059cd00000000 0x082002ce68000000 0x0000118c00000000 0x0000008c60000000

def z325 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7ff3eff380000009 0x43ff9f7f9c000000

def z326 : W := mkw 0x2112a632c5b6dbb2 0xc1089531962db6dd 0xe333ee73c7ffffff 0x7f199f739e3fffff

def z327 : W := mkw 0xdffffdff7f7fe15b 0x0effffeffbfbff0a 0xffffffffffffe1ff 0xffffffffffffff0f

def z328 : W := mkw 0xd3d78b0027f49404 0x069ebc58013fa4a0 0x63c38f8007e01e09 0x031e1c7c003f00f0

def z329 : W := mkw 0xdffff0ddff7febfb 0x46ffff86effbff5f 0xdffff1ffffffffff 0xfeffff8fffffffff

def z330 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xff006e007fe07e10 0x57f8037003ff03f0

def z331 : W := mkw 0x040070584802615b 0x00200382c240130a 0x9c00707c780061f4 0xfce00383e3c0030f

def z332 : W := mkw 0x0000042200000000 0x0000002110000000 0x20006e738000000c 0x090003739c000000

def z333 : W := mkw 0x0828000010090000 0x0041400000804800 0x9c3c100c781fe1f6 0xfce1e08063c0ff0f

def z334 : W := mkw 0x2000801085160982 0x810004008428b04c 0x00000000001e0180 0x000000000000f00c

def z335 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x800f900f8011e1f6 0xac007c807c008f0f

def z336 : W := mkw 0x1792fb006fd4741c 0x00bc97d8037ea3a0 0xfff3ff807ffe7e1f 0xf7ff9ffc03fff3f0

def z337 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7fc06f807fe01e09 0x53fe037c03ff00f0

def z338 : W := mkw 0x0400500008002008 0x0020028000400100 0x9c00100038002000 0x84e0008001c00100

def z339 : W := mkw 0x0112243240024112 0x0008912192001208 0x6333ee73c01e419f 0x7b199f739e00f20c

def z340 : W := mkw 0x53d78da784308aa0 0x4a9ebc6d3c218455 0xe3cf9f8f8471ffff 0xaf1e7cfc7c238fff

def z341 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00c3918f84607fed 0x08061c8c7c2303ff

def z342 : W := mkw 0x2045a295c5b6dbb2 0xc1022d14ae2db6dd 0x80cf918fc7ffffff 0xbc067c8c7e3fffff

def z343 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c0c707c3801e1e4 0x8ce06383e1c00f0f

def z344 : W := mkw 0x04007b004880741c 0x002003d8024403a0 0xbc007f8078007e1c 0xf5e003fc03c003f0

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x00300000401e0012 0x700180000200f000

def z346 : W := mkw 0x57d77fa76ac0741c 0x0abebbfd3b5603a0 0xffc3ff83ffe07e1d 0xf7fe1ffc1fff03f0

def z347 : W := mkw 0x7fff7fffc0825992 0x8bfffbfffe0412cc 0x7fffffff8000598f 0xebfffffffc0002cc

def z348 : W := mkw 0x0045008580000aa0 0x400228042c000055 0x00cf918f80007fef 0xa8067c8c7c0003ff

def z349 : W := mkw 0x2112a632dd9f79db 0x8108953196ecfbce 0xe333ee73ff9ff9ff 0x7f199f739ffcffcf

def z350 : W := mkw 0xdbff84ef377d8000 0x0edffc2779bbec00 0xdfff807fffff8013 0xfefffc03fffffc00

def z351 : W := mkw 0x8000a2007ffdf41c 0x0400051003ffefa0 0x800000007ffffe10 0x1400000003fffff0

def z352 : W := mkw 0x36807f32eac27d9e 0x81b403f9975613ec 0xffc07ff3ffe07f9d 0xfffe03ff9fff03fc

def z353 : W := mkw 0x0828004810090041 0x0041400240804802 0x000c000c00018060 0x0000600060000c03

def z354 : W := mkw 0x0445f0ddcc32ebfb 0x40222f86ee61975f 0x80cff1ff8471ffff 0xac067f8ffc238fff

def z355 : W := mkw 0x0112042200000000 0x0008902110000000 0x0033807380000002 0x08019c039c000000

def z356 : W := mkw 0x0112000000000000 0x0008900000000000 0x4333800000000003 0x62199c0000000000

def z357 : W := mkw 0xdfba5d6a334d0000 0x0efdd2eb519a6800 0x7f306e707b8e0000 0x53f9837383dc7000

def z358 : W := mkw 0x3fbaff7affdf7ddf 0x81fdd7fbd7fefbee 0xffffffffffffffff 0xffffffffffffffff

def z359 : W := mkw 0x0000008580000aa0 0x400000042c000055 0x0000018380001e08 0x0000000c1c0000f0

def z360 : W := mkw 0x53d7000000000000 0x029eb80000000000 0x43c3800000000001 0x021e1c0000000000

def z361 : W := mkw 0x040070584802615b 0x00200382c240130a 0x0030707c401e61f6 0x78018383e200f30f

def z362 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdf3c00007b9f8012 0xf6f9e00003dcfc00

def z363 : W := mkw 0x2000221041865112 0x81000110820c3288 0x00000000438e0000 0x10000000021c7000

def z364 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7f3fee7f80000002 0x4bf9ff73fc000000

def z365 : W := mkw 0x5fff7dff4802615b 0x0afffbeffa40130a 0x7fffffff800061ef 0xebfffffffc00030f

def z366 : W := mkw 0xdbff0000336d8000 0x06dff800019b6c00 0xdffc00007bef8000 0xd6ffe00003df7c00

def z367 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc06e007fe00011 0xf7fe037003ff0000

def z368 : W := mkw 0xdbff8b0037fd9404 0x06dffc5801bfeca0 0xffff8f807fff9e1b 0xf7fffc7c03fffcf0

def z369 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00306070479e5996 0x78018303823cf2cc

def z370 : W := mkw 0xa112a632f7ffd992 0x8508953197bffecc 0xe333ee73ffffd99f 0x7f199f739ffffecc

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c100c00000006 0xa800608060000000

def z372 : W := mkw 0xfbffa6b7f7ffdbb2 0xc7dffd35bfbffedd 0xffffffffffffffff 0xffffffffffffffff

def z373 : W := mkw 0x24007fffc0825992 0x892003fffe0412cc 0x20007fff8000598c 0x090003fffc0002cc

def z374 : W := mkw 0x08282010580b615b 0x0041410082c05b0a 0x9c3c0000781fe1f2 0xf4e1e00003c0ff0f

def z375 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe3f3fff3c7fe7f9f 0xff1f9fff9e3ff3fc

def z376 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00038003c79e599f 0x38001c001e3cf2cc

def z377 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x003c707c001fe1e6 0x0801e383e000ff0f

def z378 : W := mkw 0xd3d78da727748000 0x0e9ebc6d393ba400 0x63c38f8387e00009 0x031e1c7c1c3f0000

def z379 : W := mkw 0x2000a632c4925992 0x81000531962492cc 0x2003ee738410599f 0x29001f739c2082cc

def z380 : W := mkw 0x486d00cd00000000 0x0a43680668000000 0x000c000c00000000 0x0000600060000000

def z381 : W := mkw 0x53d78da784308aa0 0x4a9ebc6d3c218455 0x63c38f8384601e09 0x031e1c7c1c2300f0

def z382 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x63038e03c79e5999 0x13181c701e3cf2cc

def z383 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x9c3c007c781f81f2 0xfce1e003e3c0fc0f

def z384 : W := mkw 0x5bff808584308aa0 0x42dffc042c218455 0xdfff918f8471ffff 0xeefffc8c7c238fff

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c0000004600011 0xa406000000230000

def z386 : W := mkw 0x16c5598500000000 0x00b62acc28000000 0x7fcfff8f8000000f 0xebfe7ffc7c000000

def z387 : W := mkw 0x1ea87b587acb755f 0x00f543dac3d65baa 0xff3c7e7c7b9fe1f6 0xfff9e3f3e3dcff0f

def z388 : W := mkw 0xdbff8000b77d8aa0 0x46dffc0005bbec55 0xdfff80007ffffff3 0xf6fffc0003ffffff

def z389 : W := mkw 0x0445f085cc30eab8 0x40222f842e618755 0x9ccff18ffc71ffff 0xfce67f8c7fe38fff

def z390 : W := mkw 0x5eed59cd00000000 0x0af76ace68000000 0x7fcc7f8c0000000d 0xe3fe63fc60000000

def z391 : W := mkw 0x0000808584100aa0 0x400004042c208055 0x0003918f84107fff 0x28001c8c7c2083ff

def z392 : W := mkw 0x2000a632c5965992 0x81000531962cb2cc 0x20006e73c79e599c 0x190003739e3cf2cc

def z393 : W := mkw 0xdfffd900377d8000 0x06fffec801bbec00 0xffffff807fff801f 0xf7fffffc03fffc00

def z394 : W := mkw 0xdfba7b007bcd741c 0x06fdd3d803de6ba0 0xfff07f807fee7e1d 0xf7ff83fc03ff73f0

def z395 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf800f847181f3 0xac067c007c238c0f

def z396 : W := mkw 0x5fffddef05140000 0x0afffeef7828a000 0x7fffffffc79e001f 0xfbfffffffe3cf000

def z397 : W := mkw 0x80000000334d0000 0x04000000019a6800 0x000000007b8e0000 0x1000000003dc7000

def z398 : W := mkw 0x0400500000000000 0x0020028000000000 0x1c00700000000004 0xe0e0038000000000

def z399 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c0c100c781fe1f0 0x94e0608063c0ff0f

def z400 : W := mkw 0x33928f22a7d41c84 0x819c9479153ea0e4 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z401 : W := mkw 0x00002010580b615b 0x0000010082c05b0a 0x80306070781fe1f6 0x7c01830383c0ff0f

def z402 : W := mkw 0x1ea87b487ac9745d 0x00f543da43d64ba2 0xffcc7f8c7fe1fe7d 0xf7fe63fc63ff0ff3

def z403 : W := mkw 0x0d3a747a580b615b 0x0069d3a3d2c05b0a 0xff3ffe7ff81fe1ff 0xfff9fff3ffc0ff0f

def z404 : W := mkw 0xdeed59cd32698000 0x0ef76ace69934c00 0x9ccc118c38618000 0x84e6608c61c30c00

def z405 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x803c107c001fe1f6 0xac01e083e000ff0f

def z406 : W := mkw 0x80008000b77d8aa0 0x4400040005bbec55 0x800000007ffffff0 0x1400000003ffffff

def z407 : W := mkw 0x0c28704858096059 0x0061438242c04b02 0x9c0c700c7801e074 0xf4e0638063c00f03

def z408 : W := mkw 0x5fff590000000000 0x02fffac800000000 0x7fffff800000000f 0xe3fffffc00000000

def z409 : W := mkw 0x5fff7fff7acb755f 0x0afffbfffbd65baa 0xffffffffffffffff 0xffffffffffffffff

def z410 : W := mkw 0xd2c5000022608000 0x0696280001130400 0x00c0000000600000 0x0006000000030000

def z411 : W := mkw 0x0000a010dc3bebfb 0x4000050086e1df5f 0x800000007c7ffff0 0x1400000003e3ffff

def z412 : W := mkw 0xdbff000032698000 0x06dff80001934c00 0xdfff800038618003 0xe6fffc0001c30c00

def z413 : W := mkw 0x0112042200000000 0x0008902110000000 0x63306e7000000000 0x4319837380000000

def z414 : W := mkw 0xc93a0000110d0000 0x0649d00000886800 0x00300000000e0000 0x0001800000007000

def z415 : W := mkw 0x0000000010090000 0x0000000000804800 0x80000000781f8010 0x1400000003c0fc00

def z416 : W := mkw 0x7fffddff85160982 0x8bfffeeffc28b04c 0x7fffffff801e018f 0xebfffffffc00f00c

def z417 : W := mkw 0x04007fef4880741c 0x082003ff7a4403a0 0x20007fff80007e0c 0x090003fffc0003f0

def z418 : W := mkw 0x2112a63245965112 0x81089531922cb288 0x6333ee70479e0013 0x73199f73823cf000

def z419 : W := mkw 0xfbbaa632f7df5992 0x87ddd53197befacc 0x7f33ee73ff9e599f 0x7bf99f739ffcf2cc

def z420 : W := mkw 0x497f04ef00000000 0x0a4bf82778000000 0x633fee7f8000000f 0x6b19ff73fc000000

def z421 : W := mkw 0x4d7f5def00000000 0x0a6bfaef78000000 0x203fffff8000000e 0x0901fffffc000000

def z422 : W := mkw 0x16807b0040805010 0x00b403d802040280 0x7fc07f804780581d 0xf3fe03fc023c02c0

def z423 : W := mkw 0x2157a6b7c5b6dbb2 0xc10abd35be2db6dd 0x633fee7fc79fd9ff 0x7b19ff73fe3cfecf

def z424 : W := mkw 0x0000000000208220 0x4000000000010411 0x800000000061a660 0x0400000000030d33

def z425 : W := mkw 0xdfba70587b4f615b 0x06fdd382c3da7b0a 0x5f3060707b8e0000 0x52f9830383dc7000

def z426 : W := mkw 0xc97f8085953d8aa0 0x464bfc042ca9ec55 0x80ff918f847fffff 0xac07fc8c7c23ffff

def z427 : W := mkw 0x215784b785368ba2 0xc10abc25bc29b45d 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z428 : W := mkw 0x0112842205140000 0x000894211028a000 0x6333ee73c79e001f 0x7b199f739e3cf000

def z429 : W := mkw 0x3792ff32efd67d9e 0x81bc97f9977eb3ec 0x7f33ee73ff9e599f 0x7bf99f739ffcf2cc

def z430 : W := mkw 0x1680590000000000 0x00b402c800000000 0xffc07f8004607e1d 0xe7fe03fc002303f0

def z431 : W := mkw 0x0000000018092049 0x0000000000c04902 0x800000003801a060 0x0400000001c00d03

def z432 : W := mkw 0x7fbaff7ac5965992 0x8bfdd7fbd62cb2cc 0x7f33ee73c79e599f 0x7bf99f739e3cf2cc

def z433 : W := mkw 0x1680790048006018 0x00b403c802400300 0xffc07f807800601d 0xf7fe03fc03c00300

def z434 : W := mkw 0x2112862285941880 0x81089431142ca0c4 0x63338e03c79e181b 0x73199c701e3cf0c0

def z435 : W := mkw 0x5fffddef84308aa0 0x4afffeef7c218455 0x7fffffff801181ef 0xebfffffffc008c0f

def z436 : W := mkw 0x5eed5def00000000 0x0af76aef78000000 0x3ccc7fff8000000c 0x89e663fffc000000

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000004607e10 0x04000000002303f0

def z438 : W := mkw 0xdffffb007ffdf41c 0x06ffffd803ffefa0 0xffffee007fff8013 0xf7ffff7003fffc00

def z439 : W := mkw 0x2000a210efd67d9e 0x81000510877eb3ec 0x800000007ffe7f90 0x1400000003fff3fc

def z440 : W := mkw 0x4d7f74ff580b615b 0x0a6bfba7fac05b0a 0x9c3ff07ff81fe1f6 0xfce1ff83ffc0ff0f

def z441 : W := mkw 0x0045800004308000 0x00022c0000218400 0x00c3800004600001 0x00061c0000230000

def z442 : W := mkw 0xdfffddefb77d8aa0 0x4efffeef7dbbec55 0xffffffffffffffff 0xffffffffffffffff

def z443 : W := mkw 0x5eed59cd18092049 0x0af76ace68c04902 0x9ccc118c3801a060 0x84e6608c61c00d03

def z444 : W := mkw 0x8000000032698000 0x0400000001934c00 0x8000000038618000 0x0400000001c30c00

def z445 : W := mkw 0x0000008500000000 0x0000000428000000 0x0000118f8000000c 0x0800008c7c000000

def z446 : W := mkw 0x040070584802615b 0x00200382c240130a 0x0000607000000000 0x0000030380000000

def z447 : W := mkw 0xdffff0007f7de018 0x06ffff8003fbef00 0xdffff0007fffe017 0xf6ffff8003ffff00

def z448 : W := mkw 0xfffffffff7ffd992 0x8fffffffffbffecc 0xffffffffffffd99f 0xfffffffffffffecc

def z449 : W := mkw 0x0045000000000000 0x0002280000000000 0x00cf800000000003 0xa0067c0000000000

def z450 : W := mkw 0x0000800084308aa0 0x4000040004218455 0x00000000001181e0 0x0000000000008c0f

def z451 : W := mkw 0x0112842284100880 0x0008942114208044 0x6333ee738410599f 0x6b199f739c2082cc

def z452 : W := mkw 0x0c28504800000000 0x0061428240000000 0x1c30607000000000 0x40e1830380000000

def z453 : W := mkw 0x2000263240825112 0x8100013192041288 0x20006e7000000000 0x0100037380000000

def z454 : W := mkw 0x04007b584882755f 0x002003dac24413aa 0x20007ffc00007fec 0x090003ffe00003ff

def z455 : W := mkw 0xdfffffef7ffdf41c 0x0effffff7bffefa0 0xfffffffffffffe1f 0xfffffffffffffff0

def z456 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9cfc71fc7c7fffff 0xfce7e38fe3e3ffff

def z457 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c3c707c780e0006 0xf8e1e383e3c07000

def z458 : W := mkw 0x0112262240805010 0x0008913112040280 0x6333ee73c780581f 0x7b199f739e3c02c0

def z459 : W := mkw 0xdbba8000375d0000 0x06ddd40001bae800 0x5f3380007f9e0013 0x72f99c0003fcf000

def z460 : W := mkw 0x1ea859483a49244d 0x00f542ca41d24922 0x9ccc118c3861a660 0x84e6608c61c30d33

def z461 : W := mkw 0x2112a432c5164992 0x810895219628b24c 0x0033e073c01e4196 0x78019f039e00f20c

def z462 : W := mkw 0x168070006a406018 0x00b4038003520300 0xdfc070007fe06015 0xf6fe038003ff0300

def z463 : W := mkw 0x16807fef6ac0741c 0x08b403ff7b5603a0 0xffc07fffffe07e1d 0xfffe03ffffff03f0

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c000c001181e2 0x0800600060008c0f

def z465 : W := mkw 0x0000800084100880 0x0000040004208044 0x0000000004105990 0x00000000002082cc

def z466 : W := mkw 0x0445ddef84308aa0 0x48222eef7c218455 0xa0cfffff8471ffff 0xad067ffffc238fff

def z467 : W := mkw 0xdfffddef153d8000 0x0efffeef78a9ec00 0x7fffffff801f800f 0xebfffffffc00fc00

def z468 : W := mkw 0x5ffffdffdc3bebfb 0x4affffeffee1df5f 0xfffffffffc7fffff 0xffffffffffe3ffff

def z469 : W := mkw 0x415704a700000000 0x0a0ab82538000000 0x0003800380000000 0x00001c001c000000

def z470 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfcf80003fe18001 0x86fe7c0001ff0c00

def z471 : W := mkw 0x0112800005140000 0x000894000028a000 0x4303800007800001 0x02181c00003c0000

def z472 : W := mkw 0x04007058580b615b 0x00200382c2c05b0a 0x8000707c781fe1f4 0x1c000383e3c0ff0f

def z473 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c39e0182 0x5b199f739e1cf00c

def z474 : W := mkw 0x0045800004308000 0x00022c0000218400 0x80cf91800471fe1f 0xa4067c8c00238ff0

def z475 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0xe3c01f8007e07e1d 0xa71e00fc003f03f0

def z476 : W := mkw 0x0000800004100000 0x0000040000208000 0x0003800004100013 0x20001c0000208000

def z477 : W := mkw 0x0000800084308aa0 0x4000040004218455 0x800380038471ffff 0x2c001c001c238fff

def z478 : W := mkw 0x293a847a951f09c3 0x8149d423d4a8f84e 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z479 : W := mkw 0x16807b586ac2755f 0x00b403dac35613aa 0xffc07ffc7fe07ffd 0xfffe03ffe3ff03ff

def z480 : W := mkw 0x000022004880741c 0x00000110024403a0 0x0000000000007e00 0x00000000000003f0

def z481 : W := mkw 0x0045008500208220 0x4002280428010411 0x00c0018000600600 0x0006000c00030030

def z482 : W := mkw 0x1ea8594800000000 0x00f542ca40000000 0x7ffc7ffc0000000f 0xebffe3ffe0000000

def z483 : W := mkw 0x00002010580b615b 0x0000010082c05b0a 0x800c100c781fe1f6 0xbc00608063c0ff0f

def z484 : W := mkw 0x1280090022400404 0x0094004801120020 0x00c0018000600600 0x0006000c00030030

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x4300000047800011 0x72180000023c0000

def z486 : W := mkw 0x0c287b58588b755f 0x006143dac2c45baa 0xbc3c7ffc781ffffe 0xfde1e3ffe3c0ffff

def z487 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5ff380007fee0001 0x52ff9c0003ff7000

def z488 : W := mkw 0x0828000000000000 0x0041400000000000 0x1c3c000000000002 0xe0e1e00000000000

def z489 : W := mkw 0x2d3af67add9f79db 0x8169d7b3d6ecfbce 0x7f33ee73ff9e599f 0x7bf99f739ffcf2cc

def z490 : W := mkw 0x20002210c0825992 0x81000110860412cc 0x0000000000005980 0x00000000000002cc

def z491 : W := mkw 0x16807b004880741c 0x00b403d8024403a0 0x7fc07f8000007e0d 0xe3fe03fc000003f0

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000100000006014 0xa400008000000300

def z493 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xff007e007b806014 0xf7f803f003dc0300

def z494 : W := mkw 0x0c28504818092049 0x0061428240c04902 0x9c0c100c3811e1f6 0xace0608061c08f0f

def z495 : W := mkw 0x086d80dd943b8be3 0x40436c06eca1dc5f 0x80ff91ff847fffff 0xac07fc8ffc23ffff

def z496 : W := mkw 0x1680590000000000 0x00b402c800000000 0x1cc0118000000000 0x80e6008c00000000

def z497 : W := mkw 0xcd7ff0585d3fe15b 0x066bff82c2e9ff0a 0x9c3ff07c781fe1f6 0xfce1ff83e3c0ff0f

def z498 : W := mkw 0x000022006ac0741c 0x00000110035603a0 0x000000007b800000 0x1000000003dc0000

def z499 : W := mkw 0x000022107acb755f 0x0000011083d65baa 0x800000007ffffff0 0x1400000003ffffff

def z500 : W := mkw 0x80458000377d8000 0x04022c0001bbec00 0x80cf80007fff8013 0xb4067c0003fffc00

def z501 : W := mkw 0x0045a285c4b0dab0 0x40022d142e2586d5 0xe3cfff8fc7f1ffff 0xff1e7ffc7e3f8fff

def z502 : W := mkw 0x0045008500000000 0x0002280428000000 0x00c3818380000009 0x00061c0c1c000000

def z503 : W := mkw 0x0c28504800000000 0x0061428240000000 0x1c0c100c00000000 0x80e0608060000000

def z504 : W := mkw 0x1eedfbddfefbffff 0x40f76fdeeff7dfff 0xffffffffffffffff 0xffffffffffffffff

def z505 : W := mkw 0x0c28f058dc3bebfb 0x40614782c6e1df5f 0x9c3c707c7c7ffff6 0xfce1e383e3e3ffff

def z506 : W := mkw 0x3792ff22efd47c9c 0x81bc97f9177ea3e4 0xffc3ff83ffe07e1d 0xf7fe1ffc1fff03f0

def z507 : W := mkw 0xc97f8058153f8143 0x064bfc02c0a9fc0a 0x003f807c001f81e2 0x0801fc03e000fc0f

def z508 : W := mkw 0x04007b006ac0741c 0x002003d8035603a0 0xa0007f807fe07e1c 0x150003fc03ff03f0

def z509 : W := mkw 0xc97f8000153d8000 0x064bfc0000a9ec00 0x80ff8000047f8013 0xa407fc000023fc00

def z510 : W := mkw 0x0c6dd0cd9c39aae9 0x40636e866ce1cd57 0x9ccf918fbc71ffff 0xace67c8c7de38fff

def z511 : W := mkw 0x0c287dff580b615b 0x086143effac05b0a 0xbc3c7ffff81fe1fe 0xfde1e3ffffc0ff0f

def z512 : W := mkw 0x000022006ac0741c 0x00000110035603a0 0x80c011807fe07e1d 0xb406008c03ff03f0

def z513 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6303ee738780598d 0x0b181f739c3c02cc

def z514 : W := mkw 0xdffffb587ffff55f 0x06ffffdac3ffffaa 0xfffffffc7fffffff 0xffffffffe3ffffff

def z515 : W := mkw 0x12c58085a6708aa0 0x40962c042d338455 0xdfcf918ffff1ffff 0xfefe7c8c7fff8fff

def z516 : W := mkw 0x0045008500208220 0x4002280428010411 0x000c000c00018060 0x0000600060000c03

def z517 : W := mkw 0x086d808594398aa0 0x40436c042ca1cc55 0x9cff918ffc7fffff 0xfce7fc8c7fe3ffff

def z518 : W := mkw 0x20002632c0825992 0x81000131960412cc 0x63006e73c780599d 0x7b1803739e3c02cc

def z519 : W := mkw 0xd3d7800027748000 0x069ebc00013ba400 0xdfc380007fe00011 0xf6fe1c0003ff0000

def z520 : W := mkw 0x12c58b85a6f09ea4 0x40962c5c2d3784f5 0xe3cf9f8f87f1ffff 0xaf1e7cfc7c3f8fff

def z521 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fcf9f8f80000009 0x83fe7cfc7c000000

def z522 : W := mkw 0x040070584802615b 0x00200382c240130a 0x800c707c0011e1f6 0xac006383e0008f0f

def z523 : W := mkw 0xc157800005348000 0x060abc000029a400 0x0003800000000000 0x00001c0000000000

def z524 : W := mkw 0xdfffd0483f7da049 0x06fffe8241fbed02 0xdfff900c7fffa073 0xf6fffc8063fffd03

def z525 : W := mkw 0x5fff7dff580b615b 0x0afffbeffac05b0a 0x7ffffffff80e000f 0xfbffffffffc07000

def z526 : W := mkw 0x5eed59cd00208220 0x4af76ace68010411 0x9ccc118c0061a660 0x84e6608c60030d33

def z527 : W := mkw 0x5eed59cd00000000 0x0af76ace68000000 0x1cfc71fc00000006 0xe8e7e38fe0000000

def z528 : W := mkw 0x04005d6a00000000 0x082002eb50000000 0x20006e7000000000 0x0100037380000000

def z529 : W := mkw 0x0000200040004010 0x0000010002000200 0x0000600040004014 0x7000030002000200

def z530 : W := mkw 0x2157a6b7c5b6dbb2 0xc10abd35be2db6dd 0x63f3eff3c7fe5f9f 0x7b1f9f7f9e3ff2fc

def z531 : W := mkw 0x0000020022c01404 0x00000010011600a0 0x0000000007e01e00 0x00000000003f00f0

def z532 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00c3818384705f9f 0x28061c0c1c2382fc

def z533 : W := mkw 0x5bff000022400000 0x02dff80001120000 0xdfff80007fe00013 0xf6fffc0003ff0000

def z534 : W := mkw 0x5fffffefeef0febc 0x4affffff7f7787f5 0xfffffffffff1ffff 0xffffffffffff8fff

def z535 : W := mkw 0x7fffffffc5b6dbb2 0xcbfffffffe2db6dd 0xffffffffc7ffffff 0xfffffffffe3fffff

def z536 : W := mkw 0xdaa8000032490000 0x06d5400001924800 0x1c00000038000000 0x00e0000001c00000

def z537 : W := mkw 0x5fff5fef22c01404 0x0afffaff791600a0 0x7fffffff87e01e0f 0xebfffffffc3f00f0

def z538 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x0003800380000000 0x00001c001c000000

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c00000078000010 0xf4e0000003c00000

def z540 : W := mkw 0x2000062280801880 0x81000031140400c4 0x20000e0380001808 0x010000701c0000c0

def z541 : W := mkw 0x497f000000000000 0x024bf80000000000 0x003f800000000002 0x0001fc0000000000

def z542 : W := mkw 0x12802b0062c05414 0x00940158031602a0 0x63c06f8047e05e1d 0x731e037c023f02f0

def z543 : W := mkw 0x1280220062c05010 0x0094011003160280 0xffc06e007fe0581d 0xf7fe037003ff02c0

def z544 : W := mkw 0x73d7afb7c5965992 0x8b9ebd7dbe2cb2cc 0x63f3eff3c79e599f 0x7b1f9f7f9e3cf2cc

def z545 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xbcc07f8038607e0c 0x85e603fc01c303f0

def z546 : W := mkw 0xdaed8085b6798aa0 0x46d76c042db3cc55 0x9ccf918fbc71ffff 0xace67c8c7de38fff

def z547 : W := mkw 0x0045808504308000 0x00022c0428218400 0x80cf918f8471801f 0xac067c8c7c238c00

def z548 : W := mkw 0x1ea87958580b615b 0x00f543cac2c05b0a 0xfffc7ffc781fe1ff 0xffffe3ffe3c0ff0f

def z549 : W := mkw 0x80458085b77d8aa0 0x44022c042dbbec55 0x80cf918fffffffff 0xbc067c8c7fffffff

def z550 : W := mkw 0xfbffa210f7ffd992 0x87dffd1087bffecc 0xdfff80007fffd993 0xf6fffc0003fffecc

def z551 : W := mkw 0x0045008500000000 0x0002280428000000 0x000f800f80000002 0x08007c007c000000

def z552 : W := mkw 0xdfffd9003f7da40c 0x06fffec801fbed20 0xdfff91807fffa613 0xf6fffc8c03fffd30

def z553 : W := mkw 0x7fffffffdd9f79db 0x8bfffffffeecfbce 0xffffffffff9ff9ff 0xfffffffffffcffcf

def z554 : W := mkw 0x168059002a40240c 0x00b402c801520120 0xdfc011807fe02611 0xf6fe008c03ff0130

def z555 : W := mkw 0x0400700048006018 0x0020038002400300 0x0000700000006004 0x0000038000000300

def z556 : W := mkw 0xdeed50483a69a049 0x06f76a8241d34d02 0x9ccc100c3861a060 0x84e6608061c30d03

def z557 : W := mkw 0x0c6d70dd582be37b 0x40636b86eac15f1b 0x9cfc71fc787fe7f6 0xfce7e38fe3c3ff3f

def z558 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c306070781e4196 0x78e1830383c0f20c

def z559 : W := mkw 0x1280000000000000 0x0094000000000000 0x5fc0000000000001 0xe2fe000000000000

def z560 : W := mkw 0xdbffa2007ffdf41c 0x06dffd1003ffefa0 0xdfff80007ffffe13 0xf6fffc0003fffff0

def z561 : W := mkw 0x00000da700000000 0x0800006d38000000 0x20000f8380000008 0x0100007c1c000000

def z562 : W := mkw 0x16805def00000000 0x08b402ef78000000 0x7fc07fff8000000d 0xebfe03fffc000000

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000011e1f0 0x0400000000008f0f

def z564 : W := mkw 0xdffff0587f7fe15b 0x06ffff82c3fbff0a 0xdfffe0707fff8013 0xf6ffff0383fffc00

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000400581d 0x20000000002002c0

def z566 : W := mkw 0x16c57b856ae0f63c 0x40b62bdc2b5707b1 0xffcc7f8c7fe1fe7d 0xf7fe63fc63ff0ff3

def z567 : W := mkw 0x0400504800000000 0x0020028240000000 0x0000707c00000004 0x08000383e0000000

def z568 : W := mkw 0x086d800014398000 0x00436c0000a1cc00 0x9cff80007c7f8013 0xf4e7fc0003e3fc00

def z569 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7f006e007f80581d 0x73f8037003fc02c0

def z570 : W := mkw 0xdaed008532698220 0x46d7680429934c11 0x9ccc118c3861a660 0x84e6608c61c30d33

def z571 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x000f800f8411d9ff 0x28007c007c208ecf

def z572 : W := mkw 0x2000043280020982 0x810000219400104c 0x0000007380000180 0x080000039c00000c

def z573 : W := mkw 0x0000001000020102 0x0000000080001008 0x00300070001e0182 0x080180038000f00c

def z574 : W := mkw 0x0828000010090000 0x0041400000804800 0x9c0c000038018000 0x84e0600001c00c00

def z575 : W := mkw 0x1ea87b007ac9741c 0x00f543d803d64ba0 0xfffc7f807ffffe1f 0xf7ffe3fc03fffff0

def z576 : W := mkw 0x20002632c0825992 0x81000131960412cc 0x20306e73c01e599e 0x790183739e00f2cc

def z577 : W := mkw 0x17927f226ac0741c 0x00bc93f9135603a0 0xfff3fff3ffe07e1f 0xffff9fff9fff03f0

def z578 : W := mkw 0x086d80dd943b8be3 0x40436c06eca1dc5f 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z579 : W := mkw 0x0400720048807018 0x0020039002440380 0xff007e007f80781d 0xf7f803f003fc03c0

def z580 : W := mkw 0x5fff7058580b615b 0x02fffb82c2c05b0a 0xdffff07c781fe1f7 0xfeffff83e3c0ff0f

def z581 : W := mkw 0x0045808504308220 0x40022c0428218411 0x80cf918c0471a673 0xa4067c8c60238d33

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c0118000602600 0x8406008c00030130

def z583 : W := mkw 0xd3d78000377d8000 0x069ebc0001bbec00 0xc3c380007fff8011 0x161e1c0003fffc00

def z584 : W := mkw 0x2d3a767a598f715b 0x8169d3b3d2cc7b8a 0xff3c7e7c7b9fe1f6 0xfff9e3f3e3dcff0f

def z585 : W := mkw 0x293aa632d59f5992 0x8149d53196acfacc 0xff3fee73ff9fd99f 0xfff9ff739ffcfecc

def z586 : W := mkw 0xf3d7a632e7f6d992 0x879ebd31973fb6cc 0x63f3ee73c7fe599f 0x7b1f9f739e3ff2cc

def z587 : W := mkw 0xe97fa632d5bfd992 0x874bfd3196adfecc 0x633fee73c79fd99f 0x7b19ff739e3cfecc

def z588 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c30707c780e61e4 0x58e18383e3c0730f

def z589 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8071a7e2 0x8c067c8c7c038d3f

def z590 : W := mkw 0xdbff8058377f8143 0x06dffc02c1bbfc0a 0xdfff807c7fff81f3 0xfefffc03e3fffc0f

def z591 : W := mkw 0xdbff800027748000 0x06dffc00013ba400 0x5fff800007e00003 0xe2fffc00003f0000

def z592 : W := mkw 0x040072006ac0741c 0x00200390035603a0 0x9c0070007fe07e14 0xf4e0038003ff03f0

def z593 : W := mkw 0x73d78fa785941880 0x8b9ebc7d3c2ca0c4 0x63c38f8387801809 0x031e1c7c1c3c00c0

def z594 : W := mkw 0x128022006ac0741c 0x00940110035603a0 0xdfc000007fe07e11 0xf6fe000003ff03f0

def z595 : W := mkw 0x08282058500b4153 0x00414102c2805a0a 0x003c607c401fc1f6 0x7801e303e200fe0f

def z596 : W := mkw 0x5fffddef84308aa0 0x4afffeef7c218455 0x7fffffff84601e0f 0xebfffffffc2300f0

def z597 : W := mkw 0x5fba7f6a6ac0741c 0x0afdd3fb535603a0 0x7f306e707b800000 0x53f9837383dc0000

def z598 : W := mkw 0x9680fb007ffdf41c 0x04b407d803ffefa0 0xffc07f807ffffe1d 0xf7fe03fc03fffff0

def z599 : W := mkw 0x0400700048006018 0x0020038002400300 0x9cc071807c607e1d 0xf4e6038c03e303f0

def z600 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c6070781f8012 0xf4e1e30383c0fc00

def z601 : W := mkw 0xfbff8622b7fd9880 0x87dffc3115bfecc4 0xffff8e03ffff981b 0xf7fffc701ffffcc0

def z602 : W := mkw 0x5fff7fef6ac0741c 0x0afffbff7b5603a0 0x7ffffffffb80000f 0xfbffffffffdc0000

def z603 : W := mkw 0x0000201040024112 0x0000010082001208 0x803c707c401fe1f6 0xfc01e383e200ff0f

def z604 : W := mkw 0x7fff7fff41865112 0x8bfffbfffa0c3288 0x7fffffffc38e000f 0xfbfffffffe1c7000

def z605 : W := mkw 0xfbffa63277ffd112 0x87dffd3193bffe88 0xffffee707fff8013 0xf7ffff7383fffc00

def z606 : W := mkw 0x0c28504800000000 0x0061428240000000 0x9c3c707c0011e1f6 0xece1e383e0008f0f

def z607 : W := mkw 0x0828000010090000 0x0041400000804800 0x003c0000001f8002 0x0001e0000000fc00

def z608 : W := mkw 0x0112800005140000 0x000894000028a000 0x00338000001e0002 0x00019c000000f000

def z609 : W := mkw 0x0000800084308aa0 0x4000040004218455 0x80c011800471fffd 0xa406008c00238fff

def z610 : W := mkw 0x1ea870587a4b615b 0x00f54382c3d25b0a 0xdffc707c7fffe1f7 0xfeffe383e3ffff0f

def z611 : W := mkw 0xf3d78622a7f49880 0x879ebc31153fa4c4 0x63c38e0387e01809 0x031e1c701c3f00c0

def z612 : W := mkw 0x040070ddc8026bfb 0x40200386ee40135f 0x000071ff80007fec 0x0800038ffc0003ff

def z613 : W := mkw 0x5fff7dff40024112 0x0afffbeffa001208 0x7fffffffc01e419f 0xfbfffffffe00f20c

def z614 : W := mkw 0x0c6df0585c3be15b 0x00636f82c2e1df0a 0x9cfff07c7c7fe1f7 0xfce7ff83e3e3ff0f

def z615 : W := mkw 0x0d3af0585d1f615b 0x0069d782c2e8fb0a 0xdf3ff07c7f9fe1f7 0xfef9ff83e3fcff0f

def z616 : W := mkw 0x293aa67ad59f59d3 0x8149d533d6acface 0x633fee7fc79fd9ff 0x7b19ff73fe3cfecf

def z617 : W := mkw 0x0000000080000aa0 0x4000000004000055 0x0000000000007fe0 0x00000000000003ff

def z618 : W := mkw 0x0c2870ddd80b6bfb 0x40614386eec05b5f 0x9c3c71fff81ffffe 0xfce1e38fffc0ffff

def z619 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf818384719e1b 0xa4067c0c1c238cf0

def z620 : W := mkw 0xd3d7800027748000 0x069ebc00013ba400 0xc3cf800007f18013 0xa61e7c00003f8c00

def z621 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7ff07ff00000000d 0xe3ff83ff80000000

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x80cc118c0471ffff 0xac06608c60238fff

def z623 : W := mkw 0x8000800027748000 0x04000400013ba400 0x0000000007e00000 0x00000000003f0000

def z624 : W := mkw 0x0000800084100880 0x0000040004208044 0x0003800380100182 0x08001c001c00800c

def z625 : W := mkw 0x2112263241865112 0x81089131920c3288 0x63306e70478e581d 0x73198373823c72c0

def z626 : W := mkw 0x0000005800020143 0x00000002c000100a 0x0000007c000001e0 0x08000003e000000f

def z627 : W := mkw 0x0c6dd0cd84308aa0 0x40636e866c218455 0x9cfff1ff8471ffff 0xece7ff8ffc238fff

def z628 : W := mkw 0x1280000022400000 0x0094000001120000 0x9cc0000038600000 0x84e6000001c30000

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c100c0001a060 0x8400608060000d03

def z630 : W := mkw 0x16c559852a60a62c 0x40b62acc29530531 0x9ccc118c3861a660 0x84e6608c61c30d33

def z631 : W := mkw 0x0445fb85ccb0febc 0x40222fdc2e6587f5 0xa0cfff8f8471ffff 0xad067ffc7c238fff

def z632 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c780fa060 0xd4e1e383e3c07d03

def z633 : W := mkw 0xdbff8000153d8000 0x06dffc0000a9ec00 0x5fff8000001f8003 0xe2fffc000000fc00

def z634 : W := mkw 0x200026b7c0825bb2 0xc1000135be0412dd 0x20007fff80007fec 0x090003fffc0003ff

def z635 : W := mkw 0x0c2872587acb755f 0x00614392c3d65baa 0x9c3c707c7ffffff6 0xfce1e383e3ffffff

def z636 : W := mkw 0x8000a0107f7fe15b 0x0400050083fbff0a 0x800000007fffe1f0 0x1400000003ffff0f

def z637 : W := mkw 0x16c5d985ae70aeac 0x40b62ecc2d738575 0x9ccf918fbc71ffff 0xace67c8c7de38fff

def z638 : W := mkw 0xdaed800036798000 0x06d76c0001b3cc00 0x9ccf80003c718013 0xa4e67c0001e38c00

def z639 : W := mkw 0x1ea879587a4b655f 0x00f543cac3d25b2a 0x9cfc71fc787fe7f6 0xfce7e38fe3c3ff3f

def z640 : W := mkw 0x5fff7b006ac0741c 0x02fffbd8035603a0 0xffffff807fe07e1f 0xf7fffffc03ff03f0

def z641 : W := mkw 0xdfffddef27748000 0x0efffeef793ba400 0x7fffffff87e0000f 0xebfffffffc3f0000

def z642 : W := mkw 0x0000800084100880 0x0000040004208044 0x80c3918384707f9f 0xac061c8c1c2383fc

def z643 : W := mkw 0x0c28700058096018 0x0061438002c04b00 0x9c3c7000781fe016 0xf4e1e38003c0ff00

def z644 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x00300070000e0000 0x0001800380007000

def z645 : W := mkw 0xdbffa010777fc112 0x06dffd0083bbfe08 0xdfffe0707fffc197 0xfeffff0383fffe0c

def z646 : W := mkw 0x0000220040805010 0x0000011002040280 0x63006e0043800000 0x53180370021c0000

def z647 : W := mkw 0xc97f8000153d8000 0x064bfc0000a9ec00 0x433f8000479f8013 0x7219fc00023cfc00

def z648 : W := mkw 0x5fff7fef4880741c 0x0afffbff7a4403a0 0x7fffffff80007e0f 0xebfffffffc0003f0

def z649 : W := mkw 0x5fba7f6a6ac0741c 0x0afdd3fb535603a0 0xfff07ff07fe07e1d 0xf7ff83ff83ff03f0

def z650 : W := mkw 0x2112a6b7c5965bb2 0xc1089535be2cb2dd 0x6333ffffc79e7fff 0x7b199ffffe3cf3ff

def z651 : W := mkw 0x0045a285eef0febc 0x40022d142f7787f5 0x80cf918ffff1ffff 0xbc067c8c7fff8fff

def z652 : W := mkw 0x0c28504810090000 0x0061428240804800 0x9c3c707c781f8016 0xfce1e383e3c0fc00

def z653 : W := mkw 0x1680590022400000 0x00b402c801120000 0xffc07f807fe0001d 0xf7fe03fc03ff0000

def z654 : W := mkw 0x53d70fa722c01404 0x0a9eb87d391600a0 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z655 : W := mkw 0xe97f8432953f8982 0x874bfc2194a9fc4c 0x003f8073801f8182 0x0801fc039c00fc0c

def z656 : W := mkw 0x80008000153d8000 0x0400040000a9ec00 0x00000000001f8000 0x000000000000fc00

def z657 : W := mkw 0x168059002a40240c 0x00b402c801520120 0x1c00000038000000 0x00e0000001c00000

def z658 : W := mkw 0x5bff800004308000 0x02dffc0000218400 0xdfff800004718013 0xe6fffc0000238c00

def z659 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x43ff800007ff8003 0x021ffc00003ffc00

def z660 : W := mkw 0xdfffdd6a377d8000 0x0efffeeb51bbec00 0xffffee707fff8013 0xf7ffff7383fffc00

def z661 : W := mkw 0x015784a784308aa0 0x400abc253c218455 0xe3ffffff8471ffff 0xef1ffffffc238fff

def z662 : W := mkw 0x0000221040825112 0x0000011082041288 0x63306e70479e599f 0x7b198373823cf2cc

def z663 : W := mkw 0xdaed000032698000 0x06d7680001934c00 0x9cfc0000787f8012 0xf4e7e00003c3fc00

def z664 : W := mkw 0x0000800084308aa0 0x4000040004218455 0x800c100c0471fff6 0xac00608060238fff

def z665 : W := mkw 0x7fffffffefd67d9e 0x8bffffffff7eb3ec 0xfffffffffffe7f9f 0xfffffffffffff3fc

def z666 : W := mkw 0x16807b85eac07ebc 0x40b403dc2f5603f5 0xffc07f8fffe07ffd 0xfffe03fc7fff03ff

def z667 : W := mkw 0x0000220040805010 0x0000011002040280 0xe3c07f8047e07e1d 0xf71e03fc023f03f0

def z668 : W := mkw 0x00002010580b615b 0x0000010082c05b0a 0x00000000780e0000 0x1000000003c07000

def z669 : W := mkw 0x3392af32e7d65d96 0x819c9579973eb2ec 0x63f3eff3c7fe5f9f 0x7b1f9f7f9e3ff2fc

def z670 : W := mkw 0xd3d78085a7748aa0 0x469ebc042d3ba455 0xc3cf918f87f1ffff 0xae1e7c8c7c3f8fff

def z671 : W := mkw 0x3792ff32c5965992 0x81bc97f9962cb2cc 0x7ff3fff3c79e599f 0xfbff9fff9e3cf2cc

def z672 : W := mkw 0x000004ef00000000 0x0800002778000000 0x0000007f80000000 0x08000003fc000000

def z673 : W := mkw 0x0c6d50cd1829a269 0x40636a8668c14d13 0x9ccc118c3861a660 0x84e6608c61c30d33

def z674 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00cf818f84719feb 0x08067c0c7c238cff

def z675 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7f3c7e7c00000006 0xebf9e3f3e0000000

def z676 : W := mkw 0x5bff800005140000 0x02dffc000028a000 0x5fff8000479e0013 0xf2fffc00023cf000

def z677 : W := mkw 0x2112043201060102 0x8108902190083008 0x00300070000e0000 0x0001800380007000

def z678 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7f007f807b807e0c 0x53f803fc03dc03f0

def z679 : W := mkw 0x0045008500208220 0x4002280428010411 0x80cc118c0461fe7d 0xa406608c60230ff3

def z680 : W := mkw 0x0000800084100880 0x0000040004208044 0x800f900f8411f9ff 0xac007c807c208fcf

def z681 : W := mkw 0x7fba7f7a41865112 0x8bfdd3fbd20c3288 0x7f306e70438e0000 0x53f98373821c7000

def z682 : W := mkw 0x3680fb10efd67d9e 0x81b407d8877eb3ec 0xffc07f807ffe7f9d 0xf7fe03fc03fff3fc

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000100c000061e4 0x080000806000030f

def z684 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c307070780e6014 0xf4e1838383c07300

def z685 : W := mkw 0x0000020000801000 0x0000001000040080 0x63000e0007801809 0x03180070003c00c0

def z686 : W := mkw 0x0400504808002049 0x0020028240400102 0x0000100c00002060 0x0000008060000103

def z687 : W := mkw 0x04007dff4802615b 0x082003effa40130a 0x20007fff800061ec 0x090003fffc00030f

def z688 : W := mkw 0x000020104802615b 0x000001008240130a 0x00000000000061e0 0x000000000000030f

def z689 : W := mkw 0x0400700048006018 0x0020038002400300 0x1c00600078000000 0x50e0030003c00000

def z690 : W := mkw 0x2112843285160982 0x810894219428b04c 0x00338073841e599f 0x28019c039c20f2cc

def z691 : W := mkw 0xdeed70587a6be15b 0x06f76b82c3d35f0a 0x9cfc707c787fe1f6 0xfce7e383e3c3ff0f

def z692 : W := mkw 0x7bffa632c5965992 0x83dffd31962cb2cc 0x7fffee73c79e599f 0xfbffff739e3cf2cc

def z693 : W := mkw 0x0045008500000000 0x0002280428000000 0x00cc118c00000000 0x8006608c60000000

def z694 : W := mkw 0x5fff7def48006018 0x0afffbef7a400300 0xfffffffff800601f 0xffffffffffc00300

def z695 : W := mkw 0x0112a20045945010 0x00089510022ca280 0x6333ee00479e581f 0x73199f70023cf2c0

def z696 : W := mkw 0x0045008580208aa0 0x400228042c010455 0x80cc118f8061ffec 0x8c06608c7c030fff

def z697 : W := mkw 0x0000008580000aa0 0x400000042c000055 0x0000000f800001e0 0x080000007c00000f

def z698 : W := mkw 0x7fffdfef85941880 0x8bfffeff7c2ca0c4 0x7fffffff8780180f 0xebfffffffc3c00c0

def z699 : W := mkw 0x16c57b856ac0741c 0x00b62bdc2b5603a0 0xffcfff8fffe07e1f 0xfffe7ffc7fff03f0

def z700 : W := mkw 0x08282058580b615b 0x00414102c2c05b0a 0x803c007c781fe1f2 0x1c01e003e3c0ff0f

def z701 : W := mkw 0x0112a01045164112 0x000895008228b208 0x4333e070479e4197 0x7a199f03823cf20c

def z702 : W := mkw 0x04007010580b615b 0x0020038082c05b0a 0x9c007000781fe1f4 0xf4e0038003c0ff0f

def z703 : W := mkw 0x5fffddef84100880 0x0afffeef7c208044 0x7fffffff8410599f 0xebfffffffc2082cc

def z704 : W := mkw 0x2112862285941880 0x81089431142ca0c4 0x6333ee738780180f 0x6b199f739c3c00c0

def z705 : W := mkw 0x37927f326bc6751e 0x81bc93f9935e33a8 0x7f306e707b8e0000 0x53f9837383dc7000

def z706 : W := mkw 0x3392a632e7d65992 0x819c9531973eb2cc 0xfff3ee73fffe599f 0xffff9f739ffff2cc

def z707 : W := mkw 0xdbff8da7377d8000 0x0edffc6d39bbec00 0xffffeff3ffff801f 0xffffff7f9ffffc00

def z708 : W := mkw 0x92808000377d8000 0x0494040001bbec00 0x9cc000007fff8010 0x94e6000003fffc00

def z709 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c3c607c781fc1f6 0x78e1e303e3c0fe0f

def z710 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdf3f80007b9f8012 0xf6f9fc0003dcfc00

def z711 : W := mkw 0xdeed59cd32490000 0x0ef76ace69924800 0x1ccc118c38000000 0x80e6608c61c00000

def z712 : W := mkw 0x2000a210cd96799a 0x81000510866cb3cc 0x800000007f9e7990 0x1400000003fcf3cc

def z713 : W := mkw 0x0112a43245164112 0x000895219228b208 0x6333ee73c79e419f 0x7b199f739e3cf20c

def z714 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffcc7f8c7fe07e1f 0xfffe63fc63ff03f0

def z715 : W := mkw 0x040072584882755f 0x00200392c24413aa 0x0000707c00007fe4 0x08000383e00003ff

def z716 : W := mkw 0xcd7ffb005dbdf41c 0x066bffd802edefa0 0x203fff80001ffe0e 0x0101fffc0000fff0

def z717 : W := mkw 0xd7d7f0586f76e15b 0x06bebf82c37bb70a 0x43c3f07c07e061e5 0x0a1e1f83e03f030f

def z718 : W := mkw 0x0c6df0dddc3bebfb 0x40636f86eee1df5f 0x1cf3e1f3fc6e1e09 0x50e79f0f9fe370f0

def z719 : W := mkw 0xa000a210fffff9db 0x8500051087ffffce 0x800000007ffff9f0 0x1400000003ffffcf

def z720 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff918fffffa7f3 0xfefffc8c7ffffd3f

def z721 : W := mkw 0x886d8085b77d8aa0 0x44436c042dbbec55 0x9cff918fffffffff 0xfce7fc8c7fffffff

def z722 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdff000007bee0000 0xd6ff800003df7000

def z723 : W := mkw 0xdbff8422377d8000 0x06dffc2111bbec00 0xffffee707fff8013 0xf7ffff7383fffc00

def z724 : W := mkw 0xdbba0085b34d0aa0 0x46ddd0042d9a6855 0x5f30118ffb8e7fec 0x5af9808c7fdc73ff

def z725 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdffc00007fff8010 0xd6ffe00003fffc00

def z726 : W := mkw 0x2000a210cd9679db 0x81000510866cb3ce 0x00000000479e79f0 0x10000000023cf3cf

def z727 : W := mkw 0x4d7f5def00000000 0x0a6bfaef78000000 0x203fee7f80000002 0x0901ff73fc000000

def z728 : W := mkw 0x0112042200000000 0x0008902110000000 0x6303ee738000000d 0x0b181f739c000000

def z729 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00300000479e5992 0x70018000023cf2cc

def z730 : W := mkw 0xdbba0422334d0000 0x06ddd021119a6800 0x7f33ee73fb8e000f 0x7bf99f739fdc7000

def z731 : W := mkw 0x8400ddef377d8000 0x0c2006ef79bbec00 0xa0007fffffff801c 0x1d0003fffffffc00

def z732 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x633fee7fc79fd9ff 0x7b19ff73fe3cfecf

def z733 : W := mkw 0xdaa80000334d0000 0x06d54000019a6800 0x1c0000007b8e0000 0x10e0000003dc7000

def z734 : W := mkw 0x7eedfbddc5965992 0x8bf76fdeee2cb2cc 0x1ccc118c479e5990 0x90e6608c623cf2cc

def z735 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8060260f 0xeffffffffc030130

def z736 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7fc07f807fe01e0d 0xf3fe03fc03ff00f0

def z737 : W := mkw 0x2112263241865112 0x81089131920c3288 0x6333ee73c39e419f 0x7b199f739e1cf20c

def z738 : W := mkw 0xdfff5def334d0000 0x0efffaef799a6800 0xfffffffffb9f801f 0xffffffffffdcfc00

def z739 : W := mkw 0x0c285058180b214b 0x00614282c0c0590a 0x9c3c707c381fa1e6 0xece1e383e1c0fd0f

def z740 : W := mkw 0xa000a210f7df5992 0x8500051087befacc 0x000000007f9e5990 0x1000000003fcf2cc

def z741 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7f3ffe7f80000006 0xebf9fff3fc000000

def z742 : W := mkw 0xdbff0000334d0000 0x06dff800019a6800 0xdfff80007b9f8013 0xf6fffc0003dcfc00

def z743 : W := mkw 0x5fbadd6a84308aa0 0x4afdd6eb54218455 0xff306e700471fff0 0x47f9837380238fff

def z744 : W := mkw 0xfaeda210f7ffd992 0x87d76d1087bffecc 0x9ccc00007fffd990 0x94e6600003fffecc

def z745 : W := mkw 0xfaed2632f2ebd992 0x87d7693197975ecc 0xbccc6e73b861d98c 0x8de663739dc30ecc

def z746 : W := mkw 0x2400767ac88279db 0x812003b3d64413ce 0x20006e738000598c 0x090003739c0002cc

def z747 : W := mkw 0x2112a210c5965992 0x81089510862cb2cc 0x43300000479e5990 0x52198000023cf2cc

def z748 : W := mkw 0x57d75def00000000 0x0abebaef78000000 0x63cfffff8000000f 0xab1e7ffffc000000

def z749 : W := mkw 0x92808000b77d8aa0 0x4494040005bbec55 0xdfc011807ffffffd 0xf6fe008c03ffffff

def z750 : W := mkw 0xdbff846a377d8000 0x0edffc2351bbec00 0xdfff80707fff8013 0xf6fffc0383fffc00

def z751 : W := mkw 0x1eed59cd00000000 0x00f76ace68000000 0x7fffffff8000000f 0xebfffffffc000000

def z752 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff8183ffffdf9f 0xfefffc0c1ffffefc

def z753 : W := mkw 0x3792dd32af562d8e 0x81bc96e9957ab16c 0x9cf391f3b87e2782 0x8ce79c8f9dc3f13c

def z754 : W := mkw 0xdfff5def32698000 0x0efffaef79934c00 0xffffffffffe1801f 0xffffffffffff0c00

def z755 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0x5ff38183ffee1e09 0x52ff9c0c1fff70f0

def z756 : W := mkw 0xdfff5def32490000 0x0efffaef79924800 0x7fffffffb800000f 0xebfffffffdc00000

def z757 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0xe3cfff8f8471ffff 0xef1e7ffc7c238fff

def z758 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0xffc01f807fe07e1d 0xf7fe00fc03ff03f0

def z759 : W := mkw 0x215726b741a6d332 0xc10ab935ba0d3699 0xe3fc7ffc43efa660 0xd71fe3ffe21f7d33

def z760 : W := mkw 0x093a0000110d0000 0x0049d00000886800 0xdf3c00007b9f8012 0xf6f9e00003dcfc00

def z761 : W := mkw 0x5fff5def00000220 0x4afffaef78000011 0x7fffffff8000266f 0xebfffffffc000133

def z762 : W := mkw 0xdaed0000336d8000 0x06d76800019b6c00 0x9ccc00007bef8000 0x94e6600003df7c00

def z763 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7f3fffff8000000e 0x4bf9fffffc000000

def z764 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffee7f80000003 0xebffff73fc000000

def z765 : W := mkw 0x1392800027540000 0x009c9400013aa000 0x5f3380007f9e0013 0x72f99c0003fcf000

def z766 : W := mkw 0x097f8000153d8000 0x004bfc0000a9ec00 0xdfff80007fff8013 0xf6fffc0003fffc00

def z767 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8460001f 0xeffffffffc230000

def z768 : W := mkw 0xdbff8900377d8404 0x06dffc4801bbec20 0xdfff81807fff8613 0xf6fffc0c03fffc30

def z769 : W := mkw 0x5fff5def10090000 0x0afffaef78804800 0x7ffffffff80e000f 0xfbffffffffc07000

def z770 : W := mkw 0x16807b486ac0745d 0x00b403da435603a2 0xffc07f8c7fe07e7d 0xf7fe03fc63ff03f3

def z771 : W := mkw 0x0112042200000000 0x0008902110000000 0x633ffe7f8000000f 0xeb19fff3fc000000

def z772 : W := mkw 0x5eed59cd3a49244d 0x0af76ace69d24922 0x9ccc118c3861a660 0x84e6608c61c30d33

def z773 : W := mkw 0xd3d78000377d8000 0x069ebc0001bbec00 0xdfc380007fff8011 0xf6fe1c0003fffc00

def z774 : W := mkw 0x2d3ad66a9d9d38c9 0x8169d6b354ece9c6 0xff0f9e0fbf81b869 0x87f87cf07dfc0dc3

def z775 : W := mkw 0xdbff042232698000 0x06dff82111934c00 0xffffee73b861800f 0xefffff739dc30c00

def z776 : W := mkw 0x1280000022400000 0x0094000001120000 0xdff000007ffe0013 0xf6ff800003fff000

def z777 : W := mkw 0x5eed5def00000000 0x0af76aef78000000 0x3ccfffff8000000f 0xa9e67ffffc000000

def z778 : W := mkw 0x57d75def00000000 0x0abebaef78000000 0x63c3eff380000009 0x031e1f7f9c000000

def z779 : W := mkw 0x5fff5def01040000 0x0afffaef78082000 0x7fffffffc38e000f 0xfbfffffffe1c7000

def z780 : W := mkw 0x893a8000377d8000 0x0449d40001bbec00 0xdf3f80007fff8013 0xf6f9fc0003fffc00

def z781 : W := mkw 0xa000a210fffffd9e 0x8500051087ffffec 0x800000007fffff90 0x1400000003fffffc

def z782 : W := mkw 0x5fff5def00208220 0x4afffaef78010411 0xffffffff8461fe7f 0xeffffffffc230ff3

def z783 : W := mkw 0x2000a210c5b6d992 0x81000510862db6cc 0x8000000047ffd990 0x14000000023ffecc

def z784 : W := mkw 0xdaed8085b77d8aa0 0x46d76c042dbbec55 0x9ccf918fffffffff 0xbce67c8c7fffffff

def z785 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f807ff07f9f 0xfffe03fc03ff83fc

def z786 : W := mkw 0xdaed8000377d8000 0x06d76c0001bbec00 0x9cfc00007fff8012 0xf4e7e00003fffc00

def z787 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffefff8000000b 0x4bffff7ffc000000

def z788 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffcc7f807ff1fe1f 0xf7fe63fc03ff8ff0

def z789 : W := mkw 0x1392042222400000 0x009c902111120000 0xfff3ee73ffe0001f 0xffff9f739fff0000

def z790 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5ff000007fee0001 0x52ff800003ff7000

def z791 : W := mkw 0x015704a700000000 0x000ab82538000000 0x63f3eff38000000f 0x6b1f9f7f9c000000

def z792 : W := mkw 0x53d70da700000000 0x0a9eb86d38000000 0x63f3eff380000009 0x431f9f7f9c000000

def z793 : W := mkw 0x2828a210d59f5992 0x8141451086acfacc 0x9c3c00007f9fd992 0xf4e1e00003fcfecc

def z794 : W := mkw 0x92800000334d0000 0x04940000019a6800 0x5f0000007b8e0000 0x52f8000003dc7000

def z795 : W := mkw 0x497f26ef6ac0741c 0x0a4bf9377b5603a0 0x803f807fffe07e12 0x1c01fc03ffff03f0

def z796 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff900c7fffa073 0xf6fffc8063fffd03

def z797 : W := mkw 0x16c5fb85eef0febc 0x40b62fdc2f7787f5 0x7f0fee0ffb9181e2 0x5bf87f707fdc8c0f

def z798 : W := mkw 0x04005def00000000 0x082002ef78000000 0x2003ffff8000000f 0x29001ffffc000000

def z799 : W := mkw 0xdbff8422b77d8880 0x06dffc2115bbec44 0xffffee73ffffd99f 0xffffff739ffffecc

def z800 : W := mkw 0xdfff5def3a69a40c 0x0efffaef79d34d20 0xffffffffb861a60f 0xeffffffffdc30d30

def z801 : W := mkw 0x24007fffc88279db 0x892003fffe4413ce 0x20007fff800079ec 0x090003fffc0003cf

def z802 : W := mkw 0x0112842285140880 0x000894211428a044 0x6333ee73c79e599f 0x7b199f739e3cf2cc

def z803 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc01f807fe07e19 0x97fe00fc03ff03f0

def z804 : W := mkw 0x1aa80b5832cb1547 0x00d5405ac19658aa 0x63fc0ffc07ff9feb 0x0b1fe07fe03ffcff

def z805 : W := mkw 0xdbff0000334d0000 0x06dff800019a6800 0xdfff80007fee0013 0xf6fffc0003ff7000

def z806 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x9c3c107c781fe1f6 0xfce1e083e3c0ff0f

def z807 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x9c3c007c381f81e2 0x8ce1e003e1c0fc0f

def z808 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3ff07ff81fe1ff 0xfce1ff83ffc0ff0f

def z809 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdffc00007fff8013 0xf6ffe00003fffc00

def z810 : W := mkw 0x0512542200000000 0x002892a110000000 0x7f33fe738000000f 0xebf99ff39c000000

def z811 : W := mkw 0xdbff0000334d0000 0x06dff800019a6800 0x5ff380007b8e0001 0x52ff9c0003dc7000

def z812 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x63f3eff3c7fe5f9f 0x7b1f9f7f9e3ff2fc

def z813 : W := mkw 0x0c287258588b715b 0x00614392c2c45b8a 0x9c3c707c7f9ff9f6 0xfce1e383e3fcffcf

def z814 : W := mkw 0xdaed8000377d8000 0x06d76c0001bbec00 0xdfcc00007fff8011 0xf6fe600003fffc00

def z815 : W := mkw 0x5fff5def2a40240c 0x0afffaef79520120 0x7fffffffb800000f 0xebfffffffdc00000

def z816 : W := mkw 0x040072584882715b 0x00200392c244138a 0x20007e7c000079ec 0x090003f3e00003cf

def z817 : W := mkw 0xe97f84b7953f8ba2 0xc74bfc25bca9fc5d 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z818 : W := mkw 0x16807b586ac2755f 0x00b403dac35613aa 0xffc07ff07fe07e1d 0xf7fe03ff83ff03f0

def z819 : W := mkw 0x05125def00000000 0x082892ef78000000 0x6303ffff8000000d 0x0b181ffffc000000

def z820 : W := mkw 0x08282058580b615b 0x00414102c2c05b0a 0x9c3c007c781fe1f2 0xfce1e003e3c0ff0f

def z821 : W := mkw 0x17925d2200000000 0x00bc92e910000000 0x7f33ee738000000f 0x6bf99f739c000000

def z822 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdf3f80007fff8012 0x56f9fc0003fffc00

def z823 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007fffd81f 0xf6fffc0003fffec0

def z824 : W := mkw 0x08282010500b4112 0x0041410082805a08 0x9c3c707c781fe1f6 0xfce1e383e3c0ff0f

def z825 : W := mkw 0x53d72db7580b615b 0x0a9eb96dbac05b0a 0xe3c38f83f81fe1f9 0x171e1c7c1fc0ff0f

def z826 : W := mkw 0x0828000032490000 0x0041400001924800 0x9c3c00007fff8012 0xf4e1e00003fffc00

def z827 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff8003ffff801f 0xfefffc001ffffc00

def z828 : W := mkw 0x5fff5def18092049 0x0afffaef78c04902 0xffffffffb811e1ff 0xeffffffffdc08f0f

def z829 : W := mkw 0xdfff5def23440000 0x0efffaef791a2000 0x7fffffff8380000f 0xebfffffffc1c0000

def z830 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee738400581f 0x6b199f739c2002c0

def z831 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffffc01e001f 0xfbfffffffe00f000

def z832 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7ff3fff38000000f 0xebff9fff9c000000

def z833 : W := mkw 0x92c58085b77d8aa0 0x44962c042dbbec55 0xdfcf918fffffffff 0xfefe7c8c7fffffff

def z834 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0x7fc00f807fe01e09 0x53fe007c03ff00f0

def z835 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00000000439e0180 0x10000000021cf00c

def z836 : W := mkw 0x0045808585348aa0 0x40022c042c29a455 0x80cf918fc7ffffff 0xbc067c8c7e3fffff

def z837 : W := mkw 0x01120da700000000 0x0808906d38000000 0x6333eff38000000f 0x6b199f7f9c000000

def z838 : W := mkw 0x2112263241865112 0x81089131920c3288 0x6333ee73c38e0002 0x5b199f739e1c7000

def z839 : W := mkw 0x08288000151d0000 0x0041440000a8e800 0x9c3c00007f9f8012 0xf4e1e00003fcfc00

def z840 : W := mkw 0x2c28f258dd9f79db 0x81614792c6ecfbce 0x9c0c100c7f9ff9f0 0x94e0608063fcffcf

def z841 : W := mkw 0x5fff5def2a40240c 0x0afffaef79520120 0xffffffffffe0261f 0xffffffffffff0130

def z842 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c79e0193 0x7b199f739e3cf00c

def z843 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c78e180f 0x7b199f739e3c70c0

def z844 : W := mkw 0x04007b584882755f 0x002003dac24413aa 0x20007ff000007e0c 0x010003ff800003f0

def z845 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5ff380007ffe0013 0x72ff9c0003fff000

def z846 : W := mkw 0xdbff8085377d8220 0x46dffc0429bbec11 0xdfff81807fff8613 0xf6fffc0c03fffc30

def z847 : W := mkw 0x015704a700000000 0x000ab82538000000 0x633fee7f8000000f 0x6b19ff73fc000000

def z848 : W := mkw 0x2045a295c5b6dbb2 0xc1022d14ae2db6dd 0x80cc118c47fffff0 0x9406608c623fffff

def z849 : W := mkw 0x16c55def00000000 0x08b62aef78000000 0x7fcfffff8000000f 0xebfe7ffffc000000

def z850 : W := mkw 0x4d7f5def00000000 0x0a6bfaef78000000 0x20ffffff8000000f 0xa907fffffc000000

def z851 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8461ffed 0x8c067c8c7c230fff

def z852 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c381fe1e6 0x8ce1e383e1c0ff0f

def z853 : W := mkw 0x16805b002ac0340c 0x00b402d8015601a0 0xffc01f807fe03e19 0xf7fe00fc03ff01f0

def z854 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc06f807fe01e19 0xf7fe037c03ff00f0

def z855 : W := mkw 0xdbff84ef377d8000 0x0edffc2779bbec00 0xdfff91ffffff801f 0xfefffc8ffffffc00

def z856 : W := mkw 0x12802b0062c05414 0x00940158031602a0 0xffc06f807fe05e1d 0xf7fe037c03ff02f0

def z857 : W := mkw 0xdbff8422377d8000 0x06dffc2111bbec00 0xffff8e03ffff801b 0xf7fffc701ffffc00

def z858 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00000000001e5980 0x000000000000f2cc

def z859 : W := mkw 0x24007fffc8827d9e 0x892003fffe4413ec 0x20007fff80007f8c 0x090003fffc0003fc

def z860 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff918fffffbe7b 0xf6fffc8c7ffffdf3

def z861 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7f33ee7380000000 0x43f99f739c000000

def z862 : W := mkw 0xdbff8000b77d8880 0x06dffc0005bbec44 0xdfff80007fffd993 0xf6fffc0003fffecc

def z863 : W := mkw 0xfbbaa210f7df5992 0x87ddd51087befacc 0x5f3000007f9e5990 0x52f9800003fcf2cc

def z864 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x0000000007805980 0x00000000003c02cc

def z865 : W := mkw 0x1fba5d6a00000000 0x00fdd2eb50000000 0x7fffffff8000000f 0xebfffffffc000000

def z866 : W := mkw 0x0512546a00000000 0x002892a350000000 0x6333fe7f8000000f 0x6b199ff3fc000000

def z867 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfffe0707fff8017 0xfeffff0383fffc00

def z868 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x63f3fff3c79e599f 0xfb1f9fff9e3cf2cc

def z869 : W := mkw 0xdeed59cd32698220 0x4ef76ace69934c11 0x9ccc118c3861a660 0x84e6608c61c30d33

def z870 : W := mkw 0xdfff5def110d0000 0x0efffaef78886800 0x7fffffff800e000f 0xebfffffffc007000

def z871 : W := mkw 0x04455def00000000 0x08222aef78000000 0x20c3ffff8000000d 0x09061ffffc000000

def z872 : W := mkw 0xdbff8085b77d8880 0x06dffc042dbbec44 0xdfff918fffffd99f 0xfefffc8c7ffffecc

def z873 : W := mkw 0x0c285058180b214b 0x00614282c0c0590a 0x9c3c107c781fa1f2 0xfce1e083e3c0fd0f

def z874 : W := mkw 0x2445ffb7ccb2ffbe 0xc1222ffdbe6597fd 0xa0cfffff8471ffff 0xad067ffffc238fff

def z875 : W := mkw 0xdbff84efb77d8aa0 0x4edffc277dbbec55 0xdfff807fffff81f3 0xfefffc03fffffc0f

def z876 : W := mkw 0x1392042200000000 0x009c902110000000 0x7ff3ee738000000f 0xebff9f739c000000

def z877 : W := mkw 0xd3d78da7a7748aa0 0x4e9ebc6d3d3ba455 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z878 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c3c707c781f81e6 0xf8e1e383e3c0fc0f

def z879 : W := mkw 0xdbff0da7334d0000 0x0edff86d399a6800 0x7ff38f83fb8e0009 0x53ff9c7c1fdc7000

def z880 : W := mkw 0x3fba7f7a7bcf755f 0x81fdd3fbd3de7baa 0x7f306e707b8e0000 0x53f9837383dc7000

def z881 : W := mkw 0x297f84ff953f8be3 0xc14bfc27fca9fc5f 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z882 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff80007e0f 0xebfffffffc0003f0

def z883 : W := mkw 0xdfff5def334d0000 0x0efffaef799a6800 0xffffffffffee001f 0xffffffffffff7000

def z884 : W := mkw 0xdbba8000377d8000 0x06ddd40001bbec00 0xdf3380007fff8013 0x76f99c0003fffc00

def z885 : W := mkw 0xdaed000032698000 0x06d7680001934c00 0xdffc00007fff8013 0xf6ffe00003fffc00

def z886 : W := mkw 0x57d75da700000000 0x0abebaed38000000 0x7ff3fff38000000f 0xebff9fff9c000000

def z887 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff81807fff9e1b 0xf6fffc0c03fffcf0

def z888 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5fff80007b9f8003 0xf2fffc0003dcfc00

def z889 : W := mkw 0x5fff5def00208220 0x4afffaef78010411 0x7fffffff8060060f 0xebfffffffc030030

def z890 : W := mkw 0x0045008580208aa0 0x400228042c010455 0x80cf918f8061ffef 0xac067c8c7c030fff

def z891 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x00cf918f8471ffef 0x08067c8c7c238fff

def z892 : W := mkw 0x04007b104882751e 0x002003d8824413a8 0x20007ff000007f8c 0x090003ff800003fc

def z893 : W := mkw 0x0c287b58588b755f 0x006143dac2c45baa 0xbc3c7e7c781fe1f6 0xfde1e3f3e3c0ff0f

def z894 : W := mkw 0x1680590022400000 0x00b402c801120000 0xffc07f807fe07e1d 0xf7fe03fc03ff03f0

def z895 : W := mkw 0x04007b584882755f 0x002003dac24413aa 0x20006e7000000000 0x0100037380000000

def z896 : W := mkw 0x45575def00000000 0x0a2abaef78000000 0x2003ffff8000000c 0x09001ffffc000000

def z897 : W := mkw 0x2112a632c5b6dbb2 0xc1089531962db6dd 0xe3f3fff3c7ffffff 0xff1f9fff9e3fffff

def z898 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7ff3eff38000000f 0x6bff9f7f9c000000

def z899 : W := mkw 0x0c6d5def00000000 0x08636aef78000000 0x3cffffff8000000f 0xe9e7fffffc000000

def z900 : W := mkw 0x16807b586ac2755f 0x00b403dac35613aa 0xfff07ffc7ffe7fff 0xffff83ffe3fff3ff

def z901 : W := mkw 0x0112042201040000 0x0008902110082000 0x6333ee73c38e000f 0x7b199f739e1c7000

def z902 : W := mkw 0xdfff5def22608000 0x0efffaef79130400 0x7fffffff8060000f 0xebfffffffc030000

def z903 : W := mkw 0xdbff84a7377d8000 0x06dffc2539bbec00 0xffffffffffff801f 0xfffffffffffffc00

def z904 : W := mkw 0x2000a210efd67d9e 0x81000510877eb3ec 0x000000007f9e5990 0x1000000003fcf2cc

def z905 : W := mkw 0x05575def00000000 0x082abaef78000000 0x63ffffff8000000f 0xeb1ffffffc000000

def z906 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffeff38000000b 0xe3ffff7f9c000000

def z907 : W := mkw 0x0157042200000000 0x000ab82110000000 0x63ffee738000000f 0xeb1fff739c000000

def z908 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff8400581f 0xebfffffffc2002c0

def z909 : W := mkw 0x5fff5d6a00000000 0x0afffaeb50000000 0x7fffee738000000f 0xebffff739c000000

def z910 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee7380000002 0x4b199f739c000000

def z911 : W := mkw 0x0000042200000000 0x0000002110000000 0x2003ee738000000f 0x29001f739c000000

def z912 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xfff07ff07fe07e1f 0xffff83ff83ff03f0

def z913 : W := mkw 0x05125d2200000000 0x002892e910000000 0x6333fff38000000f 0x6b199fff9c000000

def z914 : W := mkw 0x16807b106ac2751e 0x00b403d8835613a8 0xffc07f807ffe7f9d 0xf7fe03fc03fff3fc

def z915 : W := mkw 0x04007fff4882755f 0x082003fffa4413aa 0x20007fff80007fec 0x090003fffc0003ff

def z916 : W := mkw 0x24007258c88279db 0x81200392c64413ce 0x0000707c000079e4 0x08000383e00003cf

def z917 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7fc07f807fe07e0d 0x53fe03fc03ff03f0

def z918 : W := mkw 0x2445f6ffccb2fbfb 0xc1222fb7fe6597df 0xa0cfffff8471ffff 0xad067ffffc238fff

def z919 : W := mkw 0x0400720048807018 0x0020039002440380 0xffc07f807fe07e1d 0xf7fe03fc03ff03f0

def z920 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe333ee73c7fe7f9f 0x7f199f739e3ff3fc

def z921 : W := mkw 0x2000a210eff6ffbe 0xc1000510877fb7fd 0x800000007ffffff0 0x1400000003ffffff

def z922 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x9cff80007fff8012 0x94e7fc0003fffc00

def z923 : W := mkw 0x0d7f54ef00000000 0x006bfaa778000000 0x7fffffff8000000f 0xebfffffffc000000

def z924 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007bff8002 0xd6fffc0003dffc00

def z925 : W := mkw 0x0c285058180b214b 0x00614282c0c0590a 0x9c3c107c381fe1f6 0xace1e083e1c0ff0f

def z926 : W := mkw 0x5fff5def22400000 0x0afffaef79120000 0xffffffffffe07e1f 0xffffffffffff03f0

def z927 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x800c100c479ff9f6 0xbc006080623cffcf

def z928 : W := mkw 0x1bba8000375d0000 0x00ddd40001bae800 0xdfff80007fff8013 0xf6fffc0003fffc00

def z929 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff91807fff801f 0xf6fffc8c03fffc00

def z930 : W := mkw 0x5fba5def00000000 0x0afdd2ef78000000 0x7f33ffff8000000f 0x6bf99ffffc000000

def z931 : W := mkw 0x1280220062c05010 0x0094011003160280 0xffc07f807fe07e1d 0xf7fe03fc03ff03f0

def z932 : W := mkw 0x5fff546a00000000 0x02fffaa350000000 0x7ffffe7f8000000f 0xebfffff3fc000000

def z933 : W := mkw 0x5fff5def22400000 0x0afffaef79120000 0x7ffffffffb80000f 0xfbffffffffdc0000

def z934 : W := mkw 0x16807b106ac2751e 0x00b403d8835613a8 0xffc07ff07fe07f9d 0xfffe03ff83ff03fc

def z935 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5fff80007fee0003 0xf2fffc0003ff7000

def z936 : W := mkw 0x88288000377d8000 0x0441440001bbec00 0x9c3000007fff8010 0x54e1800003fffc00

def z937 : W := mkw 0xdbba8000377d8000 0x06ddd40001bbec00 0xdff000007fff8011 0xf6ff800003fffc00

def z938 : W := mkw 0x53d70da700000000 0x0a9eb86d38000000 0x63c3eff38000000d 0x0b1e1f7f9c000000

def z939 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff800fffffd9ff 0xfefffc007ffffecf

def z940 : W := mkw 0x2000a210c4b2dbb2 0xc1000510862596dd 0x800000000471fff0 0x0400000000238fff

def z941 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7f3ffe7f8000000f 0xebf9fff3fc000000

def z942 : W := mkw 0x2112a632c5965bb2 0xc1089531962cb2dd 0x6333ee73c79e7fff 0x7b199f739e3cf3ff

def z943 : W := mkw 0x1aa8000032490000 0x00d5400001924800 0xdff000007fee0011 0xf6ff800003ff7000

def z944 : W := mkw 0x2112a63245965112 0x81089531922cb288 0x6333ee73c79e001f 0x7b199f739e3cf000

def z945 : W := mkw 0x004504a700000000 0x0002282538000000 0x20cfffff8000000f 0xa9067ffffc000000

def z946 : W := mkw 0x2000a210e7d65d96 0x81000510873eb2ec 0x0000000047fe5f90 0x10000000023ff2fc

def z947 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee73c01e001f 0x7b199f739e00f000

def z948 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfcf80007fff8011 0x96fe7c0003fffc00

def z949 : W := mkw 0xdbba8000375d0000 0x06ddd40001bae800 0x5f3000007f9e0010 0x52f9800003fcf000

def z950 : W := mkw 0x12800b0022c01404 0x00940058011600a0 0xffc00f803fe01e09 0x87fe007c01ff00f0

def z951 : W := mkw 0x2112a632c5b6dbb2 0xc1089531962db6dd 0x6333ee73c79fd9ff 0x7b199f739e3cfecf

def z952 : W := mkw 0x04007b584882755f 0x002003dac24413aa 0xa0cc7ffc0471ffff 0xad0663ffe0238fff

def z953 : W := mkw 0x1280800027540000 0x00940400013aa000 0xdfc000007ffe0011 0xf6fe000003fff000

def z954 : W := mkw 0xdbff8085377d8000 0x06dffc0429bbec00 0xdfff918c7fff8013 0xf6fffc8c63fffc00

def z955 : W := mkw 0x24007f324882751e 0x812003f9924413a8 0x20006e7000000000 0x0100037380000000

def z956 : W := mkw 0x2112a632cd96799a 0x81089531966cb3cc 0xe333ee73ff9e799f 0x7f199f739ffcf3cc

def z957 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c7c7ffff6 0xfce1e383e3e3ffff

def z958 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff801181ef 0xebfffffffc008c0f

def z959 : W := mkw 0x08280058100b0143 0x00414002c080580a 0x1c3c007c781f81e2 0x58e1e003e3c0fc0f

def z960 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c39e4196 0x7b199f739e1cf20c

def z961 : W := mkw 0xdbff0000336d8000 0x06dff800019b6c00 0x5f3c00007b8f8000 0x52f9e00003dc7c00

def z962 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c79e181b 0x73199f739e3cf0c0

def z963 : W := mkw 0x2112a632cd9679db 0x81089531966cb3ce 0x6333ee73c79e79ff 0x7b199f739e3cf3cf

def z964 : W := mkw 0xdfff5def10298000 0x0efffaef78814c00 0x7fffffff8001800f 0xebfffffffc000c00

def z965 : W := mkw 0x5fff5def10090041 0x0afffaef78804802 0x7fffffff8001806f 0xebfffffffc000c03

def z966 : W := mkw 0x24007b10c8827d9e 0x812003d8864413ec 0x20007f8000007f8c 0x010003fc000003fc

def z967 : W := mkw 0x0c28504810090000 0x0061428240804800 0x9c3c707c781fe1f6 0xfce1e383e3c0ff0f

def z968 : W := mkw 0xdbba0422334d0000 0x06ddd021119a6800 0x7f306e707b8e0000 0x53f9837383dc7000

def z969 : W := mkw 0xdfff5def3a69a049 0x0efffaef79d34d02 0xffffffffb861a06f 0xeffffffffdc30d03

def z970 : W := mkw 0x497f04ef00000000 0x0a4bf82778000000 0x633fee7f80000002 0x4b19ff73fc000000

def z971 : W := mkw 0xdbff8da7b77d8aa0 0x4edffc6d3dbbec55 0xffff8f83ffff9e1b 0xf7fffc7c1ffffcf0

def z972 : W := mkw 0x0c287258588b715b 0x00614392c2c45b8a 0xff3c7e7c7b9fe1f6 0xfff9e3f3e3dcff0f

def z973 : W := mkw 0x88288000377d8000 0x0441440001bbec00 0x9c0c00007fff8010 0x94e0600003fffc00

def z974 : W := mkw 0xdbba8000375d0000 0x06ddd40001bae800 0x5f3380007b9e0002 0x52f99c0003dcf000

def z975 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5fff80007fff8003 0x52fffc0003fffc00

def z976 : W := mkw 0x5bba042200000000 0x02ddd02110000000 0x7f33ee738000000f 0x6bf99f739c000000

def z977 : W := mkw 0x04007b584882755f 0x002003dac24413aa 0x20007e7c000061e4 0x090003f3e000030f

def z978 : W := mkw 0x093a8000951d0880 0x0049d40004a8e844 0xdf3f900fff9ff9ff 0xfef9fc807ffcffcf

def z979 : W := mkw 0x093a046a00000000 0x0049d02350000000 0x633fee7f8000000f 0x6b19ff73fc000000

def z980 : W := mkw 0xdaa88000377d8000 0x06d5440001bbec00 0x9c0000007fff8010 0x14e0000003fffc00

def z981 : W := mkw 0x497f04ef00000000 0x0a4bf82778000000 0x203fee7f8000000e 0x0901ff73fc000000

def z982 : W := mkw 0x04455def00000000 0x08222aef78000000 0x200fffff8000000e 0x09007ffffc000000

def z983 : W := mkw 0xdfff5def32698220 0x4efffaef79934c11 0xffffffffb861a66f 0xeffffffffdc30d33

def z984 : W := mkw 0x5fba7f7a7acb755f 0x0afdd3fbd3d65baa 0x7f306e707b8e0000 0x53f9837383dc7000

def z985 : W := mkw 0xdbff0000336d8000 0x06dff800019b6c00 0xdfff80007bef8003 0xf6fffc0003df7c00

def z986 : W := mkw 0x0112042200000000 0x0008902110000000 0x63f3fff38000000f 0xeb1f9fff9c000000

def z987 : W := mkw 0xdbff8085377d8000 0x06dffc0429bbec00 0xdfff8183ffff801b 0xf6fffc0c1ffffc00

def z988 : W := mkw 0x3280a210e7d65992 0x81940510873eb2cc 0xdfc000007ffe5991 0xf6fe000003fff2cc

def z989 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80fff1ff8471ffff 0xec07ff8ffc238fff

def z990 : W := mkw 0x16805b002ac0340c 0x00b402d8015601a0 0xffc07f803fe03e0d 0xe7fe03fc01ff01f0

def z991 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7f3fee7f8000000f 0x6bf9ff73fc000000

def z992 : W := mkw 0xdbff84ef377d8000 0x0edffc2779bbec00 0xffffee7fffff801f 0xffffff73fffffc00

def z993 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffcc7f8c7fe1fe7d 0xf7fe63fc63ff0ff3

def z994 : W := mkw 0xdbba046a334d0000 0x0eddd023519a6800 0x5f3000707b8e0000 0x52f9800383dc7000

def z995 : W := mkw 0x1aa8000032490000 0x00d5400001924800 0x5f3000007b8e0000 0x52f9800003dc7000

def z996 : W := mkw 0x5bff000032490000 0x02dff80001924800 0xdfff80007fff8013 0xf6fffc0003fffc00

def z997 : W := mkw 0xdbff8d22377d8000 0x0edffc6911bbec00 0xffff8e007fff8013 0xf7fffc7003fffc00

def z998 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c607c781f81f2 0xfce1e303e3c0fc0f

def z999 : W := mkw 0x040070104802611a 0x0020038082401308 0x9c3c707c781fe1f6 0xfce1e383e3c0ff0f

def z1000 : W := mkw 0xc97f8000153d8000 0x064bfc0000a9ec00 0xdf3f80007f9f8013 0xf6f9fc0003fcfc00

def z1001 : W := mkw 0xdbff8000b77d8aa0 0x46dffc0005bbec55 0xdfff80007fff9e13 0xf6fffc0003fffcf0

def z1002 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x1c3c707c781fe1e6 0x58e1e383e3c0ff0f

def z1003 : W := mkw 0x2400767a4882715b 0x812003b3d244138a 0x20006e7000000000 0x0100037380000000

def z1004 : W := mkw 0xdaed8000377d8000 0x06d76c0001bbec00 0x9ccf80007fff8013 0xb4e67c0003fffc00

def z1005 : W := mkw 0x2000a210c4925992 0x81000510862492cc 0x0000000004105990 0x00000000002082cc

def z1006 : W := mkw 0xc97f8000377d8000 0x064bfc0001bbec00 0x9c3f80007fff8012 0xf4e1fc0003fffc00

def z1007 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff800061ef 0xebfffffffc00030f

def z1008 : W := mkw 0x1aed8085b6798aa0 0x40d76c042db3cc55 0xdfff918fffffffff 0xfefffc8c7fffffff

def z1009 : W := mkw 0x4d7f54ef00000000 0x0a6bfaa778000000 0x7f3ffe7f8000000f 0xebf9fff3fc000000

def z1010 : W := mkw 0xdbff8da7377d8000 0x0edffc6d39bbec00 0xffff9f8fffff801f 0xfffffcfc7ffffc00

def z1011 : W := mkw 0x88288000b77d8aa0 0x4441440005bbec55 0x9c3c100c7ffffff6 0xfce1e08063ffffff

def z1012 : W := mkw 0xdbff84a7b77d8aa0 0x46dffc253dbbec55 0xffffffffffffffff 0xffffffffffffffff

def z1013 : W := mkw 0x4d7f5def00000000 0x0a6bfaef78000000 0x3c3fffff8000000e 0xe9e1fffffc000000

def z1014 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff800c7fff81f3 0xfefffc0063fffc0f

def z1015 : W := mkw 0x0d3a5def00000000 0x0869d2ef78000000 0x7f3fffff8000000f 0xebf9fffffc000000

def z1016 : W := mkw 0x1280000032490000 0x0094000001924800 0xdfc000007fff8011 0xf6fe000003fffc00

def z1017 : W := mkw 0xdbff8085377d8000 0x06dffc0429bbec00 0xdfff800fffff8013 0xfefffc007ffffc00

def z1018 : W := mkw 0x2112a632c5b6d992 0x81089531962db6cc 0xe333ee73c7ffd99f 0x7f199f739e3ffecc

def z1019 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0xc3cf918fc7f1ffff 0xfe1e7c8c7e3f8fff

def z1020 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdff380007fee0011 0xf6ff9c0003ff7000

def z1021 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8001a06f 0xeffffffffc000d03

def z1022 : W := mkw 0xdbff8000b77d8880 0x06dffc0005bbec44 0xdfff8003ffff8193 0xfefffc001ffffc0c

def z1023 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xfffffffff800001f 0xffffffffffc00000

def z1024 : W := mkw 0x0112042200000000 0x0008902110000000 0xe33ffe7f8011e1ff 0xef19fff3fc008f0f

def z1025 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c7c1ff9ff 0xfce1e383e3e0ffcf

def z1026 : W := mkw 0x093a0000110d0000 0x0049d00000886800 0x5f3000007b8e0000 0x52f9800003dc7000

def z1027 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c781fe1f0 0xd4e1e383e3c0ff0f

def z1028 : W := mkw 0x5fff5def08002049 0x0afffaef78400102 0x7fffffff8000206f 0xebfffffffc000103

def z1029 : W := mkw 0x2400767a4882715b 0x812003b3d244138a 0x20007e7c000061e4 0x090003f3e000030f

def z1030 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5f3000007b9e0012 0x72f9800003dcf000

def z1031 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc06f807fe07e19 0x57fe037c03ff03f0

def z1032 : W := mkw 0x08282058500b4153 0x00414102c2805a0a 0x9c3c607c781fc1f6 0xfce1e303e3c0fe0f

def z1033 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f807fe07e10 0xd7fe03fc03ff03f0

def z1034 : W := mkw 0x2000a210c5b6dbb2 0xc1000510862db6dd 0x0000000047fe5f90 0x10000000023ff2fc

def z1035 : W := mkw 0xdbff8085377d8220 0x46dffc0429bbec11 0xdfff800c7fff8073 0xf6fffc0063fffc03

def z1036 : W := mkw 0x093a042200000000 0x0049d02110000000 0x7f3fee738000000f 0xebf9ff739c000000

def z1037 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c78e581d 0x73199f739e3c72c0

def z1038 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xff33ee73ff9e599f 0xfff99f739ffcf2cc

def z1039 : W := mkw 0x5fff5def22400404 0x0afffaef79120020 0x7fffffff8060060f 0xebfffffffc030030

def z1040 : W := mkw 0xdbff0000336d8000 0x06dff800019b6c00 0x5ff000007bee0000 0x52ff800003df7000

def z1041 : W := mkw 0xdbff8000b77d8aa0 0x46dffc0005bbec55 0xdfff80007fff81f3 0xf6fffc0003fffc0f

def z1042 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0xff3c7e7c781fe1ff 0xfff9e3f3e3c0ff0f

def z1043 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdf3c100c7b9fe1f6 0xfef9e08063dcff0f

def z1044 : W := mkw 0x2000a210d59f5992 0x8100051086acfacc 0x800000007f9fd990 0x1400000003fcfecc

def z1045 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff8003ffff8013 0xf6fffc001ffffc00

def z1046 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff900c7fff8017 0xfefffc8063fffc00

def z1047 : W := mkw 0x5fff5def10090000 0x0afffaef78804800 0x7fffffff801f800f 0xebfffffffc00fc00

def z1048 : W := mkw 0x1aa8000032490000 0x00d5400001924800 0xdf3c00007b9f8012 0xf6f9e00003dcfc00

def z1049 : W := mkw 0xdbff84efb77d8aa0 0x4edffc277dbbec55 0xdfff91ffffffffff 0xfefffc8fffffffff

def z1050 : W := mkw 0x5fff5def10090000 0x0afffaef78804800 0xfffffffff81fe1ff 0xffffffffffc0ff0f

def z1051 : W := mkw 0x2000a210d59f59d3 0x8100051086acface 0x00000000479fd9f0 0x10000000023cfecf

def z1052 : W := mkw 0x92808000377d8000 0x0494040001bbec00 0xdf0000007fff8010 0x56f8000003fffc00

def z1053 : W := mkw 0x2112263241865112 0x81089131920c3288 0x6333ee73c38e0009 0x53199f739e1c7000

def z1054 : W := mkw 0x5fff5def00208000 0x0afffaef78010400 0xffffffff8061800f 0xeffffffffc030c00

def z1055 : W := mkw 0xa000a210f7ffdbb2 0xc500051087bffedd 0x800000007ffffff0 0x1400000003ffffff

def z1056 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c71fc781ffffe 0xfce1e38fe3c0ffff

def z1057 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7f33ee7380000009 0x43f99f739c000000

def z1058 : W := mkw 0xdbff0000336d8000 0x06dff800019b6c00 0xdffc00007bff8012 0xf6ffe00003dffc00

def z1059 : W := mkw 0xdbba0000336d8000 0x06ddd000019b6c00 0xdf3000007bef8000 0x56f9800003df7c00

def z1060 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe333fe73c79e799f 0xff199ff39e3cf3cc

def z1061 : W := mkw 0x4d7f5def00000000 0x0a6bfaef78000000 0x633fffff8000000f 0x6b19fffffc000000

def z1062 : W := mkw 0xdbba8000375d0000 0x06ddd40001bae800 0xdf3f80007f9f8013 0xf6f9fc0003fcfc00

def z1063 : W := mkw 0x5bff0da700000000 0x0adff86d38000000 0x7fffeff38000000f 0xebffff7f9c000000

def z1064 : W := mkw 0xdeed59cd3a69a40c 0x0ef76ace69d34d20 0x9ccc118c3861a600 0x84e6608c61c30d30

def z1065 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee7380000009 0x43199f739c000000

def z1066 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00000000479e5996 0x38000000023cf2cc

def z1067 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdff380007fff8011 0x56ff9c0003fffc00

def z1068 : W := mkw 0x17d75da700000000 0x00bebaed38000000 0x7fffffff8000000f 0xebfffffffc000000

def z1069 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff84601e0f 0xebfffffffc2300f0

def z1070 : W := mkw 0x2400f67acc9279db 0x812007b3d66493ce 0xa00ffe7f8411f9ff 0xad007ff3fc208fcf

def z1071 : W := mkw 0xdbff8085377d8220 0x46dffc0429bbec11 0xdfff918c7fffe7f7 0xfefffc8c63ffff3f

def z1072 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff918c7ffffff3 0xf6fffc8c63ffffff

def z1073 : W := mkw 0x5fff5def00208220 0x4afffaef78010411 0x7fffffff8001806f 0xebfffffffc000c03

def z1074 : W := mkw 0x0445fbddccb2ffff 0x40222fdeee6597ff 0xa0cfffff8471ffff 0xad067ffffc238fff

def z1075 : W := mkw 0xa000a210d5bfd992 0x8500051086adfecc 0x00000000479fd990 0x10000000023cfecc

def z1076 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c39e018f 0x7b199f739e1cf00c

def z1077 : W := mkw 0x1aa8000032490000 0x00d5400001924800 0xdffc118c7fffffff 0xfeffe08c63ffffff

def z1078 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff818fffff9ffb 0xfefffc0c7ffffcff

def z1079 : W := mkw 0x5fff5def0800240c 0x0afffaef78400120 0x7fffffff8000260f 0xebfffffffc000130

def z1080 : W := mkw 0xdbff04ef334d0000 0x0edff827799a6800 0x5f3f807ffb8e0002 0x5af9fc03ffdc7000

def z1081 : W := mkw 0x0c285058100b0143 0x00614282c080580a 0x9c3c707c781f81f6 0xfce1e383e3c0fc0f

def z1082 : W := mkw 0xdbff8422377d8000 0x06dffc2111bbec00 0xdfff8073ffff8013 0xfefffc039ffffc00

def z1083 : W := mkw 0x0c285058180b214b 0x00614282c0c0590a 0x1c3c007c381f81e2 0x08e1e003e1c0fc0f

def z1084 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f8c7fe07ffd 0xfffe03fc63ff03ff

def z1085 : W := mkw 0x05125d6a00000000 0x082892eb50000000 0x6333ee738000000f 0x6b199f739c000000

def z1086 : W := mkw 0xa000a210e7f6d992 0x85000510873fb6cc 0x0000000047fe5990 0x10000000023ff2cc

def z1087 : W := mkw 0xc97f84ef953d8aa0 0x4e4bfc277ca9ec55 0x003f807f801f81e2 0x0801fc03fc00fc0f

def z1088 : W := mkw 0xdbff8048377d8041 0x06dffc0241bbec02 0xdfff800c7fff8073 0xf6fffc0063fffc03

def z1089 : W := mkw 0x5bff04a700000000 0x02dff82538000000 0x7fffffff8000000f 0xebfffffffc000000

def z1090 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007ffffe13 0xf6fffc0003fffff0

def z1091 : W := mkw 0x015704a700208220 0x400ab82538010411 0xe3ffffff8061a66f 0xef1ffffffc030d33

def z1092 : W := mkw 0xf3d786a7a7f49aa0 0xc79ebc353d3fa4d5 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z1093 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff918c7fffffff 0xfefffc8c63ffffff

def z1094 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff918fffff9e1f 0xfefffc8c7ffffcf0

def z1095 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x43000000479e5991 0x72180000023cf2cc

def z1096 : W := mkw 0x2000a210cd967d9e 0x81000510866cb3ec 0x00000000479e7f90 0x10000000023cf3fc

def z1097 : W := mkw 0x13920d2200000000 0x009c906910000000 0x63f3eff38000000f 0x6b1f9f7f9c000000

def z1098 : W := mkw 0x5fba5d6a00000000 0x0afdd2eb50000000 0x7f33ee7380000002 0x4bf99f739c000000

def z1099 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0x7fc06f807fe05e1d 0x73fe037c03ff02f0

def z1100 : W := mkw 0x5fff5def1829a269 0x4afffaef78c14d13 0xffffffffb861a66f 0xeffffffffdc30d33

def z1101 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x633ffe7fc79e599f 0xfb19fff3fe3cf2cc

def z1102 : W := mkw 0x0c287b58588b755f 0x006143dac2c45baa 0xbcfc7ffc7c7fffff 0xfde7e3ffe3e3ffff

def z1103 : W := mkw 0x886d8000377d8000 0x04436c0001bbec00 0x9cff80007fff8013 0xf4e7fc0003fffc00

def z1104 : W := mkw 0x92800000334d0000 0x04940000019a6800 0xdfc000007fee0011 0xf6fe000003ff7000

def z1105 : W := mkw 0x13928000a7540880 0x009c9400053aa044 0xdff39183fffe7f9f 0xfeff9c8c1ffff3fc

def z1106 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5f3c00007b8e0002 0xf2f9e00003dc7000

def z1107 : W := mkw 0xdbff8085377d8220 0x46dffc0429bbec11 0xdfff918c7ffffe7f 0xf6fffc8c63fffff3

def z1108 : W := mkw 0x497f042200000000 0x024bf82110000000 0x633fee738000000f 0x6b19ff739c000000

def z1109 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8471fff9 0x84067c8c7c238fff

def z1110 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8471fff2 0x8c067c8c7c238fff

def z1111 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x80c0118047fe7f9d 0xb406008c023ff3fc

def z1112 : W := mkw 0x0112800005140000 0x000894000028a000 0xdf3380007f9e0013 0xf6f99c0003fcf000

def z1113 : W := mkw 0xdbff8048377d8000 0x06dffc0241bbec00 0xdfff807c7fff8013 0xfefffc03e3fffc00

def z1114 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007fffe1f3 0xf6fffc0003ffff0f

def z1115 : W := mkw 0xdbff8000375d0000 0x06dffc0001bae800 0x5fff80007f9e0013 0xf2fffc0003fcf000

def z1116 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73879e598f 0x0b199f739c3cf2cc

def z1117 : W := mkw 0xdbba8000375d0000 0x06ddd40001bae800 0x5f3380007f8e0001 0x52f99c0003fc7000

def z1118 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x80000000479ff9f0 0x14000000023cffcf

def z1119 : W := mkw 0x2112a632c5b6dbb2 0xc1089531962db6dd 0xe33ffe7fc7ffffff 0xff19fff3fe3fffff

def z1120 : W := mkw 0xdbff8085377d8220 0x46dffc0429bbec11 0xdfff918fffffa67f 0xfefffc8c7ffffd33

def z1121 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff918fffff81ff 0xfefffc8c7ffffc0f

def z1122 : W := mkw 0x16807b106ac2755f 0x00b403d8835613aa 0xffc07f807fe07ffd 0xf7fe03fc03ff03ff

def z1123 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5f3380007b8e0003 0x72f99c0003dc7000

def z1124 : W := mkw 0x093a042210090000 0x0049d02110804800 0xff3fee73f81f801f 0xfff9ff739fc0fc00

def z1125 : W := mkw 0x16807b586ac2755f 0x00b403dac35613aa 0xffcc7ffc7ff1ffff 0xfffe63ffe3ff8fff

def z1126 : W := mkw 0x5fff5def10090000 0x0afffaef78804800 0xffffffffb801800f 0xeffffffffdc00c00

def z1127 : W := mkw 0x12802b006ac0741c 0x00940158035603a0 0xffc00f807fe07e19 0xf7fe007c03ff03f0

def z1128 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9cfc71fc787fe7f6 0xfce7e38fe3c3ff3f

def z1129 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff90007fffe017 0xf6fffc8003ffff00

def z1130 : W := mkw 0xdbff0085334d0000 0x06dff804299a6800 0x5fff918ffb8e000f 0xfafffc8c7fdc7000

def z1131 : W := mkw 0x53d7042200000000 0x029eb82110000000 0x63f3ee738000000f 0x6b1f9f739c000000

def z1132 : W := mkw 0x5fff5def18092049 0x0afffaef78c04902 0xfffffffff81fa07f 0xffffffffffc0fd03

def z1133 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7ff3ffff8000000d 0x4bff9ffffc000000

def z1134 : W := mkw 0x5fff5def32490000 0x0afffaef79924800 0xffffffffffff801f 0xfffffffffffffc00

def z1135 : W := mkw 0xdbff8985377d8000 0x0edffc4c29bbec00 0xdfff81807fff8013 0xf6fffc0c03fffc00

def z1136 : W := mkw 0xdeed59cd3a69a049 0x0ef76ace69d34d02 0x9ccc118c3861a060 0x84e6608c61c30d03

def z1137 : W := mkw 0x5fff5def22400000 0x0afffaef79120000 0xffffffffb860000f 0xeffffffffdc30000

def z1138 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xffffee007fff801f 0xf7ffff7003fffc00

def z1139 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f807ff1fffd 0xf7fe03fc03ff8fff

def z1140 : W := mkw 0x16805b0022c01404 0x00b402d8011600a0 0xffc07f807fe01e1d 0xf7fe03fc03ff00f0

def z1141 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333fe7fc79e79ff 0x7b199ff3fe3cf3cf

def z1142 : W := mkw 0xdbff8000b77d8880 0x06dffc0005bbec44 0xdfff8003ffff981b 0xf6fffc001ffffcc0

def z1143 : W := mkw 0x24007f324882751e 0x812003f9924413a8 0x20007ff000007e0c 0x010003ff800003f0

def z1144 : W := mkw 0x5fff5def00208220 0x4afffaef78010411 0xffffffff8071e7ff 0xeffffffffc038f3f

def z1145 : W := mkw 0x2000a210e7d65992 0x81000510873eb2cc 0x800000007ffe5990 0x1400000003fff2cc

def z1146 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007fef8001 0xd6fffc0003ff7c00

def z1147 : W := mkw 0x16807b486ac0741c 0x00b403da435603a0 0xffc07ffc7fe07e1d 0xfffe03ffe3ff03f0

def z1148 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff80000009 0xc3fffffffc000000

def z1149 : W := mkw 0xdbba0d22334d0000 0x0eddd069119a6800 0x7f300e007b8e0000 0x53f9807003dc7000

def z1150 : W := mkw 0x2000a210ffdf7ddf 0x8100051087fefbee 0x800000007ffffff0 0x1400000003ffffff

def z1151 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00000000478e1800 0x10000000023c70c0

def z1152 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5f3c00007b9f8002 0x52f9e00003dcfc00

def z1153 : W := mkw 0x0000a210fefbffff 0x4000051087f7dfff 0x800000007ffffff0 0x1400000003ffffff

def z1154 : W := mkw 0x0d3a546a00000000 0x0069d2a350000000 0x7f33ee738000000f 0x6bf99f739c000000

def z1155 : W := mkw 0x1aed800036798000 0x00d76c0001b3cc00 0xdfff80007fff8013 0xf6fffc0003fffc00

def z1156 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333fff3c79e7f9f 0x7b199fff9e3cf3fc

def z1157 : W := mkw 0x57d75def00000000 0x0abebaef78000000 0x63f3ffff8000000f 0x6b1f9ffffc000000

def z1158 : W := mkw 0x17925def00000000 0x08bc92ef78000000 0x7ff3ffff8000000f 0xebff9ffffc000000

def z1159 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc3ff83ffe07e1f 0xfffe1ffc1fff03f0

def z1160 : W := mkw 0xdbff8def377d8000 0x0edffc6f79bbec00 0xffff8fffffff801b 0xfffffc7ffffffc00

def z1161 : W := mkw 0xdbff8000b77d8aa0 0x46dffc0005bbec55 0xdfff8003ffffffff 0xfefffc001fffffff

def z1162 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x00000000479e599d 0x30000000023cf2cc

def z1163 : W := mkw 0x2000a210c5965992 0x81000510862cb2cc 0x8000000047fe7f90 0x14000000023ff3fc

def z1164 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0x5f3f800ffb9f81e2 0x5af9fc007fdcfc0f

def z1165 : W := mkw 0x93928000377d8000 0x049c940001bbec00 0xdff380007fff8013 0xf6ff9c0003fffc00

def z1166 : W := mkw 0x2112263241865112 0x81089131920c3288 0x6333ee73c78e581f 0x7b199f739e3c72c0

def z1167 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f803fe07e0d 0x87fe03fc01ff03f0

def z1168 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff8183fffffffb 0xf6fffc0c1fffffff

def z1169 : W := mkw 0xdbba8000b75d0880 0x06ddd40005bae844 0x5f338003ff9e599f 0x7af99c001ffcf2cc

def z1170 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c79e5992 0x5b199f739e3cf2cc

def z1171 : W := mkw 0x1392000023440000 0x009c9000011a2000 0x5f3000007b8e0000 0x52f9800003dc7000

def z1172 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee73c780001f 0x7b199f739e3c0000

def z1173 : W := mkw 0xdbff0085336d8220 0x46dff804299b6c11 0xdffc118c7befa660 0xd6ffe08c63df7d33

def z1174 : W := mkw 0x5fff5def2a40240c 0x0afffaef79520120 0xffffffffbc607e1f 0xeffffffffde303f0

def z1175 : W := mkw 0xdaed8085b77d8aa0 0x46d76c042dbbec55 0x9ccc118c7ffffff0 0x94e6608c63ffffff

def z1176 : W := mkw 0xdbff8085377d8000 0x06dffc0429bbec00 0xdfff918ffffffe1f 0xfefffc8c7ffffff0

def z1177 : W := mkw 0x5fff5def08002008 0x0afffaef78400100 0xffffffffb800200f 0xeffffffffdc00100

def z1178 : W := mkw 0xdbff8000b77d8880 0x06dffc0005bbec44 0xdfff9183ffffff9f 0xfefffc8c1ffffffc

def z1179 : W := mkw 0x0112263240825112 0x0008913192041288 0x6333ee73c79e599f 0x7b199f739e3cf2cc

def z1180 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdf3000007b8e0010 0xf6f9800003dc7000

def z1181 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80cf918f8071ffee 0x8c067c8c7c038fff

def z1182 : W := mkw 0xdbff0000336d8000 0x06dff800019b6c00 0xdffc00007fef8011 0xf6ffe00003ff7c00

def z1183 : W := mkw 0x011204a700000000 0x0008902538000000 0x6333ffff8000000f 0x6b199ffffc000000

def z1184 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9cfc707c7c7fe1f7 0xfce7e383e3e3ff0f

def z1185 : W := mkw 0xdbff8da7b77d8aa0 0x4edffc6d3dbbec55 0xffff9f8fffffffff 0xfffffcfc7fffffff

def z1186 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9cfc71fc781fe1ff 0xfce7e38fe3c0ff0f

def z1187 : W := mkw 0x16805b002ac0340c 0x00b402d8015601a0 0x7fc00f803fe01e09 0x03fe007c01ff00f0

def z1188 : W := mkw 0xdfff5def336d8000 0x0efffaef799b6c00 0xfffffffffbef800f 0xffffffffffdf7c00

def z1189 : W := mkw 0x0d3a546a18092049 0x0069d2a350c04902 0xff3ffe7fb801a06f 0xeff9fff3fdc00d03

def z1190 : W := mkw 0x0c287258588b755f 0x00614392c2c45baa 0x9c3c707c781ffff6 0xfce1e383e3c0ffff

def z1191 : W := mkw 0x0000a210c4925992 0x00000510862492cc 0x6333ee73c79e599f 0x7b199f739e3cf2cc

def z1192 : W := mkw 0xdbff8000b77d8aa0 0x46dffc0005bbec55 0xdfff91807fffffff 0xf6fffc8c03ffffff

def z1193 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff80000002 0xcbfffffffc000000

def z1194 : W := mkw 0x0828000010090000 0x0041400000804800 0xdf3c00007f9f8013 0xf6f9e00003fcfc00

def z1195 : W := mkw 0x16807b106ac2751e 0x00b403d8835613a8 0xfffc7ffc7fffffff 0xffffe3ffe3ffffff

def z1196 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff9183fffffe1f 0xf6fffc8c1ffffff0

def z1197 : W := mkw 0x57d75def00000000 0x0abebaef78000000 0x7fc3ffff8000000d 0xebfe1ffffc000000

def z1198 : W := mkw 0x097f8085953d8aa0 0x404bfc042ca9ec55 0xdfff918fffffffff 0xfefffc8c7fffffff

def z1199 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c79e198b 0x5b199f739e3cf0cc

def z1200 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xfff07f807ffe7e1f 0xf7ff83fc03fff3f0

def z1201 : W := mkw 0xdbba8000375d0000 0x06ddd40001bae800 0xdff380007ffe0013 0xf6ff9c0003fff000

def z1202 : W := mkw 0x093a8000151d0000 0x0049d40000a8e800 0x5f3380007f9e0013 0x72f99c0003fcf000

def z1203 : W := mkw 0xdbff8085377d8000 0x06dffc0429bbec00 0xdfff918fffffe1ff 0xfefffc8c7fffff0f

def z1204 : W := mkw 0x92c58000377d8000 0x04962c0001bbec00 0xdfcf80007fff8013 0xf6fe7c0003fffc00

def z1205 : W := mkw 0x0c287958580b655f 0x006143cac2c05b2a 0x9c3c71fc781fe7f6 0xfce1e38fe3c0ff3f

def z1206 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c607c781fe1f2 0x5ce1e303e3c0ff0f

def z1207 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffffc780001f 0xfbfffffffe3c0000

def z1208 : W := mkw 0xdbff8000b77d8aa0 0x46dffc0005bbec55 0xdfff900c7ffffff7 0xfefffc8063ffffff

def z1209 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x3cffffff8000000e 0x89e7fffffc000000

def z1210 : W := mkw 0x5fff5def18092049 0x0afffaef78c04902 0x7fffffffb800000f 0xebfffffffdc00000

def z1211 : W := mkw 0x33d78fa7a7f49ea4 0xc19ebc7d3d3fa4f5 0x63c38f8387e01e09 0x031e1c7c1c3f00f0

def z1212 : W := mkw 0xfbff8422b77d8880 0x87dffc2115bbec44 0xdfff8003ffff8013 0xf6fffc001ffffc00

def z1213 : W := mkw 0xdbff0000334d0000 0x06dff800019a6800 0x5f3f80007b8e0002 0x52f9fc0003dc7000

def z1214 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdf3000007b9f8010 0x56f9800003dcfc00

def z1215 : W := mkw 0x53920d2200000000 0x0a9c906910000000 0x6333ee738000000f 0x6b199f739c000000

def z1216 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8000601f 0xeffffffffc000300

def z1217 : W := mkw 0xdfff5def32698000 0x0efffaef79934c00 0xfffffffff87f801f 0xffffffffffc3fc00

def z1218 : W := mkw 0x5fff5def3a49244d 0x0afffaef79d24922 0xffffffffb861a66f 0xeffffffffdc30d33

def z1219 : W := mkw 0xdbff8900377d8000 0x06dffc4801bbec00 0xffff8f807fff801b 0xf7fffc7c03fffc00

def z1220 : W := mkw 0x17925d222a40240c 0x00bc92e911520120 0xfff3fff3b860260f 0xefff9fff9dc30130

def z1221 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff900fffffe1f7 0xfefffc807fffff0f

def z1222 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5f3000007f8e0011 0x72f9800003fc7000

def z1223 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7ff3fff38000000d 0xe3ff9fff9c000000

def z1224 : W := mkw 0x2112a632c5b6dbb2 0xc1089531962db6dd 0x6333ee73c7fe5f9f 0x7b199f739e3ff2fc

def z1225 : W := mkw 0xdbff8000377d8220 0x46dffc0001bbec11 0xdfff80007fffa673 0xf6fffc0003fffd33

def z1226 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c38e0000 0x53199f739e1c7000

def z1227 : W := mkw 0x493a046a00000000 0x0a49d02350000000 0x6333ee738000000f 0x6b199f739c000000

def z1228 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c78e598d 0x5b199f739e3c72cc

def z1229 : W := mkw 0x16807b106ac2751e 0x00b403d8835613a8 0xfff07ff07fee7e1d 0xf7ff83ff83ff73f0

def z1230 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x63ffffff8000000f 0x0b1ffffffc000000

def z1231 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fffffff8010419f 0xebfffffffc00820c

def z1232 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe3f3ee73c7fe599f 0xff1f9f739e3ff2cc

def z1233 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdff011807fee7e1d 0xf6ff808c03ff73f0

def z1234 : W := mkw 0x240076ffc8827bfb 0xc12003b7fe4413df 0x20007fff80007fec 0x090003fffc0003ff

def z1235 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff91807fffa613 0xf6fffc8c03fffd30

def z1236 : W := mkw 0x0c287b58588b755f 0x006143dac2c45baa 0xff3c7ffc7f9fffff 0xfff9e3ffe3fcffff

def z1237 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8011801f 0xeffffffffc008c00

def z1238 : W := mkw 0x24007f7ac8827ddf 0x812003fbd64413ee 0x20007fff80007fec 0x090003fffc0003ff

def z1239 : W := mkw 0x88280000334d0000 0x04414000019a6800 0x9c3c00007b9f8012 0xf4e1e00003dcfc00

def z1240 : W := mkw 0x0c287258588b715b 0x00614392c2c45b8a 0xfffc7ffc7fffffff 0xffffe3ffe3ffffff

def z1241 : W := mkw 0x2112863285961982 0x81089431942cb0cc 0x6333ee73879e198f 0x6b199f739c3cf0cc

def z1242 : W := mkw 0xdbff80cd377d8000 0x0edffc0669bbec00 0xdfff800c7fff8013 0xf6fffc0063fffc00

def z1243 : W := mkw 0x0112042200000000 0x0008902110000000 0x6333ee738010419f 0x6b199f739c00820c

def z1244 : W := mkw 0xdbff8085b77d8aa0 0x46dffc042dbbec55 0xdfff800ffffffff3 0xfefffc007fffffff

def z1245 : W := mkw 0x13d7800027748000 0x009ebc00013ba400 0xdfff80007fff8013 0xf6fffc0003fffc00

def z1246 : W := mkw 0x0c287258588b715b 0x00614392c2c45b8a 0xbc3c7e7c781ff9fe 0xfde1e3f3e3c0ffcf

def z1247 : W := mkw 0x2400ff32cc927d9e 0x812007f9966493ec 0xa0c3fff384707f9f 0xad061fff9c2383fc

def z1248 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdf3000007fee0010 0x56f9800003ff7000

def z1249 : W := mkw 0x1392000023440000 0x009c9000011a2000 0xdff000007fee0011 0xf6ff800003ff7000

def z1250 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0x7fcfffff8000000d 0x8bfe7ffffc000000

def z1251 : W := mkw 0xdbff0000334d0000 0x06dff800019a6800 0x5ffc00007b8e0000 0xd2ffe00003dc7000

def z1252 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c79e5999 0x53199f739e3cf2cc

def z1253 : W := mkw 0x2000a210dd9f79db 0x8100051086ecfbce 0x000000007f9e5990 0x1000000003fcf2cc

def z1254 : W := mkw 0x0112a62245945010 0x00089531122ca280 0x6333ee73c79e581f 0x7b199f739e3cf2c0

def z1255 : W := mkw 0x415704a700000000 0x0a0ab82538000000 0x6333ee738000000f 0x6b199f739c000000

def z1256 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c107c781fe1f2 0x9ce1e083e3c0ff0f

def z1257 : W := mkw 0x21122632c1865992 0x81089131960c32cc 0x6333ee73c38e598f 0x7b199f739e1c72cc

def z1258 : W := mkw 0x5bff04ef00000000 0x0adff82778000000 0x7fffee7f8000000f 0xebffff73fc000000

def z1259 : W := mkw 0x0c287958580b615b 0x006143cac2c05b0a 0xbc3c7ffc781fe1fe 0xfde1e3ffe3c0ff0f

def z1260 : W := mkw 0x80008000377d8000 0x0400040001bbec00 0x9c0000007fff8010 0xf4e0000003fffc00

def z1261 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe33fee73c79fd99f 0xff19ff739e3cfecc

def z1262 : W := mkw 0xdbba8000b77d8aa0 0x46ddd40005bbec55 0xdf3000007ffffff0 0x56f9800003ffffff

def z1263 : W := mkw 0x04007b104882755f 0x002003d8824413aa 0x20007f8000007fec 0x010003fc000003ff

def z1264 : W := mkw 0x24007fb7c8827fbe 0xc12003fdbe4413fd 0x20007fff80007fec 0x090003fffc0003ff

def z1265 : W := mkw 0x5bff8000151d0000 0x02dffc0000a8e800 0xdfff80007f9f8013 0xf6fffc0003fcfc00

def z1266 : W := mkw 0xdbff84a7377d8000 0x0edffc2539bbec00 0xdfff8003ffff8013 0xf6fffc001ffffc00

def z1267 : W := mkw 0x04007bddc8827fff 0x402003deee4413ff 0x20007fff80007fec 0x090003fffc0003ff

def z1268 : W := mkw 0x2000a210ddbffbfb 0xc100051086edffdf 0x800000007ffffff0 0x1400000003ffffff

def z1269 : W := mkw 0x05125def00000000 0x082892ef78000000 0x2033ffff8000000e 0x09019ffffc000000

def z1270 : W := mkw 0x0000800084100880 0x0000040004208044 0x80cf918f8471ffff 0xac067c8c7c238fff

def z1271 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0xdf3c00007b8f8000 0xd6f9e00003dc7c00

def z1272 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0x6333ee73c39e598e 0x5b199f739e1cf2cc

def z1273 : W := mkw 0x0112042200000000 0x0008902110000000 0x2033ee738000000e 0x09019f739c000000

def z1274 : W := mkw 0x5bff800027540000 0x02dffc00013aa000 0xdfff80007ffe0013 0xf6fffc0003fff000

def z1275 : W := mkw 0x16807b006ac0741c 0x00b403d8035603a0 0xffc07f807fe03e09 0xd7fe03fc03ff01f0

def z1276 : W := mkw 0x1eed59cd3a69a66d 0x40f76ace69d34d33 0x9ccc118c3861a660 0x84e6608c61c30d33

def z1277 : W := mkw 0x0045008500000000 0x0002280428000000 0x80cf918f8471ffff 0xac067c8c7c238fff

def z1278 : W := mkw 0x2112a632cd967d9e 0x81089531966cb3ec 0x6333ee73c79e7f9f 0x7b199f739e3cf3fc

def z1279 : W := mkw 0xd3d7800027748000 0x069ebc00013ba400 0xdff380007ffe0013 0xf6ff9c0003fff000

def z1280 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x80ff918fc47fffff 0xfc07fc8c7e23ffff

def z1281 : W := mkw 0x5fff5def00000000 0x0afffaef78000000 0xffffffff8471ffff 0xeffffffffc238fff

def z1282 : W := mkw 0x0112042200000000 0x0008902110000000 0xe3f3fff384607e1f 0xef1f9fff9c2303f0

def z1283 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe3ffffffc7ffffff 0xff1ffffffe3fffff

def z1284 : W := mkw 0xdbba8000377d8000 0x06ddd40001bbec00 0x5f3000007fee0000 0x52f9800003ff7000

def z1285 : W := mkw 0x53d70da700000000 0x0a9eb86d38000000 0x63ffffff8000000f 0xeb1ffffffc000000

def z1286 : W := mkw 0x5fff5d2200000000 0x02fffae910000000 0x7ffffff38000000f 0xebffffff9c000000

def z1287 : W := mkw 0x5fff5def22400000 0x0afffaef79120000 0x7fffffff87e0000f 0xebfffffffc3f0000

def z1288 : W := mkw 0x88280000334d0000 0x04414000019a6800 0x1c3000007b8e0000 0x50e1800003dc7000

def z1289 : W := mkw 0x3680fb10efd67d9e 0x81b407d8877eb3ec 0x9cc011807ffe7f90 0x94e6008c03fff3fc

def z1290 : W := mkw 0xdbba0000334d0000 0x06ddd000019a6800 0x5ff000007b8e0001 0xf2ff800003dc7000

def z1291 : W := mkw 0x0045808584308aa0 0x40022c042c218455 0x9ccf918ffc71ffff 0xfce67c8c7fe38fff

def z1292 : W := mkw 0x5fff5def2a60a62c 0x4afffaef79530531 0xffffffffb861a66f 0xeffffffffdc30d33

def z1293 : W := mkw 0x13d78085a7748aa0 0x409ebc042d3ba455 0xdfff918fffffffff 0xfefffc8c7fffffff

def z1294 : W := mkw 0x2112a632c5965992 0x81089531962cb2cc 0xe333ee73c79ff9ff 0x7f199f739e3cffcf

def z1295 : W := mkw 0x5bff0def00000000 0x0adff86f78000000 0x63ffefff8000000f 0x6b1fff7ffc000000

def z1296 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5f3f80007f9f8013 0x72f9fc0003fcfc00

def z1297 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0xdfff80007fffc197 0xfefffc0003fffe0c

def z1298 : W := mkw 0xdbba8000377d8000 0x06ddd40001bbec00 0xdf3c00007fff8012 0xf6f9e00003fffc00

def z1299 : W := mkw 0xdbff8000377d8000 0x06dffc0001bbec00 0x5f3380007b8e0000 0x52f99c0003dc7000

def z1300 : W := mkw 0x2112862285941880 0x81089431142ca0c4 0x6333ee73c79e181f 0x7b199f739e3cf0c0

def z1301 : W := mkw 0x16805b002ac0340c 0x00b402d8015601a0 0xffc01f803fe07e1d 0xa7fe00fc01ff03f0

def z1302 : W := mkw 0x2112843285160982 0x810894219428b04c 0x6333ee73c79e019f 0x7b199f739e3cf00c

def z1303 : W := mkw 0x24007f32c8827d9e 0x812003f9964413ec 0x20006e738000598c 0x090003739c0002cc

def z1304 : W := mkw 0x011204ef00000000 0x0808902778000000 0x6333ee7f8000000f 0x6b199f73fc000000

def z1305 : W := mkw 0xdbff8000b77d8880 0x06dffc0005bbec44 0xdfff900ffffff9ff 0xfefffc807fffffcf

def z1306 : W := mkw 0xdbba8000377d8000 0x06ddd40001bbec00 0x5f3000007b9f8000 0x52f9800003dcfc00

def z1307 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0x9c3c707c781fa1e2 0xdce1e383e3c0fd0f

def z1308 : W := mkw 0x497f04ef00000000 0x0a4bf82778000000 0x63ffffff8000000f 0xeb1ffffffc000000

def z1309 : W := mkw 0x2000a210c5965bb2 0xc1000510862cb2dd 0x00000000479e7ff0 0x10000000023cf3ff

def z1310 : W := mkw 0x0c287058580b615b 0x00614382c2c05b0a 0xdf3c707c7f9fe1f7 0xfef9e383e3fcff0f

def z1311 : W := mkw 0x24007632c882799a 0x812003b1964413cc 0x20007e738000798c 0x090003f39c0003cc

def z1312 : W := mkw 0x2000a210c5b6dbb2 0xc1000510862db6dd 0x00000000479fd9f0 0x10000000023cfecf

def z1313 : W := mkw 0x9aa88000377d8000 0x04d5440001bbec00 0xdffc00007fff8013 0xf6ffe00003fffc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z5,z8]),(0,[z9,z1,z2,z3,z4,z5,z8]),(0,[z1,z10,z11,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z14,z8,z15]),(0,[z16,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z18,z8])],[(0,[z1,z2,z3,z4,z19,z5,z20]),(0,[z21,z1,z2,z3,z4,z5,z20]),(0,[z1,z22,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z23,z6]),(0,[z24,z1,z2,z25,z4,z5,z8]),(0,[z24,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z26,z27,z5]),(0,[z1,z28,z2,z3,z4,z5,z8]),(0,[z1,z29,z2,z30,z4,z5,z8]),(0,[z1,z31,z2,z3,z4,z32,z8])],[(0,[z33,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z34,z35,z8]),(0,[z36,z1,z2,z37,z4,z5,z8]),(0,[z1,z2,z3,z4,z38,z5,z8]),(0,[z1,z2,z3,z4,z32,z8,z15])],[(0,[z1,z2,z3,z39,z4,z5,z8]),(0,[z1,z11,z2,z3,z4,z5,z8]),(0,[z1,z2,z40,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z41,z8]),(0,[z1,z2,z3,z42,z4,z5,z8])],[(0,[z1,z2,z3,z4,z35,z14,z8]),(0,[z1,z2,z3,z4,z27,z5,z20]),(0,[z43,z1,z12,z2,z3,z4,z8])],[(0,[z1,z2,z44,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z4,z5,z6]),(0,[z1,z12,z2,z45,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z46])],[(0,[z1,z2,z3,z4,z47,z5,z8]),(0,[z1,z2,z3,z4,z5,z48,z8]),(0,[z1,z2,z3,z4,z5,z8,z49]),(0,[z1,z2,z3,z50,z4,z5,z8])],[(0,[z1,z2,z3,z51,z4,z5,z8]),(0,[z52,z2,z3,z4,z35,z5,z8]),(0,[z1,z53,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z8,z15])]],
   [[(0,[z1,z54,z2,z3,z4,z55,z8]),(0,[z56,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z57,z8]),(0,[z1,z2,z3,z4,z5,z58,z8]),(0,[z1,z2,z3,z17,z4,z32,z8])],[(0,[z59,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z60,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z61,z8]),(0,[z1,z62,z2,z3,z4,z5,z8]),(0,[z63,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z64,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z15]),(0,[z1,z2,z3,z4,z65,z5,z8]),(1,[z1,z12,z2,z3,z66,z8]),(0,[z1,z67,z2,z3,z4,z5,z8]),(0,[z1,z2,z68,z3,z4,z5,z8]),(0,[z69,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z20,z70]),(0,[z1,z12,z2,z3,z4,z5,z20]),(0,[z1,z71,z2,z3,z4,z20,z8]),(0,[z1,z2,z3,z4,z34,z5,z72]),(0,[z73,z1,z2,z3,z4,z5,z8]),(0,[z1,z74,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z75,z5,z8])],[(0,[z1,z2,z3,z76,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z78,z1,z2,z3,z17,z4,z8])],[(0,[z79,z1,z2,z3,z80,z5,z8]),(0,[z1,z2,z81,z3,z4,z5,z8]),(0,[z1,z2,z82,z3,z4,z5,z8]),(0,[z83,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z84,z8])],[(0,[z1,z2,z3,z85,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z86,z20]),(0,[z1,z12,z2,z3,z87,z4,z8])],[(0,[z88,z1,z2,z3,z17,z4,z8]),(0,[z89,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z90,z3,z4,z5,z8]),(1,[z1,z91,z3,z4,z5,z8]),(0,[z92,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z93]),(0,[z94,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z95,z5,z8])]],
   [[(0,[z1,z96,z2,z3,z4,z5,z8]),(0,[z97,z98,z2,z3,z4,z5,z8]),(1,[z52,z2,z3,z4,z35,z8]),(0,[z1,z2,z3,z4,z5,z99,z6]),(0,[z1,z2,z81,z4,z27,z5,z8]),(0,[z1,z100,z2,z3,z4,z5,z8]),(0,[z101,z1,z2,z3,z4,z5,z8])],[(0,[z102,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z103,z5,z8]),(0,[z104,z1,z2,z3,z4,z5,z8]),(1,[z36,z1,z2,z27,z5,z8]),(0,[z105,z1,z2,z3,z4,z5,z8])],[(0,[z79,z1,z2,z3,z4,z5,z106]),(0,[z1,z2,z3,z4,z5,z8,z107]),(0,[z1,z2,z3,z108,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z66,z8])],[(1,[z1,z109,z3,z4,z5,z8]),(0,[z1,z2,z3,z87,z4,z5,z8]),(0,[z24,z1,z2,z110,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z111,z8])],[(0,[z1,z12,z2,z3,z4,z55,z8]),(0,[z1,z2,z3,z4,z5,z112,z8])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z113,z4,z5,z8]),(0,[z1,z2,z3,z114,z4,z5,z8]),(0,[z1,z2,z115,z3,z4,z5,z8]),(0,[z116,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z117,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z118]),(0,[z1,z10,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z72]),(0,[z1,z119,z2,z3,z120,z4,z5]),(0,[z1,z2,z3,z4,z5,z121,z8]),(0,[z1,z2,z3,z122,z4,z5,z8]),(0,[z1,z12,z2,z3,z120,z4,z8]),(0,[z123,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z124,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z125,z5,z8]),(0,[z1,z31,z2,z3,z17,z4,z8])],[(0,[z1,z3,z4,z34,z5,z55,z8]),(0,[z1,z119,z29,z2,z3,z4,z5])]],
   [[(0,[z116,z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z127,z5,z8]),(0,[z1,z2,z3,z17,z4,z8,z6]),(0,[z1,z2,z3,z4,z128,z5,z8]),(0,[z129,z1,z2,z3,z4,z5,z8]),(0,[z1,z54,z2,z3,z4,z34,z8]),(0,[z1,z2,z3,z4,z130,z5,z8])],[(0,[z1,z2,z3,z4,z5,z131,z8])],[(0,[z1,z2,z3,z4,z132,z5,z8]),(0,[z88,z1,z2,z3,z4,z5,z133]),(0,[z2,z3,z134,z4,z19,z5,z8]),(0,[z21,z2,z3,z4,z5,z135,z8]),(0,[z36,z1,z91,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z8,z46])],[(0,[z1,z2,z3,z136,z4,z5,z8]),(0,[z1,z2,z137,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z138]),(0,[z1,z2,z3,z4,z5,z20,z6]),(0,[z1,z139,z2,z3,z64,z5,z8]),(0,[z1,z29,z2,z3,z120,z4,z5])],[(1,[z1,z140,z2,z3,z4,z5]),(1,[z1,z2,z3,z141,z4,z8]),(0,[z142,z1,z2,z3,z4,z5,z8]),(0,[z1,z143,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z144,z8])],[(0,[z79,z0,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z19,z18,z5,z8]),(0,[z1,z2,z3,z4,z5,z20,z46]),(0,[z1,z2,z3,z4,z145,z5,z8]),(0,[z1,z2,z3,z17,z17,z4,z8])],[(0,[z1,z2,z146,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z147]),(0,[z148,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z149,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z150,z5,z8]),(0,[z1,z2,z3,z151,z4,z5,z8]),(0,[z1,z11,z3,z4,z64,z5,z8]),(0,[z1,z152,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z153,z5,z8])],[(0,[z1,z139,z2,z3,z4,z5,z20]),(0,[z1,z10,z2,z3,z4,z154,z8]),(0,[z155,z1,z12,z2,z3,z4,z8]),(1,[z1,z12,z2,z3,z4,z8])]],
   [[(0,[z156,z1,z2,z3,z4,z5,z8]),(0,[z52,z1,z2,z3,z4,z5,z6]),(0,[z1,z54,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z157,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z158]),(0,[z1,z2,z3,z4,z5,z8,z159])],[(0,[z79,z1,z2,z3,z4,z5,z20]),(0,[z88,z1,z2,z160,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z161,z8]),(0,[z1,z2,z3,z4,z162,z5,z8]),(0,[z163,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z1,z164,z2,z3,z4,z5,z8]),(0,[z21,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z165,z5,z8]),(0,[z1,z2,z3,z166,z4,z5,z20]),(0,[z1,z2,z87,z4,z5,z167,z8]),(0,[z1,z12,z2,z3,z4,z8,z168]),(0,[z1,z2,z3,z4,z169,z5,z8]),(0,[z1,z2,z3,z170,z4,z5,z8])],[(0,[z1,z2,z3,z4,z171,z35,z8]),(0,[z1,z172,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z173,z5,z8])],[(0,[z1,z2,z3,z4,z174,z5,z8]),(0,[z175,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z176,z5,z8]),(0,[z1,z12,z2,z3,z4,z34,z8]),(0,[z1,z12,z2,z3,z4,z5,z177])],[(0,[z1,z2,z3,z4,z178,z5,z8]),(0,[z1,z2,z3,z4,z27,z5,z6]),(0,[z1,z2,z3,z179,z4,z5,z8]),(0,[z1,z12,z2,z180,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z181,z3,z17,z4,z8]),(0,[z1,z2,z30,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z182,z8]),(0,[z183,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z184,z3,z4,z5,z8]),(0,[z97,z1,z2,z3,z17,z4,z8]),(0,[z1,z185,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z186,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z23,z8]),(0,[z1,z2,z3,z4,z5,z41,z20]),(0,[z1,z2,z81,z37,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z66,z8])]],
   [[(0,[z1,z2,z187,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z126,z8]),(0,[z52,z1,z2,z3,z4,z135,z8]),(0,[z1,z2,z188,z3,z4,z5,z6]),(1,[z1,z2,z25,z4,z5,z8]),(0,[z24,z1,z2,z3,z64,z5,z8]),(0,[z1,z2,z189,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z190,z8,z168]),(0,[z1,z2,z3,z4,z191,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z8]),(0,[z192,z2,z3,z4,z5,z8,z6]),(0,[z1,z193,z2,z3,z18,z5,z8]),(0,[z1,z194,z2,z3,z4,z5,z8])],[(0,[z195,z1,z2,z3,z4,z5,z8]),(0,[z21,z1,z2,z3,z4,z135,z8]),(0,[z196,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z197,z8])],[(0,[z1,z2,z160,z87,z4,z5,z8]),(0,[z1,z2,z3,z198,z4,z5,z8]),(0,[z1,z2,z3,z4,z199,z5,z6]),(0,[z200,z1,z2,z3,z4,z5,z8]),(1,[z1,z172,z87,z4,z5,z8]),(0,[z1,z12,z10,z2,z3,z4,z8]),(0,[z1,z3,z4,z5,z41,z8,z13]),(0,[z1,z2,z37,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z201,z8]),(0,[z1,z2,z3,z18,z5,z86,z8]),(0,[z1,z202,z2,z3,z4,z86,z8])],[(0,[z116,z1,z2,z3,z4,z203,z8]),(0,[z1,z2,z3,z134,z64,z5,z8]),(0,[z1,z12,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z5,z86,z8]),(0,[z1,z2,z3,z4,z204,z5,z8])],[(0,[z2,z115,z3,z160,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z19,z8]),(0,[z1,z205,z2,z3,z4,z5,z8]),(0,[z1,z2,z206,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z207,z5,z8]),(0,[z1,z12,z2,z3,z4,z86,z8])],[(0,[z1,z10,z2,z30,z3,z4,z5]),(0,[z1,z193,z29,z2,z3,z4,z5])],[(0,[z0,z1,z181,z3,z4,z5,z8]),(0,[z1,z2,z208,z3,z4,z5,z8]),(0,[z88,z1,z2,z3,z4,z5,z209]),(0,[z1,z2,z3,z4,z5,z8,z210]),(0,[z211,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z212]),(0,[z1,z2,z3,z4,z5,z86,z6]),(0,[z1,z2,z3,z4,z213,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z214])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z215]),(0,[z1,z2,z3,z4,z64,z5,z8]),(1,[z1,z2,z82,z3,z4,z8]),(0,[z1,z2,z3,z4,z216,z5,z8]),(0,[z1,z2,z3,z217,z4,z5,z8]),(0,[z1,z218,z2,z3,z4,z5,z8])],[(0,[z219,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z220,z3,z4,z5,z8]),(0,[z52,z1,z31,z2,z3,z4,z8]),(0,[z1,z119,z2,z3,z4,z5,z13])],[(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z77,z8]),(0,[z1,z2,z3,z221,z4,z5,z8]),(0,[z1,z2,z3,z4,z171,z8,z15]),(0,[z1,z222,z2,z3,z4,z5,z8])],[(0,[z223,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z133]),(0,[z1,z2,z3,z4,z224,z5,z8]),(0,[z21,z1,z31,z2,z3,z4,z8]),(0,[z1,z12,z11,z2,z3,z4,z8]),(0,[z225,z1,z12,z2,z3,z4,z8]),(0,[z36,z1,z2,z3,z17,z4,z8]),(0,[z1,z226,z12,z2,z3,z4,z8]),(0,[z1,z12,z2,z3,z17,z5,z8])],[(0,[z1,z12,z2,z3,z4,z135,z8]),(0,[z1,z2,z3,z227,z4,z5,z8]),(0,[z1,z12,z172,z2,z3,z4,z8]),(0,[z1,z2,z3,z228,z87,z4,z5]),(0,[z1,z2,z3,z4,z5,z229,z8]),(0,[z1,z2,z3,z4,z5,z8,z230]),(0,[z1,z2,z3,z4,z86,z8,z231]),(1,[z1,z31,z2,z3,z4,z99])],[(0,[z79,z1,z2,z113,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z232,z8]),(0,[z1,z233,z2,z3,z4,z5,z8]),(0,[z98,z1,z2,z3,z134,z5,z8])],[(0,[z1,z2,z3,z166,z19,z5,z8]),(0,[z192,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z234,z4,z5,z8]),(0,[z1,z2,z30,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z99,z8])],[(0,[z98,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z235,z5,z8]),(0,[z24,z1,z2,z3,z166,z5,z8]),(1,[z1,z2,z3,z4,z5,z57]),(0,[z1,z12,z193,z2,z3,z5,z8])]],
   [[(0,[z79,z1,z2,z3,z4,z236,z8]),(0,[z1,z2,z3,z4,z5,z55,z20]),(0,[z1,z2,z30,z87,z4,z5,z8]),(0,[z1,z2,z3,z237,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z238]),(0,[z1,z2,z3,z141,z4,z5,z8]),(0,[z239,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z240,z8])],[(0,[z1,z2,z3,z4,z241,z5,z8]),(0,[z1,z2,z3,z4,z242,z5,z8]),(0,[z1,z2,z3,z4,z32,z5,z99])],[(0,[z1,z243,z2,z3,z4,z5,z6]),(1,[z1,z2,z110,z4,z5,z8]),(0,[z1,z119,z2,z3,z17,z4,z8]),(0,[z1,z2,z45,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z244])],[(0,[z1,z11,z245,z3,z4,z5,z8]),(0,[z1,z2,z3,z134,z166,z5,z8]),(0,[z1,z2,z3,z4,z5,z246,z8]),(0,[z24,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z247,z5,z8]),(0,[z248,z1,z2,z3,z4,z5,z8])],[(0,[z98,z1,z2,z3,z19,z5,z8]),(0,[z52,z1,z2,z3,z85,z5,z8]),(0,[z1,z12,z119,z2,z3,z4,z8]),(0,[z1,z2,z3,z17,z4,z4,z8]),(0,[z1,z2,z3,z4,z249,z8,z168])],[(0,[z1,z181,z3,z87,z4,z5,z8]),(0,[z1,z12,z2,z3,z166,z4,z8]),(0,[z1,z12,z31,z2,z3,z4,z8]),(0,[z250,z1,z2,z3,z17,z4,z8])],[(0,[z1,z251,z2,z3,z4,z5,z8]),(0,[z252,z1,z2,z3,z4,z5,z8]),(0,[z1,z10,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z17,z207,z4,z8]),(0,[z1,z2,z3,z120,z17,z4,z8])],[(0,[z1,z12,z2,z3,z134,z4,z8]),(0,[z1,z2,z3,z4,z5,z6,z13]),(0,[z1,z253,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z245,z2,z3,z4,z5,z20]),(0,[z1,z139,z2,z3,z4,z5,z6]),(0,[z1,z71,z2,z3,z4,z5,z20]),(0,[z36,z1,z53,z3,z4,z5,z8]),(0,[z1,z2,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z255,z4,z5,z8]),(0,[z1,z29,z2,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z5,z20,z8]),(0,[z1,z256,z2,z3,z4,z5,z6]),(0,[z257,z1,z2,z3,z4,z5,z8]),(0,[z258,z1,z2,z3,z4,z5,z8]),(0,[z1,z31,z2,z3,z4,z14,z8])],[(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z259,z5,z8]),(0,[z1,z2,z3,z260,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z261,z8]),(0,[z262,z1,z2,z3,z4,z5,z8])],[(0,[z116,z1,z109,z3,z4,z5,z8]),(0,[z1,z2,z3,z166,z4,z5,z6]),(0,[z1,z2,z3,z17,z4,z64,z8]),(0,[z1,z2,z3,z263,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z106]),(0,[z1,z264,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z265,z5,z8]),(0,[z1,z172,z2,z3,z4,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z267,z3,z4,z5,z8]),(0,[z1,z268,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z269]),(0,[z1,z31,z2,z3,z4,z99,z8])],[(0,[z270,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z55,z8,z15]),(0,[z1,z2,z3,z4,z271,z5,z8]),(0,[z1,z2,z3,z4,z272,z5,z8])],[(0,[z273,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z274,z4,z5,z8]),(0,[z52,z1,z2,z3,z4,z5,z8]),(0,[z275,z1,z2,z3,z4,z5,z8]),(0,[z1,z54,z2,z3,z4,z5,z8]),(0,[z78,z1,z12,z2,z3,z4,z8]),(1,[z1,z2,z3,z120,z5,z86]),(0,[z1,z2,z3,z120,z4,z5,z86])],[(0,[z276,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z277]),(0,[z1,z2,z3,z134,z27,z5,z8]),(0,[z1,z2,z3,z4,z35,z5,z20]),(0,[z1,z2,z3,z4,z278,z5,z8]),(0,[z1,z2,z30,z3,z4,z5,z6]),(0,[z1,z10,z2,z3,z4,z5,z15]),(0,[z1,z2,z91,z3,z4,z5,z8]),(0,[z279,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z280])]],
   [[(0,[z1,z2,z3,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z209]),(0,[z1,z2,z3,z4,z19,z5,z8]),(0,[z21,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z41,z6]),(0,[z1,z2,z3,z4,z5,z20,z215]),(0,[z1,z2,z3,z4,z281,z5,z8]),(0,[z282,z1,z2,z3,z4,z5,z8]),(0,[z1,z119,z3,z4,z5,z41,z8]),(0,[z1,z2,z3,z17,z4,z14,z8]),(0,[z283,z1,z2,z3,z4,z5,z8])],[(0,[z88,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z284,z5,z8]),(0,[z1,z2,z37,z3,z4,z285,z8]),(0,[z1,z286,z2,z3,z4,z5,z8]),(0,[z1,z2,z30,z3,z4,z5,z46]),(0,[z1,z193,z2,z3,z4,z5,z8])],[(0,[z1,z2,z287,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z288,z5,z8]),(1,[z1,z2,z3,z4,z265,z8]),(0,[z1,z12,z2,z3,z4,z27,z8])],[(0,[z1,z2,z289,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z290,z5,z8]),(0,[z1,z2,z3,z4,z291,z5,z8]),(0,[z1,z12,z54,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z292]),(0,[z1,z2,z3,z4,z27,z5,z8]),(0,[z16,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z17,z4,z99,z8])],[],[(0,[z293,z1,z2,z3,z4,z5,z8]),(0,[z294,z1,z2,z3,z4,z5,z8]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z295,z2,z3,z4,z5,z20]),(0,[z1,z139,z2,z3,z4,z296,z8]),(0,[z1,z2,z3,z297,z4,z5,z8]),(0,[z1,z2,z3,z4,z298,z5,z8])],[(0,[z116,z1,z2,z3,z4,z5,z147]),(0,[z1,z299,z2,z3,z4,z5,z8]),(0,[z1,z2,z188,z3,z4,z5,z8]),(0,[z1,z11,z2,z3,z17,z4,z8])],[(0,[z116,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z300,z5,z8]),(0,[z1,z301,z2,z3,z4,z5,z8])]],
   [[(0,[z302,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z35,z55,z8]),(1,[z1,z2,z3,z4,z8,z215]),(0,[z1,z2,z3,z4,z303,z64,z5]),(0,[z1,z2,z3,z4,z5,z304,z8]),(0,[z1,z2,z3,z305,z4,z5,z8])],[(1,[z98,z2,z3,z134,z5,z8]),(0,[z1,z2,z3,z4,z199,z5,z8]),(0,[z1,z2,z3,z4,z306,z5,z8]),(0,[z1,z2,z3,z4,z307,z5,z8]),(0,[z1,z308,z2,z3,z4,z5,z8])],[(0,[z1,z2,z309,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z5,z8])],[(1,[z1,z12,z2,z3,z19,z8]),(0,[z98,z1,z2,z3,z4,z310,z8]),(0,[z311,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z312,z5,z8])],[(0,[z1,z2,z3,z4,z313,z5,z8]),(0,[z1,z2,z3,z4,z314,z5,z8]),(0,[z1,z139,z2,z3,z4,z315,z8]),(0,[z1,z2,z3,z4,z34,z8,z15]),(0,[z1,z2,z3,z4,z154,z5,z8]),(0,[z1,z2,z3,z4,z5,z316,z8])],[(0,[z1,z2,z317,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z318,z5,z8]),(0,[z1,z67,z2,z3,z17,z4,z8]),(0,[z1,z2,z68,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z5,z86,z8]),(0,[z1,z2,z3,z5,z86,z8,z168])],[(0,[z1,z2,z3,z4,z319,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z320]),(1,[z1,z2,z3,z4,z5,z321]),(0,[z1,z322,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z20,z8]),(0,[z1,z2,z3,z4,z323,z5,z8]),(0,[z1,z324,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z325,z5,z8]),(0,[z97,z2,z3,z4,z19,z5,z8]),(0,[z52,z1,z2,z3,z326,z5,z8]),(0,[z1,z2,z3,z4,z18,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z327]),(0,[z1,z2,z3,z4,z5,z328,z8]),(0,[z1,z29,z2,z3,z4,z5,z167]),(0,[z1,z2,z3,z120,z4,z5,z168]),(0,[z1,z2,z3,z4,z5,z15,z168])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z329]),(0,[z1,z2,z330,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z135,z20]),(0,[z102,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z81,z3,z17,z4,z8]),(0,[z1,z331,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z320]),(1,[z116,z2,z160,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z332,z1,z12,z2,z3,z4,z8]),(0,[z1,z193,z2,z3,z4,z5,z86])],[(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z334,z4,z5,z8]),(0,[z92,z1,z2,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z5,z8,z212]),(0,[z335,z1,z2,z3,z4,z5,z8]),(0,[z1,z119,z2,z3,z4,z5,z99]),(0,[z1,z2,z3,z336,z4,z5,z8])],[(1,[z1,z2,z337,z4,z5,z8]),(0,[z1,z338,z2,z3,z4,z5,z8]),(0,[z1,z11,z3,z4,z5,z41,z8]),(0,[z1,z31,z2,z3,z4,z171,z8]),(0,[z1,z12,z2,z30,z3,z4,z8])],[(0,[z1,z339,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z340,z5,z8]),(0,[z341,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z254,z3,z4,z5]),(0,[z1,z2,z3,z17,z342,z4,z8]),(0,[z1,z2,z3,z108,z17,z4,z8]),(0,[z1,z343,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z160,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z310,z8]),(0,[z1,z2,z3,z87,z17,z4,z8]),(0,[z1,z344,z2,z3,z4,z5,z8]),(0,[z1,z12,z193,z2,z3,z4,z8])],[(0,[z97,z1,z2,z3,z134,z5,z8]),(0,[z345,z1,z2,z3,z4,z5,z8]),(1,[z24,z1,z3,z64,z5,z8]),(0,[z1,z2,z3,z4,z346,z5,z8]),(0,[z1,z193,z2,z3,z120,z5,z8]),(0,[z1,z2,z3,z4,z5,z347,z8]),(0,[z348,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z115,z3,z17,z4,z8]),(0,[z1,z243,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z349,z5,z8]),(1,[z1,z2,z3,z4,z5,z350]),(0,[z1,z2,z3,z4,z5,z351,z8]),(1,[z1,z202,z2,z3,z4,z8])],[(0,[z1,z245,z2,z3,z4,z5,z6]),(0,[z97,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z6,z168]),(0,[z1,z29,z2,z3,z4,z5,z99]),(0,[z1,z2,z3,z4,z352,z5,z8]),(0,[z1,z2,z3,z4,z5,z86,z15])],[(0,[z1,z2,z3,z207,z19,z5,z8]),(0,[z98,z1,z2,z3,z4,z265,z8]),(0,[z1,z353,z2,z3,z4,z5,z8]),(0,[z1,z354,z2,z3,z4,z5,z8]),(0,[z1,z355,z2,z3,z4,z5,z8]),(0,[z1,z356,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z357])],[(0,[z1,z2,z3,z80,z4,z5,z8]),(0,[z1,z2,z3,z4,z358,z5,z8]),(0,[z1,z2,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z17,z4,z171,z8])],[(0,[z359,z1,z2,z3,z4,z5,z8]),(0,[z1,z139,z3,z87,z4,z5,z8]),(0,[z1,z2,z3,z4,z360,z5,z8]),(0,[z1,z361,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z362]),(0,[z1,z2,z3,z363,z4,z5,z8]),(1,[z1,z2,z3,z4,z26,z5])],[(1,[z1,z2,z3,z4,z364,z8]),(0,[z97,z1,z2,z3,z19,z5,z8]),(0,[z1,z139,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z365,z8])],[(1,[z1,z2,z113,z4,z5,z8]),(0,[z1,z256,z2,z3,z4,z5,z8]),(0,[z97,z1,z2,z3,z4,z5,z366]),(0,[z1,z2,z3,z76,z4,z19,z8]),(0,[z1,z2,z367,z3,z4,z5,z8]),(0,[z225,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z368]),(0,[z1,z2,z3,z369,z4,z5,z8]),(0,[z142,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z5,z370,z8])]],
   [[(0,[z79,z1,z2,z3,z4,z5,z8]),(0,[z371,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z366]),(0,[z1,z2,z3,z4,z5,z8,z372]),(0,[z1,z2,z3,z4,z35,z5,z6]),(1,[z1,z2,z3,z4,z20,z215]),(0,[z1,z172,z3,z87,z4,z5,z8]),(0,[z1,z2,z3,z4,z373,z5,z8]),(0,[z1,z374,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z375,z5,z8]),(0,[z1,z2,z3,z376,z4,z5,z8]),(0,[z1,z2,z3,z166,z4,z5,z8]),(0,[z1,z377,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z378,z8])],[(0,[z1,z2,z3,z4,z5,z8,z147]),(0,[z116,z1,z2,z160,z4,z5,z8]),(0,[z1,z2,z81,z160,z4,z5,z8]),(0,[z1,z2,z3,z379,z4,z5,z20]),(0,[z1,z172,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z37,z3,z4,z8])],[(0,[z98,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z13]),(1,[z1,z119,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z380,z5,z8])],[(0,[z1,z2,z3,z4,z381,z5,z8]),(0,[z52,z1,z2,z3,z4,z35,z8]),(0,[z1,z2,z3,z382,z4,z5,z8]),(0,[z1,z383,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z249,z5,z8]),(0,[z1,z2,z3,z4,z384,z5,z8])],[(0,[z385,z1,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z115,z3,z4,z8]),(0,[z36,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z45,z3,z4,z14,z8]),(0,[z1,z2,z30,z3,z4,z5,z8])],[(0,[z1,z2,z3,z386,z4,z5,z8]),(0,[z1,z2,z3,z387,z4,z5,z8]),(0,[z21,z1,z2,z3,z4,z35,z8]),(1,[z1,z2,z3,z4,z5,z388]),(0,[z1,z389,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z41,z8]),(0,[z1,z2,z3,z4,z390,z5,z8]),(0,[z391,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z392,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z6,z329]),(0,[z24,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z393])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z394]),(0,[z395,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z396,z8])],[(0,[z79,z1,z181,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z364,z5,z8]),(0,[z102,z192,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z20,z8,z6]),(0,[z1,z2,z3,z4,z5,z397,z20]),(0,[z1,z398,z2,z3,z4,z5,z8]),(0,[z1,z399,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z400,z5,z8]),(0,[z401,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z313,z5,z8]),(0,[z1,z2,z3,z134,z4,z5,z20]),(0,[z1,z2,z3,z402,z4,z5,z8]),(0,[z1,z2,z3,z141,z4,z27,z8]),(0,[z1,z2,z403,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z404])],[(0,[z1,z405,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z406,z6]),(0,[z1,z29,z10,z2,z3,z4,z5]),(0,[z1,z407,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z408,z5,z8])],[(0,[z1,z2,z3,z4,z5,z409,z8]),(0,[z1,z2,z3,z4,z5,z410,z8])],[(0,[z79,z2,z181,z3,z4,z5,z8]),(0,[z411,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z5,z412,z8])],[(0,[z1,z413,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z414,z20]),(0,[z415,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z416,z8]),(0,[z1,z417,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z12,z2,z3,z4,z35,z8]),(0,[z1,z2,z3,z4,z18,z5,z6]),(0,[z1,z2,z3,z418,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z419]),(0,[z1,z2,z37,z3,z4,z420,z8]),(0,[z1,z2,z30,z3,z4,z421,z8]),(0,[z1,z2,z422,z3,z4,z5,z8])],[(1,[z79,z181,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z423,z5,z8]),(0,[z424,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z134,z207,z5,z8]),(0,[z1,z2,z3,z4,z5,z135,z6])],[(0,[z78,z1,z2,z3,z4,z5,z20]),(0,[z1,z11,z139,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z34,z5,z238]),(0,[z1,z2,z3,z4,z5,z8,z425]),(1,[z1,z383,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z426,z8]),(0,[z1,z31,z2,z3,z4,z5,z99])],[(0,[z1,z2,z3,z4,z427,z5,z8]),(0,[z52,z1,z2,z3,z4,z8,z15]),(0,[z1,z428,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z429,z5,z8]),(0,[z1,z2,z3,z4,z5,z118,z8]),(0,[z1,z10,z3,z87,z4,z5,z8]),(0,[z1,z2,z3,z4,z303,z5,z8]),(1,[z1,z54,z3,z4,z55,z8])],[(0,[z88,z1,z2,z3,z4,z5,z20]),(0,[z21,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z430,z3,z4,z5,z8]),(0,[z431,z1,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z167,z8])],[(1,[z1,z2,z3,z4,z310,z8]),(0,[z1,z2,z82,z3,z4,z64,z8]),(0,[z1,z10,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z154,z8])],[(0,[z1,z2,z3,z160,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z133]),(0,[z1,z2,z3,z4,z5,z432,z8]),(0,[z1,z2,z3,z4,z5,z6,z372]),(0,[z1,z3,z87,z4,z5,z41,z8]),(0,[z1,z2,z3,z4,z5,z55,z8]),(0,[z1,z2,z433,z3,z4,z5,z8]),(0,[z1,z2,z3,z434,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z435,z8]),(0,[z1,z333,z2,z3,z4,z5,z8]),(0,[z225,z1,z2,z3,z4,z34,z8]),(0,[z1,z2,z3,z17,z4,z8,z13]),(0,[z1,z2,z3,z4,z171,z5,z350]),(0,[z1,z12,z2,z3,z4,z18,z8]),(0,[z1,z2,z3,z4,z436,z5,z8])],[(0,[z437,z1,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z160,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z438]),(0,[z52,z21,z2,z3,z4,z5,z8]),(0,[z192,z1,z2,z3,z17,z4,z8]),(1,[z1,z2,z3,z4,z296,z8])],[(1,[z1,z2,z3,z80,z5,z8]),(0,[z1,z185,z2,z3,z4,z19,z8]),(1,[z1,z2,z3,z439,z4,z8]),(1,[z1,z2,z45,z4,z14,z8]),(0,[z1,z2,z3,z4,z440,z5,z8]),(1,[z1,z2,z30,z4,z5,z46]),(1,[z1,z428,z2,z3,z5,z8])],[(0,[z441,z1,z2,z3,z4,z5,z8]),(0,[z116,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z442]),(0,[z1,z2,z81,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z20,z13]),(0,[z1,z2,z3,z4,z443,z5,z8]),(0,[z1,z2,z3,z4,z5,z444,z8])],[(0,[z445,z1,z2,z3,z4,z5,z8]),(0,[z52,z1,z2,z3,z4,z5,z138]),(0,[z1,z446,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z447]),(0,[z1,z2,z3,z4,z5,z8,z448])],[(0,[z449,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z87,z4,z27,z5,z8]),(0,[z1,z193,z10,z2,z3,z4,z5]),(0,[z1,z2,z45,z3,z17,z4,z8]),(1,[z1,z2,z3,z4,z5,z201])],[(0,[z450,z1,z2,z3,z4,z5,z8]),(0,[z1,z451,z2,z3,z4,z5,z8]),(0,[z1,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z32,z5,z20]),(0,[z1,z2,z3,z17,z4,z169,z8])],[(0,[z1,z245,z2,z3,z4,z5,z8]),(0,[z1,z452,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z71,z2,z3,z4,z5,z8]),(0,[z1,z11,z2,z81,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z8,z15])]],
   [[(0,[z225,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z394]),(0,[z1,z2,z3,z4,z5,z66,z20]),(0,[z1,z454,z2,z3,z87,z4,z5]),(1,[z1,z2,z3,z4,z315,z8]),(0,[z1,z2,z45,z3,z4,z171,z8]),(0,[z1,z2,z3,z4,z5,z8,z455]),(0,[z1,z12,z2,z3,z4,z32,z8])],[(1,[z1,z456,z3,z4,z5,z8]),(0,[z1,z457,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z99,z86])],[(0,[z1,z2,z3,z4,z420,z5,z8]),(0,[z1,z458,z2,z3,z4,z5,z8])],[(0,[z1,z2,z115,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z459,z8]),(0,[z1,z2,z3,z17,z4,z5,z20]),(0,[z1,z11,z2,z87,z4,z5,z8]),(0,[z1,z140,z2,z3,z4,z64,z5]),(0,[z225,z1,z54,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z412,z8])],[(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z8]),(0,[z1,z29,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z236,z8]),(0,[z1,z2,z3,z4,z375,z5,z8]),(1,[z192,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z460,z4,z5,z8]),(0,[z1,z2,z3,z461,z4,z5,z8]),(0,[z1,z31,z2,z3,z4,z55,z8]),(0,[z1,z2,z462,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z168]),(0,[z1,z2,z3,z463,z4,z5,z8])],[(0,[z464,z1,z2,z3,z4,z5,z8]),(0,[z465,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z35,z5,z8]),(1,[z1,z71,z2,z3,z4,z20])],[(0,[z1,z466,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z20,z419]),(0,[z1,z2,z3,z4,z5,z8,z467]),(1,[z1,z12,z2,z3,z17,z8]),(0,[z1,z12,z2,z3,z4,z8,z177]),(1,[z1,z12,z2,z3,z86,z8])],[(0,[z1,z2,z3,z4,z5,z468,z8]),(0,[z21,z1,z2,z3,z4,z5,z210]),(0,[z52,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z207,z4,z5,z20]),(0,[z1,z2,z137,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z469,z5,z8]),(0,[z1,z2,z3,z4,z5,z470,z8]),(0,[z1,z471,z2,z3,z4,z5,z8]),(0,[z1,z54,z2,z3,z17,z4,z8]),(0,[z1,z472,z2,z3,z4,z5,z8])],[(1,[z1,z185,z2,z3,z4,z8]),(1,[z1,z139,z3,z166,z5,z8]),(0,[z142,z1,z2,z3,z4,z14,z8]),(1,[z1,z2,z3,z5,z8,z404])],[(1,[z1,z2,z3,z473,z5,z8]),(0,[z21,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z30,z3,z120,z4,z5]),(0,[z474,z1,z2,z3,z4,z5,z8]),(0,[z1,z202,z2,z3,z4,z5,z8])],[(0,[z1,z2,z181,z3,z4,z5,z20]),(0,[z1,z2,z475,z3,z4,z5,z8]),(0,[z476,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z134,z4,z5,z6]),(0,[z1,z295,z2,z3,z4,z5,z8]),(0,[z89,z1,z12,z2,z3,z4,z8]),(0,[z1,z193,z2,z3,z17,z4,z8]),(0,[z477,z1,z2,z3,z4,z5,z8])],[(0,[z97,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z34,z5,z20]),(0,[z1,z81,z3,z87,z4,z5,z8]),(0,[z1,z2,z3,z4,z478,z5,z8]),(0,[z1,z2,z3,z4,z5,z238,z8]),(0,[z1,z2,z3,z479,z4,z5,z8]),(0,[z480,z1,z2,z3,z4,z5,z8]),(0,[z1,z29,z2,z4,z5,z167,z8])],[(0,[z116,z1,z2,z3,z4,z364,z8]),(0,[z1,z193,z119,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z32,z5,z15])],[(0,[z481,z1,z2,z3,z4,z5,z8]),(1,[z1,z12,z2,z3,z134,z8]),(0,[z1,z2,z3,z482,z4,z5,z8]),(0,[z1,z10,z2,z3,z4,z131,z8]),(0,[z1,z2,z207,z4,z27,z5,z8])]],
   [[(0,[z97,z1,z2,z3,z4,z5,z321]),(0,[z483,z1,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z8,z6]),(0,[z1,z2,z484,z3,z4,z5,z8]),(0,[z485,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z285,z8]),(1,[z1,z486,z3,z4,z5,z8])],[(0,[z79,z1,z2,z3,z4,z5,z487]),(0,[z116,z1,z2,z3,z375,z5,z8]),(0,[z1,z488,z2,z3,z4,z5,z8]),(1,[z1,z10,z3,z4,z5,z13])],[(1,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z489,z5,z8]),(0,[z1,z2,z3,z134,z18,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z442]),(0,[z1,z2,z3,z4,z5,z406,z8]),(0,[z1,z12,z2,z3,z4,z8,z46]),(0,[z1,z2,z3,z490,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z99,z168]),(0,[z1,z2,z491,z3,z4,z5,z8])],[(0,[z492,z1,z2,z3,z4,z5,z8]),(0,[z78,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z493,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z366,z8]),(1,[z225,z1,z3,z4,z34,z8]),(0,[z1,z2,z4,z5,z167,z8,z46])],[(0,[z1,z2,z3,z473,z4,z5,z8]),(0,[z1,z2,z115,z87,z4,z5,z8]),(0,[z1,z31,z2,z3,z4,z34,z8]),(0,[z1,z2,z3,z439,z4,z27,z8]),(0,[z1,z12,z2,z3,z17,z4,z8])],[(0,[z88,z1,z2,z115,z4,z5,z8]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z494,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z17,z4,z20]),(0,[z1,z495,z2,z3,z4,z5,z8]),(0,[z1,z2,z496,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z497,z8]),(0,[z1,z2,z3,z4,z18,z5,z8])],[(0,[z498,z1,z2,z3,z4,z5,z8]),(0,[z98,z2,z3,z134,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z135,z8]),(0,[z499,z1,z2,z3,z4,z5,z8]),(0,[z1,z119,z2,z30,z3,z4,z5])]],
   [[(0,[z79,z1,z245,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z500,z8]),(0,[z1,z2,z25,z3,z4,z5,z8]),(0,[z1,z501,z2,z3,z4,z5,z8])],[(0,[z502,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z245,z3,z4,z5,z8]),(0,[z36,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z167,z20]),(0,[z142,z1,z12,z2,z3,z4,z8])],[(0,[z1,z503,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z8,z168])],[(0,[z1,z2,z3,z504,z4,z5,z8]),(0,[z1,z12,z2,z181,z3,z4,z8]),(0,[z102,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z221,z4,z64,z8])],[(0,[z1,z109,z2,z3,z4,z5,z8]),(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z6]),(0,[z1,z3,z166,z4,z64,z5,z8]),(0,[z1,z2,z3,z17,z4,z34,z8]),(0,[z1,z10,z2,z3,z120,z4,z5]),(0,[z1,z2,z3,z4,z421,z5,z8])],[(0,[z1,z2,z3,z160,z4,z5,z8]),(0,[z1,z2,z505,z3,z4,z5,z8]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z168]),(0,[z1,z2,z3,z110,z4,z5,z8]),(0,[z1,z2,z3,z4,z506,z5,z8]),(0,[z1,z2,z3,z4,z5,z507,z8]),(0,[z1,z2,z3,z439,z4,z5,z8]),(0,[z1,z2,z3,z4,z171,z5,z201]),(0,[z1,z2,z3,z18,z5,z66,z8]),(0,[z1,z2,z3,z334,z17,z4,z8]),(0,[z1,z508,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z509,z8]),(0,[z1,z2,z510,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z5,z66,z8])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z1,z12,z2,z3,z4,z66,z8]),(0,[z1,z2,z511,z3,z4,z5,z8])]],
   [[(0,[z512,z1,z2,z3,z4,z5,z8]),(0,[z1,z119,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z513,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z231])],[(0,[z1,z2,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z4,z5,z14,z20]),(0,[z1,z2,z3,z4,z5,z8,z514]),(0,[z1,z2,z515,z3,z4,z5,z8])],[(0,[z1,z446,z2,z3,z4,z5,z8]),(0,[z516,z1,z2,z3,z4,z5,z8]),(0,[z1,z517,z2,z3,z4,z5,z8])],[(0,[z0,z1,z12,z2,z3,z4,z8]),(1,[z1,z2,z3,z326,z5,z8]),(0,[z1,z2,z3,z4,z5,z138,z8]),(0,[z1,z2,z3,z4,z5,z232,z20]),(0,[z1,z2,z3,z4,z5,z315,z8]),(0,[z1,z2,z3,z518,z4,z5,z8])],[(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z1,z2,z3,z17,z4,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z519,z8]),(0,[z1,z2,z520,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z521,z5,z8]),(0,[z1,z119,z10,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z350]),(0,[z1,z2,z180,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z236,z8]),(0,[z1,z2,z3,z4,z5,z362,z8]),(0,[z1,z12,z2,z3,z4,z19,z8]),(0,[z1,z2,z3,z4,z14,z135,z8]),(0,[z1,z2,z81,z4,z5,z167,z8]),(0,[z142,z1,z2,z3,z4,z171,z8]),(0,[z1,z2,z3,z17,z4,z86,z8]),(0,[z1,z193,z2,z3,z4,z5,z168])],[(0,[z0,z1,z2,z3,z4,z5,z362]),(0,[z1,z522,z2,z3,z4,z5,z20]),(0,[z1,z29,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z523,z8]),(0,[z1,z2,z3,z4,z5,z8,z524]),(0,[z225,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z525,z8]),(0,[z1,z2,z3,z19,z64,z5,z8]),(0,[z1,z2,z3,z4,z526,z5,z8]),(0,[z1,z2,z3,z4,z527,z5,z8]),(1,[z1,z2,z3,z4,z5,z177])]],
   [[(0,[z1,z29,z486,z3,z4,z5,z8]),(0,[z1,z2,z3,z363,z17,z4,z8])],[(0,[z1,z528,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z379,z4,z5,z8]),(0,[z529,z1,z2,z3,z4,z5,z8]),(0,[z1,z139,z2,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z530,z5,z8]),(0,[z98,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z207,z4,z5,z6]),(0,[z531,z1,z2,z3,z4,z5,z8]),(0,[z532,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z533,z5,z8])],[(0,[z79,z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z5,z534,z8]),(0,[z1,z2,z3,z4,z5,z535,z8]),(0,[z1,z2,z3,z4,z5,z536,z20]),(0,[z1,z2,z3,z4,z5,z537,z8]),(0,[z225,z1,z2,z3,z4,z55,z8])],[(0,[z538,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z135,z8]),(0,[z539,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z540,z4,z5,z8]),(0,[z1,z2,z3,z4,z541,z5,z8])],[(0,[z1,z2,z181,z3,z4,z5,z6]),(0,[z1,z172,z2,z3,z17,z4,z8]),(0,[z1,z2,z542,z3,z4,z5,z8]),(0,[z1,z2,z543,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z190,z8])],[(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z171,z5,z20]),(0,[z24,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z544,z8]),(0,[z1,z193,z2,z30,z3,z4,z5]),(0,[z1,z2,z545,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z546,z8]),(0,[z547,z1,z2,z3,z4,z5,z8])],[(1,[z21,z2,z3,z4,z135,z8]),(0,[z1,z140,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z548,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z549,z8])]],
   [[(1,[z1,z2,z3,z4,z5,z277]),(0,[z1,z2,z3,z4,z5,z397,z8]),(0,[z225,z1,z3,z4,z34,z5,z8]),(0,[z1,z119,z2,z3,z4,z5,z15]),(0,[z36,z1,z2,z3,z27,z5,z8]),(1,[z1,z2,z3,z4,z285,z8]),(0,[z1,z2,z30,z3,z17,z4,z8])],[(0,[z116,z1,z456,z3,z4,z5,z8]),(0,[z1,z2,z30,z3,z4,z61,z8])],[(0,[z1,z2,z3,z134,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z388])],[(0,[z192,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z37,z207,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z550])],[(0,[z79,z1,z2,z3,z4,z325,z8]),(0,[z551,z1,z2,z3,z4,z5,z8]),(0,[z1,z11,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z552]),(0,[z1,z12,z2,z3,z4,z4,z8]),(1,[z1,z12,z2,z3,z4,z57])],[(0,[z1,z2,z3,z4,z5,z487,z8]),(0,[z1,z2,z3,z4,z5,z5,z8]),(0,[z1,z2,z3,z4,z5,z553,z8]),(0,[z1,z2,z3,z17,z166,z4,z8]),(0,[z1,z2,z554,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z414,z8]),(0,[z1,z2,z3,z4,z4,z5,z8]),(1,[z97,z2,z3,z19,z5,z8]),(0,[z1,z2,z3,z4,z34,z135,z8]),(0,[z1,z555,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z556]),(0,[z1,z12,z2,z3,z207,z4,z8]),(0,[z1,z29,z2,z3,z4,z5,z15])],[(0,[z1,z2,z557,z3,z4,z5,z8]),(0,[z1,z558,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z134,z4,z8]),(1,[z1,z2,z3,z17,z4,z6]),(0,[z1,z193,z2,z3,z4,z5,z20]),(0,[z1,z2,z559,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z560])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z561,z1,z2,z3,z4,z5,z8]),(0,[z1,z10,z2,z3,z4,z5,z13]),(0,[z1,z2,z562,z3,z4,z5,z8])],[(0,[z78,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z337,z3,z4,z5,z8]),(0,[z563,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z564]),(0,[z1,z2,z456,z3,z4,z5,z8])],[(0,[z565,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z566,z4,z5,z8]),(0,[z36,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z167,z6]),(0,[z1,z567,z2,z3,z4,z5,z8])],[(0,[z1,z568,z2,z3,z4,z5,z8]),(0,[z116,z1,z2,z3,z473,z5,z8]),(0,[z21,z1,z2,z3,z4,z5,z118]),(0,[z1,z12,z2,z3,z4,z64,z8]),(1,[z1,z29,z2,z4,z5,z167])],[(0,[z88,z1,z2,z3,z4,z5,z8]),(0,[z94,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z249,z8])],[(0,[z1,z2,z569,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z570,z6]),(0,[z571,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z572,z4,z5,z8]),(0,[z1,z12,z2,z403,z3,z4,z8])],[(0,[z1,z2,z3,z4,z5,z6,z15]),(0,[z573,z1,z2,z3,z4,z5,z8]),(0,[z1,z574,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z575,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z41,z8]),(0,[z1,z2,z3,z576,z4,z5,z8]),(0,[z1,z2,z3,z577,z4,z5,z8])],[(0,[z1,z578,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z35,z5,z135,z8]),(0,[z1,z579,z2,z3,z4,z5,z8]),(0,[z262,z1,z12,z2,z3,z4,z8]),(1,[z1,z12,z193,z2,z3,z8]),(0,[z1,z2,z3,z4,z5,z580,z8])]],
   [[(0,[z1,z245,z3,z87,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z459]),(0,[z1,z12,z2,z3,z4,z14,z8]),(0,[z581,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z8,z231])],[(0,[z1,z11,z181,z3,z4,z5,z8]),(0,[z582,z1,z2,z3,z4,z5,z8]),(0,[z88,z2,z115,z3,z4,z5,z8]),(0,[z1,z119,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z72]),(0,[z1,z10,z2,z3,z17,z4,z8])],[(1,[z1,z2,z3,z4,z5,z320]),(1,[z0,z245,z3,z4,z5,z8]),(0,[z116,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z19,z27,z5,z8]),(0,[z1,z2,z3,z4,z5,z14,z6]),(1,[z1,z2,z3,z221,z4,z8]),(0,[z1,z2,z3,z4,z5,z583,z8]),(0,[z1,z2,z3,z17,z4,z27,z8])],[(1,[z1,z2,z3,z4,z5,z487]),(0,[z1,z2,z3,z4,z584,z5,z8]),(0,[z52,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z585,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z586]),(0,[z1,z2,z3,z4,z5,z8,z587]),(0,[z1,z12,z2,z3,z4,z99,z8]),(0,[z1,z31,z2,z3,z4,z5,z8])],[(0,[z1,z588,z2,z3,z4,z5,z8]),(0,[z102,z2,z3,z4,z5,z20,z8]),(0,[z1,z2,z3,z87,z4,z5,z20]),(0,[z589,z1,z2,z3,z4,z5,z8])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z21,z1,z12,z2,z3,z4,z8]),(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z120,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z590]),(0,[z1,z2,z3,z4,z5,z591,z8]),(0,[z1,z592,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z593,z8]),(0,[z1,z2,z3,z120,z5,z86,z8]),(0,[z1,z2,z3,z4,z32,z5,z8]),(0,[z1,z2,z594,z3,z4,z5,z8])],[(0,[z1,z595,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z596,z8]),(0,[z1,z2,z3,z4,z597,z5,z8]),(0,[z1,z2,z30,z3,z4,z5,z167]),(0,[z1,z2,z3,z4,z5,z598,z8])]],
   [[(0,[z1,z599,z2,z3,z4,z5,z8]),(0,[z98,z1,z2,z3,z4,z5,z277]),(0,[z1,z600,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z601]),(0,[z1,z2,z486,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z8,z550])],[(0,[z1,z2,z3,z4,z5,z602,z8]),(0,[z603,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z604,z8]),(0,[z1,z2,z3,z4,z5,z8,z605]),(0,[z1,z2,z45,z3,z4,z5,z6]),(0,[z24,z1,z3,z4,z64,z5,z8]),(0,[z142,z1,z2,z45,z4,z5,z8]),(0,[z142,z1,z2,z4,z171,z5,z8]),(0,[z1,z29,z2,z3,z4,z5,z46])],[(0,[z1,z245,z2,z3,z17,z4,z8]),(0,[z1,z606,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z228,z4,z5,z8]),(0,[z1,z607,z2,z3,z4,z5,z8]),(0,[z1,z608,z2,z3,z4,z5,z8]),(0,[z609,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z610,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z106]),(1,[z1,z2,z3,z85,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z611])],[(0,[z1,z612,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z81,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z613,z8]),(0,[z1,z10,z3,z4,z5,z8,z13]),(0,[z1,z12,z29,z2,z3,z4,z8]),(0,[z332,z1,z2,z3,z4,z5,z8])],[(0,[z1,z12,z2,z3,z134,z5,z8]),(0,[z1,z2,z614,z3,z4,z5,z8]),(0,[z142,z1,z2,z3,z4,z5,z20]),(1,[z1,z71,z2,z3,z4,z8]),(0,[z1,z29,z383,z3,z4,z5,z8]),(0,[z1,z2,z615,z3,z4,z5,z8]),(0,[z1,z193,z2,z3,z5,z8,z168])],[(0,[z1,z12,z2,z3,z4,z20,z8]),(0,[z1,z2,z3,z4,z616,z5,z8])],[(0,[z52,z1,z2,z3,z4,z5,z388]),(0,[z1,z528,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z171,z5,z6]),(0,[z1,z2,z3,z17,z4,z55,z8]),(0,[z1,z12,z12,z2,z3,z4,z8]),(0,[z1,z31,z2,z3,z4,z5,z15])]],
   [[(0,[z617,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z618,z3,z4,z5,z8]),(1,[z1,z12,z2,z3,z4,z20]),(0,[z1,z2,z3,z207,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z190,z8])],[(0,[z1,z2,z3,z4,z5,z6,z46]),(0,[z619,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z30,z3,z4,z5,z99]),(0,[z465,z1,z2,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z5,z620,z8]),(0,[z1,z2,z3,z4,z621,z5,z8]),(0,[z622,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z623,z8])],[(0,[z1,z2,z181,z3,z4,z5,z8]),(0,[z624,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z625,z4,z5,z8]),(0,[z1,z2,z3,z4,z165,z5,z20]),(0,[z626,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z627,z3,z4,z5,z8]),(0,[z1,z2,z628,z3,z4,z5,z8])],[(0,[z629,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z203,z8]),(0,[z1,z2,z3,z630,z4,z5,z8]),(0,[z97,z1,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z19,z5,z8]),(0,[z1,z2,z3,z4,z34,z5,z8]),(0,[z1,z631,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z32,z15]),(0,[z1,z2,z3,z4,z99,z8,z15])],[(0,[z1,z632,z2,z3,z4,z5,z8]),(0,[z1,z11,z2,z3,z4,z5,z6]),(0,[z102,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z20,z8,z215]),(0,[z155,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z633,z8]),(0,[z1,z356,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z634,z4,z5,z8]),(0,[z1,z2,z254,z3,z4,z27,z5]),(0,[z1,z2,z635,z3,z4,z5,z8])],[(0,[z0,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z171,z135,z8]),(0,[z1,z2,z3,z4,z5,z636,z8])]],
   [[(0,[z0,z245,z2,z3,z4,z5,z8]),(1,[z88,z2,z115,z4,z5,z8]),(0,[z98,z1,z2,z3,z4,z5,z459]),(0,[z1,z193,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z637,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z57,z8])],[],[(0,[z1,z2,z3,z4,z5,z638,z8]),(0,[z1,z2,z3,z639,z4,z5,z8]),(0,[z1,z2,z45,z4,z5,z14,z8]),(0,[z1,z12,z2,z3,z577,z4,z8])],[(1,[z1,z2,z3,z4,z5,z210]),(0,[z1,z454,z2,z3,z4,z5,z8]),(1,[z1,z11,z81,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z171,z8]),(1,[z1,z193,z2,z3,z5,z168]),(0,[z1,z2,z3,z4,z5,z640,z8])],[(0,[z1,z2,z37,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z641]),(0,[z642,z1,z2,z3,z4,z5,z8]),(0,[z1,z643,z2,z3,z4,z5,z8])],[(0,[z116,z2,z3,z160,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z321]),(1,[z1,z454,z2,z3,z4,z5]),(0,[z1,z12,z139,z2,z3,z4,z8]),(1,[z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z490,z17,z4,z8])],[(0,[z1,z644,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z645]),(1,[z1,z2,z3,z4,z61,z8])],[(0,[z79,z1,z2,z337,z4,z5,z8]),(0,[z116,z1,z2,z115,z4,z5,z8]),(0,[z1,z2,z81,z115,z4,z5,z8]),(0,[z646,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z228,z4,z5]),(0,[z1,z139,z2,z3,z166,z5,z8]),(1,[z1,z2,z479,z4,z5,z8]),(1,[z1,z2,z189,z4,z5,z8]),(1,[z1,z2,z3,z4,z420,z8]),(0,[z1,z2,z3,z4,z5,z647,z8]),(0,[z1,z2,z30,z4,z5,z8,z46]),(0,[z1,z2,z3,z4,z5,z648,z8]),(0,[z1,z355,z12,z2,z3,z4,z8])]],
   [[(1,[z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z649,z5,z8]),(1,[z2,z3,z4,z5,z20,z6]),(0,[z1,z2,z3,z4,z650,z5,z8]),(0,[z36,z1,z2,z3,z4,z5,z8]),(0,[z1,z651,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z421,z8]),(0,[z1,z2,z3,z4,z5,z167,z8]),(0,[z1,z2,z3,z342,z4,z5,z8]),(0,[z1,z652,z2,z3,z4,z5,z8]),(0,[z1,z2,z653,z3,z4,z5,z8])],[(0,[z1,z12,z245,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z64,z5,z20]),(0,[z1,z2,z3,z4,z654,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z655]),(0,[z1,z2,z3,z5,z8,z404,z15])],[(0,[z24,z1,z139,z3,z4,z5,z8]),(0,[z1,z10,z2,z3,z4,z5,z99]),(0,[z36,z1,z2,z3,z207,z5,z8]),(0,[z1,z2,z3,z4,z5,z656,z8])],[(0,[z1,z2,z657,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z658,z5,z8]),(0,[z1,z2,z3,z4,z5,z570,z8]),(0,[z1,z2,z3,z4,z5,z659,z8]),(0,[z36,z1,z2,z4,z27,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z660]),(0,[z1,z172,z11,z3,z4,z5,z8]),(0,[z1,z661,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z17,z18,z8])],[(0,[z79,z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z296,z5,z8]),(0,[z1,z2,z3,z4,z5,z663,z8]),(0,[z664,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z665,z8])],[(1,[z1,z2,z3,z4,z325,z8]),(0,[z1,z2,z3,z666,z4,z5,z8]),(0,[z1,z233,z2,z3,z4,z5,z20]),(0,[z1,z172,z2,z81,z4,z5,z8]),(0,[z1,z12,z399,z2,z3,z4,z8])],[(0,[z192,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z99,z20]),(0,[z1,z119,z2,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z5,z57])]],
   [[(0,[z1,z2,z3,z160,z17,z4,z8]),(0,[z667,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z453,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z14,z8])],[(0,[z668,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z669,z5,z8]),(0,[z1,z2,z30,z81,z4,z5,z8]),(0,[z1,z226,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z670,z8]),(0,[z1,z2,z3,z4,z671,z5,z8]),(1,[z1,z12,z2,z3,z4,z177])],[(0,[z1,z2,z3,z4,z55,z135,z8]),(0,[z1,z172,z2,z87,z4,z5,z8]),(0,[z250,z1,z2,z3,z4,z5,z8]),(0,[z1,z119,z2,z3,z4,z5,z41]),(1,[z1,z53,z3,z4,z5,z8]),(0,[z672,z1,z2,z3,z4,z5,z8]),(0,[z1,z428,z2,z3,z5,z8,z15]),(0,[z1,z2,z3,z4,z5,z8,z15])],[(0,[z1,z2,z673,z3,z4,z5,z8]),(0,[z116,z88,z2,z3,z4,z5,z8]),(0,[z1,z2,z45,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z8,z70]),(0,[z674,z1,z2,z3,z4,z5,z8]),(0,[z1,z54,z3,z4,z5,z55,z8]),(0,[z1,z2,z3,z120,z4,z5,z8])],[(0,[z1,z2,z3,z4,z675,z5,z8]),(0,[z1,z10,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z676,z5,z8])],[(0,[z1,z2,z3,z677,z4,z5,z8]),(0,[z1,z522,z2,z3,z4,z5,z8]),(0,[z1,z29,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z18,z5,z8])],[(1,[z1,z2,z3,z76,z4,z8]),(0,[z1,z2,z678,z3,z4,z5,z8]),(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z37,z87,z4,z5,z8]),(1,[z1,z2,z3,z4,z131,z8]),(0,[z679,z1,z2,z3,z4,z5,z8])],[(0,[z1,z251,z2,z3,z4,z5,z20]),(0,[z680,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z681,z8]),(0,[z1,z2,z3,z17,z4,z682,z8])]],
   [[(0,[z683,z1,z2,z3,z4,z5,z8]),(0,[z1,z684,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z35,z8]),(0,[z685,z1,z2,z3,z4,z5,z8]),(0,[z1,z686,z2,z3,z4,z5,z8]),(0,[z1,z687,z2,z3,z4,z5,z8]),(0,[z688,z1,z2,z3,z4,z5,z8])],[(0,[z1,z689,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z690,z4,z5,z8]),(1,[z1,z12,z2,z3,z4,z6]),(0,[z225,z1,z2,z3,z17,z4,z8]),(0,[z1,z119,z2,z479,z4,z5,z8]),(0,[z1,z119,z2,z189,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z691]),(0,[z1,z2,z3,z4,z5,z692,z8])],[(0,[z1,z2,z3,z4,z5,z536,z8]),(0,[z693,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z20,z20]),(0,[z1,z2,z3,z4,z5,z694,z8]),(0,[z1,z2,z4,z171,z5,z14,z8]),(0,[z1,z695,z2,z3,z4,z5,z8]),(0,[z696,z1,z2,z3,z4,z5,z8])],[(0,[z697,z1,z2,z3,z4,z5,z8]),(0,[z1,z11,z81,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z698,z8]),(0,[z1,z2,z37,z3,z27,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z177])],[(1,[z1,z2,z3,z4,z203,z8]),(0,[z1,z2,z3,z699,z4,z5,z8]),(0,[z1,z700,z2,z3,z4,z5,z8]),(0,[z1,z413,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z682,z5,z8])],[(0,[z98,z1,z2,z3,z17,z4,z8]),(1,[z1,z2,z3,z4,z303,z5]),(0,[z1,z139,z3,z166,z4,z5,z8]),(0,[z1,z701,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z171,z5,z8]),(0,[z1,z702,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z167,z8]),(0,[z1,z12,z661,z2,z3,z4,z8])],[(0,[z79,z1,z2,z3,z313,z5,z8]),(0,[z1,z2,z3,z4,z5,z703,z8]),(0,[z1,z3,z87,z4,z64,z5,z8]),(0,[z1,z2,z3,z704,z4,z5,z8])],[(0,[z245,z2,z181,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z209,z8]),(0,[z52,z1,z2,z3,z4,z5,z20]),(0,[z1,z54,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z705,z5,z8]),(0,[z1,z2,z3,z4,z706,z5,z8])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z140,z2,z3,z4,z5])],[(0,[z1,z2,z3,z313,z5,z106]),(0,[z97,z185,z2,z3,z19,z8]),(0,[z1,z12,z2,z3,z638,z8]),(0,[z1,z172,z454,z87,z4,z5])],[(0,[z2,z3,z4,z5,z6,z244]),(0,[z1,z2,z3,z4,z296,z707]),(0,[z1,z12,z119,z3,z4,z41]),(0,[z1,z2,z3,z4,z5,z708])],[(0,[z1,z709,z3,z4,z5,z8]),(0,[z43,z413,z2,z3,z4,z8]),(0,[z1,z12,z2,z3,z66,z177]),(0,[z1,z2,z3,z4,z32,z15])],[(0,[z1,z2,z3,z4,z5,z710]),(0,[z1,z243,z2,z3,z5,z372]),(0,[z1,z2,z3,z4,z199,z442]),(0,[z1,z2,z3,z5,z20,z711]),(0,[z1,z2,z3,z712,z4,z8]),(0,[z1,z713,z2,z3,z5,z8])],[(0,[z1,z2,z714,z4,z5,z8]),(0,[z1,z2,z82,z3,z19,z8]),(0,[z1,z12,z2,z3,z85,z8]),(0,[z1,z715,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z716,z8])],[(0,[z1,z2,z3,z4,z5,z717])],[(0,[z2,z718,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z719,z8]),(0,[z1,z31,z2,z3,z4,z238]),(0,[z1,z2,z3,z4,z5,z720])],[(0,[z1,z2,z3,z4,z6,z215]),(0,[z1,z12,z2,z3,z418,z8]),(0,[z1,z12,z139,z3,z166,z8]),(0,[z1,z2,z3,z4,z5,z721]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z12,z2,z3,z4,z723])],[(0,[z1,z109,z3,z375,z5,z8]),(0,[z2,z3,z4,z5,z724,z8]),(0,[z1,z12,z2,z3,z4,z725])],[(0,[z1,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z726,z4,z8])],[(0,[z1,z10,z3,z17,z4,z13]),(0,[z1,z2,z30,z4,z5,z716])],[(0,[z43,z2,z3,z4,z35,z8]),(0,[z1,z2,z3,z4,z727,z6]),(0,[z1,z2,z25,z4,z5,z8]),(0,[z1,z454,z2,z3,z4,z5]),(0,[z1,z454,z10,z3,z4,z5]),(0,[z1,z728,z2,z3,z4,z8]),(0,[z1,z2,z3,z729,z4,z8]),(0,[z1,z2,z3,z4,z99,z177])],[(0,[z1,z344,z87,z4,z5,z8]),(0,[z1,z91,z37,z4,z5,z8])],[(0,[z1,z233,z3,z4,z5,z70]),(1,[z1,z2,z3,z4,z730]),(0,[z1,z2,z3,z228,z4,z5]),(0,[z1,z2,z3,z120,z173,z5]),(0,[z1,z29,z2,z4,z352,z5])],[(0,[z88,z2,z115,z17,z4,z8]),(0,[z98,z2,z3,z134,z5,z6]),(0,[z2,z3,z4,z5,z20,z6])]],
   [[(0,[z1,z2,z3,z313,z5,z20]),(0,[z1,z2,z3,z4,z731,z15])],[(0,[z1,z2,z3,z732,z5,z8]),(0,[z1,z12,z2,z3,z19,z6]),(0,[z52,z2,z3,z4,z35,z6]),(0,[z1,z2,z3,z4,z5,z733]),(0,[z1,z54,z403,z3,z4,z8]),(0,[z1,z12,z2,z3,z86,z57]),(0,[z1,z2,z3,z734,z66,z8]),(0,[z16,z2,z3,z363,z4,z8])],[(0,[z1,z2,z3,z4,z735,z8]),(0,[z268,z2,z3,z4,z5,z6]),(0,[z36,z1,z2,z27,z5,z6])],[(0,[z1,z2,z736,z4,z5,z8])],[(0,[z1,z2,z3,z737,z5,z8]),(0,[z1,z2,z3,z4,z362,z738]),(0,[z1,z2,z30,z4,z5,z394]),(0,[z1,z2,z82,z3,z4,z8]),(0,[z1,z739,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z325,z8]),(0,[z1,z12,z2,z3,z76,z8])],[(0,[z21,z2,z3,z4,z135,z118]),(0,[z1,z2,z3,z4,z740,z20]),(0,[z1,z2,z479,z17,z4,z8]),(0,[z1,z2,z189,z17,z4,z8]),(0,[z1,z12,z2,z3,z681,z8])],[(0,[z1,z2,z3,z4,z5,z133]),(0,[z1,z2,z3,z17,z4,z126])],[(0,[z1,z2,z3,z4,z741,z8]),(0,[z1,z2,z3,z4,z5,z742]),(0,[z1,z12,z2,z3,z134,z57]),(0,[z1,z2,z3,z4,z57,z15]),(0,[z1,z12,z2,z3,z692,z8]),(0,[z1,z31,z2,z3,z4,z99])],[(0,[z52,z2,z3,z4,z743,z8]),(0,[z1,z54,z3,z4,z55,z20]),(0,[z2,z3,z4,z384,z5,z20]),(0,[z1,z2,z3,z4,z8,z744])],[(0,[z1,z2,z337,z4,z5,z6]),(0,[z1,z193,z2,z3,z5,z745])],[(0,[z1,z2,z3,z4,z746,z5]),(0,[z1,z2,z3,z4,z310,z20]),(0,[z1,z2,z3,z4,z154,z20]),(0,[z1,z10,z3,z4,z5,z84])],[(0,[z1,z2,z3,z747,z4,z8]),(0,[z1,z2,z3,z4,z312,z15]),(0,[z1,z12,z695,z2,z3,z8])],[(0,[z1,z2,z3,z4,z748,z8]),(0,[z24,z1,z3,z64,z5,z6]),(0,[z1,z2,z3,z141,z4,z6]),(0,[z1,z2,z3,z4,z131,z8])],[(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z202,z2,z3,z4,z6]),(0,[z1,z2,z110,z4,z5,z8])],[(0,[z79,z181,z337,z4,z5,z8]),(0,[z9,z245,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z750]),(0,[z56,z2,z3,z4,z135,z8]),(0,[z1,z2,z3,z439,z4,z20])]],
   [[(0,[z1,z2,z3,z751,z4,z8]),(0,[z1,z12,z2,z3,z4,z6]),(0,[z1,z12,z2,z3,z8,z556])],[(0,[z2,z3,z4,z5,z549,z20]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z1,z53,z3,z17,z4,z8]),(0,[z1,z2,z753,z27,z5,z8]),(0,[z1,z2,z3,z4,z8,z754])],[(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z2,z3,z4,z8,z756]),(0,[z757,z12,z2,z3,z4,z8])],[(0,[z1,z2,z3,z221,z4,z303]),(0,[z1,z2,z3,z577,z4,z177]),(0,[z1,z2,z3,z8,z404,z231])],[(0,[z1,z2,z758,z4,z5,z8]),(0,[z642,z2,z3,z19,z5,z8]),(0,[z2,z3,z17,z4,z20,z6])],[(0,[z97,z2,z3,z759,z5,z8]),(0,[z1,z760,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z761,z8]),(0,[z1,z2,z3,z4,z5,z762])],[(0,[z1,z2,z3,z313,z236,z8]),(0,[z1,z2,z3,z4,z763,z8]),(0,[z1,z2,z3,z4,z764,z8]),(0,[z1,z2,z765,z3,z4,z5])],[(0,[z1,z2,z337,z80,z5,z8]),(0,[z1,z766,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z767,z8]),(0,[z1,z2,z3,z4,z5,z768])],[(0,[z1,z2,z3,z4,z769,z8]),(0,[z1,z2,z770,z4,z5,z8])],[(0,[z79,z181,z113,z4,z5,z8]),(0,[z1,z2,z3,z4,z265,z20]),(0,[z1,z2,z3,z17,z4,z277]),(0,[z192,z2,z3,z4,z5,z724]),(0,[z1,z2,z3,z120,z5,z86])],[(0,[z1,z771,z2,z3,z313,z8]),(0,[z1,z2,z3,z772,z5,z8]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z139,z3,z774,z5,z8]),(0,[z1,z2,z3,z4,z775,z8])],[(0,[z116,z456,z160,z4,z5,z8]),(0,[z1,z2,z776,z3,z4,z5])],[(0,[z97,z2,z3,z19,z5,z366]),(0,[z52,z2,z3,z85,z35,z8]),(0,[z1,z12,z2,z3,z86,z20])],[(0,[z1,z12,z2,z3,z473,z8]),(0,[z1,z2,z3,z4,z203,z126]),(0,[z1,z2,z3,z4,z777,z8]),(0,[z1,z2,z3,z4,z778,z8]),(0,[z1,z2,z3,z4,z779,z20]),(0,[z1,z2,z3,z4,z5,z780]),(0,[z89,z1,z2,z3,z4,z177])],[(0,[z1,z2,z3,z4,z781,z8])]],
   [[(0,[z1,z2,z3,z4,z782,z8]),(0,[z1,z12,z2,z3,z255,z8]),(0,[z94,z1,z12,z2,z3,z8])],[(0,[z1,z2,z3,z313,z5,z6]),(0,[z1,z2,z3,z783,z4,z8]),(0,[z1,z12,z2,z3,z382,z8]),(0,[z1,z12,z2,z3,z66,z8])],[(0,[z1,z2,z3,z4,z5,z784])],[(0,[z1,z2,z113,z80,z5,z8]),(0,[z1,z74,z87,z4,z5,z8])],[(0,[z1,z2,z785,z4,z5,z8]),(0,[z1,z12,z2,z3,z134,z20]),(0,[z1,z12,z2,z3,z4,z786])],[(0,[z335,z2,z115,z4,z5,z8]),(0,[z1,z486,z3,z4,z5,z20]),(0,[z279,z2,z3,z4,z5,z20])],[(0,[z1,z2,z3,z4,z787,z8]),(0,[z1,z2,z788,z4,z5,z8]),(0,[z116,z2,z160,z473,z5,z8]),(0,[z1,z12,z2,z3,z460,z8]),(0,[z1,z2,z789,z3,z4,z8])],[(0,[z1,z2,z3,z4,z5,z790])],[(0,[z1,z2,z113,z4,z5,z106]),(0,[z1,z791,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z792,z8]),(0,[z1,z2,z3,z4,z793,z8])],[(0,[z116,z2,z160,z4,z5,z20]),(0,[z1,z12,z172,z87,z4,z8]),(0,[z262,z1,z403,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z731])],[(0,[z1,z109,z3,z4,z5,z8]),(0,[z1,z54,z3,z4,z55,z6]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z36,z1,z2,z753,z5,z8]),(0,[z1,z2,z45,z4,z795,z8]),(0,[z1,z428,z2,z3,z171,z8])],[(0,[z1,z2,z3,z4,z5,z796]),(0,[z1,z2,z797,z4,z5,z8])],[(0,[z1,z456,z3,z375,z5,z8]),(0,[z1,z2,z3,z4,z310,z6]),(0,[z1,z2,z3,z4,z154,z6])],[(0,[z1,z479,z4,z5,z41,z8])],[(0,[z1,z10,z486,z3,z4,z5])],[(0,[z1,z798,z2,z3,z4,z366]),(0,[z1,z12,z164,z2,z3,z8]),(0,[z1,z2,z3,z4,z5,z799]),(0,[z1,z2,z3,z4,z8,z800])]],
   [[(0,[z2,z115,z797,z4,z5,z8]),(0,[z1,z2,z3,z439,z4,z6])],[(0,[z581,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z801,z5]),(0,[z1,z2,z4,z795,z5,z8])],[(0,[z2,z3,z4,z5,z6,z425]),(0,[z1,z802,z2,z3,z5,z6]),(0,[z1,z2,z803,z4,z5,z8])],[(0,[z1,z3,z804,z4,z5,z8]),(0,[z1,z2,z3,z4,z412,z15])],[(0,[z1,z2,z3,z4,z5,z805]),(0,[z1,z806,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z147])],[(0,[z1,z2,z3,z4,z325,z487]),(0,[z1,z2,z81,z254,z4,z5]),(0,[z1,z2,z82,z3,z4,z303]),(0,[z1,z12,z2,z3,z17,z177]),(0,[z1,z12,z2,z3,z775,z8]),(0,[z1,z807,z3,z4,z5,z8])],[(0,[z1,z2,z113,z4,z5,z20]),(0,[z1,z2,z3,z17,z375,z8])],[(0,[z1,z808,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z362]),(0,[z1,z2,z3,z4,z5,z809]),(0,[z1,z2,z3,z375,z5,z20]),(0,[z1,z2,z82,z3,z134,z8]),(0,[z1,z810,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z811])],[(0,[z1,z2,z3,z812,z5,z8]),(0,[z1,z2,z3,z17,z4,z138]),(0,[z1,z2,z3,z5,z6,z404]),(0,[z1,z29,z2,z3,z4,z215]),(0,[z1,z813,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z814]),(0,[z1,z2,z3,z32,z404,z15])],[(0,[z1,z2,z3,z4,z815,z8]),(0,[z1,z2,z3,z4,z265,z6]),(0,[z1,z3,z166,z774,z5,z8])],[(0,[z116,z2,z160,z4,z364,z8]),(0,[z1,z2,z3,z4,z5,z366]),(0,[z1,z2,z3,z4,z20,z215]),(0,[z1,z816,z2,z3,z4,z5])],[(0,[z1,z2,z4,z5,z8,z817]),(0,[z1,z2,z818,z4,z5,z6]),(0,[z1,z819,z2,z3,z4,z8]),(0,[z1,z820,z3,z4,z5,z8])],[(0,[z1,z12,z2,z3,z86,z6])],[(0,[z1,z2,z3,z821,z4,z8])]],
   [[(0,[z1,z264,z87,z4,z5,z8]),(0,[z1,z12,z383,z3,z4,z8]),(0,[z332,z1,z2,z3,z4,z57]),(0,[z1,z202,z2,z3,z4,z15])],[(0,[z1,z12,z2,z3,z4,z126])],[(0,[z1,z2,z3,z4,z5,z388]),(0,[z2,z3,z4,z5,z6,z280]),(0,[z1,z172,z87,z4,z5,z8]),(0,[z1,z12,z2,z3,z170,z8])],[(0,[z1,z2,z337,z4,z236,z8]),(0,[z98,z2,z3,z134,z5,z277])],[(0,[z1,z181,z113,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z97,z2,z3,z17,z19,z8])],[(0,[z1,z2,z3,z4,z5,z823]),(0,[z1,z824,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z134,z6]),(0,[z1,z11,z81,z17,z4,z8]),(0,[z1,z2,z3,z4,z825,z8]),(0,[z1,z2,z3,z4,z55,z177]),(0,[z1,z826,z2,z3,z4,z5])],[(0,[z88,z12,z2,z115,z4,z8]),(0,[z1,z486,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z827])],[(0,[z1,z2,z3,z4,z828,z8]),(0,[z1,z2,z3,z4,z20,z829])],[],[],[(0,[z1,z830,z2,z3,z4,z8]),(0,[z116,z2,z797,z4,z5,z8]),(0,[z116,z2,z160,z4,z5,z6]),(0,[z1,z383,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z831,z8])],[(0,[z1,z2,z3,z4,z832,z8]),(0,[z97,z2,z3,z19,z5,z20]),(0,[z1,z2,z3,z4,z5,z833]),(0,[z1,z2,z30,z336,z4,z5])],[(0,[z1,z2,z3,z375,z364,z8]),(0,[z1,z2,z834,z4,z5,z20])],[(0,[z79,z181,z3,z4,z5,z8]),(0,[z1,z2,z3,z835,z4,z8]),(0,[z836,z2,z3,z4,z5,z8])],[(0,[z1,z2,z113,z4,z236,z8]),(0,[z1,z837,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z57])],[(0,[z1,z12,z2,z3,z291,z8]),(0,[z1,z3,z4,z5,z41,z717]),(0,[z1,z2,z3,z838,z5,z8]),(0,[z1,z839,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z840,z8]),(0,[z1,z2,z3,z4,z841,z8])],[(0,[z1,z2,z3,z842,z5,z8]),(1,[z2,z3,z759,z5,z8]),(0,[z1,z295,z2,z3,z5,z419]),(0,[z1,z2,z3,z4,z249,z20]),(0,[z1,z10,z3,z4,z154,z13])],[],[(0,[z1,z2,z3,z326,z5,z388]),(0,[z2,z3,z4,z5,z546,z20])],[(0,[z1,z2,z3,z843,z5,z8]),(0,[z1,z844,z2,z3,z4,z5]),(0,[z88,z2,z797,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z277]),(0,[z1,z2,z430,z4,z14,z8])],[(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z847,z2,z3,z4,z8]),(0,[z97,z2,z3,z76,z19,z8]),(0,[z1,z12,z2,z3,z848,z8]),(0,[z547,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z80,z5,z8]),(0,[z1,z2,z3,z849,z4,z8]),(0,[z1,z2,z3,z4,z850,z8]),(0,[z851,z2,z3,z4,z5,z8]),(0,[z1,z852,z3,z4,z5,z8]),(0,[z1,z2,z254,z3,z17,z4])],[(0,[z16,z2,z3,z4,z5,z6]),(0,[z1,z233,z2,z3,z4,z215]),(0,[z1,z2,z853,z4,z5,z8]),(0,[z1,z2,z3,z17,z4,z238])],[(0,[z1,z2,z113,z4,z5,z6]),(0,[z1,z2,z854,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z71,z2,z3,z4,z99]),(0,[z1,z2,z856,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z857]),(0,[z1,z2,z3,z858,z4,z8])],[(0,[z1,z2,z3,z4,z859,z5]),(0,[z1,z2,z3,z4,z5,z201]),(0,[z1,z2,z653,z4,z14,z8])],[(0,[z1,z2,z3,z375,z5,z6]),(0,[z1,z119,z3,z4,z191,z5]),(0,[z1,z383,z3,z4,z5,z15])],[(0,[z1,z2,z3,z4,z5,z106]),(0,[z1,z2,z3,z4,z5,z860])],[(0,[z1,z2,z3,z4,z861,z8]),(0,[z1,z2,z3,z4,z315,z8])],[(0,[z1,z456,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z862]),(0,[z252,z2,z3,z134,z5,z8]),(0,[z2,z3,z4,z5,z6,z357]),(0,[z1,z2,z3,z4,z8,z863]),(0,[z1,z2,z3,z864,z4,z8]),(0,[z1,z29,z2,z4,z5,z240])],[(0,[z1,z2,z3,z865,z4,z8]),(0,[z1,z2,z3,z4,z154,z15])],[(0,[z1,z866,z2,z3,z4,z8])]],
   [[(0,[z1,z12,z62,z2,z3,z8])],[(0,[z1,z12,z2,z3,z4,z867])],[(0,[z1,z2,z3,z868,z5,z8]),(0,[z88,z2,z115,z4,z5,z209]),(0,[z1,z2,z3,z5,z6,z869]),(0,[z1,z2,z3,z4,z20,z870])],[(0,[z1,z871,z2,z3,z4,z362]),(0,[z1,z2,z3,z4,z5,z872])],[(0,[z1,z873,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z874,z5]),(0,[z1,z12,z2,z3,z17,z8]),(0,[z1,z2,z3,z120,z86,z231])],[(0,[z98,z2,z3,z17,z134,z8]),(0,[z1,z2,z3,z4,z5,z875]),(0,[z52,z2,z3,z4,z35,z138]),(0,[z1,z331,z87,z4,z5,z8])],[(0,[z1,z2,z876,z3,z4,z8])],[(0,[z1,z2,z3,z473,z5,z8]),(0,[z1,z2,z3,z17,z4,z209]),(0,[z1,z71,z2,z3,z4,z118]),(0,[z1,z3,z4,z5,z877,z6]),(0,[z1,z12,z193,z10,z2,z3])],[(0,[z1,z878,z3,z4,z5,z8]),(0,[z2,z3,z134,z759,z5,z8]),(0,[z1,z2,z3,z4,z5,z879]),(0,[z2,z3,z4,z880,z5,z8]),(0,[z1,z193,z2,z3,z5,z177])],[(0,[z1,z2,z4,z881,z5,z8]),(0,[z1,z2,z3,z4,z882,z8]),(0,[z1,z2,z3,z4,z8,z883]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z1,z12,z140,z2,z3,z4])],[(0,[z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z137,z3,z4,z215]),(0,[z1,z2,z3,z4,z886,z8]),(0,[z1,z2,z189,z4,z5,z99])],[(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z109,z3,z4,z5,z147]),(0,[z1,z383,z3,z4,z5,z6]),(0,[z1,z804,z87,z4,z5,z8]),(0,[z1,z428,z2,z3,z34,z8]),(0,[z1,z2,z3,z4,z421,z99]),(0,[z1,z428,z2,z3,z5,z177])],[(0,[z1,z2,z3,z4,z5,z888]),(0,[z97,z2,z3,z19,z5,z6]),(0,[z225,z1,z3,z4,z34,z20])],[(0,[z1,z2,z3,z4,z889,z8]),(0,[z1,z816,z91,z3,z4,z5]),(0,[z1,z12,z193,z2,z3,z177])],[],[(0,[z890,z2,z3,z17,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z310,z277]),(0,[z891,z2,z3,z4,z5,z8]),(0,[z1,z892,z2,z3,z4,z5]),(0,[z1,z12,z2,z3,z86,z15])],[(0,[z1,z12,z2,z3,z375,z8]),(0,[z1,z893,z3,z4,z5,z8])],[(0,[z483,z1,z3,z4,z34,z8]),(0,[z1,z2,z894,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z6]),(0,[z1,z12,z808,z3,z4,z8])],[(0,[z1,z2,z3,z4,z5,z723]),(0,[z1,z606,z3,z4,z55,z8]),(0,[z1,z895,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z896,z8]),(0,[z1,z2,z3,z897,z5,z8])],[(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z12,z2,z3,z4,z138]),(0,[z1,z579,z87,z4,z5,z8])],[(0,[z1,z2,z3,z4,z898,z8]),(0,[z225,z1,z3,z4,z825,z8]),(0,[z465,z2,z3,z342,z4,z8])],[(0,[z1,z2,z899,z3,z4,z20]),(0,[z1,z2,z900,z4,z5,z8])],[(0,[z1,z2,z3,z17,z4,z118]),(0,[z1,z901,z2,z3,z4,z8]),(0,[z1,z12,z486,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z902]),(0,[z1,z12,z10,z3,z4,z13])],[(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z12,z2,z189,z4,z8])],[(0,[z94,z1,z12,z2,z3,z57])],[(0,[z1,z2,z337,z17,z4,z8]),(0,[z116,z2,z160,z4,z5,z126]),(0,[z1,z2,z3,z904,z4,z8]),(0,[z1,z2,z3,z326,z5,z20]),(0,[z1,z12,z2,z3,z66,z57])],[(0,[z1,z905,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z118,z15]),(0,[z1,z2,z3,z4,z26,z5])],[(0,[z1,z2,z3,z4,z906,z8]),(0,[z1,z2,z3,z4,z364,z8]),(0,[z1,z193,z2,z3,z249,z8])],[(0,[z79,z181,z3,z4,z5,z487]),(0,[z97,z12,z2,z3,z19,z8]),(0,[z1,z907,z2,z3,z4,z8]),(0,[z1,z2,z3,z5,z20,z404]),(0,[z1,z2,z3,z120,z5,z745])],[(0,[z1,z2,z3,z4,z908,z8]),(0,[z1,z2,z3,z4,z265,z277]),(0,[z1,z2,z3,z17,z4,z26])]],
   [[(0,[z1,z2,z3,z4,z8,z738]),(0,[z1,z2,z3,z4,z909,z8]),(0,[z1,z901,z2,z3,z8,z215])],[(0,[z1,z2,z3,z4,z236,z8]),(0,[z1,z405,z81,z4,z5,z8]),(0,[z1,z119,z3,z4,z5,z717])],[(0,[z1,z910,z2,z3,z473,z8]),(0,[z1,z139,z3,z151,z5,z8]),(0,[z1,z12,z2,z3,z65,z8]),(0,[z1,z2,z3,z5,z86,z159])],[(0,[z1,z12,z2,z3,z625,z8])],[(0,[z911,z1,z2,z3,z4,z20]),(0,[z1,z2,z912,z4,z5,z8]),(0,[z1,z913,z2,z3,z4,z8])],[(1,[z718,z3,z4,z5,z8])],[(0,[z116,z12,z2,z160,z4,z8]),(0,[z1,z2,z914,z17,z4,z8])],[(0,[z1,z2,z3,z80,z5,z487]),(0,[z1,z915,z2,z3,z4,z5]),(0,[z1,z2,z3,z17,z4,z916])],[],[(0,[z1,z2,z917,z4,z5,z8]),(0,[z1,z2,z3,z4,z918,z5])],[],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z375,z5,z126]),(0,[z21,z2,z3,z4,z135,z8])],[(0,[z1,z919,z2,z4,z5,z8]),(0,[z1,z2,z3,z920,z5,z8]),(0,[z1,z2,z3,z921,z4,z8]),(0,[z52,z2,z3,z342,z4,z8]),(0,[z1,z119,z479,z4,z5,z41]),(0,[z1,z119,z189,z4,z5,z41]),(0,[z1,z2,z3,z4,z285,z8]),(0,[z1,z12,z2,z3,z4,z922])],[(0,[z1,z2,z923,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z2,z3,z4,z743,z5,z8]),(0,[z225,z1,z3,z4,z34,z6]),(0,[z1,z3,z4,z825,z55,z8]),(0,[z757,z2,z3,z4,z5,z8])],[],[(0,[z116,z2,z160,z4,z203,z8]),(0,[z1,z925,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z926,z6])]],
   [[(0,[z1,z2,z3,z927,z4,z8]),(0,[z43,z12,z2,z3,z134,z8]),(0,[z662,z1,z3,z64,z5,z8]),(0,[z1,z2,z3,z928,z4,z5]),(0,[z1,z3,z4,z774,z5,z8])],[(0,[z391,z2,z3,z4,z5,z20]),(0,[z1,z12,z2,z3,z4,z238])],[(0,[z1,z2,z3,z4,z5,z929]),(0,[z1,z2,z3,z4,z930,z8]),(0,[z1,z10,z2,z3,z4,z61]),(1,[z1,z2,z3,z734,z8]),(0,[z1,z12,z2,z3,z444,z8])],[(0,[z1,z2,z931,z4,z5,z8])],[(0,[z12,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z932,z8])],[],[(0,[z1,z2,z3,z4,z933,z8]),(0,[z1,z2,z934,z4,z5,z8])],[(0,[z1,z251,z2,z4,z5,z414]),(0,[z1,z12,z2,z3,z66,z20]),(0,[z1,z2,z30,z575,z4,z5]),(0,[z1,z29,z2,z4,z5,z167]),(0,[z1,z428,z2,z30,z3,z5])],[(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z3,z4,z296,z8]),(0,[z1,z428,z2,z3,z32,z15])],[(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z2,z3,z4,z5,z937]),(0,[z1,z31,z2,z3,z4,z406]),(0,[z1,z2,z45,z4,z14,z8]),(0,[z1,z2,z30,z4,z5,z46]),(0,[z1,z428,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z938,z8])],[(0,[z1,z12,z2,z113,z4,z8]),(0,[z631,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z221,z4,z20]),(0,[z1,z2,z3,z263,z5,z86])],[(0,[z36,z1,z2,z26,z27,z5]),(0,[z1,z2,z3,z4,z5,z939]),(0,[z1,z12,z193,z2,z3,z8]),(0,[z94,z1,z428,z2,z3,z8])],[(0,[z1,z2,z3,z326,z5,z6]),(0,[z1,z91,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z8,z231]),(0,[z1,z2,z3,z940,z4,z8])],[(0,[z1,z2,z3,z4,z941,z8]),(0,[z1,z2,z3,z17,z326,z8]),(0,[z1,z2,z3,z942,z5,z8])],[(0,[z0,z245,z3,z4,z5,z8]),(0,[z718,z181,z3,z4,z5,z8])],[(0,[z1,z2,z3,z375,z203,z8]),(0,[z98,z12,z2,z3,z134,z8]),(0,[z1,z2,z3,z4,z5,z786])]],
   [[(0,[z1,z2,z3,z943,z4,z5]),(0,[z1,z2,z3,z944,z5,z8]),(0,[z945,z1,z2,z3,z4,z8])],[(0,[z1,z2,z3,z17,z80,z8]),(0,[z79,z181,z3,z4,z325,z8]),(0,[z1,z12,z2,z3,z4,z209]),(0,[z1,z2,z3,z946,z4,z8]),(0,[z1,z947,z2,z3,z4,z8])],[(0,[z16,z2,z3,z4,z135,z8]),(0,[z1,z119,z2,z3,z4,z215]),(1,[z1,z3,z4,z5,z717]),(0,[z1,z12,z2,z3,z434,z8]),(0,[z1,z12,z2,z3,z4,z948]),(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z3,z4,z99,z731])],[(0,[z1,z31,z2,z3,z4,z215]),(0,[z1,z2,z950,z4,z5,z8])],[(0,[z1,z2,z3,z951,z5,z8]),(0,[z1,z2,z3,z17,z526,z8]),(0,[z1,z2,z3,z4,z131,z6]),(0,[z1,z952,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z249,z15])],[(0,[z1,z2,z953,z3,z4,z5])],[(0,[z2,z3,z797,z4,z5,z8]),(0,[z2,z3,z342,z4,z5,z6]),(0,[z196,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z86,z775,z8])],[(0,[z1,z2,z3,z85,z5,z8]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z1,z2,z4,z795,z14,z8])],[(0,[z1,z2,z3,z4,z955,z5])],[(0,[z1,z185,z2,z3,z4,z8]),(0,[z1,z12,z2,z3,z7,z8]),(0,[z1,z2,z3,z956,z5,z8]),(0,[z1,z139,z3,z166,z5,z8])],[(0,[z1,z2,z3,z80,z325,z8])],[(0,[z1,z957,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z138,z15]),(0,[z1,z2,z3,z4,z272,z15]),(0,[z1,z12,z29,z2,z4,z167])],[(0,[z245,z718,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z186,z8]),(0,[z192,z2,z3,z17,z4,z6]),(0,[z1,z3,z774,z64,z5,z8])],[(0,[z1,z2,z3,z4,z958,z8]),(0,[z1,z959,z3,z4,z5,z8]),(0,[z1,z110,z4,z64,z5,z8])],[(0,[z1,z2,z3,z960,z5,z8]),(0,[z1,z2,z3,z76,z326,z8]),(0,[z1,z2,z3,z4,z5,z961])],[(0,[z1,z2,z3,z4,z325,z106]),(0,[z1,z2,z3,z962,z5,z8]),(0,[z1,z451,z2,z3,z17,z8]),(0,[z1,z11,z542,z4,z5,z8]),(0,[z1,z2,z3,z963,z5,z8]),(0,[z1,z2,z3,z4,z8,z964])]],
   [[(0,[z21,z1,z2,z3,z4,z177]),(0,[z1,z2,z3,z4,z965,z8]),(0,[z1,z10,z3,z4,z5,z13]),(0,[z1,z193,z383,z3,z4,z5]),(0,[z1,z2,z3,z17,z4,z966])],[(0,[z1,z12,z2,z3,z4,z118]),(0,[z1,z2,z3,z363,z85,z8]),(0,[z1,z967,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z968])],[(0,[z1,z2,z3,z4,z236,z487]),(0,[z1,z2,z3,z4,z8,z969]),(0,[z1,z2,z3,z120,z17,z86])],[(0,[z1,z2,z45,z577,z4,z8])],[(0,[z88,z2,z115,z4,z5,z8]),(0,[z1,z2,z3,z4,z970,z8]),(0,[z1,z12,z2,z3,z128,z8]),(0,[z24,z1,z3,z774,z5,z8])],[(0,[z1,z12,z109,z3,z4,z8]),(0,[z1,z2,z25,z4,z5,z20]),(1,[z1,z901,z2,z3,z8]),(0,[z1,z2,z3,z4,z5,z814]),(0,[z1,z12,z2,z3,z120,z86]),(0,[z1,z12,z2,z3,z676,z8])],[(0,[z1,z2,z3,z141,z4,z26])],[(0,[z1,z486,z3,z17,z4,z8]),(0,[z1,z12,z2,z3,z8,z231]),(0,[z1,z193,z2,z3,z5,z168])],[(0,[z1,z2,z3,z17,z4,z321]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z12,z2,z3,z66,z6]),(0,[z1,z2,z3,z4,z215,z419])],[(0,[z1,z972,z3,z4,z5,z8]),(0,[z1,z739,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z26]),(0,[z1,z12,z2,z3,z4,z350]),(0,[z1,z2,z3,z4,z32,z177])],[(0,[z1,z454,z2,z4,z5,z167])],[(0,[z1,z689,z87,z4,z5,z8]),(0,[z116,z2,z160,z17,z4,z8]),(0,[z1,z2,z3,z221,z4,z6]),(0,[z1,z12,z2,z3,z60,z8]),(0,[z1,z2,z189,z4,z5,z8]),(0,[z1,z2,z479,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z10,z479,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z974])],[(0,[z1,z2,z3,z4,z5,z975]),(0,[z1,z2,z3,z4,z5,z126]),(0,[z1,z522,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z976,z8]),(0,[z1,z2,z3,z4,z421,z8]),(0,[z1,z2,z3,z4,z99,z550])],[(0,[z679,z2,z3,z134,z5,z8]),(0,[z1,z91,z3,z4,z5,z6]),(0,[z1,z2,z82,z3,z4,z20]),(0,[z1,z12,z193,z119,z2,z3])],[(0,[z1,z2,z3,z4,z325,z20]),(0,[z1,z977,z2,z3,z4,z5]),(0,[z1,z2,z3,z759,z5,z8]),(0,[z1,z12,z2,z479,z4,z8])],[(0,[z1,z978,z2,z3,z4,z5]),(0,[z1,z2,z3,z18,z8,z231])]],
   [[(0,[z662,z1,z12,z2,z3,z8]),(0,[z1,z2,z3,z17,z18,z8])],[(0,[z1,z2,z3,z4,z5,z827])],[(0,[z1,z2,z30,z3,z4,z215]),(0,[z1,z979,z2,z3,z4,z8]),(0,[z1,z2,z776,z110,z4,z5]),(0,[z1,z2,z3,z17,z4,z350]),(0,[z89,z661,z2,z3,z4,z8])],[(0,[z1,z12,z2,z3,z530,z8]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z4,z981,z8])],[(0,[z1,z982,z2,z3,z4,z209]),(0,[z1,z2,z3,z4,z8,z983]),(0,[z2,z3,z4,z984,z5,z8]),(0,[z1,z2,z3,z17,z4,z985])],[(0,[z1,z986,z2,z3,z375,z8]),(0,[z1,z2,z3,z747,z4,z20]),(0,[z1,z3,z4,z5,z717,z8]),(0,[z1,z12,z2,z3,z546,z8])],[(0,[z1,z2,z337,z313,z5,z8]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z98,z2,z3,z134,z310,z8]),(0,[z1,z2,z3,z4,z748,z20]),(0,[z1,z2,z3,z4,z131,z20]),(0,[z1,z53,z3,z4,z5,z8]),(0,[z1,z172,z804,z4,z5,z8]),(0,[z1,z140,z2,z82,z3,z4]),(0,[z1,z2,z3,z4,z988,z8]),(0,[z989,z12,z2,z3,z4,z8]),(0,[z1,z2,z990,z17,z4,z8]),(1,[z1,z2,z3,z5,z745])],[(0,[z1,z2,z3,z4,z991,z8]),(0,[z1,z2,z110,z4,z5,z20]),(0,[z1,z2,z3,z4,z420,z992])],[(0,[z1,z2,z993,z4,z5,z8]),(0,[z79,z718,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z994])],[(0,[z1,z2,z113,z17,z4,z8]),(0,[z1,z2,z3,z995,z4,z5]),(0,[z662,z1,z2,z27,z5,z8])],[(0,[z1,z2,z3,z4,z996,z5])],[(0,[z1,z2,z3,z4,z5,z997]),(0,[z1,z998,z3,z4,z5,z8]),(0,[z1,z999,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1000])],[(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z12,z2,z3,z650,z8]),(0,[z1,z428,z2,z3,z14,z8]),(0,[z1,z2,z3,z4,z190,z8])],[(0,[z1,z1002,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1003,z5]),(0,[z1,z2,z3,z4,z215,z168]),(0,[z1,z119,z3,z17,z4,z41]),(0,[z1,z12,z2,z3,z4,z1004])],[(0,[z0,z245,z3,z4,z5,z320]),(0,[z1,z2,z3,z1005,z4,z8]),(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1,z2,z3,z17,z4,z177]),(0,[z1,z2,z3,z4,z57,z177])],[(0,[z1,z2,z3,z4,z5,z277]),(0,[z1,z251,z2,z3,z4,z215])]],
   [[(0,[z1,z2,z3,z4,z1007,z8]),(0,[z1,z2,z3,z4,z203,z8]),(0,[z1,z2,z3,z1008,z4,z5]),(0,[z1,z2,z3,z4,z1009,z8]),(0,[z24,z1,z3,z17,z64,z8])],[(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z3,z76,z18,z8]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z2,z4,z5,z716,z46])],[(0,[z1,z12,z2,z3,z4,z1012]),(0,[z1,z2,z3,z4,z769,z20]),(0,[z1,z2,z3,z4,z1013,z8])],[(0,[z2,z3,z4,z5,z724,z6]),(0,[z1,z140,z3,z87,z4,z5]),(0,[z1,z2,z3,z5,z8,z745])],[(0,[z1,z2,z3,z4,z5,z1014]),(0,[z21,z2,z3,z4,z135,z210]),(0,[z1,z2,z1015,z3,z4,z8]),(0,[z1,z2,z1016,z3,z4,z5])],[(0,[z98,z2,z3,z134,z265,z8])],[(0,[z1,z2,z3,z4,z5,z1017]),(0,[z1,z2,z3,z1018,z5,z8]),(0,[z1,z2,z25,z4,z5,z6]),(0,[z1,z243,z2,z3,z5,z168]),(0,[z1019,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z12,z2,z3,z326,z8]),(0,[z1,z2,z3,z4,z777,z20])],[],[(0,[z1,z2,z3,z4,z1021,z8]),(0,[z1,z2,z3,z4,z5,z1022]),(0,[z1,z2,z3,z20,z711,z215]),(0,[z1,z2,z3,z4,z1023,z8]),(0,[z1,z2,z3,z439,z4,z26])],[(0,[z1,z1024,z2,z3,z4,z8]),(0,[z1,z12,z701,z2,z3,z8])],[(0,[z1,z12,z2,z3,z80,z8]),(0,[z1,z1025,z3,z4,z5,z8]),(0,[z1,z1026,z2,z3,z4,z5]),(0,[z1,z12,z1027,z3,z4,z8])],[(0,[z1,z2,z3,z85,z8,z15]),(0,[z1,z824,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z8,z711]),(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z4,z1028,z8]),(0,[z1,z383,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z1029,z5]),(0,[z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1030])],[(0,[z1,z2,z1031,z4,z5,z8]),(0,[z1,z2,z82,z3,z4,z6]),(0,[z1,z454,z2,z3,z17,z4]),(0,[z1,z1032,z3,z4,z5,z8]),(0,[z1,z12,z2,z1033,z4,z8])],[(0,[z1,z2,z3,z4,z325,z6]),(0,[z1,z2,z3,z1034,z4,z8]),(0,[z1,z2,z3,z4,z5,z1035]),(0,[z21,z1,z428,z2,z3,z8]),(0,[z1,z1036,z2,z3,z4,z8]),(0,[z1,z12,z2,z3,z342,z8])]],
   [[(0,[z1,z2,z3,z1037,z5,z8]),(0,[z1,z109,z3,z473,z5,z8]),(0,[z1,z12,z2,z3,z604,z8]),(0,[z1,z2,z3,z1038,z5,z8]),(0,[z1,z2,z3,z228,z17,z4]),(0,[z1,z2,z3,z4,z1039,z8]),(0,[z1,z2,z3,z4,z5,z1040])],[(0,[z1,z456,z3,z4,z5,z147]),(0,[z1,z2,z3,z453,z5,z570]),(0,[z1,z12,z243,z2,z3,z8]),(0,[z1,z12,z2,z37,z207,z8]),(0,[z1,z193,z2,z3,z249,z168])],[(0,[z1,z2,z3,z4,z5,z1041]),(0,[z1,z12,z1042,z3,z4,z8])],[(0,[z1,z2,z3,z4,z5,z1043]),(0,[z1,z109,z3,z4,z5,z20]),(0,[z1,z2,z3,z1044,z4,z8]),(0,[z1,z202,z2,z3,z4,z99])],[(0,[z1,z2,z3,z4,z5,z1045])],[(0,[z1,z2,z3,z4,z5,z1046]),(0,[z1,z193,z2,z3,z5,z419]),(0,[z1,z2,z3,z4,z1047,z8]),(0,[z1,z2,z3,z17,z704,z8]),(0,[z1,z10,z615,z3,z4,z5])],[(0,[z192,z12,z2,z3,z4,z6]),(0,[z1,z91,z4,z27,z5,z8])],[(0,[z1,z2,z3,z774,z5,z8]),(0,[z1,z29,z2,z3,z4,z131])],[(0,[z1,z2,z110,z4,z5,z6]),(0,[z1,z2,z3,z17,z4,z72])],[(0,[z1,z2,z3,z1048,z4,z5]),(0,[z52,z2,z3,z4,z8,z357]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z3,z4,z1050,z8]),(0,[z1,z251,z2,z4,z5,z167]),(0,[z1,z2,z3,z1051,z4,z8]),(0,[z1,z193,z2,z189,z4,z5]),(0,[z94,z1,z2,z3,z4,z550])],[],[(0,[z1,z2,z3,z473,z5,z147])],[(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z71,z2,z3,z4,z8]),(0,[z1,z2,z3,z1053,z5,z8])],[(0,[z1,z2,z3,z4,z1054,z8]),(0,[z1,z29,z2,z4,z5,z23])],[(0,[z1,z599,z87,z4,z5,z8]),(0,[z1,z2,z3,z4,z1055,z8]),(0,[z1,z12,z2,z3,z376,z8]),(0,[z1,z2,z758,z4,z5,z6])],[(0,[z1,z1056,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z138]),(0,[z474,z2,z3,z4,z5,z6]),(0,[z36,z1,z12,z2,z27,z8])]],
   [[(0,[z1,z2,z3,z4,z154,z238])],[(0,[z1,z2,z3,z4,z1057,z8]),(1,[z1,z3,z4,z825,z8]),(1,[z1,z2,z3,z4,z731])],[(0,[z1,z718,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z12,z2,z3,z4,z321]),(0,[z1,z295,z12,z2,z3,z8])],[(0,[z589,z2,z3,z4,z5,z6]),(0,[z1,z71,z2,z3,z4,z215])],[(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1,z2,z3,z4,z731,z8])],[],[(0,[z622,z181,z3,z4,z5,z8]),(0,[z1,z109,z3,z4,z364,z8]),(0,[z1,z2,z403,z3,z4,z177]),(0,[z1,z31,z2,z3,z4,z57]),(0,[z1,z202,z2,z3,z120,z86])],[(0,[z1,z2,z3,z1060,z5,z8]),(0,[z79,z181,z3,z4,z5,z106]),(0,[z1,z2,z3,z4,z1061,z8])],[(0,[z1,z2,z3,z4,z5,z1062]),(0,[z1,z2,z3,z4,z778,z6]),(0,[z1,z81,z804,z4,z5,z8]),(0,[z1,z2,z3,z4,z1063,z8])],[(0,[z1,z12,z2,z3,z19,z177]),(0,[z1,z2,z3,z5,z8,z1064])],[(0,[z1,z1065,z2,z3,z80,z8]),(0,[z1,z2,z3,z1066,z4,z8]),(0,[z1,z11,z81,z4,z5,z8]),(0,[z1,z454,z486,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z2,z3,z1068,z4,z8]),(0,[z1,z333,z3,z4,z5,z13]),(0,[z1,z172,z87,z4,z5,z20]),(0,[z1,z2,z30,z4,z5,z368])],[(0,[z1,z2,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z1069,z8]),(0,[z1,z2,z3,z4,z1070,z5]),(0,[z24,z1,z140,z3,z64,z5]),(0,[z1,z2,z3,z4,z533,z15])],[(0,[z1,z494,z3,z166,z5,z8]),(0,[z395,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z8]),(0,[z1,z428,z2,z3,z5,z168])],[(0,[z1,z12,z2,z3,z4,z730]),(0,[z1,z2,z3,z4,z420,z8])],[(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z12,z193,z2,z3,z168]),(0,[z1,z2,z3,z5,z86,z745])]],
   [[(0,[z1,z2,z3,z80,z5,z106]),(0,[z1,z2,z3,z326,z5,z138]),(0,[z1,z2,z804,z4,z5,z8]),(0,[z1,z2,z3,z4,z125,z15]),(0,[z1,z12,z2,z3,z4,z1072])],[(0,[z1,z2,z3,z4,z364,z147]),(0,[z1,z2,z3,z4,z1073,z8]),(0,[z1,z1074,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z154,z99]),(0,[z1,z2,z3,z4,z1075,z8]),(0,[z1,z12,z2,z3,z17,z57])],[(0,[z1,z2,z3,z1076,z5,z8])],[(0,[z1,z2,z3,z1077,z4,z5]),(0,[z2,z515,z3,z4,z5,z20])],[(0,[z1,z109,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z2,z3,z4,z1079,z8])],[(0,[z1,z2,z3,z4,z5,z1080]),(0,[z1,z1081,z3,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z1082]),(0,[z1,z356,z2,z3,z4,z177])],[(0,[z79,z181,z3,z4,z5,z20])],[(0,[z1,z2,z3,z4,z8,z870]),(0,[z1,z2,z3,z4,z5,z922])],[(0,[z1,z1083,z3,z4,z5,z8]),(0,[z52,z1,z2,z3,z4,z177]),(0,[z1,z893,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z544,z8]),(0,[z1,z12,z2,z3,z4,z177])],[(0,[z1,z2,z1084,z4,z5,z8]),(0,[z1,z12,z2,z3,z536,z8]),(0,[z1,z1085,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z1086,z8]),(0,[z1,z12,z428,z2,z3,z177]),(0,[z1,z2,z3,z4,z966,z5])],[(0,[z1,z2,z4,z5,z1087,z8]),(0,[z466,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1088])],[(0,[z1,z2,z3,z4,z5,z707])],[(0,[z1,z2,z3,z4,z1089,z8]),(0,[z1,z256,z2,z4,z5,z23]),(0,[z1,z2,z3,z4,z5,z238]),(0,[z1,z10,z3,z4,z131,z13]),(0,[z1,z486,z4,z5,z167,z8]),(0,[z1,z12,z2,z3,z95,z8])],[(0,[z1,z2,z3,z76,z4,z8]),(0,[z1,z901,z2,z3,z5,z8])],[(0,[z1,z806,z3,z4,z5,z6]),(0,[z225,z1,z3,z4,z34,z238])],[(0,[z1,z2,z3,z80,z5,z20]),(0,[z1,z2,z3,z4,z850,z20]),(0,[z1,z2,z3,z849,z4,z20])]],
   [[],[(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z1091,z2,z3,z4,z8])],[(0,[z1,z10,z3,z4,z5,z590]),(0,[z1,z428,z2,z3,z99,z8])],[(0,[z1,z456,z3,z473,z5,z8]),(0,[z1,z3,z4,z5,z8,z1092])],[(0,[z1,z2,z113,z313,z5,z8]),(0,[z12,z2,z3,z134,z19,z8]),(0,[z1,z2,z3,z4,z303,z5]),(0,[z1,z2,z3,z4,z171,z177]),(0,[z1,z2,z3,z18,z734,z8]),(0,[z1,z31,z2,z3,z4,z731])],[(0,[z1,z2,z3,z4,z315,z20]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z140,z2,z3,z17,z4]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z1,z2,z3,z1095,z4,z8]),(0,[z1,z2,z3,z1096,z4,z8]),(0,[z1,z2,z3,z17,z734,z8])],[(0,[z1,z456,z3,z4,z5,z20]),(0,[z12,z661,z2,z3,z134,z8]),(0,[z1,z892,z2,z110,z4,z5])],[(0,[z2,z3,z4,z5,z426,z20]),(0,[z1,z2,z1097,z3,z4,z8]),(0,[z1,z2,z3,z4,z1098,z8])],[(0,[z1,z2,z1099,z4,z5,z8]),(0,[z1,z2,z3,z4,z1100,z8])],[(0,[z1,z2,z3,z1101,z5,z8])],[(0,[z674,z2,z3,z4,z5,z6]),(0,[z1,z377,z81,z4,z5,z8]),(0,[z1,z12,z2,z3,z173,z8])],[(0,[z501,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z209]),(0,[z1,z172,z87,z4,z5,z6])],[(0,[z1,z12,z2,z3,z17,z20]),(0,[z1,z1102,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z948])],[(0,[z1,z2,z3,z4,z5,z1103]),(0,[z1,z12,z2,z3,z8,z93])],[(0,[z1,z2,z3,z4,z5,z1104]),(0,[z1,z2,z1105,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z473,z5,z20]),(0,[z1,z2,z3,z4,z199,z15]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z4,z5,z1107])],[(0,[z1,z12,z2,z3,z4,z459]),(0,[z1,z2,z3,z4,z1108,z8]),(0,[z1,z226,z399,z3,z4,z8])],[(0,[z1,z2,z3,z4,z727,z8]),(0,[z1,z54,z3,z4,z825,z8]),(0,[z1,z12,z2,z3,z4,z72]),(0,[z1109,z12,z2,z3,z4,z8]),(0,[z1110,z12,z2,z3,z4,z8])],[(0,[z1,z2,z3,z1111,z4,z8]),(0,[z1,z12,z2,z3,z363,z8]),(0,[z1,z1112,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1113])],[(0,[z1,z2,z3,z141,z19,z8]),(0,[z1,z2,z3,z4,z8,z215]),(0,[z1,z446,z3,z4,z5,z77]),(0,[z1,z2,z188,z4,z5,z46]),(0,[z1,z2,z189,z120,z4,z5]),(0,[z890,z2,z3,z4,z5,z8])],[(0,[z98,z2,z3,z134,z5,z8])],[(0,[z0,z245,z3,z4,z5,z362])],[(0,[z1,z2,z3,z4,z5,z1114]),(0,[z79,z181,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z19,z8]),(0,[z1,z2,z3,z4,z5,z1115]),(0,[z52,z2,z3,z4,z35,z8]),(0,[z1,z2,z3,z1116,z5,z8]),(0,[z1,z12,z2,z3,z228,z4])],[(0,[z36,z1,z2,z27,z5,z8])],[(0,[z1,z456,z3,z4,z364,z8]),(0,[z1,z2,z3,z4,z5,z1117])],[(0,[z1,z2,z3,z1118,z4,z8]),(0,[z1,z2,z3,z17,z4,z459]),(0,[z1,z2,z3,z4,z20,z756]),(0,[z1,z2,z3,z1119,z5,z8]),(0,[z1,z2,z3,z17,z4,z1120])],[(0,[z1,z2,z3,z4,z236,z106]),(0,[z1,z333,z3,z4,z5,z329]),(0,[z1,z2,z3,z4,z5,z1121])],[(0,[z1,z2,z3,z17,z4,z320]),(0,[z1,z2,z3,z4,z5,z118]),(0,[z389,z2,z3,z4,z5,z6]),(0,[z1,z454,z2,z30,z4,z5]),(0,[z1,z2,z3,z228,z4,z896]),(0,[z1,z2,z1122,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z1123]),(0,[z1,z2,z3,z4,z5,z968])],[(0,[z1,z2,z3,z17,z4,z487])],[(0,[z1,z2,z3,z17,z4,z303]),(0,[z1,z1124,z2,z3,z4,z8]),(0,[z1,z91,z3,z17,z4,z8])],[(0,[z1,z2,z3,z4,z8,z829])]],
   [[(0,[z1,z2,z337,z4,z5,z8]),(0,[z1,z2,z3,z80,z5,z6]),(0,[z1,z901,z2,z3,z4,z20]),(0,[z1,z2,z1125,z4,z5,z8])],[(0,[z1,z2,z3,z4,z32,z215]),(0,[z1,z2,z3,z4,z1126,z8]),(0,[z1,z428,z2,z3,z17,z8])],[(0,[z1,z2,z3,z4,z976,z20]),(0,[z1,z2,z254,z87,z4,z5]),(0,[z1,z2,z1127,z4,z5,z8])],[(0,[z1,z1128,z3,z4,z5,z8]),(0,[z1,z2,z3,z473,z364,z8]),(0,[z24,z1,z3,z64,z5,z8]),(0,[z1,z2,z3,z141,z4,z8]),(0,[z1,z2,z3,z5,z734,z8])],[(0,[z1,z2,z3,z4,z734,z8])],[(0,[z79,z181,z3,z80,z5,z8]),(0,[z1,z109,z3,z4,z5,z126]),(0,[z1,z2,z3,z835,z473,z8]),(0,[z1,z905,z2,z3,z4,z20])],[(0,[z1,z12,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z364,z20]),(0,[z1,z2,z3,z4,z315,z6]),(0,[z1,z2,z3,z4,z916,z5])],[(0,[z1,z456,z3,z4,z5,z6]),(0,[z52,z1,z428,z2,z3,z8]),(0,[z1,z12,z428,z2,z3,z8])],[(0,[z1,z2,z3,z4,z5,z1129]),(0,[z1,z11,z475,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1130]),(0,[z52,z2,z3,z326,z35,z8]),(0,[z1,z2,z3,z85,z5,z388]),(0,[z1,z2,z3,z120,z5,z570]),(0,[z1,z2,z3,z4,z536,z215]),(0,[z1,z10,z3,z4,z5,z70]),(0,[z1,z2,z3,z4,z1131,z8]),(0,[z1,z12,z193,z2,z3,z57]),(0,[z1,z2,z3,z4,z1132,z8])],[(0,[z1,z2,z3,z4,z1133,z8]),(0,[z1,z2,z3,z228,z4,z1134]),(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z3,z5,z8,z1136]),(0,[z1,z2,z3,z4,z1137,z8]),(0,[z1,z12,z2,z3,z4,z1138])],[(0,[z1,z2,z3,z4,z236,z20]),(0,[z1,z2,z1139,z4,z5,z8]),(0,[z1,z2,z1140,z4,z5,z8]),(0,[z1,z2,z3,z249,z86,z8])],[(0,[z1,z2,z914,z4,z5,z8])],[],[(0,[z1,z2,z3,z1141,z5,z8]),(0,[z1,z2,z3,z4,z5,z1142]),(0,[z1,z2,z3,z4,z1143,z5]),(0,[z1,z12,z2,z3,z134,z177]),(0,[z1,z12,z2,z3,z570,z8]),(0,[z1,z454,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z1144,z8]),(0,[z1,z2,z3,z1145,z4,z8])],[(0,[z1,z2,z3,z4,z5,z1146]),(0,[z1,z12,z2,z3,z17,z6])],[(0,[z116,z2,z160,z375,z5,z8]),(0,[z1,z119,z3,z4,z5,z41]),(0,[z1,z119,z486,z3,z4,z5]),(0,[z1,z2,z3,z4,z420,z708])]],
   [[(0,[z1,z185,z2,z3,z4,z6]),(0,[z1,z2,z1147,z4,z5,z8]),(0,[z1,z2,z3,z753,z5,z8]),(0,[z1,z383,z3,z4,z5,z99])],[(0,[z1,z2,z3,z4,z1148,z8]),(0,[z79,z12,z181,z3,z4,z8]),(0,[z1,z2,z3,z473,z5,z6]),(0,[z989,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1149]),(0,[z1,z2,z30,z4,z5,z598])],[(0,[z1,z2,z3,z4,z190,z20]),(0,[z1,z2,z3,z5,z745,z168])],[(0,[z1,z2,z3,z1150,z4,z8]),(0,[z1,z428,z119,z2,z3,z5])],[(0,[z1,z2,z3,z1151,z80,z8]),(0,[z21,z2,z3,z4,z135,z20]),(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z522,z3,z4,z5,z232]),(0,[z1,z2,z3,z1005,z4,z20]),(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z31,z2,z3,z4,z201])],[(0,[z1,z2,z3,z17,z4,z210]),(0,[z1,z2,z3,z4,z285,z20])],[(0,[z619,z2,z3,z4,z5,z6]),(0,[z24,z1,z12,z3,z64,z8])],[(0,[z1,z2,z3,z313,z5,z8]),(0,[z1153,z1,z2,z3,z4,z8]),(0,[z1,z986,z2,z3,z4,z8]),(0,[z517,z2,z3,z4,z5,z20]),(0,[z1,z2,z25,z17,z4,z8]),(0,[z1,z139,z3,z17,z166,z8]),(0,[z1,z2,z3,z4,z249,z99])],[(0,[z1,z2,z1154,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z12,z193,z29,z2,z3]),(0,[z1,z2,z3,z490,z4,z412]),(0,[z1,z2,z3,z17,z8,z404])],[(0,[z1,z109,z3,z4,z203,z8]),(0,[z1,z389,z87,z4,z5,z8]),(0,[z1,z2,z3,z17,z263,z8])],[(0,[z622,z2,z160,z4,z5,z8])],[(0,[z2,z3,z4,z5,z670,z20])],[(0,[z1,z2,z3,z4,z265,z459]),(1,[z2,z3,z4,z743,z8])],[(0,[z88,z2,z115,z4,z5,z133]),(0,[z1,z2,z3,z4,z5,z1012]),(0,[z1,z2,z3,z4,z740,z8])],[(0,[z97,z2,z3,z19,z5,z321])],[(0,[z1,z2,z3,z1155,z4,z5]),(0,[z1,z2,z3,z4,z933,z20]),(0,[z1,z3,z4,z34,z825,z8]),(0,[z1,z12,z2,z3,z734,z8]),(0,[z1,z193,z2,z3,z17,z168])]],
   [[(0,[z1,z2,z3,z1156,z5,z8]),(1,[z1,z3,z774,z5,z8]),(0,[z1,z54,z3,z4,z55,z8])],[(0,[z1,z528,z2,z3,z4,z406]),(0,[z1,z2,z3,z4,z296,z20]),(0,[z1,z2,z3,z4,z1157,z8]),(0,[z1,z2,z3,z1158,z4,z8]),(0,[z1,z12,z2,z1159,z4,z8])],[(0,[z1,z2,z3,z17,z4,z133]),(0,[z1,z2,z3,z4,z310,z8]),(0,[z1,z2,z45,z4,z14,z20]),(0,[z1,z428,z2,z3,z5,z20]),(0,[z1,z2,z3,z4,z5,z1160]),(0,[z1,z2,z3,z4,z154,z8]),(0,[z1,z2,z3,z4,z238,z15]),(0,[z1,z2,z3,z4,z5,z1161])],[(0,[z98,z2,z3,z134,z5,z459]),(0,[z257,z2,z3,z4,z5,z6]),(0,[z24,z1,z3,z303,z64,z5])],[(0,[z1,z2,z3,z4,z203,z147]),(0,[z1,z2,z3,z1162,z4,z8]),(0,[z21,z661,z2,z3,z4,z8]),(0,[z1,z2,z4,z5,z6,z817]),(0,[z1,z12,z193,z2,z3,z20]),(0,[z1,z139,z3,z166,z315,z8])],[(0,[z1,z1065,z2,z3,z4,z8]),(0,[z1,z2,z3,z1163,z375,z8]),(0,[z1,z2,z3,z4,z5,z1164]),(0,[z1,z2,z3,z4,z34,z177]),(0,[z1,z2,z3,z4,z5,z1165])],[(0,[z1,z2,z3,z1166,z5,z8]),(0,[z1,z2,z1167,z4,z5,z8]),(0,[z1,z2,z3,z439,z4,z8])],[(0,[z0,z245,z3,z4,z5,z20]),(0,[z1,z910,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z364,z6]),(0,[z1,z338,z87,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1168])],[(0,[z1,z2,z3,z4,z5,z1169]),(0,[z1,z802,z2,z3,z5,z8]),(0,[z1,z12,z2,z3,z392,z8])],[(0,[z1,z2,z3,z1170,z5,z8]),(0,[z1,z982,z2,z3,z4,z8]),(0,[z43,z2,z3,z134,z5,z8]),(0,[z1,z2,z1171,z3,z4,z5]),(0,[z1,z2,z110,z17,z4,z8]),(0,[z36,z1,z91,z27,z5,z8]),(0,[z1,z1172,z2,z3,z4,z8])],[(0,[z1,z2,z3,z4,z5,z1173]),(0,[z1,z2,z3,z4,z1174,z8]),(0,[z282,z2,z3,z4,z135,z8]),(0,[z1,z12,z2,z3,z4,z1175]),(0,[z1,z1042,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1176])],[(0,[z1,z2,z3,z4,z236,z6]),(0,[z1,z31,z2,z3,z85,z8]),(0,[z1,z428,z2,z3,z55,z8])],[],[(0,[z1,z2,z3,z4,z1177,z8]),(0,[z1,z12,z2,z25,z4,z8]),(0,[z1,z2,z3,z4,z5,z1178]),(0,[z1,z2,z3,z5,z86,z177])],[(0,[z1,z1179,z2,z3,z5,z8])],[(0,[z1,z2,z3,z8,z711,z215]),(0,[z1,z2,z3,z4,z5,z1180]),(0,[z1181,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z32,z731])]],
   [[(0,[z1,z2,z3,z17,z313,z8]),(0,[z79,z181,z3,z4,z236,z8]),(0,[z1,z2,z3,z4,z5,z1182]),(0,[z1,z2,z3,z85,z5,z20]),(0,[z1,z119,z2,z3,z4,z61])],[(0,[z1,z2,z337,z4,z5,z487]),(0,[z1,z2,z3,z4,z265,z8]),(0,[z192,z2,z3,z4,z5,z6]),(0,[z1,z1183,z2,z3,z4,z8]),(0,[z1,z29,z2,z479,z4,z5])],[(0,[z1,z1184,z3,z4,z5,z8]),(0,[z1,z185,z2,z3,z4,z20]),(0,[z1,z2,z3,z4,z5,z1185]),(0,[z1,z139,z3,z166,z5,z20])],[(0,[z1,z2,z818,z4,z5,z8]),(0,[z1,z1186,z3,z4,z5,z8]),(0,[z1,z2,z1187,z4,z5,z8]),(0,[z1,z2,z3,z4,z190,z6]),(0,[z1,z172,z228,z87,z4,z5])],[(0,[z1,z2,z3,z4,z366,z1188]),(0,[z1,z2,z1189,z3,z4,z8])],[(0,[z1,z2,z3,z4,z779,z8]),(0,[z21,z2,z3,z4,z135,z6]),(0,[z1,z1190,z3,z4,z5,z8])],[(0,[z1191,z1,z2,z3,z5,z8]),(0,[z1,z12,z2,z3,z4,z320]),(0,[z477,z2,z3,z19,z5,z8]),(0,[z1,z2,z3,z4,z285,z6]),(0,[z1,z959,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z1192]),(0,[z1,z2,z3,z120,z65,z5]),(0,[z1,z12,z2,z803,z4,z8]),(0,[z1,z2,z3,z5,z8,z404])],[(0,[z1,z12,z2,z3,z4,z487]),(0,[z1,z2,z3,z4,z1193,z8]),(0,[z667,z1,z2,z27,z5,z8]),(0,[z1,z12,z91,z3,z4,z8]),(0,[z1,z1194,z2,z3,z4,z5])],[(0,[z1,z2,z1195,z4,z5,z8]),(0,[z1,z2,z3,z141,z134,z8]),(0,[z1,z295,z12,z2,z3,z20]),(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z2,z3,z4,z1197,z8]),(0,[z1,z12,z2,z3,z4,z303]),(0,[z1,z2,z3,z4,z5,z745])],[(0,[z1,z2,z3,z80,z236,z8]),(0,[z1,z1198,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1199,z5,z8]),(0,[z1,z67,z3,z4,z55,z8])],[(0,[z1,z12,z2,z3,z134,z8])],[(0,[z1,z2,z113,z4,z5,z487]),(0,[z2,z3,z4,z759,z5,z8]),(0,[z1,z486,z3,z4,z5,z8]),(0,[z1,z2,z1200,z4,z5,z8]),(0,[z1,z2,z68,z4,z14,z8]),(0,[z1,z355,z2,z3,z4,z177])],[(0,[z1,z2,z3,z4,z5,z1201]),(0,[z88,z2,z115,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z321]),(0,[z1,z2,z931,z4,z5,z6]),(0,[z1,z339,z2,z3,z17,z8])],[(0,[z2,z797,z160,z4,z5,z8]),(0,[z1,z2,z3,z379,z5,z536]),(1,[z1,z901,z2,z3,z20]),(0,[z1,z119,z3,z4,z5,z378]),(0,[z1,z12,z2,z3,z144,z8])],[(0,[z1,z1202,z2,z3,z4,z5]),(0,[z2,z3,z4,z743,z135,z8]),(0,[z1,z119,z3,z4,z5,z77]),(0,[z1,z2,z30,z3,z4,z131])]],
   [[(0,[z116,z2,z160,z4,z5,z8]),(0,[z1,z2,z3,z4,z6,z231]),(0,[z1,z11,z81,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z1203])],[(0,[z1,z2,z3,z4,z5,z1204]),(0,[z1,z185,z2,z3,z4,z903]),(0,[z1,z1205,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z296,z6])],[(0,[z1,z1206,z3,z4,z5,z8]),(0,[z1,z2,z45,z4,z14,z6]),(0,[z1,z428,z2,z3,z5,z6]),(0,[z36,z1,z53,z27,z5,z8]),(0,[z1,z29,z2,z4,z5,z716])],[(0,[z1,z2,z479,z4,z5,z20]),(0,[z1,z2,z189,z4,z5,z20]),(0,[z1,z2,z3,z4,z730,z8]),(0,[z36,z1,z2,z17,z27,z8]),(0,[z1,z2,z254,z3,z4,z5]),(0,[z1,z2,z254,z3,z439,z4]),(0,[z1,z839,z2,z3,z17,z4])],[(0,[z1,z109,z3,z17,z4,z8]),(0,[z1,z12,z193,z2,z3,z6]),(0,[z1,z2,z3,z4,z20,z863]),(0,[z1,z2,z3,z4,z421,z20]),(0,[z1,z2,z3,z4,z1207,z8]),(0,[z1,z2,z3,z4,z795,z8])],[(0,[z1,z2,z3,z4,z5,z1208]),(0,[z1,z2,z3,z4,z1209,z8])],[(0,[z1,z2,z3,z4,z1210,z8]),(0,[z1,z2,z3,z848,z19,z8]),(0,[z1,z2,z3,z4,z5,z350]),(0,[z1,z12,z2,z912,z4,z8]),(0,[z1,z202,z2,z3,z4,z8])],[(0,[z1,z2,z3,z313,z5,z487]),(0,[z0,z245,z3,z4,z5,z6]),(0,[z1,z486,z30,z4,z5,z8])],[(0,[z1,z3,z4,z1211,z5,z8]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z2,z3,z17,z18,z20]),(0,[z1,z12,z2,z3,z369,z8]),(0,[z1,z12,z2,z3,z86,z177])],[(0,[z1,z456,z115,z4,z5,z8]),(0,[z2,z3,z4,z35,z743,z8]),(0,[z1,z2,z188,z4,z5,z212]),(0,[z1,z2,z3,z4,z5,z992]),(0,[z1,z12,z2,z3,z305,z8]),(0,[z1,z428,z29,z2,z3,z5])],[(0,[z1,z2,z990,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1072])],[(0,[z1,z456,z3,z4,z203,z8]),(0,[z1,z2,z1159,z4,z5,z8])],[],[(0,[z1,z2,z113,z4,z5,z8]),(0,[z24,z1,z25,z64,z5,z8])],[(0,[z1,z12,z2,z3,z4,z210]),(0,[z1,z53,z3,z4,z5,z20]),(0,[z1,z12,z2,z3,z396,z8]),(0,[z1,z2,z3,z17,z370,z8])]],
   [[(0,[z1,z2,z3,z375,z5,z8]),(0,[z1,z2,z3,z17,z4,z147]),(0,[z1,z2,z3,z4,z310,z459]),(0,[z1,z2,z3,z4,z5,z1082])],[(0,[z1,z2,z3,z85,z5,z6]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z1,z12,z53,z3,z4,z8])],[(0,[z1,z2,z3,z4,z209,z883]),(0,[z1,z11,z804,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1213]),(0,[z1,z12,z2,z3,z8,z404])],[(0,[z1,z139,z3,z166,z5,z6]),(0,[z1,z2,z3,z379,z5,z86]),(0,[z1,z2,z3,z4,z5,z1214]),(0,[z1,z2,z3,z4,z5,z177])],[(0,[z1,z2,z337,z4,z325,z8]),(0,[z1,z2,z3,z4,z1215,z8]),(0,[z1,z2,z3,z17,z4,z362]),(0,[z1,z2,z3,z4,z165,z215]),(0,[z1,z454,z2,z479,z4,z5])],[(0,[z1,z2,z3,z4,z1216,z8]),(0,[z1,z139,z110,z4,z5,z8]),(0,[z1,z12,z2,z30,z4,z46]),(0,[z1,z12,z2,z3,z412,z8]),(0,[z1,z67,z3,z108,z4,z8]),(0,[z1,z813,z3,z17,z4,z8])],[(0,[z1,z2,z3,z473,z203,z8]),(0,[z1,z2,z3,z848,z4,z8]),(0,[z1,z12,z2,z3,z235,z8]),(0,[z1,z12,z2,z3,z4,z733]),(0,[z1,z2,z3,z4,z8,z1217]),(0,[z1,z193,z2,z3,z585,z5])],[(0,[z1,z2,z3,z17,z4,z366]),(0,[z1,z12,z11,z81,z4,z8]),(0,[z1,z2,z953,z3,z17,z4])],[(0,[z1,z2,z3,z4,z364,z126]),(0,[z1,z226,z2,z3,z4,z177])],[(0,[z1,z2,z3,z4,z203,z20]),(0,[z603,z1,z3,z64,z5,z8]),(0,[z1,z2,z3,z85,z135,z8]),(0,[z539,z1,z87,z4,z5,z8])],[(0,[z1,z428,z10,z2,z3,z5])],[(0,[z1,z2,z3,z4,z1218,z8])],[(0,[z1,z12,z2,z3,z4,z133]),(0,[z1,z2,z3,z4,z5,z1219])],[(0,[z1,z3,z4,z5,z877,z8]),(0,[z1,z2,z3,z17,z4,z388]),(0,[z1,z172,z87,z17,z4,z8]),(0,[z1,z2,z3,z1220,z4,z8])],[(0,[z1,z2,z3,z1118,z313,z8]),(0,[z88,z2,z115,z4,z5,z6]),(0,[z1,z2,z3,z5,z8,z869]),(0,[z1,z2,z3,z4,z5,z1221]),(0,[z1,z2,z3,z4,z5,z1222])],[(0,[z1,z2,z4,z5,z167,z716])]],
   [[(0,[z1,z2,z3,z4,z1223,z8]),(0,[z1,z139,z3,z166,z296,z8])],[(0,[z1,z12,z2,z3,z150,z8]),(0,[z1,z11,z81,z4,z5,z6]),(0,[z1,z10,z2,z3,z4,z215]),(0,[z1,z901,z2,z3,z20,z8]),(0,[z1,z383,z3,z4,z5,z8])],[(0,[z97,z2,z3,z19,z5,z8])],[(0,[z1,z2,z834,z4,z5,z8]),(0,[z1,z2,z3,z4,z86,z215])],[(0,[z1,z2,z3,z1224,z5,z8])],[(0,[z2,z3,z4,z20,z6,z215]),(0,[z1,z2,z479,z4,z5,z6]),(0,[z1,z2,z189,z4,z5,z6]),(0,[z225,z1,z3,z4,z169,z8])],[(0,[z1,z2,z3,z4,z5,z1225]),(0,[z1,z2,z3,z4,z421,z6]),(0,[z1,z71,z2,z3,z4,z397]),(0,[z1,z2,z3,z1226,z5,z8])],[(0,[z69,z2,z3,z4,z5,z6])],[(0,[z79,z181,z3,z17,z4,z8]),(0,[z1,z2,z3,z4,z1227,z8]),(0,[z1,z2,z894,z4,z5,z8]),(0,[z1,z2,z3,z4,z6,z983]),(0,[z1,z1194,z91,z3,z4,z5]),(0,[z1,z12,z2,z3,z99,z86]),(0,[z836,z2,z3,z17,z4,z8])],[(0,[z1,z2,z3,z17,z4,z57])],[(0,[z1,z12,z2,z3,z313,z8]),(0,[z1,z2,z3,z17,z18,z6])],[(0,[z1,z2,z3,z313,z325,z8]),(0,[z1,z2,z3,z1228,z5,z8]),(0,[z1,z2,z1229,z4,z5,z8]),(0,[z1,z2,z3,z4,z1230,z8])],[(0,[z1,z2,z3,z4,z1231,z8]),(0,[z1,z2,z3,z4,z5,z459])],[(0,[z0,z12,z245,z3,z4,z8]),(0,[z1109,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z72]),(0,[z1110,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z1232,z5,z8])],[(0,[z1,z2,z3,z1151,z4,z8]),(0,[z225,z1,z3,z4,z34,z72])]],
   [[(0,[z1,z2,z3,z4,z5,z1233]),(0,[z1,z53,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1234,z5]),(0,[z1,z2,z3,z4,z5,z1235])],[(0,[z16,z2,z3,z17,z4,z6]),(0,[z1,z595,z81,z4,z5,z8]),(0,[z1,z2,z3,z4,z296,z973])],[(0,[z1,z1236,z3,z4,z5,z8])],[(0,[z1,z798,z2,z3,z4,z8]),(0,[z1,z2,z3,z17,z42,z8]),(0,[z1,z2,z3,z17,z4,z201]),(0,[z1,z2,z30,z4,z421,z46])],[(0,[z1,z2,z3,z4,z1237,z8]),(0,[z1,z71,z2,z3,z4,z20]),(0,[z1,z2,z3,z4,z1238,z5]),(0,[z1,z193,z2,z3,z706,z5])],[(0,[z1,z2,z3,z17,z4,z106]),(0,[z1,z2,z3,z4,z5,z1239]),(0,[z62,z2,z3,z4,z5,z20])],[(0,[z0,z718,z3,z4,z5,z8]),(0,[z2,z3,z759,z19,z5,z8]),(0,[z1,z2,z3,z4,z421,z201]),(0,[z1,z12,z2,z3,z86,z8]),(0,[z1,z12,z2,z3,z4,z784]),(0,[z1,z2,z3,z4,z5,z1123])],[(0,[z1,z456,z3,z17,z4,z8]),(0,[z1,z1240,z3,z4,z5,z8]),(0,[z1,z2,z3,z1241,z5,z8]),(0,[z1,z2,z3,z4,z5,z1242]),(0,[z1,z2,z3,z17,z4,z862])],[(0,[z1,z12,z2,z337,z4,z8]),(0,[z1,z1243,z2,z3,z4,z8]),(0,[z1,z428,z2,z3,z5,z86])],[(0,[z1,z2,z3,z4,z203,z6]),(0,[z1,z2,z3,z4,z5,z1244])],[(0,[z1,z456,z3,z4,z5,z126]),(0,[z1,z2,z1245,z3,z4,z5]),(0,[z36,z1,z2,z141,z27,z8]),(0,[z1,z12,z2,z254,z3,z4])],[(0,[z1,z2,z137,z4,z5,z394]),(1,[z1,z804,z4,z5,z8]),(0,[z1,z1246,z3,z4,z5,z8])],[(0,[z1,z11,z206,z4,z5,z8]),(0,[z1,z2,z3,z4,z249,z177])],[(0,[z1,z2,z3,z4,z8,z1188]),(0,[z1,z2,z3,z4,z1247,z5]),(0,[z63,z2,z3,z4,z5,z20]),(0,[z1,z12,z454,z2,z3,z4]),(0,[z1,z2,z3,z17,z443,z8])],[(0,[z98,z2,z3,z759,z5,z8]),(0,[z1,z2,z3,z4,z5,z1248])]],
   [[(0,[z155,z1,z2,z577,z4,z8])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z116,z2,z160,z4,z5,z147]),(0,[z1,z2,z1249,z3,z4,z5]),(0,[z21,z2,z3,z4,z743,z8])],[(0,[z1,z2,z3,z4,z1250,z8]),(0,[z1,z2,z3,z4,z5,z1251])],[(0,[z1,z2,z3,z1252,z5,z8]),(0,[z1,z2,z3,z1253,z4,z8]),(0,[z225,z1,z3,z4,z34,z8]),(0,[z1,z10,z3,z4,z5,z717])],[(0,[z1,z2,z3,z4,z20,z231]),(0,[z1,z2,z3,z4,z5,z1138]),(0,[z1,z1254,z2,z3,z5,z8])],[(0,[z1,z2,z3,z473,z5,z126]),(0,[z1,z2,z3,z17,z4,z20]),(0,[z1,z2,z3,z4,z926,z8]),(0,[z1,z71,z2,z3,z4,z15]),(0,[z24,z1,z3,z221,z64,z8])],[(0,[z1,z245,z113,z4,z5,z8]),(0,[z1,z2,z3,z4,z61,z20]),(0,[z1,z2,z4,z753,z5,z8]),(0,[z1,z2,z3,z4,z14,z177])],[(0,[z1,z771,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z420,z20]),(0,[z1,z2,z3,z4,z1255,z8]),(0,[z1,z383,z3,z120,z4,z5]),(0,[z1,z12,z1256,z3,z4,z8])],[(0,[z1,z2,z3,z1257,z5,z8]),(0,[z52,z2,z3,z4,z35,z388]),(0,[z1,z2,z3,z4,z1258,z8]),(0,[z1,z1259,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z743,z8]),(0,[z1,z2,z3,z4,z5,z1260]),(1,[z1,z2,z4,z5,z716])],[(0,[z1,z456,z160,z4,z5,z8]),(0,[z1,z12,z2,z3,z4,z147]),(0,[z1,z2,z3,z4,z20,z730]),(0,[z1,z12,z193,z2,z30,z3])],[(0,[z1,z2,z3,z1261,z5,z8]),(0,[z1,z185,z2,z3,z4,z980]),(0,[z1,z2,z3,z17,z85,z8]),(0,[z1,z12,z243,z2,z3,z6]),(0,[z248,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z899,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z1262]),(0,[z609,z2,z3,z4,z35,z8]),(0,[z1,z10,z3,z610,z4,z5])],[(0,[z1,z12,z2,z3,z4,z362]),(1,[z2,z797,z4,z5,z8]),(0,[z1,z1263,z2,z3,z4,z5]),(0,[z1,z1256,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1264,z5])]],
   [[(0,[z1,z2,z3,z4,z1265,z5]),(0,[z1,z140,z2,z3,z221,z4]),(0,[z1,z399,z3,z4,z34,z8])],[(0,[z1,z2,z3,z375,z5,z147]),(0,[z1,z12,z2,z3,z4,z366]),(0,[z1,z87,z4,z5,z659,z8])],[(0,[z1,z12,z2,z3,z535,z8]),(0,[z1,z2,z3,z326,z5,z8]),(0,[z1,z12,z2,z3,z536,z20]),(0,[z1,z2,z3,z4,z5,z1266])],[(0,[z1,z2,z3,z4,z1050,z6])],[(0,[z1,z1267,z2,z3,z4,z5]),(0,[z1,z2,z3,z1268,z4,z8]),(0,[z1,z12,z2,z3,z19,z57]),(0,[z1,z3,z4,z5,z717,z13])],[(0,[z1,z1269,z2,z3,z4,z8])],[(0,[z1,z12,z2,z3,z114,z8]),(0,[z1,z2,z3,z76,z4,z20]),(0,[z1,z71,z2,z3,z4,z6]),(0,[z1,z901,z2,z3,z5,z20]),(0,[z1270,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1271])],[(0,[z1,z2,z3,z1272,z5,z8]),(0,[z1,z12,z2,z3,z4,z388]),(0,[z1,z2,z189,z4,z5,z15]),(0,[z1,z1273,z2,z3,z4,z8])],[(0,[z1,z2,z3,z4,z1055,z6]),(0,[z1,z2,z3,z4,z1274,z5]),(0,[z1,z2,z3,z4,z421,z15])],[(0,[z1,z2,z1275,z4,z5,z8]),(0,[z71,z2,z3,z4,z20,z6]),(0,[z1,z2,z254,z3,z141,z4])],[(0,[z1,z2,z3,z1276,z5,z8]),(0,[z1277,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z1278,z5,z8])],[(0,[z911,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z1279]),(0,[z1280,z2,z3,z4,z5,z8]),(0,[z1,z3,z4,z825,z5,z8])],[(0,[z1,z2,z3,z4,z1281,z8])],[(0,[z1,z1282,z2,z3,z4,z8]),(0,[z1,z2,z3,z85,z35,z8])],[(0,[z36,z1,z2,z439,z27,z8])],[(0,[z1,z428,z2,z3,z32,z8])]],
   [[(0,[z1,z1027,z3,z4,z5,z8]),(0,[z1,z2,z3,z1283,z5,z8]),(0,[z1,z2,z3,z4,z5,z1284]),(0,[z1,z2,z68,z334,z4,z8])],[(0,[z1,z12,z2,z3,z432,z8]),(0,[z1,z374,z3,z4,z34,z8]),(0,[z1,z202,z2,z3,z4,z57]),(0,[z250,z1,z3,z4,z169,z8])],[(0,[z1,z2,z113,z4,z325,z8]),(0,[z1,z193,z2,z3,z190,z168])],[(0,[z24,z1,z110,z64,z5,z8]),(0,[z1,z12,z2,z3,z4,z57])],[(0,[z1,z2,z3,z4,z1285,z8]),(0,[z1,z31,z2,z3,z4,z118]),(0,[z1,z12,z2,z3,z570,z6]),(0,[z1,z2,z3,z4,z1286,z8])],[(0,[z1,z2,z3,z4,z5,z1175]),(0,[z1,z2,z3,z4,z1287,z8])],[(0,[z1,z2,z3,z17,z4,z6]),(0,[z1,z1102,z3,z4,z5,z20])],[(0,[z1,z2,z3,z1163,z4,z8]),(0,[z1,z967,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z61,z6]),(0,[z1,z2,z3,z4,z5,z1288]),(0,[z1,z2,z3,z4,z1289,z8]),(0,[z1,z2,z3,z4,z5,z1290]),(0,[z1,z2,z3,z17,z130,z8])],[(0,[z1,z2,z3,z4,z420,z6]),(0,[z2,z3,z17,z342,z4,z6]),(0,[z24,z1,z82,z3,z64,z8]),(0,[z1,z29,z486,z4,z5,z167])],[(0,[z1291,z2,z3,z4,z5,z8])],[(0,[z1,z2,z337,z4,z5,z106]),(0,[z21,z466,z2,z3,z4,z8]),(0,[z1,z31,z2,z3,z4,z138])],[(0,[z1,z871,z2,z3,z4,z8]),(0,[z1,z12,z456,z3,z4,z8]),(0,[z1,z901,z2,z3,z20,z215]),(0,[z1,z2,z3,z4,z249,z8])],[(0,[z1,z2,z3,z4,z1292,z8]),(0,[z1,z522,z2,z3,z4,z215]),(0,[z1,z10,z30,z87,z4,z5]),(0,[z1,z12,z2,z110,z4,z8]),(0,[z1,z2,z1293,z3,z4,z5])],[(0,[z43,z1,z2,z3,z4,z177]),(0,[z1,z12,z2,z3,z4,z857])],[(0,[z98,z2,z3,z134,z5,z20]),(0,[z1,z2,z3,z17,z247,z8]),(0,[z1,z12,z2,z3,z4,z201]),(0,[z1,z12,z2,z3,z297,z8])],[(0,[z1,z2,z3,z1294,z5,z8]),(0,[z1,z2,z3,z4,z1295,z8]),(0,[z1,z2,z3,z4,z5,z1120])]],
   [[(0,[z1,z12,z2,z3,z4,z106]),(0,[z1,z2,z3,z4,z5,z1296]),(0,[z1,z12,z2,z3,z19,z20])],[(0,[z1,z2,z3,z4,z5,z320]),(0,[z1,z2,z3,z4,z5,z1297]),(0,[z36,z1,z2,z27,z5,z20]),(0,[z1,z2,z3,z221,z4,z8])],[(0,[z1,z2,z3,z4,z5,z487]),(0,[z1,z2,z3,z4,z5,z1298]),(0,[z73,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z1299]),(0,[z1,z652,z3,z4,z55,z8]),(0,[z1,z2,z3,z1300,z5,z8]),(0,[z1,z29,z2,z17,z4,z167])],[(0,[z79,z181,z3,z313,z5,z8]),(0,[z1,z1085,z2,z3,z4,z6]),(0,[z1,z91,z3,z4,z5,z8])],[(0,[z1,z2,z1301,z4,z5,z8]),(0,[z1,z2,z3,z17,z473,z8]),(0,[z1,z2,z3,z134,z265,z8]),(0,[z1,z2,z4,z5,z1087,z6]),(0,[z1,z2,z3,z1302,z5,z8]),(0,[z1,z2,z30,z17,z4,z46]),(0,[z1,z29,z383,z4,z5,z167])],[(0,[z1,z2,z1033,z4,z5,z8]),(0,[z1,z2,z3,z85,z5,z138]),(0,[z1,z458,z2,z3,z17,z8]),(0,[z1,z2,z30,z4,z61,z46])],[(0,[z1,z2,z3,z4,z1303,z5]),(0,[z664,z2,z3,z4,z35,z8]),(0,[z1,z2,z3,z4,z1089,z6]),(0,[z1,z1304,z2,z3,z4,z8])],[(0,[z1,z2,z3,z76,z4,z6]),(0,[z1,z3,z4,z5,z6,z1092]),(0,[z1,z2,z3,z4,z5,z1305]),(0,[z36,z1,z2,z254,z27,z5]),(0,[z1,z2,z3,z4,z5,z1306])],[(0,[z1,z1307,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1308,z8]),(0,[z680,z2,z3,z19,z5,z8]),(0,[z1,z2,z3,z1309,z4,z8]),(0,[z1,z1310,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z201,z15])],[(0,[z1,z2,z337,z4,z5,z20]),(0,[z0,z245,z3,z17,z4,z8]),(0,[z116,z109,z160,z4,z5,z8]),(0,[z1,z2,z3,z4,z138,z215]),(0,[z1,z2,z1125,z4,z5,z20]),(0,[z1,z2,z30,z479,z4,z5]),(0,[z1,z12,z2,z3,z671,z8])],[(0,[z1,z2,z3,z17,z349,z8])],[(0,[z1,z2,z3,z19,z265,z8]),(0,[z1,z2,z3,z4,z1311,z5])],[(0,[z1,z12,z2,z3,z423,z8]),(0,[z24,z1,z3,z64,z5,z20]),(0,[z1,z2,z3,z141,z4,z20])],[(0,[z1,z202,z2,z3,z4,z20]),(0,[z1,z11,z140,z3,z4,z5]),(0,[z1,z2,z3,z17,z4,z949])],[(0,[z2,z3,z217,z4,z5,z6]),(0,[z1,z87,z4,z128,z5,z8]),(0,[z1,z2,z3,z4,z1134,z8]),(0,[z1,z12,z193,z2,z3,z86])],[(0,[z1,z2,z3,z1312,z4,z8]),(0,[z1,z12,z2,z3,z4,z20]),(0,[z1,z2,z3,z4,z5,z1313]),(0,[z1,z2,z3,z4,z5,z716])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 507) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 507).take 503) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1010).take 397) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1407)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [507, 503, 397] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 159).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 159).take 156).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 315).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 457).take 55).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [159, 156, 142, 55] = true :=
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

end PEqualNP.Outside.L_meta_38635

theorem PEqualNP.Outside.L_meta_38635 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4276136608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4276136608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38635.solve