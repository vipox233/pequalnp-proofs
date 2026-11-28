import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38755

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x48000504290e22e2#64 ++ 0xa400028214871171#64 ++ 0xf5809f3cfb1e67e7#64 ++ 0xfac04f9e7d8f33f3#64 : BitVec 256),
   (0x10032c5161628969#64 ++ 0x08019628b0b144b4#64 ++ 0xef876cd365e399f9#64 ++ 0xf7c3b669b2f1ccfc#64 : BitVec 256),
   (0xa03850a286015414#64 ++ 0x501c28514300aa0a#64 ++ 0xdef870e38603fe3f#64 ++ 0xef7c3871c301ff1f#64 : BitVec 256),
   (0xc0dd80fc06b41f80#64 ++ 0x606ec07e035a0fc0#64 ++ 0xbfff80fc07fc1fc1#64 ++ 0x5fffc07e03fe0fe0#64 : BitVec 256),
   (0x016eff0007dbe001#64 ++ 0x80b77f8003edf000#64 ++ 0x7f7fff0007ffe001#64 ++ 0x3fbfff8003fff000#64 : BitVec 256),
   (0x0077fafbd0000000#64 ++ 0x003bfd7de8000000#64 ++ 0xfc7ffffff8000000#64 ++ 0xfe3ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z2 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef876cd365e399f9 0xf7c3b669b2f1ccfc

def z3 : W := mkw 0x48000504090e2282 0xa400028204871141 0x75009f2c9b1e6607 0x3a804f964d8f3303

def z4 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xf5809f3cfb1e67e7 0xfac04f9e7d8f33f3

def z5 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xdef870e38603fe3f 0xef7c3871c301ff1f

def z6 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z7 : W := mkw 0x0028500006014000 0x001428000300a000 0xdef870208603e627 0xef7c38104301f313

def z8 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x0a7f600004e18000 0x053fb0000270c000

def z9 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x808000fc00001fc0 0x4040007e00000fe0

def z10 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x21008f1c791c01c0 0x1080478e3c8e00e0

def z11 : W := mkw 0xc89105fc292e3fe2 0xe44882fe14971ff1 0xf5809ffcfb1e7fe7 0xfac04ffe7d8f3ff3

def z12 : W := mkw 0x004d805006b00900 0x0026c02803580480 0xbfff80d007fc19c1 0x5fffc06803fe0ce0

def z13 : W := mkw 0x116fff5167fbe969 0x88b7ffa8b3fdf4b4 0xffffffd367fff9f9 0xffffffe9b3fffcfc

def z14 : W := mkw 0x00000500010a2000 0x8000028000851000 0x75009f00031e6001 0x3a804f80018f3000

def z15 : W := mkw 0x1003285160608969 0x08019428b03044b4 0x8a8760d364e199f8 0xc543b069b270ccfc

def z16 : W := mkw 0x004c800006900000 0x0026400003480000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z17 : W := mkw 0x48000004280402e2 0x2400000214020171 0x8080003cf80007e6 0xc040001e7c0003f3

def z18 : W := mkw 0x1077fefbf1428069 0x083bff7df8a14034 0xfc7ffffff8038038 0xfe3ffffffc01c01c

def z19 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x2b076cd365e199d8 0x1583b669b2f0ccec

def z20 : W := mkw 0x1003285140608909 0x08019428a0304484 0xce8760c304e39839 0xe743b0618271cc1c

def z21 : W := mkw 0xa17ffffbd7dbf415 0xd0bffffdebedfa0a 0xfffffffffffffe3f 0xffffffffffffff1f

def z22 : W := mkw 0xa13855a287dbf415 0xd09c2ad143edfa0a 0xdff870e387fffe3f 0xeffc3871c3ffff1f

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4009f3cf8000000 0xfa004f9e7c000000

def z24 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x01800000031e67e7 0x00c00000018f33f3

def z25 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff9ffcfffc1fc1 0xffffcffe7ffe0fe0

def z26 : W := mkw 0x58032c5569668beb 0x2c01962ab4b345f5 0xef876cfffde39fff 0xf7c3b67ffef1cfff

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0xd480102082026627 0xea40081041013313

def z28 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff877cf3e7e3ffff 0xffc3be79f3f1ffff

def z29 : W := mkw 0x004c8500079a2000 0x8026428003cd1000 0x7f7f9f0007fe6001 0x3fbfcf8003ff3000

def z30 : W := mkw 0xc8dd85fc2fbe3fe2 0xe46ec2fe17df1ff1 0xffff9ffcfffe7fe7 0xffffcffe7fff3ff3

def z31 : W := mkw 0xe0fdd0fe86b55f94 0x707ee87f435aafca 0xfffff0ff87ffffff 0xfffff87fc3ffffff

def z32 : W := mkw 0xc0fffafc06b41f80 0x607ffd7e035a0fc0 0xfffffffc07fc1fc1 0x7ffffffe03fe0fe0

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x40001f00f8000000 0xa0000f807c000000

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00600004038001 0x270030000201c000

def z35 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x0a7860c304019818 0x053c30618200cc0c

def z36 : W := mkw 0x0057aaf950000000 0x002bd57ca8000000 0xbc7f8ffc78000000 0x5e3fc7fe3c000000

def z37 : W := mkw 0xc088000406b41f80 0x60440002035a0fc0 0x0380000007fc1fc1 0x01c0000003fe0fe0

def z38 : W := mkw 0xa01000a280001414 0x5008005140000a0a 0x000000c300001818 0x0000006180000c0c

def z39 : W := mkw 0x0000040021020060 0x0000020010810030 0xe5800c10610201e1 0xf2c00608308100f0

def z40 : W := mkw 0x58032d55696eabeb 0xac0196aab4b755f5 0xff87ffffffffffff 0xffc3ffffffffffff

def z41 : W := mkw 0x0001005000200900 0x0000802800100480 0x0a0700c004e01800 0x0503806002700c00

def z42 : W := mkw 0x80dd80f806b01d00 0x406ec07c03580e80 0xafff00d005e019c1 0x57ff806802f00ce0

def z43 : W := mkw 0x01227f00014be001 0x80913f8000a5f000 0x6f077f0005e3e001 0x3783bf8002f1f000

def z44 : W := mkw 0x801800a006001400 0x400c005003000a00 0x9ef800e006001e01 0x4f7c007003000f00

def z45 : W := mkw 0x003850a286014000 0x001c28514300a000 0xde7870e38603e001 0xef3c3871c301f000

def z46 : W := mkw 0x10132cfbf1628969 0x0809967df8b144b4 0xef876cfffde399f9 0xf7c3b67ffef1ccfc

def z47 : W := mkw 0x10022c0161428069 0x08011600b0a14034 0x40006c0360038038 0xa0003601b001c01c

def z48 : W := mkw 0xc0dc80ac06941680 0x606e4056034a0b40 0x1078802c021c0600 0x083c4016010e0300

def z49 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x307f9f3cf8000000 0x183fcf9e7c000000

def z50 : W := mkw 0x08000500290a2062 0x8400028014851031 0x40001f00f8026026 0xa0000f807c013013

def z51 : W := mkw 0x80dd80f806b01d00 0x406ec07c03580e80 0x0a7f00c004e01800 0x053f806002700c00

def z52 : W := mkw 0x00327aa3d0000000 0x00193d51e8000000 0xdc787fe3f8000000 0xee3c3ff1fc000000

def z53 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x1a7f80ec06fc1e00 0x0d3fc076037e0f00

def z54 : W := mkw 0x4000000400040280 0x2000000200020140 0x1000802c021c0600 0x08004016010e0300

def z55 : W := mkw 0x80fffafbd6b01d00 0x407ffd7deb580e80 0xfe7ffffffce01800 0xff3ffffffe700c00

def z56 : W := mkw 0x1067fe5161628969 0x0833ff28b0b144b4 0xffffffd365e399f9 0xffffffe9b2f1ccfc

def z57 : W := mkw 0xe87fffffff0f76f6 0xf43fffffff87bb7b 0xffffffffff1fffff 0xffffffffff8fffff

def z58 : W := mkw 0x4000000400040280 0x2000000200020140 0x2100801c011c01c0 0x1080400e008e00e0

def z59 : W := mkw 0x01227f03d14be001 0x80913f81e8a5f000 0x40007f03f803e000 0xa0003f81fc01f000

def z60 : W := mkw 0x017effa287dbe001 0x80bf7fd143edf000 0xff7fffe387ffe001 0xffbffff1c3fff000

def z61 : W := mkw 0x0166ff0001daa001 0x80b37f8000ed5000 0x7d7fff0001fc0000 0x3ebfff8000fe0000

def z62 : W := mkw 0x40c5805c00b40b80 0x2062c02e005a05c0 0x2107801c01fc01c0 0x1083c00e00fe00e0

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0xce8060c304039839 0xe74030618201cc1c

def z64 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffffc307fff839 0xffffffe183fffc1c

def z65 : W := mkw 0xd09100fd60241fe8 0x6848807eb0120ff4 0x808000ff60001ff8 0xc040007fb0000ffc

def z66 : W := mkw 0x48000104080c2282 0xa400008204061141 0xb580933c9b1c67c7 0x5ac0499e4d8e33e3

def z67 : W := mkw 0xe09100fe80241f94 0x7048807f40120fca 0x808000ff80001ffe 0xc040007fc0000fff

def z68 : W := mkw 0xe0fcd0ae86955694 0x707e6857434aab4a 0x1078902c821c6606 0x083c4816410e3303

def z69 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x21808f1c7b1e67e7 0x10c0478e3d8f33f3

def z70 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x41801f00fb1e67e7 0xa0c00f807d8f33f3

def z71 : W := mkw 0x0028500006014000 0x001428000300a000 0x5e7870000603e001 0x2f3c38000301f000

def z72 : W := mkw 0x809100f800201d00 0x4048807c00100e80 0x000000c000001800 0x0000006000000c00

def z73 : W := mkw 0x81fffff807fbfd01 0xc0fffffc03fdfe80 0x7f7fffc007fff801 0x3fbfffe003fffc00

def z74 : W := mkw 0x4877fffff90e22e2 0xa43bfffffc871171 0xfdfffffffb1e67e7 0xfefffffffd8f33f3

def z75 : W := mkw 0xa07ffafbd6015414 0x503ffd7deb00aa0a 0xfefffffffe03fe3f 0xff7fffffff01ff1f

def z76 : W := mkw 0xe0fffaffd6b55f94 0x707ffd7feb5aafca 0xffffffffffffffff 0xffffffffffffffff

def z77 : W := mkw 0xa01000a280001414 0x5008005140000a0a 0xd48010e382027e3f 0xea400871c1013f1f

def z78 : W := mkw 0x2028500286014014 0x101428014300a00a 0x5e7870038603e03f 0xaf3c3801c301f01f

def z79 : W := mkw 0xf83b7df7ef6fffff 0xfc1dbefbf7b7ffff 0xffffffffffffffff 0xffffffffffffffff

def z80 : W := mkw 0xa83855a2af0b7476 0xd41c2ad15785ba3b 0xdef87fe3fe03fe3f 0xef7c3ff1ff01ff1f

def z81 : W := mkw 0x016efb0006996000 0x80b77d80034cb000 0x7c7fff00021c6000 0x3e3fff80010e3000

def z82 : W := mkw 0xc0dfaafd56b41f80 0x606fd57eab5a0fc0 0xbfff8ffc7ffc1fc1 0x5fffc7fe3ffe0fe0

def z83 : W := mkw 0x803850a286001400 0x401c285143000a00 0xdef870e386001e01 0xef7c3871c3000f00

def z84 : W := mkw 0xc09000ac00041680 0x6048005600020b40 0x0000002c00000600 0x0000001600000300

def z85 : W := mkw 0x003050a280000000 0x0018285140000000 0xdcf870e382026627 0xee7c3871c1013313

def z86 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x21070c1061e001c0 0x1083860830f000e0

def z87 : W := mkw 0xb03b7cf3e763dd7d 0x581dbe79f3b1eebe 0xffff7cf3e7e3ffff 0xffffbe79f3f1ffff

def z88 : W := mkw 0xc8dd85fc2fbe3fe2 0xe46ec2fe17df1ff1 0xbfff80fc07fe7fe7 0x5fffc07e03ff3ff3

def z89 : W := mkw 0x09227f00294be063 0x84913f8014a5f031 0x40007f00f803e026 0xa0003f807c01f013

def z90 : W := mkw 0x496eff042fdfe2e3 0xa4b77f8217eff171 0xffffff3cffffe7e7 0xffffff9e7ffff3f3

def z91 : W := mkw 0x4000000400040280 0x2000000200020140 0x8080003c000007c0 0x4040001e000003e0

def z92 : W := mkw 0xc1fffffc07ffff81 0xe0fffffe03ffffc0 0xfffffffc07ffffc1 0x7ffffffe03ffffe0

def z93 : W := mkw 0x001100fbd0000000 0x0008807de8000000 0x000000c300000000 0x0000006180000000

def z94 : W := mkw 0x0001005000000000 0x0000802800000000 0xac0700d000000000 0x5603806800000000

def z95 : W := mkw 0x005580f800000000 0x002ac07c00000000 0xbc7f80fc00000000 0x5e3fc07e00000000

def z96 : W := mkw 0x006efa0006900000 0x00377d0003480000 0x7f7fff0007fc0001 0x3fbfff8003fe0000

def z97 : W := mkw 0xc0fffaffd6b41f80 0x607ffd7feb5a0fc0 0xfffffffffffc1fc1 0xfffffffffffe0fe0

def z98 : W := mkw 0x016cd30006996000 0x80b66980034cb000 0x10789300021c6000 0x083c4980010e3000

def z99 : W := mkw 0x1001005160200968 0x08008028b01004b4 0x808000d3600019f8 0xc0400069b0000cfc

def z100 : W := mkw 0x001100fbd0000000 0x0008807de8000000 0x800000fff8000000 0xc000007ffc000000

def z101 : W := mkw 0xa17effa287dbf415 0xd0bf7fd143edfa0a 0xffffffe387fffe3f 0xfffffff1c3ffff1f

def z102 : W := mkw 0xa01000a280001414 0x5008005140000a0a 0x808000e380001e3e 0xc0400071c0000f1f

def z103 : W := mkw 0x0001005000200900 0x0000802800100480 0xaf8700d005e019c1 0x57c3806802f00ce0

def z104 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x287fefdf78000000 0x143ff7efbc000000

def z105 : W := mkw 0x1077fefbf1628969 0x083bff7df8b144b4 0xfffffffffde399f9 0xfffffffffef1ccfc

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000932c98000000 0x080049964c000000

def z107 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x1078932c98000000 0x083c49964c000000

def z108 : W := mkw 0x1077fefbf1628969 0x083bff7df8b144b4 0xefff6cd365e399f9 0xf7ffb669b2f1ccfc

def z109 : W := mkw 0x0128550007dbe001 0x80942a8003edf000 0x5f78700007ffe001 0x2fbc380003fff000

def z110 : W := mkw 0x203050a280014014 0x101828514000a00a 0xdc7870e38003e03e 0xee3c3871c001f01f

def z111 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x2b7fef0005fd8000 0x15bff78002fec000

def z112 : W := mkw 0x4000000400040280 0x2000000200020140 0xb580803c031c07c1 0x5ac0401e018e03e0

def z113 : W := mkw 0x003050a280000000 0x0018285140000000 0xdc7870e380000000 0xee3c3871c0000000

def z114 : W := mkw 0x805d80f806001400 0x402ec07c03000a00 0xbeff80fc06001e01 0x5f7fc07e03000f00

def z115 : W := mkw 0xe0dd80fe86b41f94 0x706ec07f435a0fca 0xbfff80ff87fc1fff 0xdfffc07fc3fe0fff

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x74009f0000000000 0x3a004f8000000000

def z117 : W := mkw 0x40c7aa5d50b40b80 0x2063d52ea85a05c0 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z118 : W := mkw 0x48000404290602e2 0x2400020214830171 0xe5800c3cf90207e7 0xf2c0061e7c8103f3

def z119 : W := mkw 0x1003285140608909 0x08019428a0304484 0x0a0760c304e19818 0x0503b0618270cc0c

def z120 : W := mkw 0x104fac5167f28969 0x0827d628b3f944b4 0xffffecd367ff99f9 0xfffff669b3ffccfc

def z121 : W := mkw 0x0000040001428001 0x0000020000a14000 0x0300000005e38001 0x0180000002f1c000

def z122 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x087f60c300000000 0x043fb06180000000

def z123 : W := mkw 0x01227f00014be001 0x80913f8000a5f000 0x40007f000003e000 0x20003f800001f000

def z124 : W := mkw 0xf0fffcffe7f7dffd 0x787ffe7ff3fbeffe 0xfffffcffe7ffffff 0xfffffe7ff3ffffff

def z125 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0xbc7f93fc98000000 0x5e3fc9fe4c000000

def z126 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff90fc87fe7fe7 0xffffc87e43ff3ff3

def z127 : W := mkw 0xc88805042fbe3fe2 0xe444028217df1ff1 0x0380000007fe7fe7 0x01c0000003ff3ff3

def z128 : W := mkw 0x10022c0161428069 0x08011600b0a14034 0xce806cc364039839 0xe7403661b201cc1c

def z129 : W := mkw 0x0020500000000000 0x0010280000000000 0x5c78700000000000 0x2e3c380000000000

def z130 : W := mkw 0x0147af5951daa001 0x80a3d7aca8ed5000 0x21078f1c79fc0000 0x1083c78e3cfe0000

def z131 : W := mkw 0x0047aa5950000000 0x0023d52ca8000000 0x20078f1c78000000 0x1003c78e3c000000

def z132 : W := mkw 0xa008000006015414 0x500400000300aa0a 0x028000000603fe3f 0x014000000301ff1f

def z133 : W := mkw 0x016eff03d7dbe001 0x80b77f81ebedf000 0x7f7fff03ffffe001 0xbfbfff81fffff000

def z134 : W := mkw 0x0001045021220960 0x00008228109104b0 0xef870cd065e219e1 0xf7c3866832f10cf0

def z135 : W := mkw 0x005d80f806900000 0x002ec07c03480000 0xbf7f80fc07fc0001 0x5fbfc07e03fe0000

def z136 : W := mkw 0x1047ae5971628969 0x0823d72cb8b144b4 0x21078f1c79e001c0 0x1083c78e3cf000e0

def z137 : W := mkw 0x4847af5d790e22e2 0xa423d7aebc871171 0x21078f1c791c01c0 0x1083c78e3c8e00e0

def z138 : W := mkw 0x10022c0161428069 0x08011600b0a14034 0x6f076c0365e38039 0xb783b601b2f1c01c

def z139 : W := mkw 0x0003285140000000 0x00019428a0000000 0xfc07fffff8000000 0xfe03fffffc000000

def z140 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x317f9f0003fc6000 0x18bfcf8001fe3000

def z141 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xff80ffffff1fffff 0xffc07fffff8fffff

def z142 : W := mkw 0x003050a280000000 0x0018285140000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z143 : W := mkw 0xe83855a6af0f76f6 0xf41c2ad35787bb7b 0xfff8ffffff1fffff 0xfffc7fffff8fffff

def z144 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x3f7fe00007fd8001 0x1fbff00003fec000

def z145 : W := mkw 0xc1eeff0407ffff81 0xe0f77f8203ffffc0 0x7fffff0007ffffc1 0x3fffff8003ffffe0

def z146 : W := mkw 0x0067fa5140000000 0x0033fd28a0000000 0xfc7fffd360000000 0xfe3fffe9b0000000

def z147 : W := mkw 0x007ffafbd6900000 0x003ffd7deb480000 0xff7ffffffffc0001 0xffbffffffffe0000

def z148 : W := mkw 0x01022f00014aa001 0x8081178000a55000 0x00000f0000000000 0x0000078000000000

def z149 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xc0806cd3600399f8 0xe0403669b001ccfc

def z150 : W := mkw 0x1002280140408009 0x08011400a0204004 0x0000600300018018 0x000030018000c00c

def z151 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfcfffffffa026627 0xfe7ffffffd013313

def z152 : W := mkw 0x005580f800000000 0x002ac07c00000000 0xfc7f9ffcf8000000 0xfe3fcffe7c000000

def z153 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x9ef860e306019e19 0x4f7c30718300cf0c

def z154 : W := mkw 0x00032c5141428001 0x00019628a0a14000 0xef076cd365e38001 0xf783b669b2f1c000

def z155 : W := mkw 0x017effaa97dbe001 0x80bf7fd54bedf000 0x7f7fff2c9fffe001 0x3fbfff964ffff000

def z156 : W := mkw 0x1000000000608909 0x0800000000304484 0x0200000004e19818 0x010000000270cc0c

def z157 : W := mkw 0x0146af0001daa001 0x80a3578000ed5000 0x21078f0001fc0000 0x1083c78000fe0000

def z158 : W := mkw 0x484c85042f9e22e2 0xa426428217cf1171 0xffff9f3cfffe67e7 0xffffcf9e7fff33f3

def z159 : W := mkw 0xc09800a406b41f80 0x604c0052035a0fc0 0x9ff800e007fc1fc1 0x4ffc007003fe0fe0

def z160 : W := mkw 0x0003285140000000 0x00019428a0000000 0xec076cd360000000 0xf603b669b0000000

def z161 : W := mkw 0x017ffafbd6d1c001 0x00bffd7deb68e000 0xfe7ffffffce18000 0xff3ffffffe70c000

def z162 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x2b7f80dc05fc19c0 0x15bfc06e02fe0ce0

def z163 : W := mkw 0xa008000006015414 0x500400000300aa0a 0x0200000004019818 0x010000000200cc0c

def z164 : W := mkw 0x4847af5d790e22e2 0xa423d7aebc871171 0xf5879f3cfb1e67e7 0xfac3cf9e7d8f33f3

def z165 : W := mkw 0x014c850007dbe001 0x80a6428003edf000 0x3f7f800007ffe001 0x1fbfc00003fff000

def z166 : W := mkw 0x004eac0007d28001 0x0027560003e94000 0x7f7fec0007ff8001 0x3fbff60003ffc000

def z167 : W := mkw 0x1001045161628969 0x08008228b0b144b4 0x838000d365e399f9 0xc1c00069b2f1ccfc

def z168 : W := mkw 0x00227a0000000000 0x00113d0000000000 0x40007f0000000000 0x20003f8000000000

def z169 : W := mkw 0xc09100ffd0241f80 0x6048807fe8120fc0 0x808000fff8001fc0 0xc040007ffc000fe0

def z170 : W := mkw 0x0800010008082002 0x8400008004041001 0x0000130098006006 0x000009804c003003

def z171 : W := mkw 0xe03850a686055694 0x701c28534302ab4a 0xfff8f0ff871fffff 0xfffc787fc38fffff

def z172 : W := mkw 0x0108050007dbe001 0x8084028003edf000 0x0300000007ffe001 0x0180000003fff000

def z173 : W := mkw 0xa07cd2aa96015414 0x503e69554b00aa0a 0xdef8f3ef9e03fe3f 0xef7c79f7cf01ff1f

def z174 : W := mkw 0x00022c0001428001 0x0001160000a14000 0xef876cc305e39839 0xf7c3b66182f1cc1c

def z175 : W := mkw 0x58000504296eabeb 0xac00028214b755f5 0x0380000007ffffff 0x01c0000003ffffff

def z176 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xe5800c10631e67e7 0xf2c00608318f33f3

def z177 : W := mkw 0xc8dd80fc2eb41fe2 0x646ec07e175a0ff1 0xbfff80fcfffc1fe7 0xdfffc07e7ffe0ff3

def z178 : W := mkw 0x0001005000200900 0x0000802800100480 0xef8760d305e399f9 0xf7c3b06982f1ccfc

def z179 : W := mkw 0x10022c0021628969 0x0801160010b144b4 0x6f876c0005e399f9 0x37c3b60002f1ccfc

def z180 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x75809f00031e67e7 0x3ac04f80018f33f3

def z181 : W := mkw 0x0000040021020060 0x0000020010810030 0xf5809f3cf90201e1 0xfac04f9e7c8100f0

def z182 : W := mkw 0xc089005406b41f80 0x6044802a035a0fc0 0xaf8700d007fc1fc1 0x57c3806803fe0fe0

def z183 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xa1870cd361e019f8 0xd0c38669b0f00cfc

def z184 : W := mkw 0x08000500290a2062 0x8400028014851031 0xe5801f10f90261e7 0xf2c00f887c8130f3

def z185 : W := mkw 0x006cd00006914000 0x003668000348a000 0x7f7ff00007ffe001 0x3fbff80003fff000

def z186 : W := mkw 0x0044800000900000 0x0022400000480000 0x2107800001fc0000 0x1083c00000fe0000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x2f07000005e00001 0x1783800002f00000

def z188 : W := mkw 0x40d580fc00b40b80 0x206ac07e005a05c0 0xbd7f80fc01fc01c0 0x5ebfc07e00fe00e0

def z189 : W := mkw 0xc1fcd3ac069d7680 0xe0fe69d6034ebb40 0x1078932c021c6600 0x083c4996010e3300

def z190 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xe5870c1061e201e1 0xf2c3860830f100f0

def z191 : W := mkw 0x48c5855c29be2be2 0xa462c2ae14df15f1 0xf5879f3cfbfe67e7 0xfac3cf9e7dff33f3

def z192 : W := mkw 0xa13a7fa2874bf415 0xd09d3fd143a5fa0a 0xdef87fe38603fe3f 0xef7c3ff1c301ff1f

def z193 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x317f803c03fc07c0 0x18bfc01e01fe03e0

def z194 : W := mkw 0x08000500290a2062 0x8400028014851031 0x00000f0078000000 0x000007803c000000

def z195 : W := mkw 0x00227a03d0000000 0x00113d01e8000000 0xf400ff3ff8000000 0xfa007f9ffc000000

def z196 : W := mkw 0x1001045021628969 0x0800822810b144b4 0xaf8700d005e399f9 0x57c3806802f1ccfc

def z197 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z198 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x31009f3cfb1c67c6 0x18804f9e7d8e33e3

def z199 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x1078102082006606 0x083c081041003303

def z200 : W := mkw 0x1003285140608909 0x08019428a0304484 0xaf8760d305e199d9 0x57c3b06982f0ccec

def z201 : W := mkw 0x216eff0287dbe015 0x90b77f8143edf00a 0x7f7fff0387ffe03f 0xbfbfff81c3fff01f

def z202 : W := mkw 0x10237e53f1628969 0x0811bf29f8b144b4 0xef877fd3fde399f9 0xf7c3bfe9fef1ccfc

def z203 : W := mkw 0xa03855a2870b7414 0xd01c2ad14385ba0a 0xfff8ffe3871ffe3f 0xfffc7ff1c38fff1f

def z204 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x0078000000000000 0x003c000000000000

def z205 : W := mkw 0x2020500280014014 0x101028014000a00a 0x400070038003e03e 0xa0003801c001f01f

def z206 : W := mkw 0xc1fffafc06f5df81 0x60fffd7e037aefc0 0xbfffe0fc07fd9fc1 0x5ffff07e03fecfe0

def z207 : W := mkw 0xd0dfacfd67f69fe9 0x686fd67eb3fb4ff4 0xffffecff67ff9ff9 0xfffff67fb3ffcffc

def z208 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x887f60fff8000000 0xc43fb07ffc000000

def z209 : W := mkw 0x016cd30006996000 0x80b66980034cb000 0x3f7f930007fc6001 0x1fbfc98003fe3000

def z210 : W := mkw 0xa01800a286015414 0x500c00514300aa0a 0x828000e38603fe3f 0xc1400071c301ff1f

def z211 : W := mkw 0xc0dc80ac06b41f80 0x606e4056035a0fc0 0x13f8802c07fc1fc1 0x09fc401603fe0fe0

def z212 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x0b7f600007ffe001 0x05bfb00003fff000

def z213 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x4a7f7f0004e3e000 0x253fbf800271f000

def z214 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x8af860e384019e3e 0xc57c3071c200cf1f

def z215 : W := mkw 0x496cd3040e9d6282 0xa4b66982074eb141 0x1078932c9a1c6606 0x083c49964d0e3303

def z216 : W := mkw 0xe81005a6a90e36f6 0xf40802d354871b7b 0xf5809ffffb1e7fff 0xfac04ffffd8f3fff

def z217 : W := mkw 0x004c800006900000 0x0026400003480000 0x0a7f000004e00000 0x053f800002700000

def z218 : W := mkw 0x41c7af5c01feab81 0xa0e3d7ae00ff55c0 0x21078f1c01fc01c0 0x1083c78e00fe00e0

def z219 : W := mkw 0x48000104080c2282 0xa400008204061141 0x1000932c9a1c6606 0x080049964d0e3303

def z220 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xec7f6cd360000000 0xf63fb669b0000000

def z221 : W := mkw 0xc89100fc28241fe2 0x6448807e14120ff1 0x808000fcf8001fe6 0xc040007e7c000ff3

def z222 : W := mkw 0x00227a03d0000000 0x00113d01e8000000 0x40007f03f8000000 0xa0003f81fc000000

def z223 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xdc7870e382006606 0xee3c3871c1003303

def z224 : W := mkw 0x0066fa0000000000 0x00337d0000000000 0xfc7fff3cf8000000 0xfe3fff9e7c000000

def z225 : W := mkw 0x40cd805c06b40b80 0x2066c02e035a05c0 0x3f7f801c07fc01c1 0x1fbfc00e03fe00e0

def z226 : W := mkw 0xd1fffffd67ffffe9 0xe8fffffeb3fffff4 0xffffffff67fffff9 0xffffffffb3fffffc

def z227 : W := mkw 0xc0dd85fc07be3f80 0xe06ec2fe03df1fc0 0xffff9ffc07fe7fc1 0x7fffcffe03ff3fe0

def z228 : W := mkw 0xe1fffffe87ffff95 0xf0ffffff43ffffca 0xffffffff87ffffff 0xffffffffc3ffffff

def z229 : W := mkw 0x48000004280402e2 0x2400000214020171 0xd480103cfa0267e7 0xea40081e7d0133f3

def z230 : W := mkw 0x012a7f00074be001 0x80953f8003a5f000 0x5e787f000603e001 0x2f3c3f800301f000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x5400100002026001 0x2a00080001013000

def z232 : W := mkw 0xa17efaa286d1d415 0x50bf7d514368ea0a 0xdeff70e386e3fe3f 0xef7fb871c371ff1f

def z233 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff2087ffe627 0xffffff9043fff313

def z234 : W := mkw 0x017cd3aa96996000 0x80be69d54b4cb000 0x1078932c9a1c6000 0x083c49964d0e3000

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080002080000626 0xc040001040000313

def z236 : W := mkw 0xa07cd0a286915414 0x503e68514348aa0a 0xfffff0e387fffe3f 0xfffff871c3ffff1f

def z237 : W := mkw 0x4081005c00240b80 0x2040802e001205c0 0x0000001c000001c0 0x0000000e000000e0

def z238 : W := mkw 0xa0fdd0fa86b15d14 0x507ee87d4358ae8a 0x0a7f60c304e19818 0x053fb0618270cc0c

def z239 : W := mkw 0x1000040021628969 0x0800020010b144b4 0x0100000001e001c0 0x0080000000f000e0

def z240 : W := mkw 0xc0cd805c06b41f80 0x6066c02e035a0fc0 0x2387801c07fc1fc1 0x11c3c00e03fe0fe0

def z241 : W := mkw 0x0020500000014000 0x001028000000a000 0x400070000003e000 0x200038000001f000

def z242 : W := mkw 0x016cd700079b6000 0x80b66b8003cdb000 0x75789f00031e6001 0x3abc4f80018f3000

def z243 : W := mkw 0x1000040021628969 0x0800020010b144b4 0x0380000005e399f9 0x01c0000002f1ccfc

def z244 : W := mkw 0x001000a280000000 0x0008005140000000 0x800000e380000000 0xc0000071c0000000

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x35008000031c0001 0x1a804000018e0000

def z246 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xc0801f3cf80267e6 0xe0400f9e7c0133f3

def z247 : W := mkw 0xa03950f286215d14 0x501ca8794310ae8a 0xffff70f387e3ffff 0xffffb879c3f1ffff

def z248 : W := mkw 0x4874d7aeb90e22e2 0xa43a6bd75c871171 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z249 : W := mkw 0xd0dd84fc27f69fe9 0x686ec27e13fb4ff4 0xbfff80fc07ff9ff9 0x5fffc07e03ffcffc

def z250 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xfef8fffffe03fe3f 0xff7c7fffff01ff1f

def z251 : W := mkw 0x0066ff00010a2000 0x80337f8000851000 0x7d7fff00031e6001 0x3ebfff80018f3000

def z252 : W := mkw 0xa01100fbd0001414 0x5008807de8000a0a 0x808000fff8001e3e 0xc040007ffc000f1f

def z253 : W := mkw 0x01227a000041c001 0x00913d000020e000 0x0000600000018000 0x000030000000c000

def z254 : W := mkw 0x096eff002fdbe063 0x84b77f8017edf031 0x7f7fff00ffffe027 0xbfbfff807ffff013

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z256 : W := mkw 0x005480a800000000 0x002a405400000000 0x1078802c00000000 0x083c401600000000

def z257 : W := mkw 0xc0fdd2fe96b41f80 0x607ee97f4b5a0fc0 0xbfff93fc9ffc1fc1 0x5fffc9fe4ffe0fe0

def z258 : W := mkw 0x0108050007dbe001 0x8084028003edf000 0x77009f0007ffe001 0x3b804f8003fff000

def z259 : W := mkw 0x1077fafbd0608909 0x083bfd7de8304484 0xfe7ffffffce19818 0xff3ffffffe70cc0c

def z260 : W := mkw 0xe0fdd0fe86b55f94 0x707ee87f435aafca 0xbfffe0ff07fd9fd9 0x5ffff07f83fecfec

def z261 : W := mkw 0x1000000020200968 0x08000000101004b4 0x00800000000019f8 0x0040000000000cfc

def z262 : W := mkw 0xc0dfa8fd46b41f80 0x606fd47ea35a0fc0 0xffffecff67fc1fc1 0xfffff67fb3fe0fe0

def z263 : W := mkw 0x006efa0006014000 0x00377d000300a000 0x7e7fff000603e001 0x3f3fff800301f000

def z264 : W := mkw 0xa108050007dbf415 0xd084028003edfa0a 0x0380000007fffe3f 0x01c0000003ffff1f

def z265 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xbc7fe0ff00000000 0x5e3ff07f80000000

def z266 : W := mkw 0xb00b2c516763dd7d 0x58059628b3b1eebe 0xef876cd367e3ffff 0xf7c3b669b3f1ffff

def z267 : W := mkw 0xc81805a42f0e36e2 0xe40c02d217871b71 0xfff89ffcff1e7fe7 0xfffc4ffe7f8f3ff3

def z268 : W := mkw 0x017ffffbd7dbe001 0x80bffffdebedf000 0xff7fffffffffe001 0xffbffffffffff000

def z269 : W := mkw 0x017ffff807dbe001 0x80bffffc03edf000 0xff7ffffc07ffe001 0x7fbffffe03fff000

def z270 : W := mkw 0x08000500290a2062 0x8400028014851031 0x0000000000026026 0x0000000000013013

def z271 : W := mkw 0xd08b2c5567f69fe9 0x6845962ab3fb4ff4 0xef876cd367ff9ff9 0xf7c3b669b3ffcffc

def z272 : W := mkw 0x0057a8f940000000 0x002bd47ca0000000 0xfc7fecff60000000 0xfe3ff67fb0000000

def z273 : W := mkw 0x0066fa0000000000 0x00337d0000000000 0x7c7fff0000000000 0x3e3fff8000000000

def z274 : W := mkw 0x102b7c516763c969 0x0815be28b3b1e4b4 0xffff7cd367e3f9f9 0xffffbe69b3f1fcfc

def z275 : W := mkw 0x004c800006900000 0x0026400003480000 0x10788000021c0000 0x083c4000010e0000

def z276 : W := mkw 0x0008000006900000 0x0004000003480000 0x0300000007fc0001 0x0180000003fe0000

def z277 : W := mkw 0x404c800406940280 0x20264002034a0140 0xbfff803c07fc07c1 0x5fffc01e03fe03e0

def z278 : W := mkw 0x00022d00014aa001 0x8001168000a55000 0x7f07ff0007ffe001 0x3f83ff8003fff000

def z279 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x8180003cfb1e67e7 0xc0c0001e7d8f33f3

def z280 : W := mkw 0x007ffafbd6014000 0x003ffd7deb00a000 0xfe7ffffffe03e001 0xff3fffffff01f000

def z281 : W := mkw 0xe0b950fe86255f94 0x705ca87f4312afca 0xdef870ff8603ffff 0xef7c387fc301ffff

def z282 : W := mkw 0xa07ffafbd6015414 0x503ffd7deb00aa0a 0xfc7ffffffa006606 0xfe3ffffffd003303

def z283 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x1180932c9b1e67e7 0x08c049964d8f33f3

def z284 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x12f810208603fe3f 0x097c08104301ff1f

def z285 : W := mkw 0x48000004280402e2 0x2400000214020171 0x0000001c780001c0 0x0000000e3c0000e0

def z286 : W := mkw 0xa17cd3a286997414 0xd0be69d1434cba0a 0x10789320821c6606 0x083c4990410e3303

def z287 : W := mkw 0x490805042fdfe2e3 0xa484028217eff171 0x0380000007ffe7e7 0x01c0000003fff3f3

def z288 : W := mkw 0x0067fa5950000000 0x0033fd2ca8000000 0x7c7fff1c78000000 0x3e3fff8e3c000000

def z289 : W := mkw 0x00237a53d0000000 0x0011bd29e8000000 0xec077fd3f8000000 0xf603bfe9fc000000

def z290 : W := mkw 0x4000000400040280 0x2000000200020140 0x01800000031c07c1 0x00c00000018e03e0

def z291 : W := mkw 0x496eff042fdfe2e3 0xa4b77f8217eff171 0x7f7fff1c7fffe1c1 0x3fbfff8e3ffff0e0

def z292 : W := mkw 0x801000a000001400 0x4008005000000a00 0x808000e000001e00 0x4040007000000f00

def z293 : W := mkw 0x0000040021020060 0x0000020010810030 0x21000c10610001c0 0x10800608308000e0

def z294 : W := mkw 0x40000504010e2280 0xa000028200871140 0xf5809f3c031e67c1 0x7ac04f9e018f33e0

def z295 : W := mkw 0x0001005000200900 0x0000802800100480 0x808000d0000019c0 0x4040006800000ce0

def z296 : W := mkw 0x00022c0001428001 0x0001160000a14000 0x6f076c0005e38001 0x3783b60002f1c000

def z297 : W := mkw 0x00000003d0000000 0x00000001e8000000 0x00000003f8000000 0x80000001fc000000

def z298 : W := mkw 0x4080000400b40b80 0x20400002005a05c0 0x0100000001fc01c0 0x0080000000fe00e0

def z299 : W := mkw 0xc0f7faffd0241f80 0x607bfd7fe8120fc0 0xfcfffffff8001fc0 0xfe7ffffffc000fe0

def z300 : W := mkw 0xa03950fbd6015414 0x501ca87deb00aa0a 0xdef870fffe03fe3f 0xef7c387fff01ff1f

def z301 : W := mkw 0x0000040001020000 0x0000020000810000 0x65000c0001020001 0x3280060000810000

def z302 : W := mkw 0x21227f02814be015 0x90913f8140a5f00a 0x40007f038003e03e 0xa0003f81c001f01f

def z303 : W := mkw 0x18032d51696aa96b 0x8c0196a8b4b554b5 0xef877fd3fde3f9ff 0xf7c3bfe9fef1fcff

def z304 : W := mkw 0xb03950f3e6215d7c 0x581ca879f310aebe 0xdef870f3e603ffff 0xef7c3879f301ffff

def z305 : W := mkw 0x00337afbd0000000 0x0019bd7de8000000 0xc0007ffff8000000 0xe0003ffffc000000

def z306 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x487f7fc3f8000000 0xa43fbfe1fc000000

def z307 : W := mkw 0xa028500286015414 0x501428014300aa0a 0x428070038603fe3f 0xa1403801c301ff1f

def z308 : W := mkw 0x0077fafbd0200900 0x003bfd7de8100480 0xfffffffffde019c1 0xfffffffffef00ce0

def z309 : W := mkw 0x80fffafbd6b01d00 0x407ffd7deb580e80 0x0a7f60c304e01800 0x053fb06182700c00

def z310 : W := mkw 0xa03050a280015414 0x501828514000aa0a 0xc08070e38003fe3e 0xe0403871c001ff1f

def z311 : W := mkw 0xd0932cfd61669fe9 0x6849967eb0b34ff4 0xef876cff65e39ff9 0xf7c3b67fb2f1cffc

def z312 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x507870238203e63e 0xa83c3811c101f31f

def z313 : W := mkw 0x0177fffbd14be001 0x80bbfffde8a5f000 0xfc7ffffff803e000 0xfe3ffffffc01f000

def z314 : W := mkw 0x0075d0fa80000000 0x003ae87d40000000 0xfc7ff0ff80000000 0xfe3ff87fc0000000

def z315 : W := mkw 0x0028500006014000 0x001428000300a000 0xdef870c30603f839 0xef7c38618301fc1c

def z316 : W := mkw 0x48000104080c2282 0xa400008204061141 0xd480932c9a1e6627 0xea4049964d0f3313

def z317 : W := mkw 0x1047ae5971628969 0x0823d72cb8b144b4 0xef87efdf7de399f9 0xf7c3f7efbef1ccfc

def z318 : W := mkw 0x2000000280000014 0x100000014000000a 0x000000038000003e 0x80000001c000001f

def z319 : W := mkw 0xa01000a280001414 0x5008005140000a0a 0xce8060e384039e3f 0xe7403071c201cf1f

def z320 : W := mkw 0x48000004280402e2 0x2400000214020171 0xb580803cfb1c07e7 0xdac0401e7d8e03f3

def z321 : W := mkw 0xa07efaa286015414 0x503f7d514300aa0a 0xfeffffe38603fe3f 0xff7ffff1c301ff1f

def z322 : W := mkw 0xc1dd85fc07ffff81 0xe0eec2fe03ffffc0 0xbfff80fc07ffffc1 0x5fffc07e03ffffe0

def z323 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x0af860c30603fe3f 0x057c30618301ff1f

def z324 : W := mkw 0x0003285140000000 0x00019428a0000000 0x080760c300000000 0x0403b06180000000

def z325 : W := mkw 0xe8fdd5feafbf7ff6 0xf47eeaff57dfbffb 0xffffffffffffffff 0xffffffffffffffff

def z326 : W := mkw 0xb01100f3e0201d7c 0x58088079f0100ebe 0x808000f3e0001ffe 0xc0400079f0000fff

def z327 : W := mkw 0x48010554292e2be2 0xa40082aa149715f1 0xff879ffcfffe7fe7 0xffc3cffe7fff3ff3

def z328 : W := mkw 0xc8dd85fc2fbe3fe2 0xe46ec2fe17df1ff1 0xbfff8ffc7ffc1fc1 0x5fffc7fe3ffe0fe0

def z329 : W := mkw 0x005580f800000000 0x002ac07c00000000 0x087f00c000000000 0x043f806000000000

def z330 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xaf870cd065e019c1 0x57c3866832f00ce0

def z331 : W := mkw 0x10227e03f1428069 0x08113f01f8a14034 0x40007f03f8038038 0xa0003f81fc01c01c

def z332 : W := mkw 0x016efe0007d3c001 0x00b77f0003e9e000 0x6f7f6c0005e38001 0x37bfb60002f1c000

def z333 : W := mkw 0xc0cc800406b41f80 0x60664002035a0fc0 0x3fff800007fc1fc1 0x1fffc00003fe0fe0

def z334 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xd5801020831e67e7 0xeac00810418f33f3

def z335 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xb580803c031e67e7 0x5ac0401e018f33f3

def z336 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x187ff3ef98000000 0x0c3ff9f7cc000000

def z337 : W := mkw 0x116fff5147fbe909 0x88b7ffa8a3fdf484 0x7f7fffc307fff819 0x3fbfffe183fffc0c

def z338 : W := mkw 0x0076faabd0000000 0x003b7d55e8000000 0x5078ff2ff8000000 0xa83c7f97fc000000

def z339 : W := mkw 0xa17cd3a286997414 0xd0be69d1434cba0a 0xdef8f3e3861ffe3f 0xef7c79f1c30fff1f

def z340 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x7c7fffc300000000 0x3e3fffe180000000

def z341 : W := mkw 0x48c5855c29be2be2 0xa462c2ae14df15f1 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z342 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xaf8700fc05e01fc1 0x57c3807e02f00fe0

def z343 : W := mkw 0xd088040427f69fe9 0x6844020213fb4ff4 0x0380000007ff9ff9 0x01c0000003ffcffc

def z344 : W := mkw 0xb03b7cf3e763dd7d 0x581dbe79f3b1eebe 0xefff6cd365e399f9 0xf7ffb669b2f1ccfc

def z345 : W := mkw 0x005580fbd0000000 0x002ac07de8000000 0xbc7f80fff8000000 0xde3fc07ffc000000

def z346 : W := mkw 0x0146af0001daa001 0x80a3578000ed5000 0x6f07ef0005ff8001 0x3783f78002ffc000

def z347 : W := mkw 0x00022c0001428001 0x0001160000a14000 0x40006c0000038000 0x200036000001c000

def z348 : W := mkw 0x1003285140608909 0x08019428a0304484 0x0007000000e00000 0x0003800000700000

def z349 : W := mkw 0x801800a006001400 0x400c005003000a00 0xdef860e306039e39 0xef7c30718301cf1c

def z350 : W := mkw 0x003050a280000000 0x0018285140000000 0x1078102080000000 0x083c081040000000

def z351 : W := mkw 0x30237c53e163c97d 0x1811be29f0b1e4be 0xef877cd3e5e3f9ff 0xf7c3be69f2f1fcff

def z352 : W := mkw 0x0066fe0001428001 0x00337f0000a14000 0x7f7fff0005e38001 0x3fbfff8002f1c000

def z353 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x0b8760c305e399f9 0x05c3b06182f1ccfc

def z354 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x9ef810e086007e07 0x4f7c087043003f03

def z355 : W := mkw 0x40c5805c00b40b80 0x2062c02e005a05c0 0xb587803c03fc07c1 0x5ac3c01e01fe03e0

def z356 : W := mkw 0x0000040021020060 0x0000020010810030 0x01800000010201e1 0x00c00000008100f0

def z357 : W := mkw 0xc088000406b41f80 0x60440002035a0fc0 0xb780803c07fc1fc1 0x5bc0401e03fe0fe0

def z358 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xb58080fc031c1fc1 0x5ac0407e018e0fe0

def z359 : W := mkw 0x0044800000000000 0x0022400000000000 0x3c7f800000000000 0x1e3fc00000000000

def z360 : W := mkw 0xa01000a280001414 0x5008005140000a0a 0x0000002080000606 0x0000001040000303

def z361 : W := mkw 0x11237f51616be969 0x8891bfa8b0b5f4b4 0xef877fd365e3f9f9 0xf7c3bfe9b2f1fcfc

def z362 : W := mkw 0x48000104080c2282 0xa400008204061141 0x0000830c181c0000 0x000041860c0e0000

def z363 : W := mkw 0x00227a03d0000000 0x00113d01e8000000 0x0000600300000000 0x0000300180000000

def z364 : W := mkw 0x5801005568240bea 0x2c00802ab41205f5 0x808000fff8001ffe 0xc040007ffc000fff

def z365 : W := mkw 0x80dd80f806b01d00 0x406ec07c03580e80 0x9eff00e006e01e01 0x4f7f807003700f00

def z366 : W := mkw 0x001000aa90000000 0x0008005548000000 0x0000002c98000000 0x000000164c000000

def z367 : W := mkw 0x1003285140608909 0x08019428a0304484 0xee076cd364e19818 0xf703b669b270cc0c

def z368 : W := mkw 0x116fff5167fbe969 0x88b7ffa8b3fdf4b4 0x7f7fff1067ffe1c1 0x3fbfff8833fff0e0

def z369 : W := mkw 0x08000500290a2062 0x8400028014851031 0xd4801f20fa026627 0xea400f907d013313

def z370 : W := mkw 0x00032c5161020060 0x00019628b0810030 0xed876cd3610201e1 0xf6c3b669b08100f0

def z371 : W := mkw 0xc0fdd0fc06b55f80 0x607ee87e035aafc0 0xfffff0fc07ffffc1 0x7ffff87e03ffffe0

def z372 : W := mkw 0xa07ffafbd6015414 0x503ffd7deb00aa0a 0xdeff70e38603fe3f 0xef7fb871c301ff1f

def z373 : W := mkw 0x0057aafbd0000000 0x002bd57de8000000 0xa0078ffff8000000 0xd003c7fffc000000

def z374 : W := mkw 0x90dfa8f946f09d09 0x486fd47ca3784e84 0x0a7f60c304e19818 0x053fb0618270cc0c

def z375 : W := mkw 0x490805042fdfe2e3 0xa484028217eff171 0xf7809f3cffffe7e7 0xfbc04f9e7ffff3f3

def z376 : W := mkw 0x0002280140000000 0x00011400a0000000 0x40006c0360000000 0xa0003601b0000000

def z377 : W := mkw 0xc0fdd0fe86b41f80 0x607ee87f435a0fc0 0xfffff0ff87fc1fc1 0xfffff87fc3fe0fe0

def z378 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xf5009f3cf91c01c0 0xfa804f9e7c8e00e0

def z379 : W := mkw 0x014eaf0007daa001 0x80a7578003ed5000 0x3f7f8f0007fc0001 0x1fbfc78003fe0000

def z380 : W := mkw 0x016fff5147dbe001 0x80b7ffa8a3edf000 0xff7fffd367ffe001 0xffbfffe9b3fff000

def z381 : W := mkw 0x805c80a006901400 0x402e405003480a00 0xbfff80e007fc1e01 0x5fffc07003fe0f00

def z382 : W := mkw 0x40f7faffd0b40b80 0x207bfd7fe85a05c0 0xfd7ffffff9fc01c0 0xfebffffffcfe00e0

def z383 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x23870c1065e399f9 0x11c3860832f1ccfc

def z384 : W := mkw 0x001328fbd0000000 0x0009947de8000000 0xec076cfff8000000 0xf603b67ffc000000

def z385 : W := mkw 0xc0dd80fc06941680 0x606ec07e034a0b40 0xbc7f80fc021c0600 0x5e3fc07e010e0300

def z386 : W := mkw 0x014eaf0007dbe001 0x80a7578003edf000 0x23078f0007ffe001 0x1183c78003fff000

def z387 : W := mkw 0x0067fa5bd0000000 0x0033fd2de8000000 0x6007ff1ff8000000 0xb003ff8ffc000000

def z388 : W := mkw 0xc0dd80ffd6b41f80 0x606ec07feb5a0fc0 0xbfff80fffffc1fc1 0xdfffc07ffffe0fe0

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0xd400102080000000 0xea00081040000000

def z390 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x01000000011c01c0 0x00800000008e00e0

def z391 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x5e7870c30603f819 0x2f3c38618301fc0c

def z392 : W := mkw 0x1077fefbf1628969 0x083bff7df8b144b4 0xfd7ffffff9e001c0 0xfebffffffcf000e0

def z393 : W := mkw 0xc0dc80ac06941680 0x606e4056034a0b40 0x9ef880ec061c1e01 0x4f7c4076030e0f00

def z394 : W := mkw 0xa000000000001414 0x5000000000000a0a 0x0080000000001e3e 0x0040000000000f1f

def z395 : W := mkw 0x116ffe5167f3c969 0x08b7ff28b3f9e4b4 0xefff6cd365e399f9 0xf7ffb669b2f1ccfc

def z396 : W := mkw 0x0066fa0000000000 0x00337d0000000000 0x087f600000000000 0x043fb00000000000

def z397 : W := mkw 0x8008000006001400 0x4004000003000a00 0x0280000006001e01 0x0140000003000f00

def z398 : W := mkw 0xa03854a2a7035474 0x501c2a515381aa3a 0xfff87cf3e703ffff 0xfffc3e79f381ffff

def z399 : W := mkw 0x110b2d5167fbe969 0x888596a8b3fdf4b4 0xef876cd367fff9f9 0xf7c3b669b3fffcfc

def z400 : W := mkw 0x18022d01694aa06b 0x8c011680b4a55035 0x40007f03f803e03e 0xa0003f81fc01f01f

def z401 : W := mkw 0x80dc80a806901400 0x406e405403480a00 0x0078000000000000 0x003c000000000000

def z402 : W := mkw 0x801800a006001400 0x400c005003000a00 0x1078002002000600 0x083c001001000300

def z403 : W := mkw 0x116eff0167dbe069 0x88b77f80b3edf034 0x7f7fff0367ffe039 0xbfbfff81b3fff01c

def z404 : W := mkw 0xc0fffaffd6b41f80 0x607ffd7feb5a0fc0 0xbfffe0ff07fc1fc1 0x5ffff07f83fe0fe0

def z405 : W := mkw 0x20227a03d0014014 0x10113d01e800a00a 0x40007f03f803e03e 0xa0003f81fc01f01f

def z406 : W := mkw 0xc09900fc06241f80 0x604c807e03120fc0 0x9ef800fc06001fc1 0x4f7c007e03000fe0

def z407 : W := mkw 0xe80805042f0f76f6 0xf40402821787bb7b 0x03800000071fffff 0x01c00000038fffff

def z408 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x5e7f700006e3e001 0x2f3fb8000371f000

def z409 : W := mkw 0x10022c0161428069 0x08011600b0a14034 0x00000c0060000000 0x0000060030000000

def z410 : W := mkw 0x481100fff80402e2 0x2408807ffc020171 0x808000fff80007e6 0xc040007ffc0003f3

def z411 : W := mkw 0xc8dd81fc0ebc3f82 0xe46ec0fe075e1fc1 0xbfff93fc9ffc7fc7 0x5fffc9fe4ffe3fe3

def z412 : W := mkw 0x596fff556fffebeb 0xacb7ffaab7fff5f5 0xffffffffffffffff 0xffffffffffffffff

def z413 : W := mkw 0x482855042f0f62e2 0xa4142a821787b171 0xfff8ff3cff1fe7e7 0xfffc7f9e7f8ff3f3

def z414 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfefffffffc039839 0xff7ffffffe01cc1c

def z415 : W := mkw 0x08227f03f90a2062 0x84113f81fc851031 0x40007f03f8026026 0xa0003f81fc013013

def z416 : W := mkw 0x0045805800000000 0x0022c02c00000000 0x2007801c00000000 0x1003c00e00000000

def z417 : W := mkw 0x0002280000408001 0x0001140000204000 0x0a07600004e18000 0x0503b0000270c000

def z418 : W := mkw 0x1077fafbd0608909 0x083bfd7de8304484 0x0a7f60c304e19818 0x053fb0618270cc0c

def z419 : W := mkw 0x496eff042fdfe2e3 0xa4b77f8217eff171 0x7fffff0007ffe7e7 0x3fffff8003fff3f3

def z420 : W := mkw 0x10032d51616aa969 0x880196a8b0b554b4 0xff87ffd367fff9f9 0xffc3ffe9b3fffcfc

def z421 : W := mkw 0xb07ffefbf763dd7d 0x583fff7dfbb1eebe 0xffffffffffe3ffff 0xfffffffffff1ffff

def z422 : W := mkw 0xb03854a2a763dd7d 0x581c2a5153b1eebe 0xdff870e387e3ffff 0xeffc3871c3f1ffff

def z423 : W := mkw 0x0020500280000000 0x0010280140000000 0x4000700380000000 0xa0003801c0000000

def z424 : W := mkw 0x016fff5957dbe001 0x80b7ffacabedf000 0x7f7fff1c7fffe001 0x3fbfff8e3ffff000

def z425 : W := mkw 0x4800000408040282 0x2400000204020141 0x0000002c98000606 0x000000164c000303

def z426 : W := mkw 0x4877fafff80402e2 0x243bfd7ffc020171 0xfcfffffff80007e6 0xfe7ffffffc0003f3

def z427 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x75009f1c7b1e61c1 0x3a804f8e3d8f30e0

def z428 : W := mkw 0xc188050407ffff81 0xe0c4028203ffffc0 0x0380000007ffffc1 0x01c0000003ffffe0

def z429 : W := mkw 0x0001005140000000 0x00008028a0000000 0x800000d360000000 0xc0000069b0000000

def z430 : W := mkw 0x496cd7042f9f62e2 0xa4b66b8217cfb171 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z431 : W := mkw 0x58010555692e2bea 0xac0082aab49715f5 0xf5809ffffb1e7fff 0xfac04ffffd8f3fff

def z432 : W := mkw 0x0166ff0001dbe001 0x80b37f8000edf000 0x6107ff0001ffe000 0x3083ff8000fff000

def z433 : W := mkw 0xe0dd80fc06b55f94 0x706ec07e035aafca 0xbfff80fc07ffffff 0x5fffc07e03ffffff

def z434 : W := mkw 0x0877fffbf90a2062 0x843bfffdfc851031 0xfc7ffffff8026026 0xfe3ffffffc013013

def z435 : W := mkw 0x0077fefbd1428001 0x003bff7de8a14000 0xff7ffffffde38001 0xffbffffffef1c000

def z436 : W := mkw 0x817effa007dbf401 0xc0bf7fd003edfa00 0xffffffe007fffe01 0x7ffffff003ffff00

def z437 : W := mkw 0x1000040021428069 0x0800020010a14034 0x0000000000038038 0x000000000001c01c

def z438 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xed076cd361e001c0 0xf683b669b0f000e0

def z439 : W := mkw 0x4000000400040280 0x2000000200020140 0xf5809f3cfb1c07c1 0xfac04f9e7d8e03e0

def z440 : W := mkw 0x0008000006000000 0x0004000003000000 0x1e78000006000001 0x0f3c000003000000

def z441 : W := mkw 0x01227f00014be001 0x80913f8000a5f000 0x7500ff00031fe001 0x3a807f80018ff000

def z442 : W := mkw 0x807ffafbd6001400 0x403ffd7deb000a00 0xfefffffffe001e01 0xff7fffffff000f00

def z443 : W := mkw 0x48032d55690e22e2 0xa40196aab4871171 0xfd87fffffb1e67e7 0xfec3fffffd8f33f3

def z444 : W := mkw 0xa03b78f3c6015414 0x501dbc79e300aa0a 0xfeff7cf3e603fe3f 0xff7fbe79f301ff1f

def z445 : W := mkw 0xa008000006015414 0x500400000300aa0a 0xce8060c30603fe3f 0xe74030618301ff1f

def z446 : W := mkw 0x0075d2fbd0000000 0x003ae97de8000000 0x907893fff8000000 0xc83c49fffc000000

def z447 : W := mkw 0x58032d55696eabeb 0xac0196aab4b755f5 0xf5879f3cfbfe67e7 0xfac3cf9e7dff33f3

def z448 : W := mkw 0x40c5805c00b40b80 0x2062c02e005a05c0 0xaf8780dc05fc19c1 0x57c3c06e02fe0ce0

def z449 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x4a7870c38403f83e 0xa53c3861c201fc1f

def z450 : W := mkw 0x497fffffffdfe2e3 0xa4bfffffffeff171 0xffffffffffffe7e7 0xfffffffffffff3f3

def z451 : W := mkw 0x1108050027fbe969 0x8884028013fdf4b4 0x0380000007fff9f9 0x01c0000003fffcfc

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x808000c300001838 0xc040006180000c1c

def z453 : W := mkw 0x1001005160200968 0x08008028b01004b4 0xce8060d3640399f9 0xe7403069b201ccfc

def z454 : W := mkw 0xc9fffffc2fffffe3 0xe4fffffe17fffff1 0xfffffffcffffffe7 0xfffffffe7ffffff3

def z455 : W := mkw 0x0076faa280000000 0x003b7d5140000000 0xfc7fffe380000000 0xfe3ffff1c0000000

def z456 : W := mkw 0xb03a7ca3e743d47d 0x581d3e51f3a1ea3e 0xdef87ce3e603fe3f 0xef7c3e71f301ff1f

def z457 : W := mkw 0xc88805042fbe3fe2 0xe444028217df1ff1 0xf7809f3cfffe7fe7 0xfbc04f9e7fff3ff3

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a0060c304019818 0x050030618200cc0c

def z459 : W := mkw 0x50032c5561668be9 0x2801962ab0b345f4 0xff87ecff67ff9ff9 0xffc3f67fb3ffcffc

def z460 : W := mkw 0x1003285160200968 0x08019428b01004b4 0xec876cd3600019f8 0xf643b669b0000cfc

def z461 : W := mkw 0x48000104080c2282 0xa400008204061141 0x00000000021c6606 0x00000000010e3303

def z462 : W := mkw 0x0077fffbd10a2000 0x803bfffde8851000 0xfd7ffffffb1e6001 0xfebffffffd8f3000

def z463 : W := mkw 0x00022c0021428061 0x0001160010a14030 0xef876c1065e381e1 0xf7c3b60832f1c0f0

def z464 : W := mkw 0xe0fdd0fe86b55f94 0x707ee87f435aafca 0xbfff90fc87fc7fc7 0x5fffc87e43fe3fe3

def z465 : W := mkw 0x0120530000096000 0x809029800004b000 0x0000130000006000 0x0000098000003000

def z466 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x6f076c1065e381c1 0x3783b60832f1c0e0

def z467 : W := mkw 0xe81000a6a80416f6 0x7408005354020b7b 0x808000fff8001ffe 0xc040007ffc000fff

def z468 : W := mkw 0x80dd80f806b01d00 0x406ec07c03580e80 0xbe7f80fc04e01800 0x5f3fc07e02700c00

def z469 : W := mkw 0xa16eff0007dbf415 0xd0b77f8003edfa0a 0x7fffff0007fffe3f 0x3fffff8003ffff1f

def z470 : W := mkw 0xb03b78f3c661dd1d 0x581dbc79e330ee8e 0xdeff70e386e3fe3f 0xef7fb871c371ff1f

def z471 : W := mkw 0x0003285140000000 0x00019428a0000000 0x20070c1060000000 0x1003860830000000

def z472 : W := mkw 0xc0fffaffd6941680 0x607ffd7feb4a0b40 0xfc7ffffffa1c0600 0xfe3ffffffd0e0300

def z473 : W := mkw 0x00285500070b6000 0x80142a800385b000 0x7f78ff00071fe001 0x3fbc7f80038ff000

def z474 : W := mkw 0xc0d580fc00241f80 0x606ac07e00120fc0 0xbcff80fc00001fc0 0x5e7fc07e00000fe0

def z475 : W := mkw 0xc8ffffffffbe3fe2 0xe47fffffffdf1ff1 0xfffffffffffe7fe7 0xffffffffffff3ff3

def z476 : W := mkw 0x002a7c000743c001 0x00153e0003a1e000 0x7f7f7c0007e3e001 0x3fbfbe0003f1f000

def z477 : W := mkw 0x48022d04294ea2e3 0xa401168214a75171 0xff87ff3cffffe7e7 0xffc3ff9e7ffff3f3

def z478 : W := mkw 0x0000040021020060 0x0000020010810030 0x40000c0060020020 0xa000060030010010

def z479 : W := mkw 0xc8dc85ac2f9e36e2 0xe46e42d617cf1b71 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z480 : W := mkw 0xa008000006015414 0x500400000300aa0a 0x0000000002006606 0x0000000001003303

def z481 : W := mkw 0xc0dc80ac06941680 0x606e4056034a0b40 0xb5f8803c031c07c1 0x5afc401e018e03e0

def z482 : W := mkw 0x017ffffbd7dbe001 0x80bffffdebedf000 0x7f7fffc307ffe001 0x3fbfffe183fff000

def z483 : W := mkw 0xe83851a68e0d7696 0xf41c28d34706bb4b 0xdef8f3ef9e1ffe3f 0xef7c79f7cf0fff1f

def z484 : W := mkw 0x40000404210602e0 0x2000020210830170 0xf5808c3c631e07e1 0xfac0461e318f03f0

def z485 : W := mkw 0x11227f01614be069 0x88913f80b0a5f034 0x40007f036003e038 0xa0003f81b001f01c

def z486 : W := mkw 0x30227c03e143c07d 0x18113e01f0a1e03e 0x40007c03e003e03e 0xa0003e01f001f01f

def z487 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x61076c1361e381f8 0xb083b609b0f1c0fc

def z488 : W := mkw 0x4946af0429dea2e3 0xa4a3578214ef5171 0xf5879f3cfbfe67e7 0xfac3cf9e7dff33f3

def z489 : W := mkw 0xd0dfa8fd46f49f89 0x686fd47ea37a4fc4 0xbfffe0ff07fd9fd9 0x5ffff07f83fecfec

def z490 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff3cffffe001 0xffbfff9e7ffff000

def z491 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x90f810e382007e3e 0xc87c0871c1003f1f

def z492 : W := mkw 0x08000500290a2062 0x8400028014851031 0x75009f00fb1e6027 0xba804f807d8f3013

def z493 : W := mkw 0x50c7ac5d61f68be9 0x2863d62eb0fb45f4 0x21078c1c61fc01c0 0x1083c60e30fe00e0

def z494 : W := mkw 0x0000040021020060 0x0000020010810030 0xef806cd3650399f9 0xf7c03669b281ccfc

def z495 : W := mkw 0x41efff5c07ffeb81 0xa0f7ffae03fff5c0 0x7f7fff1c07ffe1c1 0x3fbfff8e03fff0e0

def z496 : W := mkw 0x001100f800000000 0x0008807c00000000 0x800000fc00000000 0x4000007e00000000

def z497 : W := mkw 0x1057acf961628969 0x082bd67cb0b144b4 0xffffecff65e399f9 0xfffff67fb2f1ccfc

def z498 : W := mkw 0x28205502a90b6076 0x94102a815485b03b 0x40007f03f803e03e 0xa0003f81fc01f01f

def z499 : W := mkw 0x0146aa0000d08001 0x00a3550000684000 0x0007000000e00000 0x0003800000700000

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x0280000004039839 0x014000000201cc1c

def z501 : W := mkw 0x48227f07f90e22e2 0xa4113f83fc871171 0xf580ff3ffb1e67e7 0xfac07f9ffd8f33f3

def z502 : W := mkw 0x4874d3ae980c2282 0xa43a69d74c061141 0x1078932c9a1c6606 0x083c49964d0e3303

def z503 : W := mkw 0xe83855a6af0f76f6 0xf41c2ad35787bb7b 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z504 : W := mkw 0xe0fcd0ae86955694 0x707e6857434aab4a 0xdef8f0ef861ffe3f 0xef7c7877c30fff1f

def z505 : W := mkw 0x00000500010a2000 0x8000028000851000 0xf5009f3cfb1e6001 0xfa804f9e7d8f3000

def z506 : W := mkw 0x0000000000200900 0x0000000000100480 0x0380000005e019c1 0x01c0000002f00ce0

def z507 : W := mkw 0x483055a6a90e22e2 0xa4182ad354871171 0xfdf8fffffb1e67e7 0xfefc7ffffd8f33f3

def z508 : W := mkw 0xa17efaa286d1d415 0x50bf7d514368ea0a 0x0a7f60c304e19818 0x053fb0618270cc0c

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000600300038038 0xa00030018001c01c

def z510 : W := mkw 0x116eff0027fbe969 0x88b77f8013fdf4b4 0x7fffff0007fff9f9 0x3fffff8003fffcfc

def z511 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffffe0ff07ff9ff9 0xfffff07f83ffcffc

def z512 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc0060c300000000 0xe600306180000000

def z513 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x1a7ff30006fde000 0x0d3ff980037ef000

def z514 : W := mkw 0x0047aa5950000000 0x0023d52ca8000000 0xf4079f3cf8000000 0xfa03cf9e7c000000

def z515 : W := mkw 0x2077fafbd0014014 0x103bfd7de800a00a 0xfc7ffffff803e03e 0xfe3ffffffc01f01f

def z516 : W := mkw 0x0047aa5950000000 0x0023d52ca8000000 0x0007000000000000 0x0003800000000000

def z517 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff87fffffde399f9 0xffc3fffffef1ccfc

def z518 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0xffffff1067ffe1e1 0xffffff8833fff0f0

def z519 : W := mkw 0x117ffffbf7fbe969 0x88bffffdfbfdf4b4 0xfffffffffffff9f9 0xfffffffffffffcfc

def z520 : W := mkw 0x017ffafbd6d1c001 0x00bffd7deb68e000 0x0a7f60c304e18000 0x053fb0618270c000

def z521 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x0bff00c007fc1fc1 0x05ff806003fe0fe0

def z522 : W := mkw 0x4877fbffd80c2282 0xa43bfdffec061141 0xfc7ffffffa1c6606 0xfe3ffffffd0e3303

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000102082006606 0x0800081041003303

def z524 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xdc78f3ef98000000 0xee3c79f7cc000000

def z525 : W := mkw 0x2020500280014014 0x101028014000a00a 0x0000100080006006 0x0000080040003003

def z526 : W := mkw 0xe088000406b55f94 0x70440002035aafca 0x0380000007ffffff 0x01c0000003ffffff

def z527 : W := mkw 0x0000010000082000 0x8000008000041000 0x10009300021c6000 0x08004980010e3000

def z528 : W := mkw 0xc1fdd3fc06bd7f80 0xe0fee9fe035ebfc0 0xbfff93fc07fc7fc1 0x5fffc9fe03fe3fe0

def z529 : W := mkw 0x4077faffd0040280 0x203bfd7fe8020140 0xfdfffffffb1c07c1 0xfefffffffd8e03e0

def z530 : W := mkw 0x0144830000982000 0x80a24180004c1000 0x00008300001c0000 0x00004180000e0000

def z531 : W := mkw 0x003378f3c0000000 0x0019bc79e0000000 0xfc7f7cf3e0000000 0xfe3fbe79f0000000

def z532 : W := mkw 0xa077fafbd0001414 0x503bfd7de8000a0a 0xfcfffffff8001e3e 0xfe7ffffffc000f1f

def z533 : W := mkw 0x81fffaf806f1dd01 0x40fffd7c0378ee80 0x0a7f60c004e19800 0x053fb0600270cc00

def z534 : W := mkw 0x4877fffff90e22e2 0xa43bfffffc871171 0xfd7ffffff91c01c0 0xfebffffffc8e00e0

def z535 : W := mkw 0xc0dfacfc07f69f81 0x606fd67e03fb4fc0 0xffffecfc07ff9fc1 0x7ffff67e03ffcfe0

def z536 : W := mkw 0x0800000028000062 0x0400000014000031 0x00000000f8000026 0x800000007c000013

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0xa5800010010001c1 0x52c00008008000e0

def z538 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5078ff00021fe000 0x283c7f80010ff000

def z539 : W := mkw 0x010a2d0007dbe001 0x8085168003edf000 0x6f076c0007ffe001 0x3783b60003fff000

def z540 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xd4f8102082026627 0xea7c081041013313

def z541 : W := mkw 0x08000500290a2062 0x8400028014851031 0xf4009f3cf8026026 0xfa004f9e7c013013

def z542 : W := mkw 0xc1feffac07dff681 0xe0ff7fd603effb40 0x7f7fff2c07ffe601 0x3fbfff9603fff300

def z543 : W := mkw 0x58032d55696eabeb 0xac0196aab4b755f5 0xef87efdf7dff99f9 0xf7c3f7efbeffccfc

def z544 : W := mkw 0x801800a006001400 0x400c005003000a00 0xdef810e086027e27 0xef7c087043013f13

def z545 : W := mkw 0x0001005950000000 0x0000802ca8000000 0x0000001c78000000 0x0000000e3c000000

def z546 : W := mkw 0x0046aa0000000000 0x0023550000000000 0x20078f0000000000 0x1003c78000000000

def z547 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xde7870e384019818 0xef3c3871c200cc0c

def z548 : W := mkw 0x10337cf3e1628969 0x0819be79f0b144b4 0xffff7cf3e5e399f9 0xffffbe79f2f1ccfc

def z549 : W := mkw 0x2000000000014014 0x100000000000a00a 0x000000000003e03e 0x000000000001f01f

def z550 : W := mkw 0x10032c5141628909 0x08019628a0b14484 0x6f076cc305e39819 0x3783b66182f1cc0c

def z551 : W := mkw 0xa03a7ca28743d415 0x501d3e5143a1ea0a 0xffff7ce387e3fe3f 0xffffbe71c3f1ff1f

def z552 : W := mkw 0x1147af5161faa969 0x88a3d7a8b0fd54b4 0x21078f1061fc01c0 0x1083c78830fe00e0

def z553 : W := mkw 0x0002280000000000 0x0001140000000000 0x6c076c0000000000 0x3603b60000000000

def z554 : W := mkw 0x016fff5007fbe901 0x80b7ffa803fdf480 0xffffffd007fff9c1 0x7fffffe803fffce0

def z555 : W := mkw 0x005580f800200900 0x002ac07c00100480 0xbfff80fc05e019c1 0x5fffc07e02f00ce0

def z556 : W := mkw 0xe97effa6afdff6f7 0xf4bf7fd357effb7b 0xffffffffffffffff 0xffffffffffffffff

def z557 : W := mkw 0x0077fefbf1020060 0x003bff7df8810030 0xfdfffffff90201e1 0xfefffffffc8100f0

def z558 : W := mkw 0x003050a280000000 0x0018285140000000 0xdef870e384039839 0xef7c3871c201cc1c

def z559 : W := mkw 0xc0dc80ac06941680 0x606e4056034a0b40 0x3f7f802c07fc0601 0x1fbfc01603fe0300

def z560 : W := mkw 0xb00804002763dd7d 0x5804020013b1eebe 0x0380000007e3ffff 0x01c0000003f1ffff

def z561 : W := mkw 0x40c4800c00940280 0x20624006004a0140 0x0000800c001c0000 0x00004006000e0000

def z562 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x7e7fff0004e18000 0x3f3fff800270c000

def z563 : W := mkw 0x0076faaa90000000 0x003b7d5548000000 0x7c7fff2c98000000 0x3e3fff964c000000

def z564 : W := mkw 0x0000040021020060 0x0000020010810030 0xf5801c30e30267e7 0xfac00e18718133f3

def z565 : W := mkw 0x58022d05694ea2eb 0xac011682b4a75175 0xf580ff3ffb1fe7ff 0xfac07f9ffd8ff3ff

def z566 : W := mkw 0xa01800a006015414 0x500c00500300aa0a 0x9ef800e00603fe3f 0x4f7c00700301ff1f

def z567 : W := mkw 0x00000500210a2060 0x8000028010851030 0xf5809f10631e61e1 0xfac04f88318f30f0

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0xde8070e38603fe3f 0xef403871c301ff1f

def z569 : W := mkw 0xb17ffff3e7fbfd7d 0xd8bffff9f3fdfebe 0xfffffff3e7ffffff 0xfffffff9f3ffffff

def z570 : W := mkw 0x801900f006201d00 0x400c807803100e80 0xbfff00f007e01fc1 0x5fff807803f00fe0

def z571 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xdc7f70e380000000 0xee3fb871c0000000

def z572 : W := mkw 0xd0fffefff7f69fe9 0x687fff7ffbfb4ff4 0xffffffffffff9ff9 0xffffffffffffcffc

def z573 : W := mkw 0x90dfacf967f29d69 0x486fd67cb3f94eb4 0xefff6cd365e399f9 0xf7ffb669b2f1ccfc

def z574 : W := mkw 0x901b2cf167629d69 0x480d9678b3b14eb4 0xffff6cf367e39ff9 0xffffb679b3f1cffc

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x20008f1c78000000 0x1000478e3c000000

def z576 : W := mkw 0xa07cd2aa96015414 0x503e69554b00aa0a 0x1078932c9a006606 0x083c49964d003303

def z577 : W := mkw 0x00000500010a2000 0x8000028000851000 0x40001f0000026000 0x20000f8000013000

def z578 : W := mkw 0xb03b78f3c661dd1d 0x581dbc79e330ee8e 0x0a7f60c304e19818 0x053fb0618270cc0c

def z579 : W := mkw 0xa0fdd0fa86b15d14 0x507ee87d4358ae8a 0xdeff70e386e3fe3f 0xef7fb871c371ff1f

def z580 : W := mkw 0x58032d55696eabeb 0xac0196aab4b755f5 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z581 : W := mkw 0xa07ffafbd6015414 0x503ffd7deb00aa0a 0xfe7ffffffc019818 0xff3ffffffe00cc0c

def z582 : W := mkw 0x01000500014be001 0x8080028000a5f000 0x000000000003e000 0x000000000001f000

def z583 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x1a7870e38601fe1e 0x0d3c3871c300ff0f

def z584 : W := mkw 0x496eff040fdfe283 0xa4b77f8207eff141 0x7f7fff2c9fffe607 0x3fbfff964ffff303

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x9480002002000601 0x4a40001001000300

def z586 : W := mkw 0x016cd30006996000 0x80b66980034cb000 0x5e78f300061fe001 0x2f3c7980030ff000

def z587 : W := mkw 0x017ffbfbd6996000 0x80bffdfdeb4cb000 0xfc7ffffffa1c6000 0xfe3ffffffd0e3000

def z588 : W := mkw 0xa03050a280001414 0x5018285140000a0a 0xdcf870e380001e3e 0xee7c3871c0000f1f

def z589 : W := mkw 0xd0dd80fd66b41fe8 0x686ec07eb35a0ff4 0xbfff80ff67fc1ff9 0xdfffc07fb3fe0ffc

def z590 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x50009f2cfa1e6626 0xa8004f967d0f3313

def z591 : W := mkw 0x00000500010a2000 0x8000028000851000 0x21008f00011c0000 0x10804780008e0000

def z592 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x61009f1cf91e61e6 0xb0804f8e7c8f30f3

def z593 : W := mkw 0x00022c0001428001 0x0001160000a14000 0x21070c0001e00000 0x1083860000f00000

def z594 : W := mkw 0x2020500280014014 0x101028014000a00a 0xd48070238203e63f 0xea403811c101f31f

def z595 : W := mkw 0x001100fbd0000000 0x0008807de8000000 0xf4009ffff8000000 0xfa004ffffc000000

def z596 : W := mkw 0x00c5805800b00900 0x0062c02c00580480 0x0007000000e00000 0x0003800000700000

def z597 : W := mkw 0x0001005000200900 0x0000802800100480 0x2107001001e001c0 0x1083800800f000e0

def z598 : W := mkw 0xe83850a6ae0556f6 0x741c28535702ab7b 0xdef870fffe03ffff 0xef7c387fff01ffff

def z599 : W := mkw 0xc0d580fc00b41f80 0x606ac07e005a0fc0 0xa18780fc01fc1fc0 0x50c3c07e00fe0fe0

def z600 : W := mkw 0x003150fbd0000000 0x0018a87de8000000 0xdc7870fff8000000 0xee3c387ffc000000

def z601 : W := mkw 0xa17effa287dbf415 0xd0bf7fd143edfa0a 0x7f7fff2087ffe607 0x3fbfff9043fff303

def z602 : W := mkw 0x48000104080c2282 0xa400008204061141 0xf4009f3cfa1c6606 0xfa004f9e7d0e3303

def z603 : W := mkw 0x001000a000000000 0x0008005000000000 0x9c7800e000000000 0x4e3c007000000000

def z604 : W := mkw 0x0028500006014000 0x001428000300a000 0x0a78600004018000 0x053c30000200c000

def z605 : W := mkw 0x0064d20000000000 0x0032690000000000 0x1078930000000000 0x083c498000000000

def z606 : W := mkw 0xc088000406941680 0x60440002034a0b40 0x00000000021c0600 0x00000000010e0300

def z607 : W := mkw 0x1001005140200908 0x08008028a0100484 0x000000c300001818 0x0000006180000c0c

def z608 : W := mkw 0x50c7ac5d61f68be9 0x2863d62eb0fb45f4 0xef87ecdf65ff99f9 0xf7c3f66fb2ffccfc

def z609 : W := mkw 0x016cd70007dbe001 0x80b66b8003edf000 0x1378930007ffe001 0x09bc498003fff000

def z610 : W := mkw 0x1000040021628969 0x0800020010b144b4 0xcf8060c305e399f9 0xe7c0306182f1ccfc

def z611 : W := mkw 0x48000104280c22e2 0xa400008214061171 0x9080933cfa1c67e6 0xc840499e7d0e33f3

def z612 : W := mkw 0x4001005400240b80 0x2000802a001205c0 0xbf8780fc07fc1fc1 0x5fc3c07e03fe0fe0

def z613 : W := mkw 0xd0dfacfd67f69fe9 0x686fd67eb3fb4ff4 0xbfff8cfc67fc1fc1 0x5fffc67e33fe0fe0

def z614 : W := mkw 0xa07dd0fa86015414 0x503ee87d4300aa0a 0xfefff0ff8603fe3f 0xff7ff87fc301ff1f

def z615 : W := mkw 0x1001045161220968 0x08008228b09104b4 0xe5800cd3610219f9 0xf2c00669b0810cfc

def z616 : W := mkw 0x68205506a90f62f6 0xb4102a835487b17b 0xf580ff3ffb1fe7ff 0xfac07f9ffd8ff3ff

def z617 : W := mkw 0x481105fff90e22e2 0xa40882fffc871171 0xf5809ffffb1e67e7 0xfac04ffffd8f33f3

def z618 : W := mkw 0x58000504296eabeb 0xac00028214b755f5 0xf7809f3cffffffff 0xfbc04f9e7fffffff

def z619 : W := mkw 0xa03a7aa3d6015414 0x501d3d51eb00aa0a 0xdef87fe3fe03fe3f 0xef7c3ff1ff01ff1f

def z620 : W := mkw 0x0166ff00014be001 0x80b37f8000a5f000 0x7c7fff000003e000 0x3e3fff800001f000

def z621 : W := mkw 0x0044820810000000 0x0022410408000000 0x0000830c18000000 0x000041860c000000

def z622 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x4a076cc364e39838 0xa503b661b271cc1c

def z623 : W := mkw 0x10022c0161628969 0x08011600b0b144b4 0x43806c0365e399f9 0xa1c03601b2f1ccfc

def z624 : W := mkw 0x10032c5161428069 0x08019628b0a14034 0xec076cd360038038 0xf603b669b001c01c

def z625 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x5e7870208603e607 0x2f3c38104301f303

def z626 : W := mkw 0x1001005160200968 0x08008028b01004b4 0xaf8700d365e019f9 0xd7c38069b2f00cfc

def z627 : W := mkw 0x4946af0429dea2e3 0xa4a3578214ef5171 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z628 : W := mkw 0x10022c0161428069 0x08011600b0a14034 0xe5806c13610381f9 0xf2c03609b081c0fc

def z629 : W := mkw 0x101100fbf0200968 0x0808807df81004b4 0x808000fff80019f8 0xc040007ffc000cfc

def z630 : W := mkw 0xc0dd84fc27b61fe0 0x606ec27e13db0ff0 0xffff8cfc67fe1fe1 0xffffc67e33ff0ff0

def z631 : W := mkw 0x0047aa5950000000 0x0023d52ca8000000 0xec07efdf78000000 0xf603f7efbc000000

def z632 : W := mkw 0x1000040021628969 0x0800020010b144b4 0xe7800c1065e399f9 0xf3c0060832f1ccfc

def z633 : W := mkw 0x003050a280000000 0x0018285140000000 0x087860c300000000 0x043c306180000000

def z634 : W := mkw 0x485585fc290e22e2 0xa42ac2fe14871171 0xfdff9ffcfb1e67e7 0xfeffcffe7d8f33f3

def z635 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xcef860c304039839 0xe77c30618201cc1c

def z636 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x8aff00fc04e01fc0 0x457f807e02700fe0

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000003cf8000000 0xc000001e7c000000

def z638 : W := mkw 0x2020500280014014 0x101028014000a00a 0x0000600300018018 0x000030018000c00c

def z639 : W := mkw 0xa07ffafbd6015414 0x503ffd7deb00aa0a 0x0a7f60c304019818 0x053fb0618200cc0c

def z640 : W := mkw 0x012a7f0007dbe001 0x80953f8003edf000 0x43007f0007ffe001 0x21803f8003fff000

def z641 : W := mkw 0x416eff0407dfe281 0xa0b77f8203eff140 0xffffff3c07ffe7c1 0x7fffff9e03fff3e0

def z642 : W := mkw 0xc1ffffffd7ffff81 0xe0ffffffebffffc0 0xffffffffffffffc1 0xffffffffffffffe0

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4000c1060000000 0xf200060830000000

def z644 : W := mkw 0x116ffa5146f1c909 0x08b7fd28a378e484 0x0a7f60c304e19818 0x053fb0618270cc0c

def z645 : W := mkw 0xa008000006015414 0x500400000300aa0a 0xd68010208603fe3f 0xeb4008104301ff1f

def z646 : W := mkw 0xc080000400241f80 0x6040000200120fc0 0x0080000000001fc0 0x0040000000000fe0

def z647 : W := mkw 0xa028500006015414 0x501428000300aa0a 0x5ef870000603fe3f 0x2f7c38000301ff1f

def z648 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x90f880fc021c1fc0 0x487c407e010e0fe0

def z649 : W := mkw 0x00032c5001628901 0x0001962800b14480 0xef876cd005e399c1 0x77c3b66802f1cce0

def z650 : W := mkw 0x0066fa03d0000000 0x00337d01e8000000 0x7c7fff03f8000000 0xbe3fff81fc000000

def z651 : W := mkw 0x48000004280402e2 0x2400000214020171 0xf4809f3cf80007e6 0xfa404f9e7c0003f3

def z652 : W := mkw 0xb0132cf3e1629d7d 0x58099679f0b14ebe 0xef876cf3e5e39fff 0xf7c3b679f2f1cfff

def z653 : W := mkw 0x0177fffbd1daa001 0x80bbfffde8ed5000 0xfd7ffffff9fc0000 0xfebffffffcfe0000

def z654 : W := mkw 0x803850a006015400 0x401c28500300aa00 0xdef870e00603fe01 0x6f7c38700301ff00

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000100080026026 0xa000080040013013

def z656 : W := mkw 0x58032d55696eabeb 0xac0196aab4b755f5 0xef876cd367ffffff 0xf7c3b669b3ffffff

def z657 : W := mkw 0xa01800a286001414 0x500c005143000a0a 0x9ef800e386001e3f 0xcf7c0071c3000f1f

def z658 : W := mkw 0x48000004280402e2 0x2400000214020171 0x00800000000007e6 0x00400000000003f3

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e8000c004001801 0x4740006002000c00

def z660 : W := mkw 0x00000500010a2000 0x8000028000851000 0x01000000031e6001 0x00800000018f3000

def z661 : W := mkw 0xc01800a406041680 0x600c005203020b40 0xbff880fc071c1fc1 0x5ffc407e038e0fe0

def z662 : W := mkw 0x405580fc00040280 0x202ac07e00020140 0xbdff80fc031c07c1 0x5effc07e018e03e0

def z663 : W := mkw 0x0003285140000000 0x00019428a0000000 0xee876cd364039839 0xf743b669b201cc1c

def z664 : W := mkw 0x016cd20006914000 0x00b669000348a000 0x0078000000000000 0x003c000000000000

def z665 : W := mkw 0xa17effa287dbf415 0xd0bf7fd143edfa0a 0x7f7fffc307fff819 0x3fbfffe183fffc0c

def z666 : W := mkw 0x0008000006014000 0x000400000300a000 0x020000000603e001 0x010000000301f000

def z667 : W := mkw 0x2020500280014014 0x101028014000a00a 0xce8070c38403f83f 0xe7403861c201fc1f

def z668 : W := mkw 0x00022a0150000000 0x00011500a8000000 0x00000f0078000000 0x000007803c000000

def z669 : W := mkw 0x0003285140200900 0x00019428a0100480 0xef876cd365e019c1 0xf7c3b669b2f00ce0

def z670 : W := mkw 0x4866ff04290e22e2 0xa4337f8214871171 0xfdffff3cfb1e67e7 0xfeffff9e7d8f33f3

def z671 : W := mkw 0x1001005160200968 0x08008028b01004b4 0x00000010600001c0 0x00000008300000e0

def z672 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x0078000000000000 0x003c000000000000

def z673 : W := mkw 0x0146af0001daa001 0x80a3578000ed5000 0x75079f0003fe6001 0x3a83cf8001ff3000

def z674 : W := mkw 0x801800a006001400 0x400c005003000a00 0x0a7800c004001800 0x053c006002000c00

def z675 : W := mkw 0x5877fffff96eabeb 0xac3bfffffcb755f5 0xffffffffffffffff 0xffffffffffffffff

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0xb400803c00000000 0x5a00401e00000000

def z677 : W := mkw 0xc1dfaffc07febf81 0xe0efd7fe03ff5fc0 0xbfff8ffc07fc1fc1 0x5fffc7fe03fe0fe0

def z678 : W := mkw 0x0108000006d1c001 0x008400000368e000 0x0200000004e18000 0x010000000270c000

def z679 : W := mkw 0xe83855a6af0f76f6 0xf41c2ad35787bb7b 0xdff870e3871fffff 0xeffc3871c38fffff

def z680 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xb5808f3c7b1c07c1 0x5ac0479e3d8e03e0

def z681 : W := mkw 0xc09900fc06b41f80 0x604c807e035a0fc0 0x838000fc07fc1fc1 0x41c0007e03fe0fe0

def z682 : W := mkw 0x0077faf800000000 0x003bfd7c00000000 0xfc7ffffc00000000 0x7e3ffffe00000000

def z683 : W := mkw 0xc8dc81ac0e9c3682 0xe46e40d6074e1b41 0x1078932c9a1c6606 0x083c49964d0e3303

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4809f3cfa026627 0xfa404f9e7d013313

def z685 : W := mkw 0xe0b850a686b55f94 0x705c2853435aafca 0xdff870e387ffffff 0xeffc3871c3ffffff

def z686 : W := mkw 0x1000000160000068 0x08000000b0000034 0x0000000360000038 0x80000001b000001c

def z687 : W := mkw 0x80dd80f806b01d00 0x406ec07c03580e80 0x3f7f80c007fc1801 0x1fbfc06003fe0c00

def z688 : W := mkw 0x4000000400040280 0x2000000200020140 0xf580903c831e67e7 0xfac0481e418f33f3

def z689 : W := mkw 0x8088000006b01d00 0x4044000003580e80 0x0200000004e01800 0x0100000002700c00

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000002026627 0x0040000001013313

def z691 : W := mkw 0x1077fafbf0200968 0x083bfd7df81004b4 0xfcfffffff80019f8 0xfe7ffffffc000cfc

def z692 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xa1808f3cf91c07e6 0xd0c0479e7c8e03f3

def z693 : W := mkw 0x1147af5161faa969 0x88a3d7a8b0fd54b4 0xef87efd365ff99f9 0xf7c3f7e9b2ffccfc

def z694 : W := mkw 0x0100050001daa001 0x8080028000ed5000 0x0100000001fc0000 0x0080000000fe0000

def z695 : W := mkw 0xc0fcd2ae96941680 0x607e69574b4a0b40 0x1078932c9a1c0600 0x083c49964d0e0300

def z696 : W := mkw 0x0000000020000060 0x0000000010000030 0x80800010600001e0 0xc0400008300000f0

def z697 : W := mkw 0x00000500010a2000 0x8000028000851000 0xf5809f20831e6627 0xfac04f90418f3313

def z698 : W := mkw 0x0108010006996000 0x80840080034cb000 0x00000000021c6000 0x00000000010e3000

def z699 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xe5808f1c791e01e1 0xf2c0478e3c8f00f0

def z700 : W := mkw 0x0020520290000000 0x0010290148000000 0x0000130098000000 0x000009804c000000

def z701 : W := mkw 0xe80805042f0f76f6 0xf40402821787bb7b 0xf7809f3cff1fffff 0xfbc04f9e7f8fffff

def z702 : W := mkw 0x0028500006014000 0x001428000300a000 0x1078100002006000 0x083c080001003000

def z703 : W := mkw 0x49227f04294fe2e3 0xa4913f8214a7f171 0xf580ff3cfb1fe7e7 0xfac07f9e7d8ff3f3

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0xc480000000020021 0xe240000000010010

def z705 : W := mkw 0xd8dfadfd6ffebfeb 0xec6fd6feb7ff5ff5 0xffffffffffffffff 0xffffffffffffffff

def z706 : W := mkw 0xe83851a68e0d7696 0xf41c28d34706bb4b 0x1078932c9a1c6606 0x083c49964d0e3303

def z707 : W := mkw 0x1077fafbd0200908 0x083bfd7de8100484 0xfc7ffffff8001818 0xfe3ffffffc000c0c

def z708 : W := mkw 0x196eff016fdbe06b 0x8cb77f80b7edf035 0x7f7fff03ffffe03f 0xbfbfff81fffff01f

def z709 : W := mkw 0x816eff0007dbf401 0xc0b77f8003edfa00 0x7fffff0007fffe01 0x3fffff8003ffff00

def z710 : W := mkw 0x006efe0007d28001 0x00377f0003e94000 0x7f7fff0007ff8001 0x3fbfff8003ffc000

def z711 : W := mkw 0xa156afa281dab415 0xd0ab57d140ed5a0a 0xa1878fe381fc1e3e 0xd0c3c7f1c0fe0f1f

def z712 : W := mkw 0x58c7ad5d69feabeb 0xac63d6aeb4ff55f5 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z713 : W := mkw 0x405d80fc06940280 0x202ec07e034a0140 0xbfff80fc07fc07c1 0x5fffc07e03fe03e0

def z714 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fffc307ffe001 0xffbfffe183fff000

def z715 : W := mkw 0x0057aaf950000000 0x002bd57ca8000000 0xfc7fefff78000000 0xfe3ff7ffbc000000

def z716 : W := mkw 0x11227f01614be069 0x88913f80b0a5f034 0x40007f006003e000 0x20003f803001f000

def z717 : W := mkw 0x40cd805c06b40b80 0x2066c02e035a05c0 0xbfff80dc07fc19c1 0x5fffc06e03fe0ce0

def z718 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xfff8f0e3871ffe3f 0xfffc7871c38fff1f

def z719 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x6f7fef0005ff8001 0x37bff78002ffc000

def z720 : W := mkw 0x0066fa03d0000000 0x00337d01e8000000 0xfc7fff3ff8000000 0xfe3fff9ffc000000

def z721 : W := mkw 0x004ead0007daa001 0x8027568003ed5000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z722 : W := mkw 0x316eff03e7dbe07d 0x98b77f81f3edf03e 0x7f7fff03e7ffe03f 0xbfbfff81f3fff01f

def z723 : W := mkw 0xc88805042fbe3fe2 0xe444028217df1ff1 0x0380000007fc1fc1 0x01c0000003fe0fe0

def z724 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xa87feffff8000000 0xd43ff7fffc000000

def z725 : W := mkw 0x0177fafbd0d08001 0x00bbfd7de8684000 0xfc7ffffff8e00000 0xfe3ffffffc700000

def z726 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x6f876cc305e399f9 0x37c3b66182f1ccfc

def z727 : W := mkw 0x1001005160200968 0x08008028b01004b4 0xef8760d365e399f9 0xf7c3b069b2f1ccfc

def z728 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff90fc07fe7fc1 0x7fffc87e03ff3fe0

def z729 : W := mkw 0x1074d6aab1628969 0x083a6b5558b144b4 0x13f8932c9de399f9 0x09fc49964ef1ccfc

def z730 : W := mkw 0xc98805042fffffe3 0xe4c4028217fffff1 0x0380000007ffffe7 0x01c0000003fffff3

def z731 : W := mkw 0x1077fafbd0608909 0x083bfd7de8304484 0xfffffffffde199d9 0xfffffffffef0ccec

def z732 : W := mkw 0x10032c5971628969 0x0801962cb8b144b4 0xef876cdf7de399f9 0xf7c3b66fbef1ccfc

def z733 : W := mkw 0x116dd35166b96968 0x88b6e9a8b35cb4b4 0x90f893d3621c79f8 0xc87c49e9b10e3cfc

def z734 : W := mkw 0xe09100fe80241f94 0x7048807f40120fca 0x808000ff00001fd8 0x4040007f80000fec

def z735 : W := mkw 0x216eff03d7dbe015 0x90b77f81ebedf00a 0x7f7fff03ffffe03f 0xbfbfff81fffff01f

def z736 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xd0f870e38203fe3e 0xe87c3871c101ff1f

def z737 : W := mkw 0x016cd30006996000 0x80b66980034cb000 0x317f930003fc6000 0x18bfc98001fe3000

def z738 : W := mkw 0x011905fbd7dbe001 0x808c82fdebedf000 0x830000ffffffe001 0xc180007ffffff000

def z739 : W := mkw 0x0166ff0001dbe001 0x80b37f8000edf000 0x7d7fff0001ffe000 0x3ebfff8000fff000

def z740 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff80fc07fe1fe1 0xffffc07e03ff0ff0

def z741 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff90fc87fc7fc7 0x5fffc87e43fe3fe3

def z742 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x707fff3ff8000000 0xb83fff9ffc000000

def z743 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xdef870fffe03fe3f 0xef7c387fff01ff1f

def z744 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x8af860e38603fe3f 0xc57c3071c301ff1f

def z745 : W := mkw 0x0067fa5950000000 0x0033fd2ca8000000 0xfc7fffdf78000000 0xfe3fffefbc000000

def z746 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff80fc87fc1fe7 0xdfffc07e43fe0ff3

def z747 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xf7809f3cff1fffff 0xfbc04f9e7f8fffff

def z748 : W := mkw 0x00327aa3d0000000 0x00193d51e8000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z749 : W := mkw 0x80dd80f806b01d00 0x406ec07c03580e80 0xbfff80d007fc19c1 0x5fffc06803fe0ce0

def z750 : W := mkw 0x0077faf950000000 0x003bfd7ca8000000 0xfc7ffffc78000000 0x7e3ffffe3c000000

def z751 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7fffff0007ffe627 0x3fffff8003fff313

def z752 : W := mkw 0x005d80f806b00900 0x002ec07c03580480 0xbfff80fc07fc19c1 0x5fffc07e03fe0ce0

def z753 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x4af870c38603fe3f 0xa57c3861c301ff1f

def z754 : W := mkw 0x005580fbd0000000 0x002ac07de8000000 0xfc7f9ffff8000000 0xfe3fcffffc000000

def z755 : W := mkw 0x016eff03d7dbe001 0x80b77f81ebedf000 0x7f7fff0307ffe001 0x3fbfff8183fff000

def z756 : W := mkw 0x0077fafbd0200900 0x003bfd7de8100480 0xfcfffffff80019c0 0xfe7ffffffc000ce0

def z757 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xbc7fefff78000000 0x5e3ff7ffbc000000

def z758 : W := mkw 0x480805042f9e22e2 0xa404028217cf1171 0x0380000007fe67e7 0x01c0000003ff33f3

def z759 : W := mkw 0xc89100fc28241fe2 0x6448807e14120ff1 0x808000fc78001fc0 0x4040007e3c000fe0

def z760 : W := mkw 0xc0dd80ffd6b41f80 0x606ec07feb5a0fc0 0xbfff80ff07fc1fc1 0x5fffc07f83fe0fe0

def z761 : W := mkw 0xe0dd80fc06b55f94 0x706ec07e035aafca 0xffffe0ff07ffffff 0xfffff07f83ffffff

def z762 : W := mkw 0xc0dd82fc16b41f80 0x606ec17e0b5a0fc0 0xbfff83fc1ffc1fc1 0x5fffc1fe0ffe0fe0

def z763 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5f7f700007ffe001 0x2fbfb80003fff000

def z764 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xcaf870e38403fe3e 0xe57c3871c201ff1f

def z765 : W := mkw 0x0077fafbd0200900 0x003bfd7de8100480 0xfd7ffffff9e001c0 0xfebffffffcf000e0

def z766 : W := mkw 0x014eaf0007daa001 0x80a7578003ed5000 0x317f8f0003fc0000 0x18bfc78001fe0000

def z767 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xf5809ffffb1e7fff 0xfac04ffffd8f3fff

def z768 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xd0809f3cfa1e67e6 0xe8404f9e7d0f33f3

def z769 : W := mkw 0x60e5d05e80b54b94 0x3072e82f405aa5ca 0x6107f01f81ffe1fe 0xb083f80fc0fff0ff

def z770 : W := mkw 0xe0b150fe80255f94 0x7058a87f4012afca 0xc08070ff8003fffe 0xe040387fc001ffff

def z771 : W := mkw 0x004c800006900000 0x0026400003480000 0x0b7f000007fc0001 0x05bf800003fe0000

def z772 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbd7f80fc03fc07c0 0x5ebfc07e01fe03e0

def z773 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfcfffffff8020021 0xfe7ffffffc010010

def z774 : W := mkw 0xc0dd80fc06b55f80 0x606ec07e035aafc0 0xbfff80fc07ffffc1 0x5fffc07e03ffffe0

def z775 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff2087ffe001 0xffbfff9043fff000

def z776 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xafff80dc05fc19c1 0x57ffc06e02fe0ce0

def z777 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xa58000fc01001fc1 0x52c0007e00800fe0

def z778 : W := mkw 0xb03b7cf3e763dd7d 0x581dbe79f3b1eebe 0x317f1c30e3e067c6 0x18bf8e1871f033e3

def z779 : W := mkw 0xc0dd80fe86b41f80 0x606ec07f435a0fc0 0xbfff80ff87fc1fc1 0xdfffc07fc3fe0fe0

def z780 : W := mkw 0x004c800006914000 0x002640000348a000 0x3f7f800007ffe001 0x1fbfc00003fff000

def z781 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfefffffffc001801 0xff7ffffffe000c00

def z782 : W := mkw 0x096eff002fdbe063 0x84b77f8017edf031 0xff7fff3cffffe027 0xffbfff9e7ffff013

def z783 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x5a7870e38603fe3e 0xad3c3871c301ff1f

def z784 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0x7f7fff1067ffe1c1 0x3fbfff8833fff0e0

def z785 : W := mkw 0xf81100f7e8241ffe 0x7c08807bf4120fff 0x808000fff8001ffe 0xc040007ffc000fff

def z786 : W := mkw 0x216eff0287dbe015 0x90b77f8143edf00a 0x7f7fff0307ffe019 0x3fbfff8183fff00c

def z787 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbf7f80fc05fc19c0 0x5fbfc07e02fe0ce0

def z788 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x757f9f0003fe6001 0x3abfcf8001ff3000

def z789 : W := mkw 0xe0dd80ffd6b41f94 0x706ec07feb5a0fca 0xbfff80fffffc1fff 0xdfffc07ffffe0fff

def z790 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfcfffffffa000601 0xfe7ffffffd000300

def z791 : W := mkw 0x0076faabd0000000 0x003b7d55e8000000 0x7c7fff2ff8000000 0xbe3fff97fc000000

def z792 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef877fd3fde399f9 0xf7c3bfe9fef1ccfc

def z793 : W := mkw 0xc89100fff8241fe2 0x6448807ffc120ff1 0x808000fff8001fe6 0xc040007ffc000ff3

def z794 : W := mkw 0x88dd85f82fba3d62 0xc46ec2fc17dd1eb1 0x4a7f1fc0fce27826 0xa53f8fe07e713c13

def z795 : W := mkw 0x016eff0157dbe001 0x80b77f80abedf000 0x7f7fff007fffe001 0x3fbfff803ffff000

def z796 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x7c7fffdf78000000 0x3e3fffefbc000000

def z797 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x30789f3cf8000000 0x183c4f9e7c000000

def z798 : W := mkw 0x004c800006900000 0x0026400003480000 0x1a7f800006fc0000 0x0d3fc000037e0000

def z799 : W := mkw 0x116eff0167dbe069 0x88b77f80b3edf034 0xffffff1367ffe1f9 0xffffff89b3fff0fc

def z800 : W := mkw 0xa16eff0007dbf415 0xd0b77f8003edfa0a 0xffffff2087fffe3f 0xffffff9043ffff1f

def z801 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x000000ec00001e00 0x0000007600000f00

def z802 : W := mkw 0xa04faa5956015414 0x5027d52cab00aa0a 0x22878f1c7e03fe3f 0x1143c78e3f01ff1f

def z803 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x50789f2cf8000000 0xa83c4f967c000000

def z804 : W := mkw 0x1003285140608909 0x08019428a0304484 0x0b8760c305e199d9 0x05c3b06182f0ccec

def z805 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x217f801c01fc01c0 0x10bfc00e00fe00e0

def z806 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffffe387fffe3f 0xfffffff1c3ffff1f

def z807 : W := mkw 0xc89100fc08241f82 0x6448807e04120fc1 0x808000fc98001fc6 0x4040007e4c000fe3

def z808 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x33ff803c07fc1fc1 0x19ffc01e03fe0fe0

def z809 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff00ffffe001 0xbfbfff807ffff000

def z810 : W := mkw 0xc09100fe80241f80 0x6048807f40120fc0 0x808000ff80001fc0 0xc040007fc0000fe0

def z811 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x0000003c000007c0 0x0000001e000003e0

def z812 : W := mkw 0x4877fffff90e22e2 0xa43bfffffc871171 0x09ff60c3031e67e7 0x04ffb061818f33f3

def z813 : W := mkw 0x016cd30006996000 0x80b66980034cb000 0x1a7f930006fc6000 0x0d3fc980037e3000

def z814 : W := mkw 0xd09100fff0241fe8 0x6848807ff8120ff4 0x808000fff8001ff8 0xc040007ffc000ffc

def z815 : W := mkw 0x0020500000000000 0x0010280000000000 0xfc78ff3cf8000000 0xfe3c7f9e7c000000

def z816 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef877cd3e5e3f9ff 0xf7c3be69f2f1fcff

def z817 : W := mkw 0x0076faabd0000000 0x003b7d55e8000000 0x10789f2cf8000000 0x083c4f967c000000

def z818 : W := mkw 0x004c800006900000 0x0026400003480000 0xbfff801007fc01c1 0x5fffc00803fe00e0

def z819 : W := mkw 0xa16eff0007dbf415 0xd0b77f8003edfa0a 0xffffffc307fffe3f 0xffffffe183ffff1f

def z820 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x2bff80dc07fc1fc1 0x15ffc06e03fe0fe0

def z821 : W := mkw 0x014c850007dbe001 0x80a6428003edf000 0x7f7f9f0007ffe001 0x3fbfcf8003fff000

def z822 : W := mkw 0xe8fcd1ae8e9d7696 0xf47e68d7474ebb4b 0x1078932c9a1c6606 0x083c49964d0e3303

def z823 : W := mkw 0x014c800006d1c001 0x00a640000368e000 0x3f7f800007fd8001 0x1fbfc00003fec000

def z824 : W := mkw 0x084c85002f9a2062 0x8426428017cd1031 0x7f7f9f00fffe6027 0xbfbfcf807fff3013

def z825 : W := mkw 0x2077fafbd0014014 0x103bfd7de800a00a 0xfefffffffc03f83f 0xff7ffffffe01fc1f

def z826 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfc7ffffff8038038 0xfe3ffffffc01c01c

def z827 : W := mkw 0x004c840007d28001 0x0026420003e94000 0x3f7f800007ff8001 0x1fbfc00003ffc000

def z828 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x3b7f80fc07fc1fc0 0x1dbfc07e03fe0fe0

def z829 : W := mkw 0xe97cd3a68e9d7696 0xf4be69d3474ebb4b 0x1078932c9a1c6606 0x083c49964d0e3303

def z830 : W := mkw 0xc8dd80fc0eb41f82 0x646ec07e075a0fc1 0xbfff80fc9ffc1fc7 0x5fffc07e4ffe0fe3

def z831 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff8cfc67fc1fc1 0xffffc67e33fe0fe0

def z832 : W := mkw 0x0177fafbd041c001 0x00bbfd7de820e000 0xfc7ffffff8018000 0xfe3ffffffc00c000

def z833 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfe7ffffffc019818 0xff3ffffffe00cc0c

def z834 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffffe0ff07fc1fc1 0xfffff07f83fe0fe0

def z835 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff9ffcfffe7fe7 0xffffcffe7fff3ff3

def z836 : W := mkw 0x10032e5171628969 0x08019728b8b144b4 0xef876fd37de399f9 0xf7c3b7e9bef1ccfc

def z837 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff8ffc7ffc1fc1 0x5fffc7fe3ffe0fe0

def z838 : W := mkw 0xe0dd80fc06b55f94 0x706ec07e035aafca 0xffff90fc87ffffff 0xffffc87e43ffffff

def z839 : W := mkw 0x1003285160608969 0x08019428b03044b4 0xaf8760d365e199f9 0xd7c3b069b2f0ccfc

def z840 : W := mkw 0x409100fc00240b80 0x2048807e001205c0 0x800000fc000001c0 0x4000007e000000e0

def z841 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fffc307fff819 0x3fbfffe183fffc0c

def z842 : W := mkw 0xa04c800006915414 0x502640000348aa0a 0x3fff800007fffe3f 0x1fffc00003ffff1f

def z843 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xff809ffcff1e7fe7 0xffc04ffe7f8f3ff3

def z844 : W := mkw 0x483055a6a90e22e2 0xa4182ad354871171 0xddf870e3831e67e7 0xeefc3871c18f33f3

def z845 : W := mkw 0x0076faa280000000 0x003b7d5140000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z846 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x6b076cd365e399f8 0xb583b669b2f1ccfc

def z847 : W := mkw 0xe83855a6af0f76f6 0xf41c2ad35787bb7b 0x2b78efdf7d1d99d8 0x15bc77efbe8eccec

def z848 : W := mkw 0x004ea80006900000 0x0027540003480000 0x7f7fec0007fc0001 0x3fbff60003fe0000

def z849 : W := mkw 0x09227f00294be063 0x84913f8014a5f031 0x40007f000003e026 0x20003f800001f013

def z850 : W := mkw 0x0067fa5140000000 0x0033fd28a0000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z851 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0xffffff30e7ffe7e7 0xffffff9873fff3f3

def z852 : W := mkw 0x11227f00214be069 0x88913f8010a5f034 0x40007f000003e038 0x20003f800001f01c

def z853 : W := mkw 0x002a7d00074be001 0x80153e8003a5f000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z854 : W := mkw 0xd0deacad67d696e9 0x686f5656b3eb4b74 0x5078ec2f621f8638 0xa83c7617b10fc31c

def z855 : W := mkw 0x2077fafbd0014014 0x103bfd7de800a00a 0xfcfffffffa03e63f 0xfe7ffffffd01f31f

def z856 : W := mkw 0xc0dd80fd56b41f80 0x606ec07eab5a0fc0 0xbfff80fc7ffc1fc1 0x5fffc07e3ffe0fe0

def z857 : W := mkw 0xa0fffafbd6b15d14 0x507ffd7deb58ae8a 0x0a7f60c304e19818 0x053fb0618270cc0c

def z858 : W := mkw 0x0075d2fbd0000000 0x003ae97de8000000 0xf4789ffff8000000 0xfa3c4ffffc000000

def z859 : W := mkw 0x40d580fc00b40b80 0x206ac07e005a05c0 0xbfff80fc05fc19c1 0x5fffc07e02fe0ce0

def z860 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff2c9fffe001 0x3fbfff964ffff000

def z861 : W := mkw 0xe09100ffd0241f94 0x7048807fe8120fca 0x808000fff8001ffe 0xc040007ffc000fff

def z862 : W := mkw 0xe09900fc06255f94 0x704c807e0312afca 0x828000fc0603ffff 0x4140007e0301ffff

def z863 : W := mkw 0x116eff0147dbe009 0x88b77f80a3edf004 0x7f7fff0307ffe019 0x3fbfff8183fff00c

def z864 : W := mkw 0x004c800006900000 0x0026400003480000 0xffffe0c307ff9839 0xfffff06183ffcc1c

def z865 : W := mkw 0xc0dc80a406b41f80 0x606e4052035a0fc0 0xbfff80e007fc1fc1 0x5fffc07003fe0fe0

def z866 : W := mkw 0x48000104080c2282 0xa400008204061141 0xf5809f3cfb1c67c7 0xfac04f9e7d8e33e3

def z867 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xdef8f3ef9e03fe3f 0xef7c79f7cf01ff1f

def z868 : W := mkw 0x1077fafbd0608909 0x083bfd7de8304484 0xfc7ffffff8e00000 0xfe3ffffffc700000

def z869 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff80fc07ff9ff9 0x5fffc07e03ffcffc

def z870 : W := mkw 0x40cc800406b40b80 0x20664002035a05c0 0x3f7f800007fc01c1 0x1fbfc00003fe00e0

def z871 : W := mkw 0xc05c80a406941680 0x602e4052034a0b40 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z872 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x207f8f1c78000000 0x103fc78e3c000000

def z873 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x1b7ff30007ffe001 0x0dbff98003fff000

def z874 : W := mkw 0x0077fafbd0014000 0x003bfd7de800a000 0xfc7ffffff803e000 0xfe3ffffffc01f000

def z875 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x387ffffff8000000 0x1c3ffffffc000000

def z876 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff80fcfffc1fc1 0xdfffc07e7ffe0fe0

def z877 : W := mkw 0x014c850007daa001 0x80a6428003ed5000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z878 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3f7f9f0007fc6001 0x1fbfcf8003fe3000

def z879 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x587fffeff8000000 0xac3ffff7fc000000

def z880 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x808000fcf8001fc0 0xc040007e7c000fe0

def z881 : W := mkw 0x0077fafbd0408001 0x003bfd7de8204000 0xfe7ffffffce18000 0xff3ffffffe70c000

def z882 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff0007ffe021 0xffffff8003fff010

def z883 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x3fff80c007fc1fc1 0x1fffc06003fe0fe0

def z884 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfc7ffffffa026001 0xfe3ffffffd013000

def z885 : W := mkw 0x1003285140608909 0x08019428a0304484 0x8a8760d304e199d8 0x4543b0698270ccec

def z886 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xab876cd365e199f8 0xd5c3b669b2f0ccfc

def z887 : W := mkw 0x40d580fc00b40b80 0x206ac07e005a05c0 0x297f80dc01fc01c0 0x14bfc06e00fe00e0

def z888 : W := mkw 0xa03050a280015414 0x501828514000aa0a 0xdcf870e38003fe3e 0xee7c3871c001ff1f

def z889 : W := mkw 0x004c800006900000 0x0026400003480000 0xff7f9f3cfffc0001 0xffbfcf9e7ffe0000

def z890 : W := mkw 0x18032c516962896b 0x0c019628b4b144b5 0xef876cd3fde399ff 0xf7c3b669fef1ccff

def z891 : W := mkw 0x004c800006900000 0x0026400003480000 0x7f7f9f0007fc0001 0x3fbfcf8003fe0000

def z892 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x0b0760c305e199d8 0x0583b06182f0ccec

def z893 : W := mkw 0x004eaa0006900000 0x0027550003480000 0x3f7f8f0007fc0001 0x1fbfc78003fe0000

def z894 : W := mkw 0xc0aa7a07d6b41f80 0x60553d03eb5a0fc0 0x43807f03fffc1fc1 0xa1c03f81fffe0fe0

def z895 : W := mkw 0x0028500006014000 0x001428000300a000 0xdef870e38603fe3f 0xef7c3871c301ff1f

def z896 : W := mkw 0x216eff0287dbe015 0x90b77f8143edf00a 0xffffff2387ffe63f 0xffffff91c3fff31f

def z897 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x6f076cd365e399d9 0x3783b669b2f1ccec

def z898 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x8b8760d365e399f9 0xc5c3b069b2f1ccfc

def z899 : W := mkw 0x48000504294ea2e3 0xa400028214a75171 0xf7809f3cffffe7e7 0xfbc04f9e7ffff3f3

def z900 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x7f7fff0007fd8001 0x3fbfff8003fec000

def z901 : W := mkw 0x016cd70007dbe001 0x80b66b8003edf000 0x3f7f930007ffe001 0x1fbfc98003fff000

def z902 : W := mkw 0xc0cd805406b41f80 0x6066c02a035a0fc0 0xbfff80d007fc1fc1 0x5fffc06803fe0fe0

def z903 : W := mkw 0xa16eff0287dbf415 0xd0b77f8143edfa0a 0x7fffff0387fffe3f 0xbfffff81c3ffff1f

def z904 : W := mkw 0x096eff03ffdbe063 0x84b77f81ffedf031 0x7f7fff03ffffe027 0xbfbfff81fffff013

def z905 : W := mkw 0x096eff002fdbe063 0x84b77f8017edf031 0x7f7fff0007ffe027 0x3fbfff8003fff013

def z906 : W := mkw 0x004ea80006d08001 0x0027540003684000 0x3f7fe00007fd8001 0x1fbff00003fec000

def z907 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x3f7f803c07fc07c1 0x1fbfc01e03fe03e0

def z908 : W := mkw 0x0001005000200900 0x0000802800100480 0xaf8760d305e199d9 0x57c3b06982f0ccec

def z909 : W := mkw 0xe90805042fdff6f7 0xf484028217effb7b 0x0380000007ffffff 0x01c0000003ffffff

def z910 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xfef8ffe38603fe3f 0xff7c7ff1c301ff1f

def z911 : W := mkw 0x00337afbd0000000 0x0019bd7de8000000 0xdc787ffff8000000 0xee3c3ffffc000000

def z912 : W := mkw 0x11032f51616aa969 0x888197a8b0b554b4 0xef876fd365e399f9 0xf7c3b7e9b2f1ccfc

def z913 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xf47f9f3cf8000000 0xfa3fcf9e7c000000

def z914 : W := mkw 0xe0dd80fe86b41f94 0x706ec07f435a0fca 0xbfff80fc87fc1fc7 0x5fffc07e43fe0fe3

def z915 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef876cf3e5e39fff 0xf7c3b679f2f1cfff

def z916 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xff7ffffffde00001 0xffbffffffef00000

def z917 : W := mkw 0x0066fa0000900000 0x00337d0000480000 0x7d7fff0001fc0000 0x3ebfff8000fe0000

def z918 : W := mkw 0xc1b37ffc016fff81 0xe0d9bffe00b7ffc0 0xc0807ffc0003ffc0 0x60403ffe0001ffe0

def z919 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfefffffffe03fe3f 0xff7fffffff01ff1f

def z920 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7fffff0007fff839 0x3fffff8003fffc1c

def z921 : W := mkw 0xe0dd80fc06b55f94 0x706ec07e035aafca 0xbfff80fc07fd9fd9 0x5fffc07e03fecfec

def z922 : W := mkw 0xc09900fc06241f80 0x604c807e03120fc0 0x828000fc06001fc1 0x4140007e03000fe0

def z923 : W := mkw 0x405580fc00240b80 0x202ac07e001205c0 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z924 : W := mkw 0x1001045021628969 0x0800822810b144b4 0xef8760d305e399f9 0xf7c3b06982f1ccfc

def z925 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff87ffffffe3ffff 0xffc3fffffff1ffff

def z926 : W := mkw 0x0166ff0001daa001 0x80b37f8000ed5000 0x7f7fff0005ff8001 0x3fbfff8002ffc000

def z927 : W := mkw 0x004c800006900000 0x0026400003480000 0x2b7f800005fc0000 0x15bfc00002fe0000

def z928 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xaf876cd365e199d9 0x57c3b669b2f0ccec

def z929 : W := mkw 0x004c800006900000 0x0026400003480000 0xbf7f803c07fc0001 0x5fbfc01e03fe0000

def z930 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff9ffc07fc1fc1 0x7fffcffe03fe0fe0

def z931 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x1af870e38603fe3f 0x0d7c3871c301ff1f

def z932 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x0a7f600006fde000 0x053fb000037ef000

def z933 : W := mkw 0x496efa042ed5c2e3 0x24b77d02176ae171 0x8aff603cfce187e6 0xc57fb01e7e70c3f3

def z934 : W := mkw 0x016eff0297dbe001 0x80b77f814bedf000 0x7f7fff009fffe001 0x3fbfff804ffff000

def z935 : W := mkw 0x01227f00214be061 0x80913f8010a5f030 0x40007f006003e020 0xa0003f803001f010

def z936 : W := mkw 0x006cd00006900000 0x0036680003480000 0x7f7ff00007fc0001 0x3fbff80003fe0000

def z937 : W := mkw 0x016eff0007daa001 0x80b77f8003ed5000 0x7f7fff0007fc0001 0x3fbfff8003fe0000

def z938 : W := mkw 0x490805042fdfe2e3 0xa484028217eff171 0x0300000007ffe1c1 0x0180000003fff0e0

def z939 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef876cfffde399f9 0xf7c3b67ffef1ccfc

def z940 : W := mkw 0xc09100fe90241f80 0x6048807f48120fc0 0x808000fc98001fc0 0x4040007e4c000fe0

def z941 : W := mkw 0x016cd700079b6000 0x80b66b8003cdb000 0x7f7f9f0007fe6001 0x3fbfcf8003ff3000

def z942 : W := mkw 0x016cd20006914000 0x00b669000348a000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z943 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x1a7fe00006fd8000 0x0d3ff000037ec000

def z944 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xfffff0ff87ffffff 0xfffff87fc3ffffff

def z945 : W := mkw 0x004c800006900000 0x0026400003480000 0xbfff802007fc0601 0x5fffc01003fe0300

def z946 : W := mkw 0xc09100ffd0241f80 0x6048807fe8120fc0 0x808000ff00001fc0 0x4040007f80000fe0

def z947 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff877cf3e5e399f9 0xffc3be79f2f1ccfc

def z948 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xc87f7ffff8000000 0xe43fbffffc000000

def z949 : W := mkw 0xf80805042f6fffff 0xfc04028217b7ffff 0x0380000007ffffff 0x01c0000003ffffff

def z950 : W := mkw 0x116eff0027dbe069 0x88b77f8013edf034 0x7f7fff0007ffe039 0x3fbfff8003fff01c

def z951 : W := mkw 0xe80805042f0f76f6 0xf40402821787bb7b 0x01800000031e67e7 0x00c00000018f33f3

def z952 : W := mkw 0x0047aa5950000000 0x0023d52ca8000000 0x3c7f8f1c78000000 0x1e3fc78e3c000000

def z953 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x717fff0003ffe000 0x38bfff8001fff000

def z954 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xca876cd364e399f8 0xe543b669b271ccfc

def z955 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xf580ff3ffb1fe7ff 0xfac07f9ffd8ff3ff

def z956 : W := mkw 0x490805042f9f62e2 0xa484028217cfb171 0x01800000031e67e7 0x00c00000018f33f3

def z957 : W := mkw 0x40cd805c06b40b80 0x2066c02e035a05c0 0x2b7f801c05fc01c0 0x15bfc00e02fe00e0

def z958 : W := mkw 0x005480a800000000 0x002a405400000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z959 : W := mkw 0xc09100fd40241f80 0x6048807ea0120fc0 0x808000ff60001fc0 0xc040007fb0000fe0

def z960 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff87ecd367ff99f9 0xffc3f669b3ffccfc

def z961 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x0b7f600005fd8000 0x05bfb00002fec000

def z962 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x4b876cc365e399f9 0xa5c3b661b2f1ccfc

def z963 : W := mkw 0x31227f03e14be07d 0x98913f81f0a5f03e 0x40007f03e003e03e 0xa0003f81f001f01f

def z964 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfdfffffff90001c1 0xfefffffffc8000e0

def z965 : W := mkw 0xe09100fe80241f94 0x7048807f40120fca 0x808000fc80001fc6 0x4040007e40000fe3

def z966 : W := mkw 0x004c800006900000 0x0026400003480000 0xffff902087fe6627 0xffffc81043ff3313

def z967 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffff90fc87fc1fc1 0xffffc87e43fe0fe0

def z968 : W := mkw 0x003150fbd0000000 0x0018a87de8000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z969 : W := mkw 0xe0fcd0ae86955694 0x707e6857434aab4a 0x1078802c021c0600 0x083c4016010e0300

def z970 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x8e8000fc04001fc1 0x4740007e02000fe0

def z971 : W := mkw 0x0077fafbd0200900 0x003bfd7de8100480 0xfffffffffde399f9 0xfffffffffef1ccfc

def z972 : W := mkw 0x016cd50007dbe001 0x80b66a8003edf000 0x7f7ff00007ffe001 0x3fbff80003fff000

def z973 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xcef860c30603fe3f 0xe77c30618301ff1f

def z974 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff93fc9ffc1fc1 0x5fffc9fe4ffe0fe0

def z975 : W := mkw 0xa077fafbd0001414 0x503bfd7de8000a0a 0xfcfffffffa027e3f 0xfe7ffffffd013f1f

def z976 : W := mkw 0x1003285160608969 0x08019428b03044b4 0xee876cd364e199f8 0xf743b669b270ccfc

def z977 : W := mkw 0x404d805406b40b80 0x2026c02a035a05c0 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z978 : W := mkw 0x80f7fafbd0201d00 0x407bfd7de8100e80 0xfc7ffffff8001800 0xfe3ffffffc000c00

def z979 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfd7ffffffb1c0001 0xfebffffffd8e0000

def z980 : W := mkw 0x006cd20006900000 0x0036690003480000 0x3f7f930007fc0001 0x1fbfc98003fe0000

def z981 : W := mkw 0x480805042f0f62e2 0xa40402821787b171 0x03800000071fe7e7 0x01c00000038ff3f3

def z982 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x217f8f0001fc0000 0x10bfc78000fe0000

def z983 : W := mkw 0x014c830006982000 0x80a64180034c1000 0x3f7f830007fc0001 0x1fbfc18003fe0000

def z984 : W := mkw 0x19227f01694be06b 0x8c913f80b4a5f035 0x40007f03f803e03e 0xa0003f81fc01f01f

def z985 : W := mkw 0x006efc0007d3c001 0x00377e0003e9e000 0x7f7ffc0007ffe001 0x3fbffe0003fff000

def z986 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x808000ff00001ff8 0xc040007f80000ffc

def z987 : W := mkw 0x1003285160608969 0x08019428b03044b4 0xce8760d364e399f9 0xe743b069b271ccfc

def z988 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff2007ffe601 0x7fffff9003fff300

def z989 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x1bff80ec07fc1fc1 0x0dffc07603fe0fe0

def z990 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3f7fef0007fd8001 0x1fbff78003fec000

def z991 : W := mkw 0xe0fcd2ae96955694 0x707e69574b4aab4a 0x1078932c9a1c6606 0x083c49964d0e3303

def z992 : W := mkw 0xc80805042f0e36e2 0xe404028217871b71 0x03800000071e7fe7 0x01c00000038f3ff3

def z993 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xb48080fc00001fc0 0x5a40407e00000fe0

def z994 : W := mkw 0x004c810006982000 0x80264080034c1000 0x3f7f930007fc6001 0x1fbfc98003fe3000

def z995 : W := mkw 0x014eaf0007daa001 0x80a7578003ed5000 0x7f7f9f0007fe6001 0x3fbfcf8003ff3000

def z996 : W := mkw 0xa03850a286915414 0x501c28514348aa0a 0xdff870e387fffe3f 0xeffc3871c3ffff1f

def z997 : W := mkw 0x014eaa0006d08001 0x00a7550003684000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z998 : W := mkw 0x40c5805c00b40b80 0x2062c02e005a05c0 0x3d7f801c01fc01c0 0x1ebfc00e00fe00e0

def z999 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfcfffffff8001838 0xfe7ffffffc000c1c

def z1000 : W := mkw 0x0067fa5bd0000000 0x0033fd2de8000000 0x7c7fff1ff8000000 0xbe3fff8ffc000000

def z1001 : W := mkw 0xd09100fd40241f88 0x6848807ea0120fc4 0x808000ff00001fd8 0x4040007f80000fec

def z1002 : W := mkw 0x0057aaf950000000 0x002bd57ca8000000 0x307f8f3c78000000 0x183fc79e3c000000

def z1003 : W := mkw 0x216eff0287dbe015 0x90b77f8143edf00a 0x7f7fff0087ffe007 0x3fbfff8043fff003

def z1004 : W := mkw 0x1003285140608909 0x08019428a0304484 0xef8760d305e399f9 0xf7c3b06982f1ccfc

def z1005 : W := mkw 0x0166ff0001daa001 0x80b37f8000ed5000 0x7d7fff0003fe6001 0x3ebfff8001ff3000

def z1006 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x5e7ff30006ffe001 0x2f3ff980037ff000

def z1007 : W := mkw 0x006efa03d6900000 0x00377d01eb480000 0x7f7fff03fffc0001 0xbfbfff81fffe0000

def z1008 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xd48010fc82027fe7 0xea40087e41013ff3

def z1009 : W := mkw 0x0076faabd0000000 0x003b7d55e8000000 0xf478ff3ff8000000 0xfa3c7f9ffc000000

def z1010 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0xffffffd367fff9f9 0xffffffe9b3fffcfc

def z1011 : W := mkw 0x006eff00079a2000 0x80377f8003cd1000 0x7f7fff0007fe6001 0x3fbfff8003ff3000

def z1012 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xafff00d007fc1fc1 0x57ff806803fe0fe0

def z1013 : W := mkw 0x0044800000900000 0x0022400000480000 0x3d7f800001fc0000 0x1ebfc00000fe0000

def z1014 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0x2b876cd365e399f9 0x15c3b669b2f1ccfc

def z1015 : W := mkw 0xc09100fd50241f80 0x6048807ea8120fc0 0x808000fc78001fc0 0x4040007e3c000fe0

def z1016 : W := mkw 0x00f7fafbd0b00900 0x007bfd7de8580480 0xfc7ffffff8e00000 0xfe3ffffffc700000

def z1017 : W := mkw 0x004c800006900000 0x0026400003480000 0x317f800003fc0000 0x18bfc00001fe0000

def z1018 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x3f7ff30007fde001 0x1fbff98003fef000

def z1019 : W := mkw 0x006cd500079b6000 0x80366a8003cdb000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1020 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xff80ff3cff1fe7e7 0xffc07f9e7f8ff3f3

def z1021 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0xfc7f9ffcf8000000 0xfe3fcffe7c000000

def z1022 : W := mkw 0x116eff0167dbe069 0x88b77f80b3edf034 0x7f7fff0067ffe001 0x3fbfff8033fff000

def z1023 : W := mkw 0x4000000400040280 0x2000000200020140 0xf5809f3cfb1e67e7 0xfac04f9e7d8f33f3

def z1024 : W := mkw 0xa03850aa96015414 0x501c28554b00aa0a 0xdef870ef9e03fe3f 0xef7c3877cf01ff1f

def z1025 : W := mkw 0xd0dd80fd46b41f88 0x686ec07ea35a0fc4 0xbfff80ff07fc1fd9 0x5fffc07f83fe0fec

def z1026 : W := mkw 0x801800a006001400 0x400c005003000a00 0xdef870e38603fe3f 0xef7c3871c301ff1f

def z1027 : W := mkw 0xa008000006015414 0x500400000300aa0a 0xf6809f3cfe03fe3f 0xfb404f9e7f01ff1f

def z1028 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xf4809ffcf8001fc0 0xfa404ffe7c000fe0

def z1029 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5a7fff0006ffe000 0x2d3fff80037ff000

def z1030 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xff879f3cfffe67e7 0xffc3cf9e7fff33f3

def z1031 : W := mkw 0xa077fafbd0001414 0x503bfd7de8000a0a 0xfefffffffc039e3f 0xff7ffffffe01cf1f

def z1032 : W := mkw 0x0057a8f940000000 0x002bd47ca0000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1033 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfffe0ff07fd9fd9 0x5ffff07f83fecfec

def z1034 : W := mkw 0x58032955486cab8b 0xac0194aaa43655c5 0x1a07f3ef9efdfe1e 0x0d03f9f7cf7eff0f

def z1035 : W := mkw 0x0057aaf950000000 0x002bd57ca8000000 0x287f8fdc78000000 0x143fc7ee3c000000

def z1036 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3b7fff0007fde000 0x1dbfff8003fef000

def z1037 : W := mkw 0x0067fa5950000000 0x0033fd2ca8000000 0x307f9f1c78000000 0x183fcf8e3c000000

def z1038 : W := mkw 0xa01800a006015414 0x500c00500300aa0a 0xdef860e30603fe3f 0xef7c30718301ff1f

def z1039 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xfd80fffffb1e67e7 0xfec07ffffd8f33f3

def z1040 : W := mkw 0xc0cc800406b41f80 0x60664002035a0fc0 0x0bff000007fc1fc1 0x05ff800003fe0fe0

def z1041 : W := mkw 0x096eff000fdbe003 0x84b77f8007edf001 0x7f7fff009fffe007 0x3fbfff804ffff003

def z1042 : W := mkw 0x0044800000000000 0x0022400000000000 0xfc7f9f3cf8000000 0xfe3fcf9e7c000000

def z1043 : W := mkw 0x404c800406940280 0x20264002034a0140 0x3f7f801c07fc01c1 0x1fbfc00e03fe00e0

def z1044 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef87efdf7de399f9 0xf7c3f7efbef1ccfc

def z1045 : W := mkw 0xd89100fd68241fea 0x6c48807eb4120ff5 0x808000fff8001ffe 0xc040007ffc000fff

def z1046 : W := mkw 0x10032d51616aa969 0x880196a8b0b554b4 0xff87fff3e7ffffff 0xffc3fff9f3ffffff

def z1047 : W := mkw 0x0075d0fa80000000 0x003ae87d40000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1048 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff87ffd365e399f9 0xffc3ffe9b2f1ccfc

def z1049 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x000000dc000019c0 0x0000006e00000ce0

def z1050 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xabff80fc05fc1fc0 0x55ffc07e02fe0fe0

def z1051 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x337f9f0007ffe001 0x19bfcf8003fff000

def z1052 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x6f7f6c0007ffe001 0x37bfb60003fff000

def z1053 : W := mkw 0x016efb0006996000 0x80b77d80034cb000 0x7f7fff0007fc6001 0x3fbfff8003fe3000

def z1054 : W := mkw 0x004c800006900000 0x0026400003480000 0x7f7f900007fe6001 0x3fbfc80003ff3000

def z1055 : W := mkw 0x0057aaf950000000 0x002bd57ca8000000 0xfc7f9ffcf8000000 0xfe3fcffe7c000000

def z1056 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xd078fffff8000000 0xe83c7ffffc000000

def z1057 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xffff70e387e3fe3f 0xffffb871c3f1ff1f

def z1058 : W := mkw 0x0057aafbd0000000 0x002bd57de8000000 0xbc7f8ffff8000000 0xde3fc7fffc000000

def z1059 : W := mkw 0x096eff002fdbe063 0x84b77f8017edf031 0x7f7fff007fffe001 0x3fbfff803ffff000

def z1060 : W := mkw 0x014c810006996000 0x80a64080034cb000 0x3f7f800007fc6001 0x1fbfc00003fe3000

def z1061 : W := mkw 0x004c800006900000 0x0026400003480000 0x7f7fe00007ff8001 0x3fbff00003ffc000

def z1062 : W := mkw 0x016efe0007d3c001 0x00b77f0003e9e000 0x7f7fec0007ff8001 0x3fbff60003ffc000

def z1063 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xfef8f0ff8603fe3f 0xff7c787fc301ff1f

def z1064 : W := mkw 0xc0dd80ffd6b41f80 0x606ec07feb5a0fc0 0xffff9ffffffc1fc1 0xffffcffffffe0fe0

def z1065 : W := mkw 0x409100ffd0240b80 0x2048807fe81205c0 0x800000fff80001c0 0xc000007ffc0000e0

def z1066 : W := mkw 0x004c800006b00900 0x0026400003580480 0x3fff800007fc19c1 0x1fffc00003fe0ce0

def z1067 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffffc007fff801 0x7fffffe003fffc00

def z1068 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x2b7fef0007ffe001 0x15bff78003fff000

def z1069 : W := mkw 0xa077fafbd0015414 0x503bfd7de800aa0a 0xfcfffffff803fe3e 0xfe7ffffffc01ff1f

def z1070 : W := mkw 0x09227f03f94be063 0x84913f81fca5f031 0x40007f03f803e026 0xa0003f81fc01f013

def z1071 : W := mkw 0x016cd30006996000 0x80b66980034cb000 0x7f7ff30007ffe001 0x3fbff98003fff000

def z1072 : W := mkw 0x10032d51616aa969 0x880196a8b0b554b4 0xff87fffffffff9f9 0xffc3fffffffffcfc

def z1073 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef876cd367e3ffff 0xf7c3b669b3f1ffff

def z1074 : W := mkw 0x10022c0021628969 0x0801160010b144b4 0xef876cc305e399f9 0xf7c3b66182f1ccfc

def z1075 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xdef87fe3fe03fe3f 0xef7c3ff1ff01ff1f

def z1076 : W := mkw 0x216eff0007dbe015 0x90b77f8003edf00a 0x7f7fff0007ffe03f 0x3fbfff8003fff01f

def z1077 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x948000fc02001fc1 0x4a40007e01000fe0

def z1078 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x7f7ff00007ffe001 0x3fbff80003fff000

def z1079 : W := mkw 0x10032c5141628909 0x08019628a0b14484 0xef876cd305e399d9 0x77c3b66982f1ccec

def z1080 : W := mkw 0x104eac0167d28069 0x08275600b3e94034 0x7f7fec0367ff8039 0xbfbff601b3ffc01c

def z1081 : W := mkw 0x29227f02a94be077 0x94913f8154a5f03b 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1082 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0xffffff3cffffe1e1 0xffffff9e7ffff0f0

def z1083 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xbc7f9ffcf8000000 0x5e3fcffe7c000000

def z1084 : W := mkw 0x2077fafbd0014014 0x103bfd7de800a00a 0xfc7ffffff8006006 0xfe3ffffffc003003

def z1085 : W := mkw 0xe0dd80fe86b41f94 0x706ec07f435a0fca 0xffffe0ff87ff9fff 0xfffff07fc3ffcfff

def z1086 : W := mkw 0x18032d51696aa96b 0x8c0196a8b4b554b5 0xff87ffd3fffff9ff 0xffc3ffe9fffffcff

def z1087 : W := mkw 0x2077fafbd0014014 0x103bfd7de800a00a 0xfc7ffffff8018018 0xfe3ffffffc00c00c

def z1088 : W := mkw 0xc0dc80ac06b41f80 0x606e4056035a0fc0 0x3fff802c07fc1fc1 0x1fffc01603fe0fe0

def z1089 : W := mkw 0x1077fafbd0408009 0x083bfd7de8204004 0xfc7ffffff8018018 0xfe3ffffffc00c00c

def z1090 : W := mkw 0x1003285160608969 0x08019428b03044b4 0x0a8760c304e199f8 0x0543b0618270ccfc

def z1091 : W := mkw 0x00032c5001628901 0x0001962800b14480 0xef876cd305e399f9 0xf7c3b66982f1ccfc

def z1092 : W := mkw 0x004c8500079a2000 0x8026428003cd1000 0x3f7f800007fe6001 0x1fbfc00003ff3000

def z1093 : W := mkw 0x016eff0817dbe001 0x80b77f840bedf000 0x7f7fff0c1fffe001 0x3fbfff860ffff000

def z1094 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x75009f3cfb1e67c7 0x3a804f9e7d8f33e3

def z1095 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z1096 : W := mkw 0x014eaf0007daa001 0x80a7578003ed5000 0x7f7fef0007ff8001 0x3fbff78003ffc000

def z1097 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff80fc07fe7fe7 0x5fffc07e03ff3ff3

def z1098 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff87ecff65e399f9 0xffc3f67fb2f1ccfc

def z1099 : W := mkw 0x096eff002fdbe063 0x84b77f8017edf031 0xffffff20ffffe627 0xffffff907ffff313

def z1100 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x8bff00fc07fc1fc1 0x45ff807e03fe0fe0

def z1101 : W := mkw 0xc0b37affd0241f80 0x6059bd7fe8120fc0 0xc0807ffff8001fc0 0xe0403ffffc000fe0

def z1102 : W := mkw 0xc0dd80fd46b41f80 0x606ec07ea35a0fc0 0xbfff80ff67fc1fc1 0xdfffc07fb3fe0fe0

def z1103 : W := mkw 0xc0cc800406b41f80 0x60664002035a0fc0 0xbfff803c07fc1fc1 0x5fffc01e03fe0fe0

def z1104 : W := mkw 0x014eaf0007dbe001 0x80a7578003edf000 0x3f7f8f0007ffe001 0x1fbfc78003fff000

def z1105 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xbfff80ff07fc1ff9 0xdfffc07f83fe0ffc

def z1106 : W := mkw 0xf09100ffe0241ffc 0x7848807ff0120ffe 0x808000ffe0001ffe 0xc040007ff0000fff

def z1107 : W := mkw 0x404c800406940280 0x20264002034a0140 0x3fff800007fc07c1 0x1fffc00003fe03e0

def z1108 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0x7fffff0007ffe1e1 0x3fffff8003fff0f0

def z1109 : W := mkw 0x40dd80fc06b40b80 0x206ec07e035a05c0 0xbf7f80fc07fc01c1 0x5fbfc07e03fe00e0

def z1110 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff1067ffe001 0xffbfff8833fff000

def z1111 : W := mkw 0x40cd805c06b40b80 0x2066c02e035a05c0 0x317f801c03fc01c0 0x18bfc00e01fe00e0

def z1112 : W := mkw 0x0076faabd0000000 0x003b7d55e8000000 0xdc78ffeff8000000 0xee3c7ff7fc000000

def z1113 : W := mkw 0x0067fa5950000000 0x0033fd2ca8000000 0x287fef1c78000000 0x143ff78e3c000000

def z1114 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff877cd367e3f9f9 0xffc3be69b3f1fcfc

def z1115 : W := mkw 0x004c800006900000 0x0026400003480000 0xbfff80c007fc1801 0x5fffc06003fe0c00

def z1116 : W := mkw 0x004c840027920060 0x0026420013c90030 0xffff8c1067fe01e1 0xffffc60833ff00f0

def z1117 : W := mkw 0x09227f00294be063 0x84913f8014a5f031 0x40007f007803e000 0x20003f803c01f000

def z1118 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0xce8060ff04039ff9 0xe740307f8201cffc

def z1119 : W := mkw 0x003050a280000000 0x0018285140000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z1120 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x9ef860e30603fe3f 0x4f7c30718301ff1f

def z1121 : W := mkw 0x805d80f006b01d00 0x402ec07803580e80 0xbfff80f007fc1fc1 0x5fffc07803fe0fe0

def z1122 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x3f7f80dc07fc19c1 0x1fbfc06e03fe0ce0

def z1123 : W := mkw 0xc0cd805c06b41f80 0x6066c02e035a0fc0 0x3fff801c07fc1fc1 0x1fffc00e03fe0fe0

def z1124 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0307ffe039 0xbfbfff8183fff01c

def z1125 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xff876cf367e39ff9 0xffc3b679b3f1cffc

def z1126 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xb07f9ffff8000000 0xd83fcffffc000000

def z1127 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0x5ef870c30603fe3f 0x2f7c38618301ff1f

def z1128 : W := mkw 0x016eff0147dbe001 0x80b77f80a3edf000 0x7f7fff0367ffe001 0xbfbfff81b3fff000

def z1129 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0087ffe027 0xbfbfff8043fff013

def z1130 : W := mkw 0x00022c0021428061 0x0001160010a14030 0xef876cd365e399f9 0xf7c3b669b2f1ccfc

def z1131 : W := mkw 0x004d805006b00900 0x0026c02803580480 0x3f7f801007fc01c1 0x1fbfc00803fe00e0

def z1132 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff1007ffe1c1 0x7fffff8803fff0e0

def z1133 : W := mkw 0xc0d580fc00b41f80 0x606ac07e005a0fc0 0xbdff80fc01fc1fc0 0x5effc07e00fe0fe0

def z1134 : W := mkw 0x216eff0287dbe015 0x90b77f8143edf00a 0xffffffc387fff83f 0xffffffe1c3fffc1f

def z1135 : W := mkw 0xa16eff0007dbf415 0xd0b77f8003edfa0a 0x7f7fff0007ffe607 0x3fbfff8003fff303

def z1136 : W := mkw 0xa03852a296015414 0x501c29514b00aa0a 0xdef873e39e03fe3f 0xef7c39f1cf01ff1f

def z1137 : W := mkw 0xe1fcd3ae869d7694 0xf0fe69d7434ebb4a 0x1078932c821c6606 0x083c4996410e3303

def z1138 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xffffe0fc07ff9fc1 0x7ffff07e03ffcfe0

def z1139 : W := mkw 0xe0dd80fc06b55f94 0x706ec07e035aafca 0xbfff80fc07fc7fc7 0x5fffc07e03fe3fe3

def z1140 : W := mkw 0xe09100fc00241f94 0x7048807e00120fca 0x808000fc00001ffe 0x4040007e00000fff

def z1141 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xb5809f3cfb1c67c7 0x5ac04f9e7d8e33e3

def z1142 : W := mkw 0xc09100fc20241fe0 0x6048807e10120ff0 0x808000fc60001fe0 0xc040007e30000ff0

def z1143 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x7e7fff0006fde000 0x3f3fff80037ef000

def z1144 : W := mkw 0x0076faaa90000000 0x003b7d5548000000 0xfc7fff3cf8000000 0xfe3fff9e7c000000

def z1145 : W := mkw 0x0067fa5950000000 0x0033fd2ca8000000 0xfc7fff3cf8000000 0xfe3fff9e7c000000

def z1146 : W := mkw 0x206cd00286914014 0x103668014348a00a 0x7f7ff00387ffe03f 0xbfbff801c3fff01f

def z1147 : W := mkw 0x1077fafbd0608909 0x083bfd7de8304484 0xfefffffffce39839 0xff7ffffffe71cc1c

def z1148 : W := mkw 0x10032d51616aa969 0x880196a8b0b554b4 0xef87efd365ff99f9 0xf7c3f7e9b2ffccfc

def z1149 : W := mkw 0xa16eff0007dbf415 0xd0b77f8003edfa0a 0x7f7fff0007fff819 0x3fbfff8003fffc0c

def z1150 : W := mkw 0xc89105fc292e3fe2 0xe44882fe14971ff1 0xc0801ffcf8027fe6 0xe0400ffe7c013ff3

def z1151 : W := mkw 0x10032d51616aa969 0x880196a8b0b554b4 0xef876cd367fff9f9 0xf7c3b669b3fffcfc

def z1152 : W := mkw 0x016eff0027dbe061 0x80b77f8013edf030 0x7f7fff0067ffe021 0xbfbfff8033fff010

def z1153 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xec7fefdf78000000 0xf63ff7efbc000000

def z1154 : W := mkw 0xd09100fd60241fe8 0x6848807eb0120ff4 0x808000fc60001fc0 0x4040007e30000fe0

def z1155 : W := mkw 0x11227f03f14be069 0x88913f81f8a5f034 0x40007f03f803e038 0xa0003f81fc01f01c

def z1156 : W := mkw 0x014eaf0007daa001 0x80a7578003ed5000 0x2b7f8f0005fc0000 0x15bfc78002fe0000

def z1157 : W := mkw 0xc0dd80fe96b41f80 0x606ec07f4b5a0fc0 0xbfff80fc9ffc1fc1 0x5fffc07e4ffe0fe0

def z1158 : W := mkw 0x18032d51696aa96b 0x8c0196a8b4b554b5 0xff87fffffde3f9ff 0xffc3fffffef1fcff

def z1159 : W := mkw 0x004eac0007d28001 0x0027560003e94000 0x3f7f8c0007fc0001 0x1fbfc60003fe0000

def z1160 : W := mkw 0xe88805042fbf7ff6 0xf444028217dfbffb 0x0380000007ffffff 0x01c0000003ffffff

def z1161 : W := mkw 0x38227d03e94be07f 0x9c113e81f4a5f03f 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1162 : W := mkw 0x2077fafbd0000014 0x103bfd7de800000a 0xfc7ffffff800003e 0xfe3ffffffc00001f

def z1163 : W := mkw 0x48000104280c22e2 0xa400008214061171 0xf4809f3cfa1c67e6 0xfa404f9e7d0e33f3

def z1164 : W := mkw 0x116eff03f7dbe069 0x88b77f81fbedf034 0x7f7fff03ffffe039 0xbfbfff81fffff01c

def z1165 : W := mkw 0xa077fafbd0001414 0x503bfd7de8000a0a 0xfc7ffffff8000606 0xfe3ffffffc000303

def z1166 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x0a7fe30004fd8000 0x053ff180027ec000

def z1167 : W := mkw 0x10032d51616aa969 0x880196a8b0b554b4 0xef877fd365e3f9f9 0xf7c3bfe9b2f1fcfc

def z1168 : W := mkw 0x5947af5569feabeb 0xaca3d7aab4ff55f5 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z1169 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0005fd8000 0x3fbfff8002fec000

def z1170 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xf5009f3cfb1c67c6 0xfa804f9e7d8e33e3

def z1171 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3f7fe00007ffe001 0x1fbff00003fff000

def z1172 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x808000fc80001fe6 0xc040007e40000ff3

def z1173 : W := mkw 0x003050a280000000 0x0018285140000000 0xdef870e38603fe3f 0xef7c3871c301ff1f

def z1174 : W := mkw 0xc09900f406b41f80 0x604c807a035a0fc0 0xbfff00f007fc1fc1 0x5fff807803fe0fe0

def z1175 : W := mkw 0x014ead0007dbe001 0x80a7568003edf000 0x7f7fec0007ffe001 0x3fbff60003fff000

def z1176 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x31809f3cfb1e67e7 0x18c04f9e7d8f33f3

def z1177 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xcf8760c305e399f9 0xe7c3b06182f1ccfc

def z1178 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfe7ffffffc038001 0xff3ffffffe01c000

def z1179 : W := mkw 0xa077fafbd0001414 0x503bfd7de8000a0a 0xfc7ffffff8001818 0xfe3ffffffc000c0c

def z1180 : W := mkw 0x18032d51696aa96b 0x8c0196a8b4b554b5 0xff877ff3ffe3ffff 0xffc3bff9fff1ffff

def z1181 : W := mkw 0x5847af5d796eabeb 0xac23d7aebcb755f5 0x21078f1c79fc01c0 0x1083c78e3cfe00e0

def z1182 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfcfffffff8000626 0xfe7ffffffc000313

def z1183 : W := mkw 0x004c8500079a2000 0x8026428003cd1000 0x3f7f8f0007fc0001 0x1fbfc78003fe0000

def z1184 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x7c7fff3cf8000000 0x3e3fff9e7c000000

def z1185 : W := mkw 0x0001045021220960 0x00008228109104b0 0xef876cd365e399f9 0xf7c3b669b2f1ccfc

def z1186 : W := mkw 0xd0932cfd61669fe9 0x6849967eb0b34ff4 0xc0806cff60039ff8 0xe040367fb001cffc

def z1187 : W := mkw 0xc88805042f9e36e2 0xe444028217cf1b71 0x01800000031e67e7 0x00c00000018f33f3

def z1188 : W := mkw 0x0003285140200900 0x00019428a0100480 0xef876cd365e399f9 0xf7c3b669b2f1ccfc

def z1189 : W := mkw 0x40d580fc00b40b80 0x206ac07e005a05c0 0xbdff80fc03fc07c1 0x5effc07e01fe03e0

def z1190 : W := mkw 0x0077fafbd0900000 0x003bfd7de8480000 0xfd7ffffff9fc0000 0xfebffffffcfe0000

def z1191 : W := mkw 0x8077fafbd0001400 0x403bfd7de8000a00 0xfcfffffff8001e00 0xfe7ffffffc000f00

def z1192 : W := mkw 0x0066ff00014aa001 0x80337f8000a55000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1193 : W := mkw 0x58000504294ea2eb 0xac00028214a75175 0xf5809f3cfb1fe7ff 0xfac04f9e7d8ff3ff

def z1194 : W := mkw 0x0146af0001daa001 0x80a3578000ed5000 0x3d7f8f0001fc0000 0x1ebfc78000fe0000

def z1195 : W := mkw 0x0066fa0000000000 0x00337d0000000000 0x7c7fff1c78000000 0x3e3fff8e3c000000

def z1196 : W := mkw 0x48000504290e22e2 0xa400028214871171 0x71009f3cfb1e67e6 0xb8804f9e7d8f33f3

def z1197 : W := mkw 0xe0dd80fc06b41f94 0x706ec07e035a0fca 0xbfff80fc07fc1fff 0x5fffc07e03fe0fff

def z1198 : W := mkw 0xe0dd80fe86b55f94 0x706ec07f435aafca 0xbfff80ff87ffffff 0xdfffc07fc3ffffff

def z1199 : W := mkw 0xc89100fc28241fe2 0x6448807e14120ff1 0x808000fc00001fe6 0x4040007e00000ff3

def z1200 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x4b7f7f0007ffe001 0x25bfbf8003fff000

def z1201 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff3cffffe627 0xffffff9e7ffff313

def z1202 : W := mkw 0x296eff02afdbe077 0x94b77f8157edf03b 0x7f7fff03ffffe03f 0xbfbfff81fffff01f

def z1203 : W := mkw 0x006efa0006900000 0x00377d0003480000 0x3f7fe00007fc0001 0x1fbff00003fe0000

def z1204 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x0b7f600007fd8001 0x05bfb00003fec000

def z1205 : W := mkw 0x006cd00006914000 0x003668000348a000 0x3f7f900007fc6001 0x1fbfc80003fe3000

def z1206 : W := mkw 0x116eff0167dbe069 0x88b77f80b3edf034 0xffffffc367fff839 0xffffffe1b3fffc1c

def z1207 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff3c07ffe001 0x7fbfff9e03fff000

def z1208 : W := mkw 0x016eff03d7dbe001 0x80b77f81ebedf000 0xff7fff3fffffe001 0xffbfff9ffffff000

def z1209 : W := mkw 0x581100fff8240bea 0x2c08807ffc1205f5 0x808000fff8001ffe 0xc040007ffc000fff

def z1210 : W := mkw 0x0166ff0001daa001 0x80b37f8000ed5000 0x317f9f0001fc0000 0x18bfcf8000fe0000

def z1211 : W := mkw 0x590805042fffebeb 0xac84028217fff5f5 0x0380000007ffffff 0x01c0000003ffffff

def z1212 : W := mkw 0x006cd00006914000 0x003668000348a000 0x3f7fe00007fd8001 0x1fbff00003fec000

def z1213 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xaf8760d305e399f9 0x57c3b06982f1ccfc

def z1214 : W := mkw 0x016efb0006d9e001 0x80b77d80036cf000 0x107f930002fc6000 0x083fc980017e3000

def z1215 : W := mkw 0x014c850007dbe001 0x80a6428003edf000 0x0b7f000007ffe001 0x05bf800003fff000

def z1216 : W := mkw 0x40d580fc00b40b80 0x206ac07e005a05c0 0x317f803c01fc01c0 0x18bfc01e00fe00e0

def z1217 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x9fff00e007fc1fc1 0x4fff807003fe0fe0

def z1218 : W := mkw 0xc01900f406241f80 0x600c807a03120fc0 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z1219 : W := mkw 0x1003285160608969 0x08019428b03044b4 0x0a0760d364e199d8 0x0503b069b270ccec

def z1220 : W := mkw 0x18227f03f94aa06b 0x8c113f81fca55035 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1221 : W := mkw 0xd09100fc20241fe8 0x6848807e10120ff4 0x808000fc00001ff8 0x4040007e00000ffc

def z1222 : W := mkw 0xc09100fc00241f80 0x6048807e00120fc0 0x008000c000001fc0 0x0040006000000fe0

def z1223 : W := mkw 0x18032d51696aa96b 0x8c0196a8b4b554b5 0xef876fd37de399f9 0xf7c3b7e9bef1ccfc

def z1224 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff2087ffe607 0x3fbfff9043fff303

def z1225 : W := mkw 0x1003285140608909 0x08019428a0304484 0xef876cd365e199d9 0xf7c3b669b2f0ccec

def z1226 : W := mkw 0x10032c5161628969 0x08019628b0b144b4 0xef076cd365e199d8 0xf783b669b2f0ccec

def z1227 : W := mkw 0x0166ff0001daa001 0x80b37f8000ed5000 0x297fef0001fc0000 0x14bff78000fe0000

def z1228 : W := mkw 0xc0dc80ac06941680 0x606e4056034a0b40 0xbfff803c07fc07c1 0x5fffc01e03fe03e0

def z1229 : W := mkw 0x0077fafbd0200900 0x003bfd7de8100480 0xfe7ffffffce01800 0xff3ffffffe700c00

def z1230 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff1c7fffe001 0x3fbfff8e3ffff000

def z1231 : W := mkw 0xe0dd80fe86b41f94 0x706ec07f435a0fca 0xffff90ff87fe7fff 0xffffc87fc3ff3fff

def z1232 : W := mkw 0x1003285140608909 0x08019428a0304484 0x2b0760d305e199d8 0x1583b06982f0ccec

def z1233 : W := mkw 0xe0dd80fe86b41f94 0x706ec07f435a0fca 0xbfff80ff07fc1fd9 0x5fffc07f83fe0fec

def z1234 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7d7fff0003fc6000 0x3ebfff8001fe3000

def z1235 : W := mkw 0x18032d51696aa96b 0x8c0196a8b4b554b5 0xef876cd365e3f9ff 0xf7c3b669b2f1fcff

def z1236 : W := mkw 0x006efa0006914000 0x00377d000348a000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1237 : W := mkw 0x0077faf800000000 0x003bfd7c00000000 0xfc7ffffcf8000000 0xfe3ffffe7c000000

def z1238 : W := mkw 0x012a7d0007dbe001 0x80953e8003edf000 0x7f7f7c0007ffe001 0x3fbfbe0003fff000

def z1239 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xb5ff803c03fc07c1 0x5affc01e01fe03e0

def z1240 : W := mkw 0x804c800006901400 0x4026400003480a00 0x3fff800007fc1e01 0x1fffc00003fe0f00

def z1241 : W := mkw 0xc09104fc21261fe0 0x6048827e10930ff0 0xe5800cfc61021fe1 0xf2c0067e30810ff0

def z1242 : W := mkw 0x003378f3c0000000 0x0019bc79e0000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1243 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x6b7fff0005ffe000 0x35bfff8002fff000

def z1244 : W := mkw 0x016efa0006d1c001 0x00b77d000368e000 0x2b7fe00005fd8000 0x15bff00002fec000

def z1245 : W := mkw 0x016eff0287dbe001 0x80b77f8143edf000 0x7f7fff0387ffe001 0xbfbfff81c3fff000

def z1246 : W := mkw 0x004c840007920000 0x0026420003c90000 0x7f7f8c0007fe0001 0x3fbfc60003ff0000

def z1247 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0x687fffdff8000000 0xb43fffeffc000000

def z1248 : W := mkw 0x48000504290e22e2 0xa400028214871171 0xb1809f3cfb1c67e6 0xd8c04f9e7d8e33f3

def z1249 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0xb1ff80fc03fc1fc0 0x58ffc07e01fe0fe0

def z1250 : W := mkw 0x096eff002fdbe063 0x84b77f8017edf031 0xffffff10ffffe1e7 0xffffff887ffff0f3

def z1251 : W := mkw 0x0064d20000000000 0x0032690000000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z1252 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xfff870f38703ffff 0xfffc3879c381ffff

def z1253 : W := mkw 0xd88805042ffebfeb 0xec44028217ff5ff5 0x0380000007ffffff 0x01c0000003ffffff

def z1254 : W := mkw 0xc0dd80fc06b41f80 0x606ec07e035a0fc0 0x0b7f00c005fc19c0 0x05bf806002fe0ce0

def z1255 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfc7ffffff8026026 0xfe3ffffffc013013

def z1256 : W := mkw 0xa028500006015414 0x501428000300aa0a 0xdef870c30603fe3f 0xef7c38618301ff1f

def z1257 : W := mkw 0x001000a000000000 0x0008005000000000 0xfc789ffcf8000000 0xfe3c4ffe7c000000

def z1258 : W := mkw 0x40cd805c06b40b80 0x2066c02e035a05c0 0xbfff803c07fc07c1 0x5fffc01e03fe03e0

def z1259 : W := mkw 0xa03850a286015414 0x501c28514300aa0a 0xfef87cf3e603fe3f 0xff7c3e79f301ff1f

def z1260 : W := mkw 0xe89100fea8241ff6 0x7448807f54120ffb 0x808000fff8001ffe 0xc040007ffc000fff

def z1261 : W := mkw 0x0077fafbd0000000 0x003bfd7de8000000 0xfc7ffffffa006606 0xfe3ffffffd003303

def z1262 : W := mkw 0x005580f800000000 0x002ac07c00000000 0xbc7f8ffc78000000 0x5e3fc7fe3c000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z9,z6]),(0,[z0,z2,z10,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z11])],[(0,[z12,z0,z1,z2,z13,z4,z5]),(0,[z14,z0,z1,z15,z4,z5,z6]),(0,[z16,z0,z2,z17,z4,z5,z6]),(0,[z0,z1,z2,z18,z4,z5,z6]),(1,[z0,z1,z19,z4,z5,z6]),(0,[z0,z1,z20,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z21,z6]),(0,[z0,z1,z2,z4,z5,z22,z6]),(0,[z23,z0,z1,z2,z24,z5,z6]),(0,[z23,z0,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z4,z26,z5,z6]),(0,[z27,z0,z1,z28,z4,z5,z6]),(1,[z29,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z30,z31])],[(0,[z0,z1,z2,z4,z5,z6,z32]),(0,[z0,z1,z2,z4,z5,z6,z25]),(0,[z33,z0,z1,z2,z4,z5,z6]),(0,[z34,z0,z1,z2,z4,z5,z6]),(0,[z14,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z35,z5,z6]),(0,[z36,z0,z1,z2,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z37,z6]),(0,[z0,z1,z2,z4,z38,z5,z6]),(0,[z39,z0,z1,z2,z40,z5,z6]),(0,[z41,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z42,z5,z6]),(0,[z0,z43,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z44,z31])],[(0,[z45,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z46,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z14,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z47,z4,z5,z48,z6])],[(1,[z49,z1,z2,z4,z5,z6]),(1,[z0,z1,z50,z2,z51,z5]),(0,[z52,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z54,z4,z5,z6]),(1,[z0,z1,z47,z4,z5,z48]),(0,[z0,z1,z2,z4,z55,z5,z6])]],
   [[(0,[z0,z1,z2,z56,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z57]),(1,[z12,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z58,z4,z5,z6])],[(0,[z0,z59,z1,z2,z4,z5,z6]),(0,[z0,z1,z60,z2,z4,z5,z6]),(0,[z0,z61,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z17,z4,z5,z6]),(0,[z16,z0,z2,z62,z4,z5,z6]),(0,[z63,z0,z64,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z65]),(0,[z0,z1,z2,z66,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z67]),(0,[z0,z1,z2,z4,z5,z6,z68])],[(0,[z23,z1,z2,z4,z5,z37,z6]),(0,[z0,z1,z2,z69,z4,z5,z6]),(0,[z0,z1,z2,z70,z4,z5,z6]),(0,[z71,z0,z2,z4,z5,z9,z6]),(0,[z0,z2,z4,z72,z5,z9,z6]),(0,[z0,z1,z2,z4,z73,z5,z6])],[(0,[z1,z2,z4,z74,z5,z75,z6]),(0,[z0,z1,z2,z4,z5,z6,z76]),(0,[z0,z1,z2,z4,z77,z5,z6]),(0,[z0,z1,z2,z78,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z79]),(0,[z0,z1,z2,z4,z5,z80,z6])],[(0,[z0,z81,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z82]),(0,[z63,z16,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z83,z5,z6]),(0,[z0,z2,z4,z5,z84,z9,z6])],[(0,[z85,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z86,z2,z4,z87,z6])],[(0,[z0,z1,z2,z4,z5,z6,z88]),(0,[z0,z1,z89,z2,z4,z90,z5]),(0,[z0,z1,z2,z91,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z6,z92])]],
   [[(0,[z93,z0,z1,z2,z4,z5,z6]),(0,[z94,z0,z1,z2,z4,z5,z6]),(0,[z95,z0,z1,z2,z4,z5,z6]),(0,[z96,z0,z2,z4,z5,z6,z97]),(0,[z16,z0,z98,z2,z4,z5,z6]),(0,[z16,z0,z99,z2,z4,z5,z6]),(0,[z63,z0,z1,z86,z4,z5,z6])],[(0,[z100,z0,z2,z4,z5,z101,z6]),(0,[z0,z2,z4,z102,z5,z9,z6]),(1,[z103,z16,z0,z2,z4,z5]),(0,[z103,z16,z0,z1,z2,z4,z5]),(0,[z104,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z105,z4,z5,z6,z97]),(0,[z106,z0,z1,z2,z4,z5,z6]),(0,[z23,z107,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z108,z4,z5,z6]),(0,[z0,z109,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z110,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z101,z6]),(1,[z16,z0,z2,z4,z5,z9]),(0,[z16,z0,z47,z2,z4,z5,z6]),(0,[z27,z0,z111,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z6])],[(0,[z113,z0,z1,z2,z4,z5,z6]),(0,[z113,z0,z1,z2,z4,z75,z6]),(0,[z0,z1,z2,z4,z114,z5,z6]),(0,[z71,z0,z1,z2,z4,z102,z6]),(0,[z0,z1,z2,z4,z102,z5,z115]),(0,[z0,z1,z2,z4,z5,z87,z6])],[(0,[z116,z0,z1,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z74,z5,z6]),(0,[z0,z1,z2,z117,z4,z5,z6]),(0,[z0,z1,z2,z118,z4,z5,z6]),(0,[z0,z1,z99,z119,z4,z5,z6]),(0,[z0,z1,z2,z120,z4,z5,z6])],[(0,[z121,z0,z1,z2,z4,z5,z6]),(1,[z122,z1,z2,z24,z5,z6]),(0,[z14,z0,z8,z2,z4,z5,z6]),(0,[z103,z0,z123,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z124]),(0,[z125,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z126]),(0,[z1,z2,z4,z5,z6,z127,z30]),(0,[z0,z1,z128,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z129,z0,z1,z2,z4,z5,z6]),(0,[z0,z130,z1,z2,z4,z5,z6]),(1,[z131,z1,z2,z4,z132,z6]),(1,[z0,z133,z2,z4,z5,z6]),(0,[z0,z2,z13,z4,z90,z5,z6]),(0,[z0,z98,z2,z4,z90,z5,z6]),(0,[z27,z0,z1,z19,z4,z5,z6]),(0,[z134,z0,z1,z2,z4,z5,z6])],[(0,[z135,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z136,z4,z5,z6]),(0,[z0,z1,z2,z4,z137,z5,z6]),(0,[z16,z0,z86,z2,z4,z5,z6]),(0,[z0,z138,z2,z4,z5,z9,z6]),(0,[z139,z0,z1,z2,z4,z5,z6]),(0,[z0,z140,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z141,z5,z6]),(0,[z142,z1,z2,z4,z5,z6,z143]),(1,[z0,z144,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z145]),(0,[z146,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z147,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z30]),(0,[z0,z1,z2,z4,z44,z5,z31]),(1,[z0,z2,z4,z5,z6,z67])],[(0,[z1,z2,z24,z4,z5,z37,z6]),(0,[z0,z148,z1,z2,z4,z5,z6]),(0,[z0,z1,z149,z2,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z5,z6]),(0,[z63,z0,z1,z4,z5,z87,z6]),(0,[z0,z1,z2,z62,z4,z5,z48]),(1,[z151,z1,z2,z4,z5,z6]),(0,[z152,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z153,z5,z6]),(0,[z0,z1,z2,z4,z44,z5,z6])],[(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z155,z2,z4,z5,z6]),(0,[z0,z8,z2,z4,z5,z101,z6])],[(0,[z0,z1,z156,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z132,z5,z6]),(0,[z0,z157,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z4,z158,z5,z6])],[(0,[z0,z1,z2,z4,z5,z159,z6]),(0,[z16,z0,z1,z2,z4,z5,z92]),(0,[z27,z0,z1,z2,z5,z6,z143])],[(1,[z160,z1,z105,z4,z5,z6]),(0,[z0,z61,z2,z4,z132,z5,z6]),(0,[z0,z1,z15,z2,z4,z5,z6]),(0,[z0,z1,z161,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z162,z6]),(0,[z0,z1,z50,z2,z51,z5,z6])],[(0,[z0,z1,z2,z4,z163,z5,z6]),(0,[z0,z1,z2,z4,z164,z5,z6]),(1,[z0,z165,z2,z4,z5,z6]),(0,[z166,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z167,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z25]),(0,[z95,z0,z1,z2,z62,z4,z5])]],
   [[(0,[z168,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z169,z6]),(0,[z0,z2,z4,z5,z9,z48,z6]),(0,[z0,z1,z170,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z171])],[(0,[z131,z172,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z173,z6]),(0,[z174,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z175,z5,z6])],[(0,[z16,z122,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z37,z9,z6]),(0,[z0,z2,z4,z5,z87,z9,z6]),(0,[z0,z1,z47,z2,z4,z5,z48])],[(0,[z0,z1,z2,z176,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z177]),(1,[z39,z0,z1,z40,z5,z6]),(1,[z63,z0,z1,z4,z87,z6]),(0,[z178,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z179,z2,z4,z5,z6]),(0,[z0,z1,z2,z180,z4,z5,z6]),(0,[z181,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z182,z6]),(0,[z131,z122,z1,z2,z4,z5,z6]),(0,[z0,z1,z183,z2,z4,z5,z6]),(0,[z71,z0,z2,z4,z5,z101,z6]),(0,[z0,z1,z184,z2,z4,z5,z6]),(1,[z185,z0,z2,z4,z5,z6])],[(0,[z186,z0,z1,z2,z4,z5,z6]),(0,[z187,z16,z0,z2,z4,z5,z6])],[(0,[z1,z2,z105,z24,z4,z5,z6]),(0,[z0,z1,z2,z188,z4,z132,z5]),(0,[z0,z1,z2,z4,z5,z6,z189]),(0,[z0,z1,z190,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z191,z5,z6])],[(0,[z0,z1,z2,z4,z5,z192,z6]),(1,[z0,z1,z2,z4,z5,z193]),(0,[z0,z1,z194,z2,z4,z5,z6]),(0,[z195,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z196,z2,z4,z5,z6]),(0,[z197,z1,z119,z2,z4,z5,z6]),(1,[z0,z1,z2,z198,z5,z6]),(0,[z0,z1,z4,z199,z5,z87,z6]),(0,[z0,z1,z86,z4,z199,z5,z6]),(0,[z0,z1,z50,z200,z4,z5,z6]),(0,[z0,z1,z2,z201,z4,z5,z6])],[(0,[z0,z1,z2,z202,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z203,z6])],[(0,[z204,z0,z1,z2,z4,z5,z6]),(1,[z0,z157,z2,z4,z102,z6]),(0,[z16,z0,z2,z205,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z126])],[(0,[z0,z1,z2,z4,z5,z6,z206]),(0,[z0,z2,z4,z102,z5,z101,z6]),(0,[z16,z0,z2,z4,z5,z6,z207])],[(0,[z16,z0,z2,z105,z4,z5,z6])],[(0,[z131,z95,z1,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z6,z97]),(0,[z208,z0,z1,z2,z4,z5,z6]),(0,[z0,z209,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z210,z5,z6]),(0,[z0,z1,z2,z4,z5,z211,z6]),(0,[z23,z0,z212,z2,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z75,z6]),(0,[z16,z0,z2,z4,z5,z6,z143]),(0,[z0,z1,z47,z2,z4,z5,z207]),(0,[z0,z213,z1,z2,z4,z5,z6])],[(1,[z0,z2,z4,z5,z169,z6]),(0,[z0,z1,z2,z4,z214,z5,z6]),(0,[z0,z1,z2,z4,z215,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z216]),(0,[z217,z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z218,z4,z5,z6]),(1,[z0,z1,z119,z219,z5,z6]),(0,[z220,z0,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z221])]],
   [[(0,[z222,z95,z1,z2,z4,z5,z6]),(0,[z0,z1,z119,z13,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z5,z30])],[(0,[z0,z1,z2,z4,z223,z5,z6]),(0,[z222,z0,z1,z2,z4,z5,z6]),(0,[z224,z0,z1,z2,z4,z5,z6]),(0,[z0,z157,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z225,z4,z102,z5]),(0,[z0,z2,z4,z5,z9,z6,z6])],[(0,[z23,z1,z2,z105,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z226]),(0,[z0,z1,z2,z4,z5,z6,z227]),(0,[z0,z1,z2,z4,z5,z6,z228]),(0,[z0,z1,z2,z229,z4,z5,z6]),(0,[z0,z230,z1,z2,z4,z5,z6])],[(0,[z231,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z232,z6]),(1,[z0,z140,z2,z4,z5,z6]),(0,[z0,z1,z233,z2,z4,z5,z6])],[(0,[z0,z1,z234,z2,z4,z5,z6]),(0,[z0,z1,z2,z13,z4,z5,z6]),(0,[z103,z16,z0,z2,z4,z5,z6]),(0,[z103,z0,z1,z2,z4,z5,z48])],[(0,[z16,z0,z2,z4,z90,z5,z6]),(0,[z235,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z236,z6]),(0,[z0,z2,z237,z4,z5,z9,z6]),(0,[z63,z0,z1,z2,z4,z199,z6]),(0,[z103,z0,z1,z4,z199,z5,z6]),(0,[z0,z1,z2,z62,z4,z51,z5]),(0,[z0,z1,z2,z4,z5,z238,z6])],[(0,[z0,z1,z239,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z240,z6])],[(1,[z14,z0,z2,z90,z5,z6]),(0,[z241,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z9,z6,z11]),(0,[z0,z242,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z127]),(1,[z0,z2,z201,z4,z5,z6])]],
   [[(0,[z0,z1,z243,z4,z40,z5,z6]),(0,[z95,z0,z1,z2,z4,z5,z37])],[(0,[z222,z0,z165,z2,z4,z5,z6]),(0,[z0,z123,z1,z50,z2,z4,z5]),(0,[z29,z0,z1,z2,z4,z5,z6])],[(0,[z0,z172,z1,z2,z4,z5,z6]),(0,[z244,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z97]),(0,[z0,z1,z2,z4,z5,z97,z30]),(0,[z245,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z2,z246,z4,z5,z6]),(0,[z0,z1,z2,z219,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z247,z6])],[(0,[z0,z1,z2,z4,z248,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z249]),(0,[z0,z1,z2,z4,z5,z250,z6]),(0,[z251,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z252,z5,z6]),(0,[z0,z253,z1,z2,z4,z5,z6]),(1,[z16,z0,z2,z4,z5,z92]),(0,[z0,z50,z254,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z31])],[(0,[z255,z0,z1,z2,z4,z5,z6]),(0,[z256,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z257]),(0,[z0,z258,z1,z2,z4,z5,z6]),(0,[z0,z86,z2,z4,z5,z9,z6]),(0,[z1,z119,z2,z259,z4,z5,z6]),(0,[z0,z1,z119,z219,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z6,z143]),(0,[z0,z1,z2,z4,z5,z6,z260]),(0,[z0,z144,z50,z2,z4,z5,z6])],[(0,[z0,z1,z261,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z262]),(0,[z23,z0,z1,z2,z4,z250,z6]),(0,[z23,z0,z2,z4,z5,z9,z6]),(0,[z263,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z264,z6]),(0,[z0,z1,z119,z2,z40,z5,z6]),(0,[z0,z2,z4,z5,z6,z65,z207]),(0,[z265,z0,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z75,z9,z6]),(0,[z131,z1,z2,z4,z5,z37,z6]),(0,[z0,z1,z2,z4,z5,z266,z6]),(0,[z255,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z267])]],
   [[(0,[z0,z1,z268,z2,z4,z5,z6]),(0,[z0,z1,z269,z2,z4,z5,z6]),(0,[z63,z49,z1,z2,z4,z5,z6]),(0,[z103,z0,z1,z2,z4,z5,z207])],[(0,[z16,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z219,z4,z5,z9,z6]),(0,[z0,z1,z2,z219,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z5,z6])],[(0,[z160,z0,z1,z2,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z270,z2,z4,z5,z6]),(0,[z222,z1,z2,z4,z5,z37,z6]),(0,[z0,z1,z2,z4,z5,z6,z271]),(0,[z14,z0,z2,z4,z90,z5,z6]),(0,[z272,z0,z1,z2,z4,z5,z6]),(1,[z0,z233,z2,z4,z5,z6])],[(0,[z273,z0,z172,z2,z4,z5,z6]),(1,[z107,z1,z243,z4,z5,z6]),(0,[z0,z157,z8,z2,z4,z5,z6]),(0,[z0,z1,z2,z274,z4,z5,z6]),(0,[z275,z16,z0,z2,z4,z5,z6])],[(0,[z276,z0,z1,z2,z4,z5,z6]),(0,[z107,z0,z2,z4,z5,z9,z6]),(1,[z0,z1,z2,z277,z4,z5]),(0,[z0,z1,z2,z4,z102,z5,z6]),(0,[z278,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z279,z4,z5,z6]),(0,[z16,z107,z0,z2,z4,z5,z6]),(0,[z131,z1,z2,z4,z132,z5,z6]),(0,[z0,z280,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z281]),(0,[z0,z1,z2,z4,z5,z282,z6]),(0,[z0,z1,z2,z62,z4,z44,z5])],[(0,[z0,z1,z2,z283,z4,z5,z6]),(0,[z0,z1,z2,z4,z284,z5,z6]),(0,[z0,z1,z2,z285,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z286,z6]),(0,[z0,z1,z119,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z131,z107,z1,z2,z4,z5,z6]),(0,[z0,z212,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z287,z5,z6]),(0,[z288,z1,z2,z4,z102,z5,z6]),(0,[z289,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z290,z4,z5,z6])],[(1,[z0,z98,z99,z4,z5,z6]),(0,[z0,z1,z119,z86,z4,z5,z6]),(0,[z0,z1,z2,z4,z291,z5,z6]),(1,[z1,z2,z4,z5,z6,z127])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z222,z107,z1,z2,z4,z5,z6]),(0,[z95,z1,z2,z4,z5,z6,z97]),(0,[z0,z1,z133,z2,z4,z5,z6]),(0,[z288,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z292,z5,z9,z6]),(0,[z293,z0,z1,z2,z4,z5,z6]),(0,[z0,z151,z1,z2,z4,z5,z6]),(0,[z29,z0,z2,z4,z5,z6,z30])],[(1,[z0,z212,z2,z4,z5,z6]),(0,[z0,z1,z2,z294,z4,z5,z6])],[(0,[z0,z172,z8,z2,z4,z5,z6]),(0,[z1,z2,z4,z132,z5,z75,z6]),(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z9,z6])],[(0,[z296,z16,z0,z2,z4,z5,z6]),(0,[z27,z104,z1,z2,z4,z5,z6])],[(0,[z297,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z298,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z299])],[(0,[z0,z1,z2,z4,z5,z300,z6]),(0,[z39,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z301,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z302,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z86,z2,z4,z199,z6]),(1,[z27,z0,z1,z2,z6,z143]),(1,[z0,z1,z303,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z304,z6]),(0,[z305,z16,z0,z2,z4,z5,z6]),(0,[z16,z0,z2,z10,z4,z5,z6]),(0,[z39,z0,z2,z4,z5,z9,z6]),(0,[z63,z0,z1,z2,z141,z5,z6]),(0,[z306,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z307,z5,z6]),(0,[z95,z0,z1,z2,z4,z5,z31]),(0,[z0,z1,z2,z4,z5,z84,z6]),(0,[z16,z0,z2,z4,z5,z48,z6]),(0,[z0,z123,z1,z2,z112,z4,z5]),(0,[z0,z1,z119,z4,z5,z87,z6]),(1,[z308,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z309,z5,z6]),(0,[z0,z1,z2,z4,z310,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z311]),(0,[z0,z1,z2,z4,z312,z5,z6]),(0,[z166,z0,z2,z4,z5,z6,z207])],[(0,[z0,z1,z313,z2,z4,z5,z6]),(0,[z314,z0,z1,z2,z4,z5,z6])],[(0,[z273,z0,z157,z2,z4,z5,z6]),(0,[z95,z0,z2,z4,z5,z9,z6]),(0,[z315,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z17,z4,z5,z6])],[(0,[z160,z0,z1,z243,z4,z5,z6]),(0,[z107,z0,z1,z243,z4,z5,z6]),(0,[z0,z1,z2,z316,z4,z5,z6]),(0,[z0,z1,z2,z112,z5,z6,z30])],[(0,[z0,z1,z2,z317,z4,z5,z6]),(1,[z0,z1,z15,z4,z5,z6]),(0,[z0,z2,z17,z4,z5,z9,z6]),(0,[z0,z1,z2,z318,z4,z5,z6]),(0,[z27,z0,z233,z2,z4,z5,z6])]],
   [[(0,[z113,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z37,z6]),(0,[z0,z1,z2,z4,z319,z5,z6]),(0,[z16,z0,z2,z4,z35,z5,z6]),(0,[z0,z1,z2,z320,z4,z5,z6])],[(1,[z16,z0,z2,z4,z5,z97]),(0,[z222,z0,z1,z2,z4,z5,z37]),(1,[z0,z123,z2,z4,z5,z9]),(0,[z0,z1,z2,z35,z5,z6,z143])],[(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z0,z1,z2,z4,z5,z6,z322]),(0,[z23,z0,z1,z2,z4,z323,z6]),(0,[z0,z1,z219,z4,z40,z5,z6]),(0,[z0,z1,z2,z10,z4,z35,z6])],[(0,[z160,z107,z1,z2,z4,z5,z6]),(0,[z324,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z250,z6]),(1,[z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z325])],[(0,[z16,z0,z50,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z326,z6]),(0,[z0,z1,z2,z4,z327,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z328])],[(0,[z329,z0,z1,z2,z4,z5,z6]),(1,[z16,z0,z50,z2,z4,z5]),(0,[z0,z1,z2,z62,z4,z5,z6]),(0,[z0,z1,z330,z2,z4,z5,z6])],[(0,[z0,z1,z2,z331,z4,z5,z6]),(0,[z95,z1,z2,z24,z4,z5,z6]),(0,[z0,z332,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z333,z6]),(0,[z16,z0,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z334,z4,z5,z6]),(0,[z0,z1,z2,z335,z4,z5,z6]),(0,[z0,z1,z4,z40,z5,z48,z6]),(0,[z0,z1,z2,z4,z44,z6,z31])]],
   [[(0,[z336,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z337,z4,z5,z6]),(1,[z338,z1,z2,z4,z5,z6])],[(0,[z113,z1,z2,z24,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z339,z6]),(1,[z0,z1,z89,z2,z4,z5]),(0,[z0,z2,z78,z4,z5,z9,z6])],[(0,[z16,z0,z243,z2,z4,z5,z6]),(0,[z340,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z198,z5,z6]),(0,[z0,z1,z2,z4,z341,z5,z6])],[(0,[z0,z1,z2,z4,z5,z342,z6]),(0,[z0,z1,z2,z4,z5,z6,z92]),(0,[z0,z1,z2,z4,z5,z6,z343]),(0,[z0,z1,z2,z4,z5,z207,z31]),(0,[z0,z1,z2,z4,z5,z344,z6]),(0,[z0,z1,z2,z4,z5,z6,z221])],[(0,[z0,z1,z99,z2,z4,z5,z6]),(0,[z345,z0,z1,z2,z4,z5,z6]),(0,[z0,z346,z1,z2,z4,z5,z6])],[(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z348,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z349,z5,z6])],[(0,[z350,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z243,z119,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z101,z6]),(0,[z0,z2,z4,z5,z101,z9,z6]),(0,[z0,z123,z1,z47,z2,z4,z5]),(0,[z0,z1,z47,z2,z4,z5,z6]),(0,[z0,z1,z2,z351,z4,z5,z6])],[(0,[z352,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z353,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z354,z5,z6]),(0,[z27,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z355,z4,z5,z6])]],
   [[(0,[z356,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z357,z6]),(0,[z0,z1,z2,z4,z5,z358,z6]),(0,[z359,z16,z0,z2,z4,z5,z6])],[(0,[z100,z273,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z132,z5,z9,z6]),(0,[z0,z1,z2,z4,z51,z5,z37]),(0,[z187,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z360,z5,z6])],[(0,[z172,z1,z268,z2,z4,z5,z6]),(0,[z0,z1,z2,z361,z4,z5,z6]),(0,[z0,z1,z2,z362,z4,z5,z6])],[(0,[z23,z0,z1,z353,z4,z5,z6]),(0,[z0,z2,z4,z74,z5,z9,z6]),(0,[z363,z0,z1,z2,z4,z5,z6]),(0,[z0,z123,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z364,z5,z6]),(0,[z0,z1,z2,z4,z365,z5,z6])],[(0,[z366,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z367,z2,z4,z5,z6]),(0,[z0,z2,z4,z40,z5,z9,z6]),(0,[z0,z1,z2,z368,z4,z5,z6]),(0,[z0,z1,z369,z2,z4,z5,z6])],[(0,[z370,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z371]),(0,[z63,z0,z140,z2,z4,z5,z6]),(0,[z0,z1,z2,z205,z4,z44,z6])],[(0,[z100,z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z372,z6]),(0,[z373,z0,z1,z2,z4,z5,z6]),(0,[z0,z157,z2,z4,z102,z5,z6]),(0,[z0,z1,z2,z4,z374,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z375,z5,z6]),(0,[z376,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z377]),(0,[z0,z1,z2,z378,z4,z5,z6]),(0,[z16,z16,z0,z2,z4,z5,z6]),(0,[z0,z379,z2,z205,z4,z5,z6])]],
   [[(0,[z0,z1,z380,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z381,z5,z6]),(0,[z16,z0,z2,z4,z199,z5,z6]),(0,[z27,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z193,z6]),(0,[z0,z1,z2,z382,z4,z5,z6])],[(0,[z0,z1,z383,z2,z4,z5,z6]),(0,[z384,z0,z1,z2,z4,z5,z6]),(0,[z27,z151,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z385,z6]),(0,[z0,z386,z1,z2,z4,z5,z6]),(0,[z387,z0,z1,z2,z4,z5,z6])],[(0,[z100,z0,z1,z2,z4,z5,z388]),(0,[z389,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z390,z4,z5,z6]),(0,[z131,z0,z2,z4,z5,z9,z6]),(0,[z222,z0,z1,z2,z4,z5,z31]),(0,[z217,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z391,z5,z6]),(0,[z0,z2,z4,z5,z9,z6,z31]),(0,[z0,z1,z2,z392,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z393,z6])],[(0,[z0,z1,z2,z4,z394,z5,z6]),(0,[z222,z0,z133,z2,z4,z5,z6]),(0,[z0,z1,z2,z395,z4,z5,z6]),(0,[z338,z0,z1,z2,z4,z5,z6])],[(0,[z396,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z397,z5,z6]),(0,[z0,z1,z2,z4,z5,z398,z6])],[(0,[z0,z1,z2,z399,z4,z5,z6]),(0,[z222,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z37,z30]),(0,[z0,z157,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z292,z5,z6]),(1,[z16,z0,z2,z112,z4,z5]),(0,[z0,z1,z2,z400,z4,z5,z6]),(0,[z0,z1,z2,z4,z401,z5,z6]),(0,[z0,z1,z2,z4,z402,z5,z6])],[(1,[z0,z1,z2,z4,z323,z6]),(0,[z0,z1,z2,z403,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z388]),(0,[z160,z0,z1,z105,z4,z5,z6]),(0,[z107,z0,z1,z105,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z404]),(0,[z0,z1,z2,z405,z4,z5,z6]),(1,[z0,z61,z2,z4,z5,z6]),(1,[z96,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z287,z5,z6]),(0,[z71,z0,z1,z2,z4,z101,z6]),(0,[z0,z1,z2,z4,z5,z406,z6]),(0,[z103,z0,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z407]),(0,[z0,z408,z1,z2,z4,z5,z6])],[(0,[z0,z172,z2,z4,z90,z5,z6]),(0,[z0,z1,z2,z277,z4,z90,z5]),(0,[z63,z103,z0,z1,z4,z5,z6]),(0,[z0,z1,z409,z2,z4,z5,z6])],[(0,[z0,z1,z105,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z410,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z411]),(0,[z0,z2,z4,z5,z6,z221,z30])],[(0,[z160,z1,z2,z105,z4,z5,z6]),(0,[z296,z0,z1,z13,z4,z5,z6]),(0,[z296,z0,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z4,z412,z5,z6]),(0,[z16,z0,z2,z112,z4,z5,z6]),(0,[z0,z1,z2,z259,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z162])],[(0,[z1,z243,z2,z105,z4,z5,z6]),(0,[z107,z1,z2,z4,z5,z6,z97]),(0,[z95,z1,z2,z4,z5,z75,z6]),(0,[z14,z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z413,z5,z6]),(0,[z0,z2,z4,z5,z9,z6,z281]),(1,[z414,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z198,z4,z5,z6])],[(0,[z0,z1,z415,z2,z4,z5,z6]),(0,[z0,z1,z89,z2,z4,z5,z6]),(0,[z16,z0,z2,z120,z4,z5,z6]),(0,[z36,z1,z2,z205,z4,z5,z6])],[(0,[z416,z0,z1,z2,z4,z5,z6]),(0,[z417,z0,z1,z2,z4,z5,z6]),(0,[z0,z98,z1,z13,z4,z5,z6]),(0,[z0,z47,z2,z4,z5,z9,z6])],[(0,[z0,z172,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z418,z4,z5,z6]),(0,[z113,z1,z2,z4,z5,z75,z6]),(0,[z0,z157,z1,z2,z4,z102,z6]),(0,[z0,z1,z2,z4,z5,z6,z207])]],
   [[(0,[z0,z1,z2,z105,z4,z5,z6]),(0,[z0,z1,z2,z4,z419,z5,z6]),(0,[z14,z0,z1,z420,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z421,z6]),(0,[z0,z1,z2,z4,z5,z422,z6]),(0,[z423,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z424,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z97]),(0,[z0,z1,z2,z425,z4,z5,z6]),(0,[z71,z16,z0,z2,z4,z5,z6]),(0,[z16,z0,z1,z50,z2,z4,z5]),(1,[z0,z1,z2,z10,z35,z6])],[(0,[z0,z1,z2,z4,z426,z5,z6]),(0,[z0,z1,z2,z427,z4,z5,z6]),(0,[z16,z0,z149,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z44,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z428]),(0,[z0,z1,z2,z4,z5,z6,z143])],[(0,[z429,z0,z1,z2,z4,z5,z6]),(0,[z222,z0,z1,z2,z62,z4,z5]),(0,[z0,z1,z2,z4,z430,z5,z6]),(0,[z0,z1,z2,z4,z431,z5,z6]),(0,[z0,z308,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z5,z31]),(0,[z0,z432,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z75,z37,z6]),(0,[z0,z1,z2,z4,z5,z6,z433]),(0,[z0,z1,z434,z2,z4,z5,z6]),(0,[z0,z1,z2,z303,z4,z5,z6])],[(0,[z0,z435,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z9,z6,z299]),(0,[z0,z2,z4,z199,z5,z9,z6])],[(1,[z0,z1,z2,z188,z4,z5]),(1,[z0,z2,z403,z4,z5,z6]),(0,[z0,z1,z2,z4,z436,z5,z6])],[(0,[z160,z0,z2,z4,z5,z9,z6]),(0,[z1,z2,z105,z4,z5,z75,z6]),(0,[z0,z1,z437,z2,z4,z5,z6]),(0,[z0,z1,z438,z2,z4,z5,z6]),(0,[z0,z1,z2,z439,z4,z5,z6]),(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z440,z16,z0,z2,z4,z5,z6]),(0,[z0,z441,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z442,z5,z6])]],
   [[(0,[z273,z1,z268,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z443,z5,z6]),(0,[z0,z1,z2,z4,z5,z444,z6]),(0,[z0,z1,z2,z4,z445,z5,z6]),(1,[z0,z1,z353,z4,z5,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z447,z5,z6]),(0,[z0,z1,z2,z448,z4,z5,z6]),(0,[z0,z1,z50,z2,z4,z51,z5])],[(0,[z0,z1,z2,z4,z90,z5,z6]),(0,[z0,z1,z2,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z449,z5,z6]),(1,[z0,z254,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z450,z5,z6]),(0,[z0,z1,z2,z451,z4,z5,z6]),(0,[z452,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z453,z2,z4,z5,z6]),(1,[z16,z0,z47,z2,z4,z5]),(0,[z0,z2,z4,z5,z9,z6,z311])],[(0,[z122,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z454]),(0,[z455,z0,z1,z2,z4,z5,z6]),(0,[z0,z209,z47,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z456,z6])],[(0,[z122,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z132,z35,z6]),(0,[z0,z1,z2,z4,z5,z6,z457]),(1,[z1,z2,z259,z4,z5,z6]),(0,[z0,z111,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z67,z31])],[(0,[z0,z157,z98,z2,z4,z5,z6]),(0,[z0,z1,z2,z246,z4,z5,z6]),(0,[z39,z0,z1,z4,z40,z5,z6]),(0,[z458,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z459,z5,z6]),(1,[z0,z1,z200,z4,z5,z6])],[(0,[z273,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z460,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z461,z4,z5,z6]),(0,[z107,z1,z2,z24,z4,z5,z6]),(0,[z0,z462,z1,z2,z4,z5,z6]),(0,[z463,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z464]),(0,[z27,z0,z1,z2,z4,z5,z162]),(1,[z178,z0,z1,z4,z5,z6])],[(0,[z0,z2,z24,z4,z5,z9,z6]),(0,[z296,z0,z1,z2,z4,z5,z6]),(0,[z0,z465,z1,z2,z4,z5,z6]),(0,[z0,z1,z466,z2,z4,z5,z6]),(0,[z295,z0,z2,z4,z5,z9,z6])],[(0,[z113,z0,z1,z2,z4,z132,z6]),(0,[z0,z119,z2,z4,z5,z9,z6]),(0,[z0,z2,z4,z5,z9,z6,z30]),(0,[z0,z2,z62,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z467])],[(0,[z0,z1,z2,z4,z468,z5,z6]),(0,[z0,z1,z2,z4,z5,z469,z6]),(0,[z0,z123,z1,z2,z4,z5,z37]),(1,[z296,z0,z13,z4,z5,z6]),(1,[z0,z1,z420,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z388]),(0,[z122,z0,z1,z2,z24,z5,z6]),(0,[z0,z98,z1,z2,z4,z5,z6]),(0,[z0,z2,z17,z4,z90,z5,z6]),(0,[z0,z2,z4,z44,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z470,z6])],[(0,[z471,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z24,z4,z5,z6]),(0,[z63,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z472]),(0,[z473,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z474,z6]),(0,[z0,z1,z2,z4,z5,z6,z475]),(0,[z96,z0,z1,z2,z4,z5,z6]),(0,[z476,z0,z1,z2,z4,z5,z6])],[(0,[z95,z0,z1,z2,z4,z5,z97]),(0,[z0,z1,z2,z4,z477,z5,z6]),(0,[z0,z2,z4,z90,z5,z9,z6])]],
   [[(0,[z478,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z479])],[(0,[z0,z1,z2,z4,z480,z5,z6]),(0,[z0,z1,z2,z4,z5,z481,z6]),(0,[z142,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z205,z62,z4])],[(0,[z0,z1,z482,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z112,z4,z5]),(0,[z0,z2,z4,z5,z9,z6,z92]),(0,[z0,z1,z2,z4,z5,z6,z483]),(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z484,z4,z5,z6])],[(0,[z16,z0,z2,z4,z74,z5,z6]),(0,[z0,z1,z2,z485,z13,z4,z5]),(0,[z0,z1,z2,z486,z4,z5,z6]),(0,[z0,z1,z487,z2,z4,z5,z6])],[(1,[z95,z1,z2,z4,z5,z97])],[(0,[z16,z0,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z10,z40,z5,z6]),(0,[z27,z0,z1,z2,z4,z35,z6]),(0,[z0,z2,z205,z201,z4,z5,z6])],[(0,[z0,z1,z2,z4,z488,z5,z6]),(0,[z16,z0,z2,z4,z5,z236,z6]),(0,[z0,z1,z2,z4,z5,z6,z489])],[(0,[z23,z0,z490,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z491,z5,z6]),(0,[z0,z1,z2,z485,z4,z5,z6]),(0,[z0,z1,z492,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6]),(0,[z185,z0,z2,z4,z5,z6,z31])]],
   [[(0,[z16,z273,z0,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z433]),(0,[z494,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z495,z4,z5,z6])],[(0,[z496,z0,z1,z2,z4,z5,z6]),(0,[z23,z1,z2,z4,z74,z5,z6]),(0,[z0,z1,z2,z497,z4,z5,z6]),(0,[z0,z1,z2,z498,z4,z5,z6])],[(1,[z0,z2,z4,z5,z469,z6]),(1,[z0,z1,z2,z485,z4,z5]),(0,[z0,z499,z1,z2,z4,z5,z6])],[(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z501,z5,z6]),(0,[z0,z8,z1,z2,z17,z5,z6]),(0,[z496,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z62,z4,z6,z31])],[(0,[z0,z2,z105,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z502,z5,z6]),(0,[z0,z165,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z193]),(0,[z0,z1,z2,z4,z5,z6,z503]),(1,[z0,z209,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z504])],[(0,[z505,z0,z1,z2,z4,z5,z6]),(0,[z506,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z8,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z508,z6]),(0,[z16,z0,z2,z4,z5,z6,z31]),(0,[z509,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z510,z4,z5,z6]),(0,[z122,z0,z1,z2,z74,z5,z6]),(0,[z0,z98,z8,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z4,z5,z6,z511]),(0,[z0,z1,z2,z4,z5,z48,z6])],[(0,[z512,z0,z1,z2,z4,z5,z6]),(0,[z0,z513,z1,z2,z4,z5,z6]),(0,[z514,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z4,z51,z5]),(1,[z1,z2,z515,z4,z5,z6])]],
   [[(0,[z516,z0,z1,z2,z4,z5,z6]),(0,[z14,z0,z1,z2,z17,z5,z6]),(1,[z0,z1,z2,z112,z5,z30])],[(0,[z100,z0,z172,z2,z4,z5,z6]),(0,[z0,z47,z2,z403,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z407])],[(0,[z100,z0,z1,z2,z4,z5,z333]),(0,[z16,z0,z172,z2,z4,z5,z6]),(0,[z131,z1,z2,z105,z4,z5,z6]),(0,[z23,z0,z1,z517,z4,z5,z6]),(0,[z296,z0,z1,z99,z4,z5,z6]),(0,[z16,z0,z2,z219,z4,z5,z6]),(1,[z0,z518,z2,z4,z5,z6]),(1,[z0,z1,z28,z4,z5,z6])],[],[(0,[z359,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z519,z4,z5,z6]),(0,[z0,z1,z520,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z4,z5,z521]),(0,[z0,z1,z2,z4,z522,z5,z6]),(0,[z523,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z4,z5,z48,z6]),(0,[z524,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z525,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z526])],[(0,[z222,z1,z2,z105,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z132,z6]),(0,[z527,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z528]),(0,[z0,z98,z1,z99,z4,z5,z6]),(0,[z0,z123,z1,z2,z4,z5,z31]),(0,[z0,z414,z1,z2,z4,z5,z6]),(0,[z103,z0,z1,z47,z4,z5,z6]),(0,[z103,z0,z1,z4,z5,z6,z207]),(0,[z0,z1,z2,z529,z4,z5,z6])],[(0,[z107,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z188,z4,z5,z6]),(0,[z0,z530,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z47,z2,z4,z5]),(0,[z0,z1,z86,z2,z4,z5,z6]),(0,[z531,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z13,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z532,z6]),(0,[z0,z1,z2,z4,z533,z5,z6]),(0,[z0,z1,z2,z4,z534,z5,z6])]],
   [[(0,[z23,z273,z1,z2,z4,z5,z6]),(0,[z1,z2,z24,z4,z74,z5,z6]),(0,[z0,z2,z4,z132,z5,z469,z6]),(0,[z0,z1,z2,z4,z5,z6,z535]),(0,[z0,z123,z2,z4,z5,z9,z6]),(0,[z63,z0,z1,z2,z4,z87,z6]),(0,[z0,z1,z50,z2,z4,z5,z6])],[(0,[z107,z1,z243,z2,z4,z5,z6]),(0,[z0,z2,z4,z90,z5,z101,z6]),(0,[z0,z1,z536,z2,z4,z5,z6]),(0,[z537,z0,z1,z2,z4,z5,z6]),(0,[z0,z538,z1,z2,z4,z5,z6])],[(0,[z0,z539,z1,z2,z4,z5,z6]),(1,[z288,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z540,z5,z6])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z541,z2,z4,z5,z6]),(0,[z0,z8,z1,z2,z90,z5,z6]),(0,[z0,z157,z2,z4,z90,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z542]),(0,[z0,z1,z2,z4,z543,z5,z6]),(0,[z0,z1,z2,z4,z544,z5,z6])],[],[(0,[z545,z0,z1,z2,z4,z5,z6]),(0,[z23,z16,z0,z2,z4,z5,z6]),(0,[z0,z379,z1,z2,z4,z5,z6])],[(0,[z546,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z547,z5,z6]),(0,[z0,z1,z2,z548,z4,z5,z6]),(0,[z0,z1,z2,z549,z4,z5,z6]),(0,[z224,z1,z2,z4,z90,z5,z6]),(0,[z0,z1,z550,z2,z4,z5,z6]),(0,[z255,z16,z0,z2,z4,z5,z6]),(0,[z16,z0,z123,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z9,z6,z207]),(0,[z63,z414,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z126])],[(0,[z0,z1,z2,z4,z72,z5,z6]),(0,[z0,z1,z2,z10,z4,z6,z143])]],
   [[(0,[z0,z2,z4,z5,z9,z6,z97]),(0,[z0,z1,z2,z4,z5,z551,z6]),(0,[z0,z1,z2,z552,z4,z5,z6]),(0,[z14,z0,z1,z2,z90,z5,z6]),(0,[z39,z0,z1,z2,z219,z5,z6]),(0,[z0,z1,z4,z5,z6,z68,z31])],[(0,[z553,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z554,z2,z4,z5,z6]),(0,[z0,z1,z200,z2,z4,z5,z6])],[(0,[z100,z0,z157,z2,z4,z5,z6]),(0,[z555,z0,z1,z2,z4,z5,z6]),(0,[z0,z8,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z556]),(0,[z0,z557,z1,z2,z4,z5,z6]),(1,[z0,z1,z86,z4,z199,z6]),(0,[z0,z1,z4,z199,z5,z48,z6])],[(0,[z558,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z157,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z310,z5,z6]),(0,[z0,z147,z1,z2,z4,z5,z6]),(0,[z39,z0,z1,z119,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z559,z6]),(0,[z276,z16,z0,z2,z4,z5,z6]),(0,[z0,z123,z1,z2,z62,z4,z5]),(0,[z103,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z560,z6]),(0,[z0,z1,z2,z561,z4,z5,z6]),(0,[z0,z1,z254,z2,z4,z5,z6])],[(0,[z0,z562,z1,z2,z4,z5,z6]),(0,[z563,z0,z1,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z565,z5,z6]),(0,[z0,z1,z2,z62,z4,z5,z30])],[(0,[z172,z1,z2,z24,z4,z5,z6]),(0,[z0,z1,z119,z105,z4,z5,z6]),(0,[z0,z1,z2,z4,z566,z5,z6]),(0,[z567,z0,z1,z2,z4,z5,z6]),(1,[z71,z0,z2,z4,z101,z6]),(0,[z16,z0,z2,z4,z5,z87,z6]),(0,[z568,z0,z1,z2,z4,z5,z6]),(1,[z0,z379,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z64,z2,z4,z5,z6]),(0,[z0,z1,z2,z205,z4,z5,z31])],[(0,[z0,z1,z2,z4,z5,z569,z6]),(1,[z1,z2,z4,z5,z532,z6]),(0,[z0,z2,z205,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z570,z5,z6]),(0,[z571,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z205,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z572]),(0,[z16,z0,z1,z2,z62,z4,z5]),(1,[z0,z1,z2,z4,z5,z511]),(0,[z103,z338,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z407,z143]),(0,[z0,z1,z2,z4,z573,z5,z6]),(0,[z0,z1,z2,z4,z574,z5,z6])],[(1,[z273,z268,z2,z4,z5,z6]),(0,[z575,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z576,z6]),(0,[z577,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z578,z6]),(0,[z0,z1,z2,z4,z5,z579,z6])],[(0,[z16,z0,z2,z4,z5,z6,z30]),(0,[z0,z1,z2,z4,z580,z5,z6]),(0,[z0,z1,z2,z4,z199,z5,z6]),(1,[z103,z0,z1,z4,z5,z207]),(0,[z0,z1,z2,z4,z5,z581,z6])],[(0,[z0,z582,z1,z2,z4,z5,z6]),(0,[z16,z0,z8,z2,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z583,z5,z6])],[(0,[z0,z2,z4,z5,z9,z9,z6]),(0,[z0,z1,z2,z4,z584,z5,z6]),(0,[z585,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z517,z4,z5,z6]),(0,[z16,z0,z2,z4,z132,z5,z6]),(0,[z0,z1,z2,z420,z4,z5,z6]),(0,[z1,z2,z4,z287,z90,z5,z6]),(0,[z16,z0,z2,z4,z158,z5,z6]),(0,[z0,z586,z1,z2,z4,z5,z6])]],
   [[(0,[z273,z0,z268,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z5,z97]),(0,[z0,z1,z587,z2,z4,z5,z6]),(1,[z0,z1,z2,z225,z4,z5]),(0,[z39,z16,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z588,z5,z6]),(1,[z0,z1,z2,z4,z5,z521]),(0,[z0,z1,z2,z4,z5,z6,z589]),(0,[z0,z1,z2,z4,z5,z6,z115]),(0,[z0,z1,z2,z590,z4,z5,z6]),(0,[z1,z2,z205,z515,z4,z5,z6])],[(0,[z591,z0,z1,z2,z4,z5,z6]),(0,[z0,z50,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z592,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z333]),(0,[z593,z0,z1,z2,z4,z5,z6]),(0,[z440,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z594,z4,z5,z6])],[(0,[z0,z243,z2,z4,z5,z9,z6]),(0,[z595,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z40,z5,z87,z6]),(0,[z0,z596,z1,z2,z4,z5,z6])],[(0,[z23,z1,z2,z4,z132,z5,z6]),(1,[z0,z8,z2,z17,z5,z6]),(0,[z597,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z598]),(0,[z71,z0,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z599,z6]),(0,[z600,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z601,z6]),(0,[z0,z1,z50,z2,z4,z5,z30])],[(0,[z0,z1,z2,z602,z4,z5,z6]),(0,[z603,z0,z1,z2,z4,z5,z6]),(0,[z113,z16,z0,z2,z4,z5,z6]),(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z237,z4,z5,z6]),(1,[z0,z64,z2,z4,z5,z6])]],
   [[(0,[z605,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z606,z6]),(0,[z0,z1,z607,z2,z4,z5,z6]),(0,[z0,z1,z2,z205,z62,z4,z5])],[(1,[z16,z0,z2,z4,z5,z31]),(0,[z0,z1,z2,z4,z608,z5,z6])],[(0,[z0,z268,z2,z4,z90,z5,z6]),(0,[z0,z609,z1,z2,z4,z5,z6]),(0,[z0,z1,z610,z2,z4,z5,z6]),(0,[z0,z1,z2,z611,z4,z5,z6]),(1,[z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z612,z4,z5,z6]),(0,[z0,z1,z19,z2,z4,z5,z6]),(0,[z178,z0,z1,z4,z5,z6,z31])],[(0,[z1,z2,z4,z5,z37,z6,z97]),(0,[z0,z2,z112,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z613])],[(0,[z273,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z614,z6]),(1,[z224,z1,z2,z4,z5,z6]),(0,[z0,z1,z615,z2,z4,z5,z6]),(0,[z0,z123,z1,z2,z4,z5,z92]),(0,[z0,z1,z2,z4,z616,z5,z6])],[(0,[z0,z1,z2,z4,z617,z5,z6]),(0,[z0,z1,z2,z4,z618,z5,z6]),(0,[z0,z1,z2,z4,z5,z619,z6]),(0,[z0,z620,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z141,z5,z6]),(1,[z0,z2,z4,z5,z6,z65]),(1,[z0,z1,z4,z5,z6,z68])],[(0,[z621,z0,z1,z2,z4,z5,z6]),(0,[z131,z1,z2,z4,z74,z5,z6]),(0,[z296,z0,z2,z4,z5,z9,z6]),(0,[z0,z1,z622,z2,z4,z5,z6])],[(0,[z113,z131,z1,z2,z4,z5,z6]),(0,[z0,z144,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z205,z62,z4,z6])]],
   [[(0,[z0,z268,z2,z4,z5,z9,z6]),(0,[z0,z1,z623,z2,z4,z5,z6]),(0,[z0,z1,z624,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z625,z5,z6]),(0,[z305,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z626,z2,z4,z5,z6]),(0,[z0,z1,z2,z515,z4,z5,z6])],[(0,[z122,z1,z2,z24,z4,z5,z6]),(0,[z0,z2,z13,z4,z5,z9,z6]),(0,[z0,z98,z2,z4,z5,z9,z6]),(0,[z0,z2,z4,z35,z5,z9,z6])],[(0,[z0,z1,z2,z4,z627,z5,z6]),(0,[z0,z1,z138,z2,z4,z5,z6]),(0,[z0,z1,z628,z2,z4,z5,z6])],[(0,[z0,z1,z2,z629,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z37]),(0,[z0,z1,z2,z4,z5,z6,z630]),(0,[z631,z0,z1,z2,z4,z5,z6])],[(0,[z23,z113,z1,z2,z4,z5,z6]),(0,[z0,z1,z632,z2,z4,z5,z6]),(0,[z1,z2,z24,z4,z132,z5,z6]),(1,[z197,z1,z2,z4,z5,z6])],[(0,[z273,z1,z2,z24,z4,z5,z6]),(0,[z172,z1,z2,z4,z5,z75,z6]),(0,[z633,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z634,z5,z6]),(0,[z0,z1,z2,z4,z635,z5,z6])],[(0,[z0,z2,z4,z5,z169,z6,z97]),(0,[z0,z1,z2,z4,z5,z636,z6]),(0,[z0,z1,z518,z2,z4,z5,z6]),(0,[z0,z1,z2,z28,z4,z5,z6])],[(0,[z637,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z51,z5,z9,z6]),(0,[z39,z0,z513,z2,z4,z5,z6]),(0,[z0,z1,z2,z638,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z639,z6]),(0,[z0,z640,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z641,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z642]),(0,[z643,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z644,z4,z5,z6]),(0,[z186,z16,z0,z2,z4,z5,z6]),(1,[z16,z0,z2,z62,z4,z5]),(0,[z0,z1,z50,z2,z112,z5,z6])],[(1,[z23,z1,z2,z74,z5,z6]),(0,[z0,z1,z2,z4,z645,z5,z6]),(0,[z0,z2,z4,z5,z646,z9,z6]),(0,[z0,z1,z2,z62,z4,z5,z207]),(1,[z142,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z647,z5,z6]),(0,[z0,z1,z2,z4,z5,z648,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z650,z0,z1,z2,z4,z5,z6]),(0,[z39,z0,z518,z2,z4,z5,z6])],[(0,[z0,z1,z2,z651,z4,z5,z6]),(0,[z0,z157,z1,z2,z4,z101,z6]),(0,[z0,z1,z2,z4,z5,z652,z6]),(0,[z0,z2,z91,z4,z5,z9,z6])],[(0,[z131,z273,z1,z2,z4,z5,z6]),(0,[z0,z99,z2,z13,z4,z5,z6]),(0,[z0,z1,z653,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z115]),(0,[z0,z1,z2,z4,z654,z5,z6]),(0,[z650,z0,z2,z4,z5,z9,z6]),(0,[z103,z0,z1,z119,z4,z5,z6]),(0,[z0,z1,z119,z4,z5,z48,z6]),(0,[z655,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z656,z5,z6]),(1,[z222,z1,z2,z4,z5,z37]),(0,[z0,z1,z99,z4,z40,z5,z6]),(0,[z0,z492,z2,z4,z5,z9,z6]),(0,[z197,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z277,z4,z5,z6]),(0,[z27,z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z657,z5,z6])]],
   [[(0,[z0,z1,z2,z658,z4,z5,z6]),(0,[z100,z172,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z132,z5,z433]),(0,[z16,z95,z0,z2,z4,z5,z6]),(0,[z659,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z48,z31]),(0,[z0,z1,z2,z10,z4,z5,z6])],[(0,[z660,z0,z1,z2,z4,z5,z6]),(1,[z0,z513,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z521,z6]),(0,[z131,z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z132,z6,z143]),(0,[z0,z1,z2,z225,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z661,z6]),(0,[z152,z1,z2,z4,z5,z6,z30]),(0,[z0,z1,z50,z303,z4,z5,z6])],[(0,[z100,z0,z268,z2,z4,z5,z6]),(0,[z0,z1,z2,z662,z4,z5,z6]),(0,[z663,z0,z1,z2,z4,z5,z6]),(0,[z0,z664,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z665,z6])],[(0,[z16,z0,z268,z2,z4,z5,z6]),(0,[z23,z172,z1,z2,z4,z5,z6]),(0,[z666,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z323,z5,z6]),(0,[z0,z1,z2,z40,z5,z6,z143]),(0,[z0,z1,z2,z667,z4,z5,z6])],[(0,[z668,z0,z1,z2,z4,z5,z6]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z222,z16,z0,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z51,z5,z6]),(0,[z0,z1,z86,z4,z40,z5,z6]),(1,[z152,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z670,z5,z6]),(0,[z273,z0,z2,z4,z5,z101,z6]),(0,[z296,z0,z98,z2,z4,z5,z6]),(0,[z0,z1,z671,z2,z4,z5,z6]),(0,[z0,z123,z1,z2,z4,z5,z9]),(0,[z0,z1,z2,z4,z672,z5,z6]),(0,[z0,z673,z1,z2,z4,z5,z6])],[(0,[z23,z122,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z74,z5,z6]),(0,[z0,z1,z2,z4,z35,z75,z6]),(0,[z0,z1,z2,z219,z5,z6,z143]),(1,[z166,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z35,z5,z6]),(0,[z0,z1,z2,z4,z674,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z675,z5,z6]),(0,[z0,z1,z490,z2,z4,z5,z6]),(0,[z676,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z677]),(0,[z1,z2,z4,z102,z5,z532,z6]),(0,[z16,z0,z2,z4,z102,z5,z6]),(0,[z185,z0,z1,z2,z4,z5,z6])],[(0,[z0,z678,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z679]),(0,[z0,z98,z99,z2,z4,z5,z6])],[(0,[z0,z123,z1,z2,z4,z5,z97]),(0,[z16,z0,z119,z2,z4,z5,z6]),(0,[z0,z1,z119,z2,z219,z5,z6]),(1,[z36,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z680,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z681,z6]),(0,[z0,z2,z13,z4,z5,z101,z6]),(0,[z0,z98,z2,z4,z5,z101,z6]),(0,[z16,z0,z1,z2,z4,z5,z9]),(0,[z682,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z683])],[(0,[z0,z8,z268,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z646,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z685]),(0,[z0,z1,z686,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z687,z5,z6]),(0,[z0,z1,z2,z688,z4,z5,z6])],[(0,[z100,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z689,z5,z6]),(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z31]),(1,[z104,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z51,z5,z6,z30])],[(0,[z245,z16,z0,z2,z4,z5,z6])],[(0,[z100,z0,z2,z4,z5,z9,z6]),(0,[z122,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z691,z4,z5,z6]),(0,[z0,z1,z2,z692,z4,z5,z6]),(0,[z103,z308,z1,z2,z4,z5,z6])]],
   [[(0,[z23,z95,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z693,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z9,z6])],[(0,[z0,z694,z1,z2,z4,z5,z6]),(0,[z0,z1,z243,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z4,z5,z6]),(1,[z113,z1,z2,z4,z75,z6]),(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z696,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z6]),(1,[z16,z0,z2,z4,z5,z37]),(0,[z103,z0,z1,z4,z40,z5,z6])],[(0,[z273,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z517,z4,z5,z6]),(0,[z222,z0,z1,z2,z4,z5,z97]),(0,[z697,z0,z1,z2,z4,z5,z6])],[(0,[z0,z698,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z75,z6,z143]),(0,[z0,z2,z4,z5,z9,z6,z143]),(0,[z63,z0,z1,z2,z4,z5,z511])],[(1,[z100,z172,z2,z4,z5,z6]),(0,[z0,z99,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z699,z4,z5,z6]),(1,[z0,z111,z2,z4,z5,z6])],[(0,[z160,z16,z0,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z48,z6,z207])],[(0,[z700,z0,z1,z2,z4,z5,z6]),(1,[z0,z490,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z701]),(0,[z702,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z703,z5,z6]),(0,[z704,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z705]),(0,[z0,z1,z2,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z4,z5,z6]),(0,[z0,z420,z4,z5,z9,z6]),(0,[z0,z2,z708,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z281]),(0,[z0,z1,z119,z316,z5,z6])],[(0,[z95,z1,z2,z4,z5,z25]),(0,[z0,z2,z4,z709,z5,z6])],[(0,[z103,z16,z0,z4,z40,z5])],[(0,[z710,z0,z2,z4,z5,z6]),(0,[z0,z157,z2,z4,z711,z6]),(0,[z0,z1,z2,z4,z712,z6])],[(0,[z0,z1,z2,z713,z4,z5]),(0,[z0,z714,z2,z4,z5,z6]),(0,[z16,z308,z1,z2,z4,z5]),(0,[z197,z2,z4,z5,z9,z6])],[(0,[z0,z123,z1,z200,z4,z5]),(0,[z2,z515,z201,z4,z5,z6])],[(0,[z107,z243,z4,z5,z9,z6]),(0,[z0,z64,z2,z4,z5,z193]),(0,[z63,z0,z1,z4,z87,z6]),(0,[z715,z1,z2,z4,z5,z6])],[(0,[z23,z1,z2,z670,z5,z6]),(0,[z1,z89,z2,z4,z287,z5]),(0,[z185,z0,z2,z4,z5,z6]),(0,[z2,z4,z5,z532,z9,z6]),(0,[z0,z1,z2,z716,z4,z5])],[(0,[z142,z1,z2,z4,z5,z6]),(0,[z142,z1,z2,z4,z75,z6]),(0,[z0,z1,z2,z717,z4,z5])],[(0,[z16,z0,z2,z4,z5,z299])],[(0,[z95,z1,z2,z4,z5,z82]),(0,[z16,z0,z2,z4,z718,z6])],[(0,[z0,z1,z517,z4,z323,z6]),(0,[z0,z2,z4,z5,z9,z433]),(0,[z0,z123,z2,z4,z5,z67]),(0,[z0,z28,z4,z5,z9,z6])],[(0,[z222,z1,z2,z4,z5,z37]),(0,[z222,z133,z2,z4,z5,z37]),(0,[z16,z147,z2,z4,z5,z37]),(0,[z16,z0,z554,z2,z4,z5]),(0,[z0,z719,z2,z4,z5,z6])],[(0,[z720,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z9,z115]),(0,[z16,z2,z515,z4,z5,z6]),(0,[z721,z0,z2,z4,z5,z6]),(0,[z0,z2,z722,z4,z5,z6])],[(0,[z16,z0,z270,z2,z4,z5]),(0,[z0,z61,z2,z188,z4,z5]),(0,[z275,z0,z149,z4,z5,z6]),(0,[z537,z16,z0,z2,z4,z5]),(0,[z16,z0,z2,z218,z4,z5]),(0,[z151,z1,z2,z4,z6,z143]),(0,[z1,z2,z4,z5,z6,z723])]],
   [[(0,[z131,z1,z2,z4,z210,z6]),(0,[z0,z2,z4,z5,z469,z433]),(0,[z724,z1,z2,z4,z5,z6]),(1,[z16,z308,z2,z4,z5]),(0,[z0,z518,z4,z40,z5,z6])],[(0,[z16,z0,z2,z4,z5,z80]),(0,[z0,z233,z19,z4,z5,z6])],[(0,[z23,z1,z2,z74,z5,z25]),(0,[z0,z15,z4,z5,z9,z6]),(0,[z1,z725,z2,z4,z5,z6])],[(0,[z0,z1,z726,z4,z5,z6]),(0,[z0,z1,z727,z4,z5,z6]),(0,[z152,z1,z2,z4,z5,z31])],[(0,[z0,z1,z2,z4,z5,z728])],[(0,[z160,z1,z729,z4,z5,z6]),(0,[z222,z165,z2,z4,z5,z37]),(0,[z1,z2,z4,z5,z6,z730]),(0,[z1,z2,z731,z4,z5,z6])],[(0,[z273,z147,z2,z4,z5,z6]),(0,[z0,z1,z732,z4,z5,z6]),(0,[z23,z2,z74,z5,z9,z6]),(0,[z152,z2,z4,z5,z9,z6]),(0,[z0,z1,z128,z4,z5,z48]),(0,[z0,z1,z50,z200,z51,z5])],[(0,[z16,z0,z2,z4,z323,z6]),(0,[z0,z140,z2,z4,z5,z6]),(0,[z0,z99,z733,z4,z5,z6]),(0,[z0,z47,z4,z5,z9,z48]),(0,[z0,z2,z4,z5,z6,z734])],[(0,[z0,z2,z485,z403,z4,z5]),(0,[z63,z0,z1,z4,z87,z193])],[(0,[z36,z1,z2,z4,z5,z6]),(0,[z0,z2,z735,z4,z5,z6]),(0,[z16,z0,z2,z4,z736,z6]),(0,[z1,z119,z259,z219,z5,z6]),(0,[z414,z64,z2,z4,z5,z6]),(0,[z0,z737,z2,z4,z5,z6])],[(0,[z100,z738,z2,z4,z5,z6]),(0,[z131,z16,z2,z4,z5,z37]),(0,[z0,z2,z277,z4,z5,z9]),(0,[z103,z308,z1,z4,z5,z207])],[(0,[z0,z739,z2,z4,z5,z6]),(0,[z0,z2,z201,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z740]),(0,[z0,z1,z2,z4,z5,z741]),(0,[z742,z1,z2,z4,z5,z6])],[(0,[z107,z1,z2,z4,z5,z25]),(0,[z178,z0,z4,z5,z6,z67])],[(0,[z152,z1,z2,z4,z5,z25]),(0,[z684,z0,z1,z2,z6,z143])],[(0,[z345,z1,z2,z4,z5,z97]),(0,[z104,z2,z4,z5,z9,z6])],[(0,[z0,z1,z2,z4,z743,z6])]],
   [[(0,[z113,z1,z2,z4,z75,z6]),(0,[z0,z123,z254,z2,z4,z5]),(0,[z0,z1,z2,z667,z62,z4])],[(0,[z0,z1,z2,z4,z744,z6]),(0,[z172,z2,z4,z252,z5,z6])],[(0,[z745,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z746])],[(0,[z0,z1,z2,z747,z5,z6]),(0,[z85,z1,z2,z4,z75,z6]),(1,[z0,z2,z4,z711,z6]),(0,[z748,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z749,z5]),(0,[z750,z1,z2,z4,z5,z6])],[(0,[z0,z212,z2,z4,z5,z521]),(0,[z0,z751,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z570,z5]),(0,[z0,z1,z400,z4,z5,z48])],[(0,[z178,z0,z123,z1,z4,z5])],[(0,[z135,z0,z2,z4,z5,z9]),(0,[z752,z0,z1,z2,z4,z5]),(0,[z107,z1,z243,z4,z5,z6]),(0,[z0,z1,z2,z4,z753,z6]),(0,[z16,z0,z2,z277,z4,z5]),(0,[z754,z1,z2,z4,z5,z6]),(0,[z0,z2,z141,z5,z9,z6])],[(0,[z0,z755,z2,z4,z5,z6]),(0,[z756,z2,z4,z5,z9,z6]),(0,[z0,z140,z2,z4,z5,z193]),(0,[z757,z1,z2,z4,z5,z6]),(0,[z36,z1,z2,z62,z4,z5])],[(0,[z16,z0,z2,z4,z5,z681]),(0,[z296,z12,z0,z2,z4,z5]),(0,[z29,z0,z2,z4,z5,z6]),(0,[z224,z1,z2,z277,z4,z5]),(0,[z16,z0,z2,z4,z5,z371])],[(0,[z1,z2,z4,z74,z250,z6]),(0,[z0,z165,z2,z4,z5,z37]),(0,[z217,z0,z2,z246,z5,z6]),(0,[z16,z36,z2,z4,z5,z6]),(0,[z2,z515,z4,z5,z9,z6])],[(0,[z16,z0,z2,z4,z5,z357])],[],[(0,[z49,z1,z2,z4,z5,z6]),(0,[z16,z0,z2,z331,z4,z5]),(0,[z1,z2,z4,z5,z6,z127])],[(0,[z16,z2,z4,z758,z5,z6]),(0,[z16,z0,z200,z4,z5,z6]),(0,[z0,z2,z91,z5,z6,z11]),(0,[z0,z2,z4,z5,z6,z759])],[(0,[z0,z1,z2,z4,z5,z760]),(0,[z305,z16,z2,z4,z5,z37]),(0,[z12,z0,z1,z2,z4,z5]),(0,[z1,z2,z225,z4,z5,z532]),(0,[z16,z0,z2,z112,z158,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z761]),(0,[z178,z0,z1,z4,z5,z48])],[(0,[z0,z1,z2,z4,z5,z762]),(0,[z0,z763,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z764,z6]),(0,[z765,z1,z2,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z404]),(0,[z0,z766,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z6,z143])],[(0,[z160,z16,z105,z4,z5,z6]),(0,[z0,z1,z2,z767,z5,z6]),(0,[z16,z0,z2,z768,z5,z6]),(0,[z568,z0,z1,z2,z6,z143]),(0,[z0,z1,z2,z4,z769,z6])],[(0,[z16,z0,z2,z4,z5,z481]),(0,[z16,z0,z2,z4,z5,z411])],[],[(0,[z0,z2,z4,z102,z711,z6]),(0,[z16,z0,z2,z4,z5,z770]),(0,[z29,z0,z2,z62,z4,z5]),(0,[z0,z2,z205,z201,z62,z4])],[(0,[z1,z243,z729,z4,z5,z6]),(0,[z771,z0,z2,z4,z5,z521])],[(0,[z0,z1,z2,z4,z5,z772])],[(0,[z1,z2,z4,z250,z37,z6]),(0,[z0,z1,z15,z4,z5,z6]),(0,[z276,z305,z2,z4,z5,z6])],[(0,[z152,z1,z2,z4,z5,z37]),(0,[z16,z0,z2,z403,z4,z5]),(0,[z773,z1,z2,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z9]),(0,[z23,z16,z2,z74,z5,z6]),(0,[z131,z1,z2,z4,z307,z6]),(0,[z0,z123,z2,z4,z5,z9]),(0,[z16,z0,z2,z641,z4,z5])],[(0,[z0,z1,z2,z4,z5,z774]),(0,[z23,z212,z2,z74,z5,z6]),(0,[z0,z775,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z428]),(0,[z0,z2,z4,z5,z9,z126]),(0,[z0,z1,z2,z141,z5,z6]),(0,[z0,z1,z2,z4,z5,z776]),(0,[z49,z1,z2,z4,z5,z193])],[(0,[z0,z2,z4,z5,z9,z6]),(0,[z195,z1,z2,z4,z5,z37]),(0,[z0,z2,z4,z5,z777,z6]),(0,[z0,z1,z2,z4,z778,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z779]),(0,[z780,z0,z2,z4,z5,z6]),(0,[z781,z1,z2,z4,z5,z6])],[(0,[z0,z782,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z783,z6])],[(0,[z0,z784,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z785]),(0,[z0,z47,z403,z4,z5,z48]),(0,[z0,z2,z786,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z787]),(0,[z0,z788,z2,z4,z5,z6])],[(0,[z338,z1,z2,z4,z5,z6]),(0,[z0,z490,z2,z4,z323,z6]),(0,[z0,z1,z2,z4,z5,z789]),(0,[z0,z165,z2,z4,z5,z31]),(0,[z790,z1,z2,z4,z5,z6]),(0,[z27,z1,z2,z6,z407,z143])],[(0,[z16,z0,z2,z117,z4,z5]),(0,[z16,z0,z2,z294,z4,z5]),(0,[z0,z1,z4,z5,z48,z511])],[(0,[z0,z1,z2,z4,z5,z25]),(0,[z178,z16,z0,z2,z4,z5]),(0,[z0,z111,z2,z4,z5,z162])],[(0,[z791,z1,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z247])],[(0,[z0,z1,z792,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z793]),(0,[z288,z1,z2,z225,z4,z5]),(0,[z39,z0,z513,z40,z5,z6]),(0,[z0,z1,z2,z51,z794,z5])],[(0,[z0,z795,z2,z4,z5,z6]),(0,[z796,z1,z2,z4,z5,z6]),(0,[z0,z1,z47,z361,z4,z5])],[(0,[z0,z1,z19,z4,z5,z162]),(0,[z797,z1,z2,z4,z5,z6])],[(0,[z798,z0,z2,z4,z5,z6]),(0,[z0,z2,z799,z4,z5,z6])],[(0,[z0,z2,z4,z5,z800,z6]),(0,[z0,z2,z4,z5,z801,z6])],[(0,[z1,z2,z4,z132,z802,z6]),(0,[z178,z16,z0,z1,z4,z5]),(0,[z803,z1,z2,z4,z5,z6])],[(0,[z142,z1,z2,z4,z250,z6]),(0,[z16,z122,z2,z24,z5,z6]),(0,[z0,z1,z804,z4,z5,z6])],[(0,[z0,z1,z2,z4,z718,z6]),(0,[z0,z1,z2,z198,z5,z6]),(0,[z0,z1,z2,z4,z5,z805]),(0,[z414,z1,z2,z4,z5,z511]),(0,[z0,z1,z2,z141,z5,z193])]],
   [[(0,[z0,z806,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z807])],[(0,[z0,z1,z2,z4,z5,z808]),(0,[z0,z1,z2,z4,z323,z521])],[(0,[z0,z809,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z810,z6]),(0,[z16,z12,z0,z2,z4,z5]),(0,[z0,z2,z4,z5,z811,z6])],[(1,[z1,z2,z812,z5,z6]),(0,[z0,z813,z2,z4,z5,z6])],[],[(0,[z0,z157,z2,z4,z210,z6]),(0,[z0,z2,z4,z5,z6,z814]),(0,[z23,z1,z2,z248,z5,z6]),(0,[z0,z2,z13,z277,z4,z5]),(0,[z649,z16,z0,z2,z4,z5])],[(0,[z815,z1,z2,z4,z5,z6]),(0,[z63,z16,z0,z4,z87,z6]),(0,[z0,z1,z816,z4,z5,z6]),(0,[z817,z1,z2,z4,z5,z6])],[(0,[z296,z0,z120,z4,z5,z6]),(0,[z818,z0,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z162,z143])],[(0,[z1,z2,z4,z507,z75,z6])],[(0,[z0,z2,z4,z5,z819,z6]),(0,[z0,z1,z2,z4,z5,z820])],[(0,[z107,z1,z610,z4,z5,z6])],[(0,[z0,z821,z2,z4,z5,z6]),(0,[z16,z0,z86,z4,z199,z6]),(1,[z178,z16,z0,z4,z5]),(0,[z0,z1,z4,z5,z6,z822])],[(0,[z96,z0,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z407]),(0,[z0,z823,z2,z4,z5,z6]),(0,[z16,z0,z824,z2,z4,z5]),(0,[z1,z2,z825,z4,z5,z6]),(0,[z29,z152,z2,z4,z5,z6])],[(0,[z826,z1,z2,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z211]),(0,[z827,z0,z2,z4,z5,z6]),(0,[z0,z1,z517,z4,z5,z521]),(0,[z14,z0,z2,z90,z5,z6]),(0,[z0,z1,z2,z4,z5,z828])],[(0,[z0,z1,z4,z5,z6,z829]),(0,[z0,z64,z2,z4,z5,z511])]],
   [[(0,[z0,z1,z2,z4,z5,z830]),(0,[z157,z2,z4,z102,z532,z6]),(0,[z0,z1,z2,z198,z5,z193])],[(0,[z0,z1,z2,z4,z5,z831]),(0,[z1,z832,z2,z4,z5,z6]),(0,[z833,z1,z2,z4,z5,z6])],[(0,[z178,z0,z1,z4,z44,z31])],[(0,[z0,z1,z2,z4,z5,z834]),(0,[z131,z61,z2,z4,z5,z6]),(0,[z103,z16,z0,z149,z4,z5]),(0,[z0,z2,z4,z5,z811,z193])],[(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z1,z836,z4,z5,z6]),(0,[z0,z157,z2,z4,z77,z6]),(0,[z39,z0,z40,z5,z9,z6]),(0,[z2,z4,z5,z9,z6,z127]),(0,[z0,z303,z4,z5,z9,z6])],[(0,[z222,z1,z2,z4,z5,z182]),(0,[z113,z1,z2,z4,z250,z6]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z0,z1,z2,z4,z5,z838]),(0,[z0,z1,z839,z4,z5,z6]),(0,[z288,z1,z2,z4,z5,z115]),(0,[z0,z1,z4,z199,z6,z504])],[],[(0,[z16,z0,z517,z4,z5,z6]),(0,[z0,z2,z840,z4,z5,z6]),(0,[z0,z841,z2,z4,z5,z6]),(0,[z103,z0,z1,z141,z5,z6])],[(0,[z61,z2,z4,z5,z75,z6]),(0,[z0,z2,z4,z5,z842,z6]),(0,[z0,z2,z4,z5,z9,z177]),(0,[z16,z0,z2,z225,z4,z5]),(0,[z16,z0,z2,z612,z4,z5]),(0,[z0,z1,z2,z843,z5,z6])],[(0,[z16,z0,z2,z4,z5,z521]),(0,[z669,z16,z0,z2,z4,z5]),(0,[z0,z1,z2,z688,z5,z30])],[(0,[z23,z1,z2,z74,z323,z6]),(0,[z0,z2,z403,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z333]),(0,[z1,z2,z4,z844,z5,z6]),(0,[z131,z2,z4,z132,z9,z6]),(0,[z0,z1,z2,z277,z4,z5]),(0,[z845,z1,z2,z4,z5,z6]),(0,[z0,z1,z20,z219,z5,z6]),(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z1,z2,z10,z6,z847])],[],[],[(0,[z1,z2,z4,z287,z5,z6]),(0,[z848,z0,z2,z4,z5,z6]),(0,[z0,z1,z849,z2,z4,z5]),(0,[z16,z0,z2,z4,z5,z377]),(0,[z850,z1,z2,z4,z5,z6]),(0,[z0,z851,z2,z4,z5,z6])],[(0,[z0,z1,z2,z852,z4,z5]),(0,[z0,z2,z4,z250,z9,z6]),(0,[z0,z2,z4,z5,z6,z770])]],
   [[(0,[z0,z98,z99,z4,z5,z6]),(0,[z359,z147,z2,z4,z5,z6]),(0,[z853,z0,z2,z4,z5,z6]),(0,[z0,z1,z47,z4,z5,z854])],[(0,[z1,z2,z259,z4,z5,z6]),(0,[z131,z16,z2,z4,z132,z6]),(0,[z131,z1,z2,z188,z4,z5]),(0,[z16,z0,z622,z2,z4,z5])],[(0,[z0,z212,z2,z4,z5,z6]),(0,[z71,z0,z2,z4,z236,z6]),(0,[z0,z1,z200,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z847]),(0,[z1,z2,z855,z4,z5,z6])],[(0,[z107,z1,z196,z4,z5,z6]),(0,[z16,z0,z2,z58,z4,z5]),(0,[z0,z1,z2,z112,z158,z5]),(0,[z568,z0,z1,z4,z87,z6]),(0,[z0,z144,z200,z4,z5,z6])],[(0,[z0,z138,z13,z4,z5,z6]),(0,[z1,z2,z4,z5,z532,z115]),(0,[z0,z2,z237,z225,z4,z5]),(0,[z178,z0,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z856]),(0,[z0,z1,z2,z5,z857,z6])],[(0,[z858,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z859,z4,z5]),(0,[z0,z860,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z861]),(0,[z0,z2,z4,z5,z6,z862]),(0,[z0,z2,z863,z4,z5,z6])],[(0,[z0,z2,z4,z323,z9,z6]),(0,[z0,z8,z2,z229,z5,z6]),(0,[z864,z0,z2,z4,z5,z6]),(0,[z29,z0,z2,z112,z5,z30])],[(0,[z738,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z865]),(0,[z16,z0,z2,z4,z5,z182]),(0,[z0,z1,z2,z866,z5,z6]),(0,[z0,z1,z2,z4,z802,z6]),(0,[z0,z1,z2,z768,z5,z6]),(0,[z0,z157,z2,z225,z4,z102]),(0,[z103,z338,z1,z4,z5,z207]),(0,[z0,z1,z2,z794,z5,z6])],[(1,[z16,z0,z200,z4,z5]),(0,[z16,z0,z2,z688,z4,z5]),(0,[z0,z2,z112,z5,z221,z30])],[(0,[z12,z0,z157,z2,z4,z5])],[(0,[z379,z2,z515,z4,z5,z6])],[(0,[z414,z140,z2,z4,z5,z6])],[(0,[z16,z0,z2,z495,z4,z5]),(1,[z0,z1,z4,z778,z6])],[(0,[z1,z2,z105,z4,z5,z25]),(0,[z0,z1,z2,z4,z867,z6]),(0,[z1,z2,z868,z4,z5,z6])]],
   [[(0,[z16,z2,z105,z4,z5,z97]),(0,[z0,z1,z2,z4,z5,z869])],[],[(0,[z506,z16,z0,z2,z4,z5]),(0,[z0,z1,z2,z870,z4,z5]),(0,[z0,z1,z2,z4,z5,z871]),(0,[z872,z1,z2,z4,z5,z6])],[(0,[z0,z873,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z433]),(0,[z0,z2,z302,z4,z5,z9]),(0,[z27,z16,z0,z2,z6,z143])],[(0,[z874,z1,z2,z4,z5,z6]),(0,[z16,z0,z50,z2,z4,z5]),(0,[z875,z1,z2,z4,z5,z6])],[(0,[z0,z98,z2,z277,z4,z5]),(0,[z16,z0,z2,z4,z5,z115]),(0,[z151,z2,z4,z5,z9,z6])],[(0,[z0,z2,z4,z5,z469,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z558,z1,z2,z4,z75,z6]),(0,[z771,z0,z2,z4,z5,z6]),(0,[z0,z877,z2,z4,z5,z6]),(0,[z0,z878,z2,z4,z5,z6]),(0,[z27,z0,z233,z2,z6,z143])],[(0,[z305,z172,z2,z4,z5,z6]),(0,[z0,z1,z729,z4,z5,z6]),(0,[z1,z2,z24,z5,z6,z457]),(0,[z16,z0,z492,z2,z4,z5]),(0,[z879,z1,z2,z4,z5,z6])],[(0,[z95,z1,z2,z117,z4,z5]),(0,[z0,z209,z2,z4,z5,z6]),(0,[z16,z0,z2,z18,z4,z5])],[(0,[z0,z2,z4,z5,z880,z6]),(0,[z881,z1,z2,z4,z5,z6]),(0,[z0,z882,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z883]),(0,[z1,z2,z729,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z342]),(0,[z884,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z250,z25]),(0,[z1,z2,z4,z802,z75,z6]),(0,[z0,z1,z885,z4,z5,z6]),(0,[z166,z0,z47,z2,z4,z5])],[(0,[z63,z0,z64,z4,z87,z6])],[(0,[z0,z1,z886,z4,z5,z6]),(0,[z16,z0,z28,z4,z5,z6]),(0,[z0,z1,z28,z4,z5,z126]),(0,[z0,z1,z2,z35,z6,z847])],[(0,[z0,z1,z2,z887,z4,z5]),(0,[z16,z0,z2,z4,z888,z6])],[]],
   [[(0,[z889,z0,z2,z4,z5,z6]),(0,[z296,z0,z733,z4,z5,z6]),(0,[z0,z1,z890,z4,z5,z6])],[],[(0,[z891,z0,z2,z4,z5,z25])],[(0,[z1,z353,z105,z4,z5,z6]),(0,[z0,z89,z254,z2,z4,z5]),(0,[z0,z2,z4,z5,z9,z193])],[(0,[z0,z490,z517,z4,z5,z6]),(0,[z0,z1,z892,z4,z5,z6]),(0,[z893,z0,z2,z4,z5,z6]),(0,[z222,z1,z2,z4,z5,z894]),(0,[z895,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z5,z6,z847]),(0,[z0,z2,z896,z4,z5,z6])],[(0,[z0,z1,z897,z4,z5,z6])],[(0,[z0,z1,z898,z4,z5,z6]),(0,[z288,z1,z2,z4,z5,z6]),(0,[z100,z172,z2,z4,z5,z333]),(0,[z0,z490,z2,z4,z5,z521])],[(0,[z0,z1,z2,z899,z5,z6]),(0,[z0,z900,z2,z4,z5,z6]),(0,[z0,z1,z2,z794,z5,z30])],[(0,[z0,z901,z2,z4,z5,z6]),(0,[z12,z0,z1,z119,z4,z5]),(0,[z16,z0,z2,z66,z4,z5]),(0,[z0,z1,z2,z4,z794,z5])],[(0,[z0,z1,z2,z4,z5,z902]),(0,[z0,z2,z4,z5,z903,z6]),(0,[z0,z1,z2,z4,z544,z31])],[],[(0,[z0,z904,z2,z4,z5,z6]),(0,[z0,z905,z2,z4,z5,z6]),(0,[z906,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z646,z333]),(0,[z113,z2,z4,z75,z9,z6]),(0,[z0,z1,z2,z4,z5,z907]),(0,[z0,z8,z2,z246,z5,z6]),(0,[z16,z0,z409,z2,z4,z5]),(0,[z908,z0,z1,z4,z5,z6]),(0,[z1,z2,z112,z5,z127,z30]),(0,[z36,z1,z2,z205,z62,z4])],[(0,[z0,z242,z99,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z489])],[(0,[z0,z1,z2,z4,z323,z6]),(0,[z1,z2,z4,z5,z6,z909]),(0,[z16,z0,z2,z4,z5,z358])],[(0,[z295,z16,z0,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z910,z6]),(0,[z107,z1,z729,z4,z5,z6]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z911,z1,z2,z4,z5,z6])],[(0,[z224,z490,z2,z4,z5,z6])],[(0,[z296,z12,z0,z13,z4,z5]),(0,[z0,z1,z912,z4,z5,z6]),(0,[z16,z0,z194,z2,z4,z5])],[(0,[z0,z379,z2,z4,z5,z6]),(0,[z0,z2,z4,z381,z5,z9]),(0,[z913,z1,z2,z4,z5,z6]),(0,[z49,z64,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z914]),(0,[z0,z1,z915,z4,z5,z6]),(0,[z16,z916,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z44,z31]),(0,[z0,z2,z4,z5,z9,z162]),(0,[z414,z1,z2,z141,z5,z6])],[(0,[z1,z2,z4,z5,z532,z6]),(0,[z414,z2,z4,z5,z9,z6]),(0,[z917,z0,z2,z4,z5,z6])],[(0,[z16,z0,z50,z2,z51,z5]),(0,[z0,z123,z2,z4,z5,z918])],[(0,[z0,z2,z4,z5,z711,z6]),(0,[z919,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z594,z62,z4])],[(0,[z0,z920,z2,z4,z5,z6]),(0,[z95,z1,z2,z4,z5,z894]),(0,[z0,z1,z4,z5,z778,z6])],[(0,[z0,z1,z2,z4,z5,z921]),(0,[z16,z0,z2,z590,z4,z5])],[(0,[z0,z2,z4,z5,z922,z6]),(0,[z288,z157,z2,z4,z102,z6])],[(0,[z16,z0,z2,z4,z5,z646]),(0,[z0,z1,z517,z4,z5,z6])],[(0,[z0,z1,z2,z923,z4,z5]),(0,[z0,z1,z2,z225,z4,z5]),(0,[z103,z166,z0,z4,z5,z207])],[(0,[z0,z1,z924,z4,z5,z6])],[(0,[z16,z2,z4,z287,z5,z6])],[(0,[z23,z490,z2,z74,z5,z6]),(0,[z16,z0,z2,z4,z5,z535])]],
   [[(0,[z29,z0,z2,z4,z5,z97]),(0,[z12,z0,z8,z2,z4,z5]),(0,[z0,z89,z2,z4,z5,z9]),(0,[z16,z2,z4,z5,z6,z127]),(0,[z104,z1,z28,z4,z5,z6])],[(0,[z0,z2,z78,z4,z101,z6])],[(0,[z0,z1,z925,z4,z5,z6]),(0,[z131,z2,z4,z132,z469,z6])],[(0,[z14,z0,z2,z277,z90,z5]),(0,[z63,z0,z1,z4,z87,z511])],[(0,[z0,z926,z2,z4,z5,z6]),(0,[z0,z86,z4,z199,z9,z6]),(0,[z0,z64,z2,z141,z5,z6])],[(0,[z927,z0,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z126]),(0,[z414,z1,z2,z198,z5,z6])],[(0,[z16,z0,z2,z4,z5,z6]),(0,[z1,z2,z24,z5,z6,z701]),(0,[z0,z1,z2,z4,z657,z31])],[(0,[z0,z212,z2,z4,z250,z6]),(0,[z0,z1,z928,z4,z5,z6])],[(0,[z224,z1,z2,z4,z5,z6]),(0,[z929,z0,z2,z4,z5,z6]),(0,[z0,z1,z353,z4,z5,z25]),(0,[z0,z492,z2,z72,z5,z6]),(0,[z0,z1,z2,z198,z5,z511])],[(0,[z0,z1,z4,z199,z778,z6]),(0,[z27,z151,z1,z2,z6,z143])],[(0,[z0,z1,z2,z4,z5,z930]),(0,[z0,z1,z2,z4,z931,z6]),(0,[z23,z1,z517,z74,z5,z6]),(0,[z0,z2,z188,z4,z5,z469]),(0,[z0,z233,z28,z4,z5,z6])],[(0,[z0,z123,z2,z4,z5,z169])],[(0,[z0,z932,z2,z4,z5,z6]),(0,[z23,z1,z2,z74,z5,z521]),(0,[z16,z0,z2,z62,z4,z236])],[(0,[z0,z2,z4,z5,z9,z388])],[(0,[z308,z2,z4,z5,z9,z6])],[(0,[z16,z0,z2,z4,z5,z32]),(1,[z0,z2,z933,z5,z6]),(0,[z16,z0,z1,z200,z4,z5]),(0,[z295,z0,z4,z5,z6,z311])]],
   [[(0,[z197,z1,z2,z4,z5,z6]),(0,[z0,z934,z2,z4,z5,z6]),(0,[z0,z935,z518,z2,z4,z5]),(0,[z0,z1,z86,z4,z540,z6])],[(0,[z936,z0,z2,z4,z5,z6]),(0,[z0,z937,z2,z4,z5,z6]),(0,[z1,z2,z4,z938,z5,z6])],[],[(0,[z0,z1,z939,z4,z5,z6]),(0,[z0,z2,z4,z5,z940,z6]),(0,[z0,z2,z225,z4,z5,z101]),(0,[z178,z16,z0,z4,z5,z6]),(0,[z0,z941,z2,z4,z5,z6]),(0,[z0,z140,z2,z4,z5,z511])],[(0,[z0,z942,z2,z4,z5,z6])],[(0,[z95,z2,z4,z5,z9,z97]),(0,[z16,z0,z2,z4,z5,z67]),(0,[z494,z0,z1,z40,z5,z6]),(0,[z0,z64,z2,z198,z5,z6]),(0,[z178,z817,z1,z4,z5,z6])],[(0,[z0,z943,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z433]),(0,[z131,z1,z2,z4,z132,z433]),(0,[z0,z19,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z944])],[(0,[z945,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z946,z6])],[(0,[z0,z1,z947,z4,z5,z6]),(0,[z948,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z949]),(0,[z63,z414,z1,z4,z87,z6]),(0,[z0,z1,z28,z10,z5,z6])],[(0,[z16,z0,z2,z298,z4,z5])],[(0,[z0,z2,z950,z4,z5,z6]),(0,[z1,z2,z812,z74,z5,z6]),(0,[z0,z111,z19,z4,z5,z6])],[(0,[z0,z513,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z951])],[(0,[z16,z0,z437,z2,z4,z5]),(0,[z952,z1,z2,z4,z5,z6]),(0,[z0,z953,z2,z4,z5,z6])],[(0,[z16,z0,z954,z4,z5,z6]),(0,[z16,z0,z119,z219,z5,z6])]],
   [[(0,[z597,z16,z0,z2,z4,z5]),(0,[z0,z1,z2,z955,z5,z6])],[(0,[z1,z2,z4,z956,z5,z6]),(0,[z0,z1,z2,z957,z4,z5]),(0,[z0,z1,z28,z4,z5,z6]),(0,[z958,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z888,z6]),(0,[z0,z2,z4,z5,z959,z6]),(0,[z0,z2,z485,z4,z5,z9]),(0,[z16,z0,z960,z4,z5,z6])],[],[(0,[z16,z0,z2,z4,z5,z145]),(0,[z151,z1,z28,z4,z5,z6])],[(0,[z0,z961,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z770,z31]),(0,[z0,z138,z4,z5,z84,z6])],[(0,[z172,z490,z2,z4,z5,z6]),(0,[z0,z1,z962,z4,z5,z6]),(0,[z0,z1,z2,z963,z4,z5]),(0,[z496,z2,z4,z5,z6,z299]),(0,[z103,z0,z4,z5,z9,z207]),(0,[z2,z4,z5,z9,z6,z407]),(0,[z964,z1,z2,z4,z5,z6])],[(0,[z0,z2,z840,z188,z4,z5]),(0,[z0,z157,z2,z4,z310,z6]),(0,[z0,z2,z4,z5,z6,z965]),(0,[z927,z0,z2,z4,z5,z162])],[(0,[z16,z0,z686,z2,z4,z5]),(0,[z104,z1,z2,z4,z5,z126])],[(0,[z966,z0,z2,z4,z5,z6]),(0,[z16,z0,z254,z2,z4,z5]),(0,[z197,z1,z119,z219,z5,z6]),(0,[z49,z1,z2,z4,z5,z511])],[(0,[z2,z4,z5,z6,z127,z221])],[(0,[z0,z1,z2,z4,z5,z967]),(0,[z14,z0,z420,z90,z5,z6]),(0,[z968,z1,z2,z4,z5,z6]),(0,[z39,z0,z518,z40,z5,z6]),(0,[z0,z1,z4,z5,z6,z969])],[(0,[z0,z2,z4,z5,z970,z6]),(0,[z971,z1,z2,z4,z5,z6])],[(0,[z0,z972,z2,z4,z5,z6]),(0,[z16,z0,z2,z382,z4,z5]),(0,[z27,z0,z1,z2,z6,z847])],[(0,[z0,z1,z2,z4,z973,z6])],[(0,[z0,z1,z2,z4,z5,z974]),(0,[z1,z2,z4,z5,z975,z6]),(0,[z16,z2,z4,z5,z6,z407])]],
   [[],[(0,[z100,z172,z2,z4,z5,z6])],[(0,[z0,z1,z976,z4,z5,z6]),(0,[z0,z8,z2,z651,z5,z6]),(0,[z0,z1,z2,z977,z4,z5]),(0,[z1,z2,z4,z978,z5,z6]),(0,[z0,z1,z86,z4,z199,z6])],[(0,[z0,z490,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z240]),(0,[z756,z1,z2,z4,z5,z6]),(0,[z0,z824,z2,z4,z5,z6])],[(0,[z0,z212,z353,z4,z5,z6]),(0,[z12,z0,z2,z4,z90,z5])],[(0,[z1,z2,z4,z5,z802,z6]),(0,[z0,z254,z200,z4,z5,z6])],[(0,[z979,z1,z2,z4,z5,z6]),(0,[z308,z1,z119,z4,z5,z6])],[(0,[z980,z0,z2,z4,z5,z6]),(0,[z0,z1,z119,z3,z5,z6]),(0,[z1,z2,z4,z981,z5,z6]),(0,[z0,z982,z2,z4,z5,z6])],[(0,[z0,z98,z453,z4,z5,z6]),(0,[z0,z2,z4,z5,z9,z918]),(0,[z0,z983,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z44,z31])],[(0,[z0,z1,z2,z984,z4,z5]),(0,[z985,z0,z2,z4,z5,z6])],[(0,[z273,z268,z2,z4,z5,z6]),(0,[z131,z1,z2,z4,z445,z6]),(0,[z16,z0,z2,z91,z4,z5]),(0,[z0,z1,z2,z141,z5,z511]),(0,[z0,z2,z4,z5,z986,z6]),(0,[z0,z1,z50,z2,z51,z5])],[(0,[z0,z1,z987,z4,z5,z6]),(0,[z0,z119,z219,z5,z9,z6]),(0,[z0,z2,z4,z5,z9,z511]),(0,[z0,z988,z2,z4,z5,z6]),(0,[z0,z144,z50,z2,z51,z5])],[(0,[z0,z1,z2,z4,z5,z989]),(0,[z16,z107,z2,z4,z5,z97]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z63,z0,z1,z4,z778,z6])],[(0,[z16,z0,z2,z4,z5,z599])],[(0,[z16,z0,z2,z4,z5,z227]),(0,[z16,z0,z2,z4,z5,z228])],[(0,[z95,z96,z2,z4,z5,z97]),(0,[z0,z990,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z521]),(0,[z0,z1,z517,z4,z250,z6]),(0,[z0,z1,z4,z5,z6,z991]),(0,[z14,z0,z2,z158,z5,z6]),(0,[z16,z0,z303,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z992])],[(0,[z0,z2,z4,z5,z993,z6]),(0,[z71,z0,z2,z4,z711,z6]),(0,[z994,z0,z2,z4,z5,z6]),(0,[z0,z995,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z333]),(0,[z1,z2,z24,z812,z5,z6]),(0,[z0,z2,z277,z17,z4,z5]),(0,[z16,z0,z2,z4,z996,z6]),(0,[z0,z997,z2,z4,z5,z6])],[(0,[z0,z1,z2,z998,z4,z5]),(0,[z16,z0,z2,z4,z5,z685]),(0,[z567,z0,z1,z40,z5,z6])],[(0,[z999,z1,z2,z4,z5,z6]),(0,[z16,z2,z259,z4,z5,z6]),(0,[z1000,z2,z4,z5,z9,z6])],[(0,[z463,z0,z13,z4,z5,z6]),(0,[z288,z2,z4,z5,z101,z6]),(0,[z0,z379,z2,z62,z4,z5])],[(0,[z0,z2,z4,z5,z6,z1001])],[(0,[z23,z1,z2,z634,z5,z6]),(0,[z16,z288,z2,z4,z5,z6]),(0,[z1002,z1,z2,z4,z5,z6])],[(0,[z0,z2,z1003,z4,z5,z6]),(0,[z0,z1,z1004,z4,z5,z6])],[(0,[z0,z1005,z2,z4,z5,z6]),(0,[z0,z1006,z2,z4,z5,z6]),(0,[z178,z0,z1,z4,z5,z207]),(0,[z0,z1,z2,z4,z5,z126])],[(0,[z1007,z0,z2,z4,z5,z6]),(0,[z12,z0,z1,z4,z40,z5]),(0,[z0,z2,z4,z5,z1008,z6]),(0,[z1009,z1,z2,z4,z5,z6])],[(0,[z305,z1,z2,z4,z5,z37]),(0,[z0,z144,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z711,z6]),(0,[z0,z2,z4,z292,z6,z281]),(0,[z0,z1010,z2,z4,z5,z6])],[(0,[z1011,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z67]),(0,[z16,z0,z2,z62,z4,z310]),(0,[z151,z1,z2,z4,z5,z126])],[(0,[z0,z1,z733,z4,z5,z6]),(0,[z174,z0,z13,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1012]),(0,[z0,z1,z86,z141,z5,z6]),(0,[z27,z142,z1,z2,z6,z143])],[(0,[z1013,z0,z2,z4,z5,z6]),(0,[z0,z1,z86,z4,z778,z6])]],
   [[(0,[z0,z1,z1014,z4,z5,z6]),(0,[z0,z2,z4,z5,z1015,z6])],[(0,[z160,z1,z105,z4,z5,z6]),(0,[z16,z0,z89,z2,z4,z5]),(0,[z1016,z1,z2,z4,z5,z6])],[(0,[z0,z165,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z406]),(0,[z1017,z0,z2,z4,z5,z6]),(0,[z0,z1018,z2,z4,z5,z6]),(0,[z1019,z0,z2,z4,z5,z6])],[(0,[z122,z1,z2,z334,z5,z6]),(0,[z0,z1,z2,z1020,z5,z6]),(0,[z14,z0,z2,z933,z5,z6]),(0,[z224,z1,z89,z2,z4,z5]),(0,[z1021,z1,z2,z4,z5,z6])],[(0,[z2,z4,z287,z5,z9,z6]),(0,[z0,z2,z1022,z4,z5,z6])],[(0,[z0,z1,z2,z1023,z5,z6]),(0,[z0,z1,z184,z40,z5,z6]),(0,[z104,z233,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1024,z6]),(0,[z0,z98,z149,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1025]),(0,[z186,z0,z2,z4,z310,z6]),(0,[z0,z1,z2,z4,z1026,z6])],[(0,[z39,z0,z1,z40,z5,z6]),(0,[z49,z140,z2,z4,z5,z6])],[(0,[z1,z2,z4,z1027,z5,z6]),(0,[z0,z2,z4,z5,z1028,z6]),(0,[z16,z0,z536,z2,z4,z5]),(0,[z16,z0,z2,z62,z4,z5]),(0,[z818,z0,z518,z2,z4,z5]),(0,[z0,z1029,z2,z4,z5,z6]),(0,[z63,z0,z1,z141,z87,z6])],[(0,[z23,z1,z2,z74,z5,z6])],[(0,[z16,z0,z2,z4,z5,z76]),(0,[z16,z0,z2,z1030,z5,z6]),(0,[z16,z0,z2,z4,z5,z193]),(0,[z0,z2,z205,z62,z4,z9]),(0,[z103,z0,z1,z4,z5,z489]),(0,[z185,z0,z4,z5,z6,z68])],[(0,[z16,z0,z541,z2,z4,z5]),(0,[z1,z2,z4,z5,z1031,z6]),(0,[z1032,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1033]),(0,[z0,z1,z119,z1034,z5,z6])],[(0,[z684,z1,z2,z74,z5,z6]),(0,[z0,z1,z2,z4,z5,z115]),(0,[z0,z1,z2,z112,z794,z5])],[(0,[z1035,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z101,z333]),(0,[z0,z2,z4,z5,z9,z589]),(0,[z14,z224,z2,z90,z5,z6]),(0,[z16,z0,z2,z62,z4,z31]),(0,[z103,z0,z1,z120,z4,z5]),(1,[z0,z2,z4,z5,z918])],[(0,[z295,z12,z0,z2,z4,z5]),(0,[z0,z4,z5,z9,z6,z68])]],
   [[(0,[z0,z1,z353,z4,z323,z6]),(0,[z720,z2,z4,z5,z9,z6]),(0,[z0,z1,z1034,z40,z5,z6]),(0,[z29,z0,z2,z112,z4,z5])],[(0,[z16,z2,z4,z5,z75,z37]),(0,[z0,z165,z2,z62,z4,z5]),(0,[z0,z1036,z2,z4,z5,z6])],[(0,[z23,z1,z2,z812,z5,z6]),(0,[z1037,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z169,z6]),(0,[z0,z1,z2,z4,z1038,z6]),(0,[z0,z1,z954,z4,z5,z6]),(0,[z0,z1,z119,z219,z5,z6]),(0,[z1017,z0,z2,z4,z5,z193])],[(0,[z152,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1039,z5,z6]),(0,[z16,z2,z4,z5,z37,z97]),(0,[z0,z1,z2,z4,z5,z1040]),(0,[z166,z0,z2,z4,z5,z31]),(0,[z1,z2,z205,z515,z62,z4])],[(0,[z16,z0,z2,z4,z5,z322]),(0,[z1,z729,z105,z4,z5,z6]),(0,[z0,z1,z960,z4,z5,z6]),(0,[z308,z123,z1,z2,z4,z5])],[(0,[z0,z98,z733,z4,z5,z6]),(0,[z224,z2,z4,z5,z101,z6]),(0,[z16,z0,z4,z5,z68,z31])],[(0,[z478,z16,z0,z2,z4,z5]),(0,[z0,z1041,z2,z4,z5,z6]),(0,[z0,z140,z2,z141,z5,z6]),(0,[z36,z1,z2,z4,z5,z31])],[(0,[z1042,z16,z2,z4,z5,z6]),(0,[z63,z0,z1,z198,z87,z6])],[(0,[z178,z185,z0,z4,z5,z6])],[(0,[z16,z555,z0,z2,z4,z5]),(0,[z16,z0,z2,z4,z5,z162]),(0,[z36,z2,z4,z5,z9,z6])],[(0,[z104,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1043,z4,z5])],[(0,[z172,z738,z2,z4,z5,z6]),(0,[z0,z2,z225,z4,z5,z9])],[(0,[z0,z1,z1044,z4,z5,z6])],[(0,[z0,z172,z2,z277,z4,z5]),(0,[z16,z0,z2,z4,z5,z171]),(0,[z16,z0,z2,z4,z5,z92]),(0,[z0,z2,z4,z5,z6,z1045])]],
   [[(0,[z95,z1,z2,z382,z4,z5]),(0,[z0,z157,z2,z4,z102,z115]),(0,[z440,z0,z2,z4,z236,z6]),(0,[z178,z0,z1,z4,z5,z511])],[(0,[z100,z2,z4,z5,z264,z6]),(0,[z296,z0,z485,z13,z4,z5]),(0,[z0,z2,z4,z933,z5,z6]),(0,[z0,z1,z1046,z4,z5,z6])],[],[(0,[z1047,z1,z2,z4,z5,z6]),(0,[z152,z1,z2,z62,z4,z5])],[],[(0,[z0,z1,z1048,z4,z5,z6]),(0,[z0,z233,z2,z4,z5,z126])],[(0,[z1,z2,z24,z375,z5,z6]),(0,[z0,z233,z2,z4,z5,z6]),(0,[z0,z379,z2,z205,z62,z4])],[(0,[z0,z2,z4,z687,z5,z9])],[(0,[z0,z490,z2,z4,z250,z6]),(0,[z16,z0,z353,z4,z5,z6]),(1,[z1,z2,z4,z802,z6]),(0,[z16,z2,z4,z5,z532,z6]),(0,[z16,z308,z2,z4,z5,z6]),(0,[z29,z0,z2,z4,z5,z31])],[(0,[z131,z1,z2,z188,z4,z132]),(0,[z0,z61,z2,z4,z5,z433]),(0,[z315,z0,z2,z4,z101,z6]),(0,[z0,z2,z4,z5,z1049,z6]),(0,[z0,z140,z2,z198,z5,z6]),(0,[z151,z233,z2,z4,z5,z6]),(0,[z0,z4,z5,z6,z67,z68])],[(0,[z0,z738,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z206]),(0,[z0,z2,z198,z5,z9,z6])],[(0,[z273,z424,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1050])],[(0,[z0,z1051,z2,z4,z5,z6]),(0,[z0,z1052,z2,z4,z5,z6]),(0,[z16,z152,z2,z4,z5,z6])],[(0,[z0,z1053,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z894,z6]),(0,[z152,z2,z4,z5,z6,z221])],[(0,[z49,z1,z2,z141,z5,z6]),(0,[z63,z49,z1,z4,z87,z6]),(0,[z63,z0,z1,z4,z247,z6]),(0,[z1054,z0,z2,z4,z5,z126]),(0,[z1055,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z769,z5])],[(0,[z0,z98,z615,z4,z5,z6]),(0,[z103,z16,z338,z2,z4,z5]),(0,[z49,z2,z4,z5,z9,z6]),(0,[z0,z935,z1,z2,z4,z5]),(0,[z1054,z0,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z91,z277,z4,z5]),(0,[z16,z1056,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z1057,z6]),(0,[z27,z0,z2,z9,z6,z143])],[(0,[z100,z2,z4,z5,z6,z299]),(0,[z0,z1,z2,z439,z5,z30]),(0,[z0,z157,z2,z277,z4,z5]),(0,[z16,z0,z434,z2,z4,z5])],[(0,[z197,z1,z353,z4,z5,z6]),(0,[z1058,z1,z2,z4,z5,z6]),(0,[z0,z1059,z2,z4,z5,z6])],[(0,[z222,z2,z4,z5,z37,z9]),(0,[z16,z979,z2,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z388]),(0,[z818,z0,z1,z2,z4,z5]),(0,[z0,z1,z303,z4,z5,z6]),(0,[z0,z1,z2,z4,z769,z31])],[(0,[z0,z1060,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z250,z521]),(0,[z1061,z0,z2,z4,z5,z6]),(0,[z0,z144,z303,z4,z5,z6])],[(1,[z1,z729,z4,z5,z6]),(0,[z0,z1062,z2,z4,z5,z6]),(0,[z0,z1,z28,z4,z5,z162])],[(0,[z0,z1,z2,z4,z1063,z6])],[(0,[z12,z0,z2,z4,z5,z101]),(0,[z14,z2,z287,z90,z5,z6]),(0,[z0,z1,z2,z4,z5,z1064]),(0,[z103,z16,z0,z2,z4,z5]),(0,[z0,z2,z1065,z4,z5,z6])],[(0,[z197,z1,z105,z4,z5,z6]),(0,[z1066,z0,z1,z2,z4,z5]),(0,[z122,z2,z24,z5,z9,z6]),(0,[z16,z0,z2,z4,z5,z9]),(0,[z16,z0,z2,z205,z62,z4])],[(0,[z1056,z1,z2,z4,z5,z6]),(0,[z187,z0,z120,z4,z5,z6]),(0,[z0,z1067,z2,z4,z5,z6]),(0,[z36,z2,z201,z4,z5,z6])],[(0,[z0,z1068,z2,z4,z5,z6]),(0,[z16,z151,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z854])],[(0,[z122,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z4,z566,z31])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z133,z2,z4,z5,z6]),(0,[z131,z1,z2,z4,z132,z6]),(0,[z131,z1,z2,z4,z802,z6]),(0,[z16,z0,z2,z4,z5,z97]),(0,[z142,z16,z2,z4,z5,z6])],[(0,[z16,z0,z2,z4,z250,z6]),(0,[z16,z0,z2,z4,z42,z5]),(0,[z1,z2,z4,z5,z1069,z6]),(0,[z0,z518,z119,z4,z5,z6]),(0,[z104,z1,z2,z4,z5,z162])],[(0,[z0,z1,z1070,z2,z4,z5]),(0,[z49,z1,z2,z198,z5,z6]),(0,[z0,z1071,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z1072,z4,z5,z6]),(0,[z151,z1,z2,z4,z5,z6])],[(0,[z222,z16,z2,z4,z5,z37])],[(0,[z16,z0,z2,z439,z4,z5]),(0,[z16,z0,z2,z485,z4,z5])],[],[(0,[z0,z1,z1073,z4,z5,z6])],[(0,[z650,z268,z2,z4,z5,z6]),(0,[z0,z1,z1074,z4,z5,z6]),(0,[z0,z1,z2,z4,z1075,z6]),(0,[z142,z1,z2,z4,z132,z6]),(0,[z16,z95,z2,z4,z5,z97]),(0,[z0,z1,z89,z2,z4,z5])],[(0,[z0,z2,z4,z647,z101,z6]),(0,[z27,z0,z1,z19,z6,z143])],[(0,[z0,z492,z2,z90,z5,z6])],[(0,[z0,z2,z4,z5,z9,z25]),(0,[z0,z2,z1076,z4,z5,z6]),(0,[z16,z0,z2,z112,z5,z30])],[(0,[z0,z50,z824,z2,z4,z5]),(0,[z0,z2,z4,z5,z1077,z6]),(0,[z0,z1078,z2,z4,z5,z6])],[(0,[z23,z16,z2,z4,z5,z37]),(0,[z61,z2,z24,z4,z5,z6]),(0,[z0,z1,z1079,z4,z5,z6]),(0,[z0,z2,z1080,z4,z5,z6])],[(0,[z16,z0,z2,z290,z4,z5]),(0,[z0,z1,z2,z1081,z4,z5])],[(0,[z273,z653,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z464])],[(0,[z95,z1,z2,z4,z5,z76]),(0,[z7,z0,z2,z4,z101,z6]),(0,[z27,z0,z1,z28,z6,z143])],[(0,[z0,z1082,z2,z4,z5,z6]),(0,[z23,z1,z2,z74,z250,z6]),(0,[z0,z1,z2,z1030,z5,z6]),(0,[z142,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z193])],[(0,[z1,z2,z4,z132,z6,z679]),(0,[z293,z0,z1,z40,z5,z6]),(0,[z1083,z1,z2,z4,z5,z6]),(0,[z1,z2,z1084,z4,z5,z6])]],
   [[(0,[z23,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1085]),(0,[z103,z16,z0,z4,z199,z5]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z1,z2,z1087,z4,z5,z6])],[(0,[z29,z0,z2,z4,z5,z37]),(0,[z16,z0,z2,z4,z5,z636]),(0,[z0,z157,z2,z4,z102,z6])],[],[(0,[z0,z1,z2,z4,z5,z1088]),(0,[z1,z2,z405,z4,z5,z37]),(0,[z1,z2,z1089,z4,z5,z6]),(0,[z178,z971,z1,z4,z5,z6])],[(0,[z0,z1,z1090,z4,z5,z6]),(0,[z113,z16,z2,z4,z75,z6])],[(0,[z0,z490,z353,z4,z5,z6]),(0,[z1091,z0,z1,z4,z5,z6]),(0,[z0,z1,z50,z2,z703,z5])],[(0,[z1,z2,z4,z132,z250,z6]),(0,[z1092,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z221]),(0,[z39,z16,z0,z40,z5,z6])],[(0,[z1,z2,z4,z5,z37,z25]),(0,[z122,z1,z2,z812,z5,z6])],[],[(0,[z0,z1093,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1094,z5,z6]),(0,[z1095,z1,z2,z4,z5,z6]),(0,[z0,z1096,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1097])],[(0,[z0,z353,z4,z5,z9,z6]),(0,[z113,z1,z2,z4,z802,z6])],[(0,[z0,z1,z1098,z4,z5,z6]),(0,[z103,z16,z0,z120,z4,z5]),(0,[z16,z0,z2,z529,z4,z5])],[(0,[z139,z1,z105,z4,z5,z6]),(0,[z23,z1,z2,z188,z4,z5]),(0,[z514,z1,z2,z4,z132,z6]),(0,[z0,z1099,z2,z4,z5,z6])],[(0,[z100,z172,z2,z4,z5,z388]),(0,[z178,z0,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z162])]],
   [[(0,[z0,z1,z2,z4,z5,z1100]),(0,[z0,z99,z4,z5,z6,z311])],[(0,[z0,z1,z2,z812,z5,z6]),(0,[z0,z2,z4,z5,z1101,z6])],[(0,[z0,z1,z2,z4,z5,z1102]),(0,[z0,z1,z2,z4,z5,z1103]),(0,[z0,z1,z353,z4,z5,z521]),(0,[z0,z1104,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1105]),(0,[z16,z0,z2,z4,z5,z511])],[(0,[z1,z2,z188,z24,z4,z5]),(0,[z1,z2,z4,z5,z37,z88]),(0,[z278,z0,z13,z4,z5,z6]),(0,[z39,z818,z0,z2,z4,z5]),(0,[z0,z2,z4,z5,z6,z1106]),(0,[z152,z1,z2,z112,z5,z30]),(1,[z0,z1,z2,z4,z769])],[(0,[z181,z0,z1,z40,z5,z6]),(0,[z0,z1,z2,z1107,z4,z5]),(0,[z16,z0,z2,z10,z35,z6]),(0,[z103,z0,z1,z4,z5,z854])],[(0,[z505,z0,z2,z90,z5,z6]),(0,[z0,z1108,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z648])],[(0,[z0,z1,z2,z1109,z4,z5]),(0,[z172,z2,z4,z419,z5,z6]),(0,[z0,z1110,z2,z4,z5,z6]),(0,[z0,z1,z2,z1111,z4,z5]),(0,[z16,z224,z2,z4,z5,z6]),(0,[z1112,z1,z2,z4,z5,z6])],[(0,[z663,z1,z105,z4,z5,z6]),(0,[z0,z1,z119,z602,z5,z6]),(0,[z0,z733,z13,z4,z5,z6])],[(0,[z16,z0,z2,z448,z4,z5])],[(0,[z273,z2,z4,z5,z21,z6]),(0,[z16,z0,z2,z188,z4,z5]),(0,[z16,z0,z2,z4,z5,z528]),(0,[z1113,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1114,z4,z5,z6]),(0,[z1115,z0,z2,z4,z5,z6])],[],[(0,[z1116,z0,z2,z4,z5,z6]),(0,[z0,z1,z1117,z2,z4,z5])],[(0,[z0,z2,z4,z5,z1118,z6]),(0,[z0,z1,z2,z62,z4,z769])],[(0,[z16,z0,z2,z237,z4,z5])],[(0,[z0,z1,z2,z378,z35,z6]),(0,[z1119,z1,z2,z4,z5,z6])]],
   [[],[(0,[z0,z1,z2,z4,z1120,z6]),(0,[z0,z1,z2,z4,z1121,z5]),(0,[z0,z1,z2,z4,z5,z1122])],[(0,[z1,z2,z277,z4,z287,z5]),(0,[z0,z2,z4,z44,z67,z31]),(0,[z0,z1,z2,z205,z4,z769])],[(0,[z0,z1,z2,z4,z5,z1123]),(0,[z564,z0,z1,z40,z5,z6]),(0,[z0,z1124,z2,z4,z5,z6])],[(0,[z0,z2,z17,z5,z6,z11]),(0,[z0,z1,z4,z778,z87,z6]),(0,[z27,z104,z1,z2,z6,z143])],[(0,[z172,z1,z2,z4,z250,z6]),(0,[z0,z111,z28,z4,z5,z6]),(0,[z0,z1,z1125,z4,z5,z6])],[(0,[z1126,z1,z2,z4,z5,z6]),(0,[z16,z0,z420,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1127,z6]),(0,[z0,z1128,z2,z4,z5,z6]),(0,[z296,z0,z13,z4,z5,z6])],[(0,[z122,z1,z2,z4,z250,z6]),(0,[z0,z1129,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z996,z6]),(0,[z308,z1,z2,z4,z5,z6]),(0,[z16,z107,z243,z4,z5,z6]),(0,[z0,z1,z2,z62,z4,z307]),(0,[z16,z414,z2,z4,z5,z6]),(0,[z2,z259,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z349,z31]),(0,[z0,z209,z47,z4,z5,z48])],[(0,[z0,z2,z78,z237,z4,z6]),(1,[z0,z1,z4,z5,z854])],[(0,[z0,z212,z2,z4,z5,z25]),(0,[z23,z1,z353,z74,z5,z6]),(0,[z1130,z0,z1,z4,z5,z6]),(0,[z16,z0,z50,z2,z112,z5]),(0,[z1131,z0,z1,z2,z4,z5])],[(0,[z0,z1132,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1133]),(0,[z245,z0,z2,z158,z5,z6]),(0,[z0,z2,z1134,z4,z5,z6])],[(0,[z1,z2,z418,z24,z5,z6]),(0,[z0,z2,z4,z5,z1135,z6]),(0,[z0,z1,z4,z44,z68,z31])],[(0,[z0,z1,z2,z4,z1136,z6]),(0,[z16,z0,z2,z486,z4,z5]),(0,[z16,z0,z50,z303,z4,z5])]],
   [[(0,[z669,z1,z105,z4,z5,z6]),(0,[z95,z1,z2,z4,z5,z97]),(0,[z0,z1,z4,z5,z6,z1137])],[(0,[z95,z1,z2,z4,z250,z6]),(0,[z0,z1,z2,z4,z5,z1138]),(0,[z16,z0,z2,z112,z246,z5]),(0,[z0,z1,z141,z5,z48,z6])],[(0,[z0,z1,z2,z4,z250,z6])],[(0,[z16,z0,z2,z4,z5,z474]),(0,[z0,z1,z2,z62,z4,z310]),(0,[z0,z123,z2,z403,z4,z5]),(0,[z2,z4,z978,z5,z9,z6])],[(0,[z0,z1,z2,z4,z5,z1139]),(0,[z0,z2,z4,z5,z1140,z433]),(0,[z0,z1,z2,z1141,z5,z6])],[(0,[z0,z8,z2,z118,z5,z6]),(0,[z1,z200,z731,z4,z5,z6])],[(0,[z0,z1,z2,z485,z4,z5]),(0,[z0,z2,z4,z5,z1142,z6]),(0,[z0,z1,z2,z10,z635,z6])],[(0,[z0,z1143,z2,z4,z5,z6]),(0,[z1144,z1,z2,z4,z5,z6]),(0,[z16,z948,z2,z4,z5,z6]),(0,[z16,z338,z2,z4,z5,z6])],[(0,[z0,z1,z4,z5,z854,z207])],[(0,[z891,z0,z2,z4,z5,z6]),(0,[z0,z165,z2,z4,z5,z97]),(0,[z338,z2,z4,z5,z9,z6])],[(0,[z1145,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z711,z101,z6]),(0,[z16,z197,z2,z4,z5,z6]),(0,[z0,z233,z2,z4,z5,z162])],[(0,[z0,z2,z1146,z4,z5,z6]),(0,[z791,z2,z4,z5,z9,z6]),(0,[z1,z2,z1147,z4,z5,z6]),(0,[z0,z1,z2,z112,z5,z30])],[(0,[z0,z1,z1148,z4,z5,z6]),(1,[z818,z0,z2,z4,z5])],[(0,[z0,z2,z4,z5,z1149,z6]),(0,[z0,z2,z4,z5,z6,z1150]),(0,[z16,z0,z369,z2,z4,z5]),(0,[z0,z2,z4,z5,z1049,z162])],[(0,[z0,z1,z1151,z4,z5,z6]),(0,[z0,z2,z4,z5,z9,z559]),(0,[z0,z2,z10,z35,z9,z6]),(0,[z0,z1,z40,z5,z398,z6]),(0,[z63,z0,z140,z4,z87,z6])]],
   [[],[(0,[z0,z2,z4,z5,z169,z388])],[(0,[z0,z2,z4,z5,z880,z25]),(0,[z12,z0,z2,z4,z5,z9]),(0,[z0,z2,z933,z90,z5,z6]),(0,[z0,z1152,z2,z4,z5,z6]),(0,[z1153,z1,z2,z4,z5,z6])],[(0,[z0,z50,z2,z51,z5,z9])],[(0,[z0,z2,z4,z5,z6,z1154])],[(0,[z0,z1,z2,z1155,z4,z5]),(0,[z0,z1,z219,z1034,z5,z6]),(0,[z0,z1156,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1157]),(0,[z0,z2,z4,z5,z6,z918]),(0,[z0,z2,z4,z5,z986,z511])],[(0,[z222,z1,z2,z4,z5,z526]),(0,[z0,z1,z1158,z4,z5,z6]),(0,[z0,z1,z2,z933,z5,z6]),(0,[z1159,z0,z2,z4,z5,z6])],[(0,[z1,z367,z105,z4,z5,z6])],[(0,[z95,z2,z4,z5,z169,z97]),(0,[z63,z103,z16,z0,z4,z5]),(0,[z1,z2,z4,z5,z6,z1160])],[(0,[z273,z490,z2,z4,z5,z6]),(0,[z0,z1,z2,z1161,z4,z5]),(0,[z27,z0,z111,z2,z6,z143])],[(0,[z107,z1,z2,z4,z250,z6]),(1,[z1,z2,z4,z5,z894]),(0,[z152,z1,z2,z4,z5,z97])],[(0,[z1,z2,z1162,z4,z5,z6])],[(0,[z0,z1,z2,z1163,z5,z6]),(0,[z0,z2,z1164,z4,z5,z6]),(0,[z1,z2,z4,z5,z1165,z6]),(0,[z16,z0,z2,z112,z4,z5]),(0,[z0,z1166,z2,z4,z5,z6]),(0,[z0,z111,z2,z4,z5,z126])],[(0,[z273,z738,z2,z4,z5,z6]),(0,[z0,z1,z1167,z4,z5,z6]),(0,[z0,z1,z2,z1034,z5,z6])],[(0,[z0,z61,z2,z4,z5,z6]),(0,[z131,z61,z2,z4,z132,z6]),(0,[z0,z1,z2,z4,z1168,z6]),(0,[z14,z0,z15,z90,z5,z6]),(0,[z288,z157,z2,z4,z5,z6])]],
   [[(0,[z0,z1169,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1170,z5,z6]),(0,[z0,z1171,z2,z4,z5,z6]),(0,[z103,z16,z0,z119,z4,z5]),(0,[z16,z0,z19,z4,z5,z6])],[(0,[z16,z0,z2,z4,z5,z918]),(0,[z0,z2,z4,z5,z918,z92])],[(0,[z414,z1,z2,z4,z5,z6]),(0,[z71,z0,z2,z4,z101,z6]),(0,[z0,z2,z4,z5,z1172,z126])],[(0,[z0,z268,z2,z277,z4,z5]),(0,[z1173,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1174]),(0,[z0,z2,z4,z44,z9,z31])],[(0,[z151,z1,z2,z4,z5,z162])],[(0,[z0,z172,z2,z4,z5,z333]),(0,[z16,z0,z308,z2,z4,z5])],[(0,[z0,z1175,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z323,z25]),(0,[z16,z0,z47,z4,z5,z48]),(0,[z0,z254,z303,z4,z5,z6])],[(0,[z0,z1,z2,z1176,z5,z6]),(0,[z0,z1,z2,z10,z35,z6])],[(0,[z0,z1,z1177,z4,z5,z6]),(0,[z1178,z1,z2,z4,z5,z6]),(0,[z0,z8,z2,z933,z5,z6])],[(0,[z103,z16,z0,z47,z4,z5]),(0,[z103,z166,z0,z2,z4,z5])],[(0,[z16,z0,z2,z4,z5,z526]),(0,[z1,z2,z4,z758,z5,z6])],[],[(0,[z0,z1,z2,z188,z4,z5]),(0,[z1,z2,z4,z5,z1179,z6])],[],[(0,[z224,z172,z2,z4,z5,z6]),(0,[z0,z1,z353,z4,z5,z6]),(0,[z1000,z1,z2,z4,z5,z6]),(0,[z0,z1,z1180,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z1181,z6]),(0,[z0,z254,z2,z4,z5,z6]),(0,[z1182,z1,z2,z4,z5,z6]),(0,[z16,z0,z50,z200,z4,z5]),(0,[z1183,z0,z2,z4,z5,z6]),(0,[z0,z1,z50,z2,z794,z5])],[(0,[z16,z0,z2,z4,z5,z159]),(0,[z1184,z1,z2,z4,z5,z6]),(0,[z16,z0,z47,z2,z4,z5]),(0,[z1185,z0,z1,z4,z5,z6])],[(0,[z738,z268,z2,z4,z5,z6]),(0,[z1013,z0,z2,z188,z4,z5]),(0,[z0,z2,z4,z5,z6,z1186]),(0,[z151,z1,z2,z4,z35,z6])],[(0,[z0,z64,z2,z4,z5,z6]),(0,[z39,z0,z1,z1034,z5,z6])],[(0,[z0,z1,z517,z4,z5,z25]),(0,[z1,z2,z188,z4,z5,z75]),(0,[z1,z2,z4,z5,z894,z97]),(0,[z0,z1,z541,z2,z51,z5]),(0,[z414,z1,z2,z4,z5,z193]),(0,[z1,z2,z4,z5,z6,z1187]),(0,[z29,z0,z50,z2,z4,z5])],[(0,[z0,z157,z2,z225,z4,z5])],[(0,[z650,z2,z4,z5,z646,z6])],[(0,[z1188,z0,z1,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z169]),(0,[z0,z1,z2,z4,z1057,z6]),(0,[z16,z0,z2,z141,z5,z6])],[(0,[z0,z157,z2,z4,z5,z333]),(0,[z0,z1,z2,z1189,z4,z5]),(0,[z1190,z1,z2,z4,z5,z6]),(0,[z16,z0,z4,z5,z6,z68]),(0,[z308,z1,z4,z40,z5,z6])],[],[(0,[z16,z0,z624,z2,z4,z5]),(0,[z0,z1,z420,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z388]),(0,[z1,z2,z105,z4,z250,z6])],[],[(0,[z0,z885,z4,z5,z9,z6]),(0,[z2,z4,z1191,z5,z9,z6])],[(0,[z160,z105,z4,z5,z9,z6])],[(0,[z1,z2,z4,z588,z75,z6]),(0,[z1192,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z1193,z5,z6]),(0,[z16,z0,z2,z4,z5,z25]),(0,[z23,z1,z2,z507,z5,z6]),(0,[z952,z16,z2,z4,z5,z6]),(0,[z16,z0,z138,z2,z4,z5])]],
   [[(0,[z16,z0,z2,z4,z5,z1101]),(0,[z0,z2,z277,z4,z5,z101]),(0,[z104,z111,z2,z4,z5,z6]),(0,[z0,z1,z2,z205,z62,z4])],[(0,[z224,z157,z2,z4,z5,z6]),(0,[z16,z2,z4,z5,z1069,z6]),(1,[z0,z1,z2,z6,z847])],[(0,[z178,z16,z0,z4,z5,z31]),(0,[z0,z1,z28,z5,z6,z143]),(0,[z36,z379,z2,z4,z5,z6])],[(0,[z16,z1190,z2,z4,z5,z6])],[(0,[z0,z1194,z2,z4,z5,z6]),(0,[z1,z2,z4,z1191,z5,z6]),(0,[z104,z1,z19,z4,z5,z6]),(0,[z1195,z1,z2,z4,z5,z6])],[(0,[z1,z2,z110,z4,z75,z6]),(0,[z697,z0,z2,z90,z5,z6]),(0,[z0,z1,z2,z1196,z5,z6]),(0,[z803,z1,z200,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1197])],[],[(0,[z107,z1,z353,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z82]),(0,[z16,z0,z2,z198,z5,z6])],[(0,[z0,z2,z4,z102,z6,z281])],[(0,[z0,z1,z2,z4,z5,z1198]),(0,[z0,z2,z4,z5,z6,z1199]),(0,[z780,z0,z2,z4,z5,z433])],[(0,[z0,z1200,z2,z4,z5,z6]),(0,[z0,z1201,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z456]),(0,[z0,z2,z1202,z4,z5,z6])],[(0,[z1203,z0,z2,z4,z5,z6]),(0,[z0,z1204,z2,z4,z5,z6]),(0,[z0,z8,z420,z4,z5,z6]),(0,[z1205,z0,z2,z4,z5,z6]),(0,[z0,z2,z1206,z4,z5,z6])],[(0,[z0,z517,z4,z5,z9,z6])],[(0,[z0,z1207,z2,z4,z5,z6]),(0,[z1,z2,z515,z4,z5,z6]),(0,[z0,z47,z2,z1080,z4,z5]),(0,[z0,z1208,z2,z4,z5,z6])],[(0,[z103,z0,z1,z4,z5,z511]),(0,[z103,z0,z4,z5,z65,z207])]],
   [[(0,[z14,z0,z89,z2,z90,z5])],[(0,[z0,z2,z4,z1209,z5,z6]),(0,[z0,z1210,z2,z4,z5,z6]),(0,[z16,z0,z415,z2,z4,z5]),(0,[z0,z518,z2,z4,z5,z6])],[(0,[z1,z2,z4,z1211,z5,z6]),(0,[z1212,z0,z2,z4,z5,z6])],[(0,[z0,z212,z2,z4,z323,z6]),(0,[z0,z1,z1213,z4,z5,z6]),(0,[z916,z1,z2,z4,z5,z6]),(0,[z166,z0,z2,z4,z5,z6]),(0,[z0,z1214,z2,z4,z5,z6]),(0,[z0,z1215,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1216,z4,z5]),(0,[z197,z1,z243,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1217]),(0,[z417,z0,z13,z4,z5,z6]),(0,[z0,z157,z2,z4,z319,z6]),(0,[z911,z16,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1218])],[],[(0,[z0,z1,z1219,z4,z5,z6])],[(0,[z0,z1,z2,z1220,z4,z5]),(0,[z0,z2,z4,z5,z6,z1221]),(0,[z0,z2,z4,z5,z1222,z521]),(0,[z14,z0,z2,z277,z4,z5])],[(0,[z0,z1,z1223,z4,z5,z6])],[(1,[z738,z2,z4,z5,z6])],[(0,[z0,z1224,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z48,z854])],[(0,[z288,z2,z4,z5,z9,z6]),(0,[z0,z1086,z4,z5,z9,z6])],[(0,[z131,z1,z2,z4,z645,z6]),(0,[z0,z1,z1225,z4,z5,z6]),(0,[z567,z0,z2,z90,z5,z6]),(0,[z0,z2,z4,z5,z67,z115]),(0,[z16,z0,z128,z2,z4,z5])],[(0,[z16,z49,z2,z4,z5,z6]),(0,[z16,z0,z2,z4,z5,z661]),(1,[z0,z1,z1034,z5,z6])],[(0,[z16,z0,z2,z4,z5,z37]),(0,[z0,z2,z112,z5,z9,z30])],[(0,[z0,z1,z1226,z4,z5,z6])]],
   [[(0,[z16,z0,z2,z4,z5,z642]),(0,[z0,z212,z517,z4,z5,z6]),(0,[z0,z1227,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1228]),(0,[z1229,z1,z2,z4,z5,z6]),(0,[z29,z2,z4,z5,z6,z127])],[(0,[z0,z2,z4,z5,z1222,z6]),(0,[z0,z2,z188,z4,z5,z9]),(0,[z0,z111,z2,z4,z5,z6]),(0,[z1061,z0,z2,z4,z5,z511])],[(0,[z0,z1230,z2,z4,z5,z6]),(1,[z0,z733,z4,z5,z6]),(0,[z166,z0,z2,z62,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1231]),(0,[z0,z1,z1232,z4,z5,z6])],[(0,[z595,z172,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1233]),(0,[z151,z111,z2,z4,z5,z6]),(0,[z0,z1,z19,z4,z5,z126])],[(0,[z0,z1234,z2,z4,z5,z6]),(0,[z0,z2,z17,z933,z5,z6]),(0,[z1042,z1,z2,z4,z5,z6]),(0,[z0,z1,z19,z4,z5,z6]),(0,[z0,z1,z4,z1034,z5,z6]),(0,[z27,z0,z1,z2,z126,z143]),(0,[z0,z1,z50,z303,z51,z5]),(0,[z0,z379,z2,z4,z5,z31])],[(0,[z0,z1,z1235,z4,z5,z6]),(0,[z1236,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z918])],[(0,[z1237,z1,z2,z4,z5,z6]),(0,[z0,z1,z119,z590,z5,z6]),(0,[z0,z2,z4,z5,z1172,z6]),(1,[z0,z1,z2,z794,z5])],[(0,[z0,z268,z2,z4,z5,z333]),(0,[z0,z2,z4,z5,z1101,z97]),(0,[z16,z0,z2,z1080,z4,z5]),(0,[z151,z1,z19,z4,z5,z6]),(0,[z0,z50,z254,z2,z51,z5])],[(0,[z16,z0,z2,z662,z4,z5]),(0,[z16,z0,z2,z400,z4,z5]),(0,[z0,z1,z2,z4,z5,z511])],[(0,[z0,z1238,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1239])],[(0,[z103,z0,z1,z4,z5,z207]),(0,[z0,z1,z47,z4,z5,z48]),(0,[z0,z1,z4,z5,z6,z854])],[(0,[z0,z490,z2,z4,z5,z25]),(0,[z0,z2,z4,z1240,z5,z6]),(0,[z0,z2,z4,z5,z1241,z6]),(0,[z1242,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z48,z464]),(0,[z0,z1243,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z769,z44])],[(0,[z0,z1244,z2,z4,z5,z6])],[(0,[z1,z2,z4,z812,z5,z6]),(0,[z0,z1245,z2,z4,z5,z6]),(0,[z12,z0,z99,z2,z4,z5]),(0,[z1246,z0,z2,z4,z5,z6]),(0,[z0,z1,z141,z5,z87,z6]),(0,[z1247,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1248,z5,z6]),(0,[z0,z1,z2,z4,z5,z1249]),(0,[z16,z0,z2,z4,z5,z677]),(0,[z16,z0,z2,z4,z764,z6]),(0,[z16,z0,z2,z355,z4,z5]),(0,[z63,z0,z4,z87,z9,z6]),(0,[z0,z1250,z2,z4,z5,z6])]],
   [[],[(0,[z273,z130,z2,z4,z5,z6]),(0,[z224,z268,z2,z4,z5,z6]),(0,[z1251,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1252,z6])],[(0,[z0,z2,z4,z5,z9,z521]),(0,[z0,z200,z4,z5,z9,z6])],[(0,[z16,z2,z24,z4,z5,z37]),(0,[z0,z13,z4,z477,z5,z6])],[(0,[z0,z2,z4,z5,z9,z333]),(0,[z0,z1,z353,z4,z250,z6]),(0,[z0,z8,z2,z17,z5,z6]),(0,[z16,z0,z200,z2,z4,z5]),(0,[z1,z2,z4,z5,z6,z1253]),(0,[z0,z1,z2,z6,z847,z143]),(0,[z0,z1,z369,z2,z51,z5])],[],[(0,[z273,z1,z2,z4,z250,z6]),(0,[z0,z1,z2,z4,z5,z1254]),(0,[z16,z104,z2,z4,z5,z6]),(0,[z1255,z1,z2,z4,z5,z6]),(0,[z185,z0,z2,z4,z44,z31])],[(0,[z16,z0,z15,z4,z5,z6]),(0,[z103,z16,z0,z4,z5,z207])],[(0,[z16,z0,z2,z4,z5,z31])],[(0,[z16,z0,z2,z4,z5,z257]),(0,[z0,z2,z4,z5,z6,z1140]),(0,[z16,z0,z2,z4,z5,z260])],[(0,[z0,z1,z2,z4,z1256,z6]),(0,[z16,z0,z2,z4,z5,z262]),(0,[z0,z420,z4,z90,z5,z6]),(0,[z103,z16,z308,z2,z4,z5]),(0,[z1257,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1258,z4,z5])],[(0,[z0,z2,z4,z5,z6,z65]),(0,[z0,z1,z4,z5,z6,z68])],[(0,[z0,z1,z2,z4,z1259,z6]),(0,[z1,z2,z4,z5,z37,z894]),(0,[z0,z2,z733,z4,z5,z6]),(0,[z224,z2,z4,z5,z9,z6]),(0,[z0,z2,z4,z5,z6,z1260])],[(0,[z1261,z1,z2,z4,z5,z6])],[(0,[z555,z1,z2,z4,z5,z97]),(0,[z633,z1,z2,z4,z75,z6]),(0,[z16,z0,z2,z498,z4,z5]),(0,[z1262,z1,z2,z4,z5,z6])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 507).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1022).take 262) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1284)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [507, 515, 262] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 168).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 168).take 166).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 334).take 177).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 511).take 1).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [168, 166, 177, 1] = true :=
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

end PEqualNP.Outside.L_meta_38755

theorem PEqualNP.Outside.L_meta_38755 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38755.solve