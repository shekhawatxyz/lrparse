dot = '.'
eps = ''
dollar = '$'
goto = "goto"
shift = "shift"
red = "reduce"
acc = "accept"


def dotattach(prod):
	LHS, RHS = prod
	return [LHS, dot + RHS]


def dotsym(item):
	LHS, RHS = item
	if RHS.endswith(dot):
		return eps
	return RHS.split(dot)[1][0]


def rmdot(item):
	LHSi, RHSi = item
	return [LHSi, RHSi.replace(dot,eps)]


def dotprogress(item):
	LHSi, RHSi = item
	ls = list(RHSi)
	i = ls.index(dot)
	ls[i],ls[i+1] = ls[i+1],ls[i]
	return [LHSi,eps.join(ls)]


def makeitems(G):
	nterminals = set([LHS for LHS, RHS in G])
	terminals = set([t for LHS, RHS in G for t in RHS if t not in nterminals])

	def inner(I):
		J = list(I)
		done = False
		while not done:
			done = True
			for item in J:
				B = dotsym(item)
				if B not in nterminals:
					continue
				for prod in G:
					LHS, RHS = prod
					if LHS != B:
						continue
					new_item = dotattach(prod)
					if new_item in J:
						continue
					J.append(list(new_item))
					done = False
		return J

	def goto(I,X):
		J = []
		for item in I:
			B = dotsym(item)
			if B == X:
				new_item = dotprogress(item)
				J.append(list(new_item))
		return J

	def items():
		C = [ inner([ dotattach(G[0]) ]) ]
		S = list(nterminals.union(terminals))
		goto_moves = {}
		done = False
		while not done:
			done = True
			for index,I in enumerate(C):
				goto_moves[index] = [None]*len(S)
				for sym in S:
					J = inner(goto(I,sym))
					if len(J) == 0:
						continue
					if J not in C:
						C.append(J)
						done = False
					goto_moves[index][S.index(sym)] = C.index(J)
					
		return C,S,goto_moves

	return items	


def getfnf(G):
	fsym = G[0][0]
	fcache, scache = {}, {}
	nterminals = set([LHS for LHS, RHS in G])
	terminals = set([t for LHS, RHS in G for t in RHS if t not in nterminals])

	def first(X):
		if X in fcache:
			return fcache[X]
		res = set()
		Xp = [P for P in G if P[0] == X]
		for prod in Xp:
			LHS, RHS = prod
			for index, sym in enumerate(RHS):
				if sym == X:
					break
				if sym in terminals.union(eps):
					res = res.union(sym)
					break
				fy = first(sym)
				res = res.union(fy - {eps})
				if eps not in fy:
					break
				if index == len(RHS)-1:
					res = res.union({eps})
		fcache[X] = res
		return fcache[X]
	
	def fof(b):
		res = set()
		for index, sym in enumerate(b):
			if sym in terminals.union({eps}):
				res = res.union({sym})
				break
			fy = first(sym)
			res = res.union(fy - {eps})
			if eps not in fy:
				break
			if index == len(b)-1:
				res = res.union({eps})
		return res

	def follow(X):
		if X in scache:
			return scache[X]
		res = set()
		if X == fsym:
			res = res.union({dollar})
		Xp = [P for P in G if X in P[1]]
		for prod in Xp:
			LHS, RHS = prod
			for index,sym in enumerate(RHS):
				if sym != X:
					continue
				if (index == len(RHS) - 1) and (LHS != sym):
					res = res.union(follow(LHS))
					continue
				fb = fof(RHS[index + 1:])
				res = res.union(fb - {eps})
				if (eps in fb) and (LHS != sym):
					res = res.union(follow(LHS))
			
		scache[X] = res
		return scache[X]

	return first,follow


def construct(G):
	items = makeitems(G)
	first, follow = getfnf(G)
	states, syms, T = items()
	syms.append(dollar)
	table = [dict() for i in states]
	nterminals = set([s for s in syms if s.isupper()])
	terminals = set([s for s in syms if s not in nterminals])

	for i in range(len(states)):
		for j in range(len(syms)-1):
			sym = syms[j]
			if T[i][j] == None:
				continue
			if sym in nterminals:
				table[i][sym] = [goto, T[i][j]]
			else:
				table[i][sym] = [shift, T[i][j]]

	for index, I in enumerate(states):
		for item in I:
			B = dotsym(item)
			if B != eps:
				continue
			LHSi, RHSi = item
			pidx = G.index(rmdot(item))
			if pidx == 0:
				table[index][dollar] = [acc, index]
				break
			foleft = follow(LHSi)
			for sym in foleft:
				sym_index = syms.index(sym)
				if sym in table[index]:
					print("Conflict in state-sym: ", index, sym)
					break
				table[index][sym] = [red, pidx]

	return table


def parser(string, G):
	index = 0
	sstack = [0]
	symstack = []
	actionstr = ""
	buf = list(string + dollar)
	table = construct(G)

	while True:
		sym = buf[index]
		s = sstack[-1]

		if sym not in table[s]:
			actionstr = "Parsing error at " + str(index) + " sym " + sym
			print(actionstr)
			break
		action, value = table[s][sym]

		if action == shift:
			actionstr = "Shift " + sym
			symstack.append(sym)
			sstack.append(value)
			index += 1

		if action == red:
			LHS, RHS = G[value]
			for i in range(len(RHS)):
				sstack.pop()
				symstack.pop()
			s = sstack[-1]
			sstack.append(table[s][LHS][1])
			symstack.append(LHS)
			actionstr = "Reduce " + LHS + " -> " + RHS

		if action == acc:
			actionstr = "accepted\n"
			print(actionstr)
			break

		print(''.join(symstack), '\t', actionstr)


G = [
	["S", "E"],
	["E", "E+T"],
	["E", "T"],
	["T", "T*F"],
	["T", "F"],
	["F", "(E)"],
	["F", "x"]
]

G2 = [
	["S","A"],
	["A","aA"],
	["A","bA"],
	["A","aB"],
	["B","bC"],
	["C","bD"],
	["D",""]
]

parser("x*x+x", G)
parser("x*(x+x)+x", G)
parser("x*(x+x+x", G)

parser("ababb", G2)
