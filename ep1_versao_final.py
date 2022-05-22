# This code has been adapted from: https://bitbucket.org/Andrew-Kay/dcaa/src/master
# Refer to the Author whenever the code is used

## TREES

class Tree:
	def __init__(self, children=None, value=None, parent=None):
		self.value = value
		self.parent_node = parent
		if children is not None:
			for child in children:
				if isinstance(child, Tree):
					child = self.__class__(child.children(), child.value, self)
					self.add_child_node(child)
				elif hasattr(child, '__iter__'):
					child = self.__class__(children=child, parent=self)
					self.add_child_node(child)
				else:
					self.add_child(child)
	#
	
	def parent(self):
		return self.parent_node
	def children(self):
		raise NotImplementedError()
	def root_node(self):
		a = self
		while a.parent() is not None:
			a = a.parent()
		return a
	def height(self):
		h = 0
		a = self
		while a.parent() is not None:
			a = self.parent()
			h += 1
		return h
	def ancestors(self):
		a = self
		ancestors = [self]
		while a.parent() is not None:
			a = a.parent()
			ancestors.append(a)
		return ancestors
	def descendants(self):
		descendants = [self]
		for c in self.children():
			descendants.extend(c.descendants())
		return descendants

	def values(self):
		return [ node.value for node in self.descendants() if node.value is not None ]
	def is_leaf_node(self):
		return len(self.children()) == 0
	def leaf_nodes(self):
		if self.is_leaf_node():
			leaf_nodes = [self]
		else:
			leaf_nodes = []
			for c in self.children():
				leaf_nodes.extend(c.leaf_nodes())
		return leaf_nodes
	#
	
	def filter(self, predicate):
		def find_shallowest_descendants(root,node):
			if node is not root and predicate(node):
				return [node]
			else:
				result = []
				for c in node.children():
					result.extend(find_shallowest_descendants(root,c))
				return result
		new_root = self.__class__(value=self.value)
		for c in find_shallowest_descendants(self,self):
			new_child = c.filter(predicate)
			new_child.parent_node = new_root
			new_root.add_child_node(new_child)
		return new_root
	#
	
	def add_child(self, value=None):
		child = self.__class__(value=value, parent=self)
		self.add_child_node(child)
		return child
	def add_child_node(self):
		raise NotImplementedError()
	def delete_child_node(self):
		raise NotImplementedError()
	#
	
	def __contains__(self, x):
		return any( x == node.value for node in self.descendants() )
	def __str__(self):
		def format_node(node):
			first_line = '*' if node.value is None else repr(node.value)
			children = node.children()
			n = len(children)
			if n == 0:
				return [ first_line ]
			space = ' '*len(first_line)
			rows = []
			for i in range(0, n):
				child_rows = format_node(children[i])
				if i == 0:
					rows.append(first_line + ' +-> ' + child_rows[0])
				else:
					rows.append(space + ' +-> ' + child_rows[0])
				prefix = ' |   ' if i < n-1 else '     '
				rows.extend(space + prefix + cr for cr in child_rows[1:])
				if i < n-1:
					rows.append(space + ' |')
			return rows
		return '\n'.join(format_node(self))
	def __repr__(self):
		params = []
		children = self.children()
		if len(children) > 0:
			params.append(repr(children))
		if self.value is not None:
			params.append('value='+repr(self.value))
		return '{0}({1})'.format(self.__class__.__name__, ', '.join(params))
	def to_graph(self):
		from graphs import PredicateGraph
		def edge_relation(x,y):
			return y == x.parent() or x == y.parent()
		return PredicateGraph(self.descendants(), edge_relation)
#
class ListTree(Tree):
	def __init__(self, children=None, value=None, parent=None):
		self.child_list = []
		Tree.__init__(self, children, value, parent)
	def children(self):
		return self.child_list
	def __getitem__(self, index):
		return self.child_list[index]
	#
	
	def add_child_node(self, child):
		self.child_list.append(child)
	def remove_child_node(self, child):
		if child not in self.children(): raise ValueError('child not found')
		self.child_list.remove(child)
#


## LOGIC

# quantifier: "there exists a unique ..."
# e.g. exactly_one( n*n == 9 for n in range(1,10) ) is True
def exactly_one(S):
	return len([ s for s in S if s ]) == 1
#

def in_order(L):
	return all( L[i] <= L[i+1] for i in range(0, len(L)-1) )
#

def set_to_predicate(S):
	return lambda x: x in S
#

def truth_table_rows(variables):
	if len(variables) == 0:
		return [dict()]
	variables = list(variables)
	P = variables[0]
	R = truth_table_rows(variables[1:])
	add_P = lambda v: [ dict([(P,v)] + list(r.items())) for r in R ]
	return add_P(True) + add_P(False)
#

def vars(*var_names):
        return ( Variable(name) for name in var_names )
#

def cast_to_proposition(p):
	if isinstance(p, Proposition):
		return p
	elif isinstance(p, str):
		return Variable(p)
	elif isinstance(p, bool):
		return Constant(p)
	else:
		raise ValueError()
#

class Proposition:
	symbol = ''
	empty_str = ''
	def __init__(self, *children):
		self.children = [ cast_to_proposition(c) for c in children ]
	def __str__(self):
		if len(self.children) == 0: return self.empty_str
		return self.symbol.join( c.child_str() for c in self.children )
	def evaluate(self, **assignments):
		raise NotImplementedError()
	def variables(self):
		if len(self.children) == 0:
			return frozenset()
		else:
			return frozenset.union(*[ c.variables() for c in self.children ])
	def __repr__(self):
		return 'Proposition( {0} )'.format(self)
	def child_str(self):
		return ('{0}' if isinstance(self, (Constant,Variable,Not)) else '({0})').format(self)
	def print_truth_table(self):
		vars = sorted( self.variables() )
		rows = truth_table_rows(vars)
		
		formula_header = str(self)
		formula_len = max(5,len(formula_header))
		header = '{0}  #  {1: ^{2}}'.format('  '.join('{0: ^5}'.format(v) for v in vars), formula_header, formula_len)
		print(header)
		print('#'*len(header))
		
		for r in rows:
			var_cols = '  '.join('{0: ^{1}}'.format(str(r[v]), max(5,len(v))) for v in vars)
			result_col = '{0: ^{1}}'.format(str(self.evaluate(**r)), formula_len)
			print('{0}  #  {1}'.format(var_cols, result_col)) 
		print()
	def to_tree(self):
		result = ListTree(value=str(self))
		for c in self.children:
			result.add_child_node(c.to_tree())
		return result
	def __and__(self,other):
		#v = self.children if isinstance(self,And) else [self]
		#w = other.children if isinstance(other,And) else [other]
		#return And(*(v+w))
		return And(self, other)        
	def __rand__(self,other):
		return cast_to_proposition(other) & self
	def __or__(self,other):
		#v = self.children if isinstance(self,Or) else [self]
		#w = other.children if isinstance(other,Or) else [other]
		#return Or(*(v+w))
		return Or(self, other)
	def __ror__(self,other):
		return cast_to_proposition(other) | self
	def __invert__(self):
		return Not(self)
	def __rshift__(self,other):
		return Implies(self,other)
	def __rrshift__(self,other):
		return Implies(other,self)
	def __lshift__(self,other):
		return ImpliedBy(self,other)
	def __rlshift__(self,other):
		return ImpliedBy(other,self)
	def disjunction(self,other):
		return self | other
	def conjunction(self,other):
		return self & other
	def negation(self):
		return ~self
	def implies(self,other):
		return self >> other
	def impliedby(self,other):
		return self << other
	def iff(self,other):
		return Iff(self,other)
	def is_tautology(self):
		return all( self.evaluate(**r) for r in truth_table_rows(self.variables()) )
	def is_contradiction(self):
		return all( not self.evaluate(**r) for r in truth_table_rows(self.variables()) )
	def is_contingency(self):
		return not self.is_tautology() and not self.is_contradiction()
	def __eq__(self,other):
		return self.is_equivalent(other)
	def is_equivalent(self,other):
		other = cast_to_proposition(other)
		return all( self.evaluate(**r) == other.evaluate(**r) for r in truth_table_rows(self.variables() | other.variables()) )
	def is_identical(self,other):
		return self.__class__ == other.__class__ \
			and len(self.children) == len(other.children) \
			and all( c.is_identical(d) for (c,d) in zip(self.children,other.children) )
	def substitute(self, e1, e2):
		if self.is_identical(e1):
			return e2
		else:
			return self.__class__( *[c.substitute(e1,e2) for c in self.children] )
#

class Constant(Proposition):
	def __init__(self,value):
		self.children = []
		self.value = bool(value)
	def substitute(self, e1, e2):
		return Constant(self.value)
	def __str__(self):
		return str(self.value)
	def evaluate(self, **assignments):
		return self.value
	def is_identical(self,other):
		return isinstance(other, Constant) and self.value == other.value
#

class Variable(Proposition):
	def __init__(self,name):
		self.children = []
		self.name = name
	def substitute(self, e1, e2):
		if self.is_identical(e1):
			return e2
		else:
			return Variable(self.name)
	def variables(self):
		return frozenset({ self.name })
	def __str__(self):
		return self.name
	def evaluate(self, **assignments):
		return assignments[self.name]
	def is_identical(self,other):
		return isinstance(other, Variable) and self.name == other.name
#

class Not(Proposition):
	def __init__(self,child):
		Proposition.__init__(self,child)
	def __str__(self):
		return u'¬{0}'.format(self.children[0].child_str()) 
	def evaluate(self, **assignments):
		return not self.children[0].evaluate(**assignments)
#

class And(Proposition):
	symbol = ' ^ '
	empty_str = 'True'
	def evaluate(self, **assignments):
		return all( child.evaluate(**assignments) for child in self.children )
#

class Or(Proposition):
	symbol = ' v '
	empty_str = 'False'
	def evaluate(self, **assignments):
		return any( child.evaluate(**assignments) for child in self.children )
#

class Implies(Proposition):
	symbol = ' => '
	def __init__(self,child1,child2):
		Proposition.__init__(self,child1,child2)
	def evaluate(self, **assignments):
		if self.children[0].evaluate(**assignments):
			return self.children[1].evaluate(**assignments)
		else:
			return True
#

class ImpliedBy(Proposition):
	symbol = ' <= '
	def __init__(self,child1,child2):
		Proposition.__init__(self,child1,child2)
	def evaluate(self, **assignments):
		if self.children[1].evaluate(**assignments):
			return self.children[0].evaluate(**assignments)
		else:
			return True
#

class Iff(Proposition):
	symbol = ' <=> '
	def __init__(self,child1,child2):
		Proposition.__init__(self,child1,child2)
	def evaluate(self, **assignments):
		return self.children[0].evaluate(**assignments) == self.children[1].evaluate(**assignments)
#

class ArgumentForm:
	def __init__(self, *premises, conclusion):
		self.premises = [ cast_to_proposition(c) for c in premises ]
		self.conclusion = cast_to_proposition(conclusion)
	def variables(self):
		return frozenset.union(self.conclusion.variables(), *[ c.variables() for c in self.premises ])
	def __repr__(self):
		return 'ArgumentForm( {0} )'.format(self)
	def __str__(self):
		return ((', '.join(str(c) for c in self.premises) + ', ') if self.premises else '') + 'conclusion = ' + str(self.conclusion)
	def print_truth_table(self):
		vars = sorted( self.variables() )
		rows = truth_table_rows(vars)
		
		var_strings = [ '{0: ^5}'.format(v) for v in vars ]
		premise_strings = [ '{0: ^6}'.format(str(c)) for c in self.premises ]
		conclusion_string = '{0: ^10}'.format(str(self.conclusion))
		vars_header = '  '.join(var_strings)
		premises_header = '{0: ^8}'.format('   '.join(premise_strings))
		print('{0}  #  {1: ^{2}}  #  {3: ^{4}}'.format(' '*len(vars_header), 'premises', len(premises_header), 'conclusion', len(conclusion_string)))
		header = '{0}  #  {1: ^8}  #  {2}'.format(vars_header, premises_header, conclusion_string)
		print(header)
		print('#'*len(header))
		
		for r in rows:
			premise_values = [ c.evaluate(**r) for c in self.premises ]
			conclusion_value = self.conclusion.evaluate(**r)
			star = '*' if all( v for v in premise_values ) else ''
			var_cols = '  '.join( '{0: ^{1}}'.format(str(r[v]), len(k)) for (k,v) in zip(var_strings, vars) )
			premise_cols = '   '.join( '{0: ^{1}}'.format(str(v)+star, len(k)) for (k,v) in zip(premise_strings, premise_values) )
			conclusion_col = '{0: ^{1}}'.format(str(conclusion_value)+star, len(conclusion_string))
			print('{0}  #  {1: ^8}  #  {2}'.format(var_cols, premise_cols, conclusion_col))
		print()
	def is_valid_truth_table(self): #adapted by acvm
		vars = (frozenset.union(*[ c.variables() for c in self.premises ]) if self.premises else frozenset()) | self.conclusion.variables()
		return all( self.conclusion.evaluate(**r) for r in truth_table_rows(vars) if all( c.evaluate(**r) for c in self.premises ) )
	def substitute(self, e1, e2):
		return ArgumentForm( *[ c.substitute(e1,e2) for c in self.premises ], conclusion = self.conclusion.substitute(e1,e2) )
#

def get_nodes(formula):
  nodes = [formula]
  if (len(formula.children)>0):
    nodes.extend(get_nodes(formula.children[0]))
  if (len(formula.children)>1):
    nodes.extend(get_nodes(formula.children[1]))
  return nodes


# -------------------------------------------------
# Ínicio do provador por tableaux analíticos
# O code_base foi alterado nas funções das linhas 234 e 227 para melhor
# funcionamento do provador. O código anterior foi comentado.

def cria_ramo(premissas: list, conclusao: list):
    """Cria o vetor ramo."""
    
    # determina o tamanho do vetor ramo
    tam_vetor = 0
    for i in premissas:
        tam_vetor += len(i.to_tree().descendants())
    tam_vetor += len(conclusao.to_tree().descendants())
    
    # cria o vetor ramo
    ramo = [None] * tam_vetor
    for i in range(len(premissas)):
        ramo[i] = [True, premissas[i]] 
    ramo[len(premissas)] = [False, conclusao]

    return(ramo)    

def tamanho_atual(ramo: list):
    """Checa o tamanho atual do vetor ramo."""
    
    tam_atual = 0
    for i in ramo:
        if i is not None:
            tam_atual += 1
    return(tam_atual)
        
def eh_alfa(formula: list):
    """Recebe uma lista ramo e diz se o elemento ramo[i] dessa ramo é uma 
    expansão do tipo alfa."""
    if formula is None:
        return(False)
    
    # alfa T A&B, alfa T ~A
    if formula[0] == True and (isinstance(formula[1], And) or isinstance(formula[1], Not)):
            return(True)
    # alfa F A|B, alfa F A>>B
    elif formula[0] == False and ((isinstance(formula[1], Or)) or isinstance(formula[1], Implies)):
            return(True)
            
    return(False)

def eh_beta(formula: list):
    """Recebe uma lista ramo e diz se o elemento ramo[i] dessa ramo é uma 
    expansão do tipo beta."""
    if formula is None:
        return(False)
    
    # beta T A|B, alfa T A>>B
    if formula[0] == True and (isinstance(formula[1], Or) or isinstance(formula[1], Implies)):
            return(True)
    # beta F A&B, alfa F ~A
    elif formula[0] == False and ((isinstance(formula[1], And)) or isinstance(formula[1], Not)):
            return(True)
            
    return(False)

def cria_alfas(ramo: list):
    """Recebe uma lista ramo e devolve uma lista alfas. Se o elemento[i] da
    lista ramo for uma expansão do tipo alfa, marca a posição i com o valor True.
    Se não, marca a posição i com o valor False."""
    
    # alfa T&, alfa T~, alfa F>>, alfa F|
    # verifica as expansões alfa pendentes
    alfas = [False] * len(ramo)
    for i in range(len(ramo)):
        alfas[i] = eh_alfa(ramo[i])
    return(alfas)

def cria_betas(ramo: list):
    """Recebe uma lista ramo e devolve uma lista betas. Se o elemento[i] da
    lista ramo for uma expansão do tipo beta, marca a posição i com o valor True.
    Se não, marca a posição i com o valor False."""
    
    # beta F&, beta F~, beta T>>, beta T|
    # verifica as expansões beta pendentes
    betas = [False] * len(ramo)
    for i in range(len(ramo)):
        betas[i] = eh_beta(ramo[i])
    return(betas)

def fechado(ramo: list):
    """Recebe o vetor ramo e verifica se há fórmulas conjugadas nele (existe uma
    contradição do tipo T A e F A."""

    n = tamanho_atual(ramo)
    posicao = [False] * n   # armazena as posicoes dos atomos do vetor ramo
    
    for i in range(n):
        if isinstance(ramo[i][1], Variable):
            posicao[i] = True # há um átomo nesta posição
    
    for i in range(n):
        if posicao[i] == True:
            for j in range(n):
                if posicao[j] == True and ramo[j][0] != ramo[i][0] and ramo[j][1] == ramo[i][1]:
                    return(True)
    return(False)

def saturado(betas: list, alfas: list):
    """Recebe o vetor ramo e verifica se ele está saturado (não é possível
    aplicar mais expansões)."""
    if True not in betas and True not in alfas:
        return(True)
    return(False)
        
def seleciona_beta(ramo: list, betas: list):
    """Define o índice i no vetor ramos da próxima fórmula beta a ser expandida 
    (ordem inversa). Se não houver mais fórmulas beta pendentes, retorna
    None."""
    
    n = len(betas)
    for i in reversed(range(n)):
        if betas[i] == True:
            return(i)
    return(None)

def seleciona_alfa(ramo: list, alfas: list):
    """Define o índice i no vetor ramos da próxima fórmula alfa a ser expandida 
    (ordem inversa). Se não houver mais fórmulas alfa pendentes, retorna
    None."""
    
    n = len(alfas)
    for i in reversed(range(n)):
        if alfas[i] == True:
            return(i)
    return(None)

def guarda_valores(ramo: list):
    """Guarda os valores dos átomos em um ramo saturado e os devolve em uma
    lista."""
    
    valores = []
    n = tamanho_atual(ramo)
    for i in range(n):
        if isinstance(ramo[i][1], Variable):
            valores.append(ramo[i])
    valores1 = []
    for formula in valores:
        if formula not in valores1:
            valores1.append(formula)
    return(valores1)

def expansao_alfa(formula: list, i: int, ramo: list, alfas: list, betas: list):
    """Aplica a expansão alfa na fórmula e adiciona alfa1 e alfa2, resultados
    dessa expansão, no vetor ramo."""
    
    if isinstance(formula[1], Variable):
        return(ramo)
    
    n = tamanho_atual(ramo)
    nodes = get_nodes(formula[1])
    alfa1 = nodes[1]
    
    if isinstance(formula[1], Not):
        alfa2 = alfa1
    else:
        n_alfa1 = len(alfa1.to_tree().descendants())
        alfa2 = nodes[n_alfa1+1]
        
    # atualiza alfas depois da expansao de formula
    alfas[i] = False
    
    # alfa T A&B, alfa T ~A 
    if formula[0] == True:
        if isinstance(formula[1], And): # alfa1 = TA, alfa2 = TB
            ramo[n] = [True, alfa1]
            ramo[n+1] = [True, alfa2]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            alfas[n+1] = eh_alfa(ramo[n+1])
            betas[n+1] = eh_beta(ramo[n+1])
        elif isinstance(formula[1], Not): # alfa1 = FA
            ramo[n] = [False, alfa1]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            
    # alfa F A|B, alfa F A>>B
    elif formula[0] == False:
        if isinstance(formula[1], Or): # alfa1 = FA, alfa2 = FB
            ramo[n] = [False, alfa1]
            ramo[n+1] = [False, alfa2]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            alfas[n+1] = eh_alfa(ramo[n+1])
            betas[n+1] = eh_beta(ramo[n+1])
        elif isinstance(formula[1], Implies): # alfa1 = TA, alfa2 = FB
            ramo[n] = [True, alfa1]
            ramo[n+1] = [False, alfa2]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            alfas[n+1] = eh_alfa(ramo[n+1])
            betas[n+1] = eh_beta(ramo[n+1])    
    return(ramo)

def expansao_beta(formula: list, i: int, ramo: list, alfas: list, betas: list, pilha: list):
    """Aplica a expansão beta na fórmula e adiciona beta1 e beta2, resultados
    dessa expansão, no vetor ramo."""
    
    if isinstance(formula[1], Variable):
        return(ramo)
    
    n = tamanho_atual(ramo)
    nodes = get_nodes(formula[1])
    beta1 = nodes[1]
    
    if isinstance(formula[1], Not):
        beta2 = beta1
    else:
        n_beta1 = len(beta1.to_tree().descendants())
        beta2 = nodes[n_beta1+1]
        
    # atualiza betas depois da expansao de formula
    betas[i] = False
    
    # beta T A|B, beta T A>>B 
    if formula[0] == True:
        if isinstance(formula[1], Or): # beta1 = TA, beta2 = TB
            ramo[n] = [True, beta1]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            alfas[n+1] = eh_alfa(ramo[n+1])
            betas[n+1] = eh_beta(ramo[n+1])
            # guarda beta2 na pilha
            pilha.append([[True, beta2], n, betas])
        elif isinstance(formula[1], Implies): # beta1 = FA, beta2 = TB
            ramo[n] = [False, beta1]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            alfas[n+1] = eh_alfa(ramo[n+1])
            betas[n+1] = eh_beta(ramo[n+1])
            # guarda beta2 na pilha
            pilha.append([[True, beta2], n, betas])
            
    # beta F A&B, beta F ~A
    elif formula[0] == False:
        if isinstance(formula[1], And): # beta1 = FA, beta2 = FB
            ramo[n] = [False, beta1]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
            alfas[n+1] = eh_alfa(ramo[n+1])
            betas[n+1] = eh_beta(ramo[n+1])
            # guarda beta2 na pilha
            pilha.append([[False, beta2], n, betas])
        elif isinstance(formula[1], Not): # beta1 = TA
            ramo[n] = [True, beta1]
            # atualiza betas e alfas
            alfas[n] = eh_alfa(ramo[n])
            betas[n] = eh_beta(ramo[n])
    return(ramo)

def imprime(n, ramo):
    """Recebe a lista ramo atual de tamanho n e imprime cada fórmula do ramo,
    indicando se a fórmula recebeu uma expansão alfa ou beta."""
    
    for i in range(n):
        regra = "Alfa"
        if eh_beta(ramo[i]):
            regra = "Beta"
        if not(isinstance(ramo[i][1], Variable)):
            print(f"{regra}, {ramo[i]}")
        else:
            print(ramo[i])

def main():
    """Aplica o método de tableaux analíticos para um sequente."""
    
    P,Q,R,S = vars('P', 'Q', 'R', 'S')  # declaração de variáveis usadas no sequente
    
    formula =  ArgumentForm(
  P >> ( Q| R),     #premises
  conclusion = ~( S & Q ) >> (( P & S ) >> R))


    premissas = formula.premises
    conclusao = formula.conclusion
    
    # cria o vetor ramo original
    ramo = cria_ramo(premissas, conclusao)
    
    # cria as listas de posição alfas e betas
    alfas = cria_alfas(ramo)
    betas = cria_betas(ramo)
    
    pilha = []
    
    print("Sequente a ser provado:")
    n = tamanho_atual(ramo)
    imprime(n, ramo)
    print()
    
    while not(fechado(ramo)):
        print("*")
        
        if saturado(betas, alfas):
            if not(fechado(ramo)): # se houver um ramo saturado sem contradição
                valores = guarda_valores(ramo)
                n = tamanho_atual(ramo)
                print("Último ramo testado:")
                imprime(n, ramo)
                print()
                print("Não é válido. Valores do contra exemplo:")
                return(valores)
        
        while True:
            i = seleciona_alfa(ramo, alfas) # procura por expansões alfa pendentes
            if i is None:
                break 
            ramo = expansao_alfa(ramo[i], i, ramo, alfas, betas)
            print("Expansão alfa:")
            n = tamanho_atual(ramo)
            imprime(n, ramo)
            print()
            
        i = seleciona_beta(ramo, betas) # procura por expansões beta pendentes    
        if i is not None:
            ramo = expansao_beta(ramo[i], i, ramo, alfas, betas, pilha)
            print("Expansão beta:")
            n = tamanho_atual(ramo)
            imprime(n, ramo)
            print()
            
        while fechado(ramo):        # enquanto houver ramo fechado
            print("O ramo atual fechou.")
            print()
            if pilha:
                atual = pilha.pop()
                print(f"Pega o próximo valor na pilha (beta2 = {atual[0]})")
                print()
                tam_corte = atual[1]
                for i in range(tam_corte, len(ramo)):
                    ramo[i] = None
                    betas[i] = False
                ramo[tam_corte] = atual[0]
                betas[tam_corte] = eh_beta(atual[0])
                alfas[tam_corte] = eh_alfa(atual[0])
                n = tamanho_atual(ramo)
                imprime(n, ramo)
                print()
            else:
               print("Não há mais valores na pilha.")
               print()
               break   
    
    n = tamanho_atual(ramo)
    print("Último ramo testado:")
    imprime(n, ramo)
    print()
    print("É válido.")
    return(True)
                
resultado = main()
print(resultado)