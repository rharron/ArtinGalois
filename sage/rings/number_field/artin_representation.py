"""
Artin representations for number fields

AUTHORS:

- Robert Harron (2013): initial version

TESTS:

Standard test of pickleability::

    sage: from sage.rings.number_field.galois_group import GaloisGroup_v3
    sage: from sage.rings.number_field.artin_representation import ArtinRepresentation
    sage: K = NumberField(x^3 - 2, 'a')
    sage: G = GaloisGroup_v3(K, names='b')
    sage: chi = ArtinRepresentation(G, [2, 0, -1])
    sage: chi == loads(dumps(chi))
    True

"""

from sage.structure.sage_object import SageObject
from sage.groups.perm_gps.permgroup import PermutationGroup_generic, PermutationGroup_subgroup
from sage.groups.perm_gps.permgroup_element import PermutationGroupElement
from sage.misc.cachefunc import cached_method
from sage.libs.pari.gen import pari
from sage.rings.infinity import infinity
from sage.rings.number_field.number_field import refine_embedding
from sage.rings.number_field.morphism import NumberFieldHomomorphism_im_gens
from sage.rings.integer_ring import ZZ
from sage.sets.set import Set

from sage.rings.fast_arith import prime_range
from sage.misc.misc_c import prod
from sage.rings.rational_field import QQ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from sage.groups.class_function import ClassFunction_gap

class ArtinRepresentation(ClassFunction_gap):
    """
    TESTS::
    
        sage: from sage.rings.number_field.galois_group import GaloisGroup_v3
        sage: from sage.rings.number_field.artin_representation import ArtinRepresentation
        sage: K = NumberField(x^3 - 2, 'a')
        sage: G = GaloisGroup_v3(K, names='b2')
        sage: chi = ArtinRepresentation(G, [1, 1, 1])
        sage: chi.conductor()
        1
        sage: chi = ArtinRepresentation(G, [1, -1, 1])
        sage: chi.conductor()
        3
        sage: chi.kernel()
        Subgroup [Ring endomorphism of Number Field in b2 with defining polynomial x^6 + 40*x^3 + 1372
          Defn: b2 |--> b2, Ring endomorphism of Number Field in b2 with defining polynomial x^6 + 40*x^3 + 1372
          Defn: b2 |--> 1/36*b2^4 + 1/18*b2, Ring endomorphism of Number Field in b2 with defining polynomial x^6 + 40*x^3 + 1372
          Defn: b2 |--> -1/36*b2^4 - 19/18*b2] of Galois group of Galois closure in b2 of Number Field in a with defining polynomial x^3 - 2 v3
        sage: chi.ramified_primes_base()
        (3,)
        sage: chi.ramified_primes()
        (Fractional ideal (3, 1/2646*b2^5 - 1/189*b2^4 - 1/108*b2^3 + 118/1323*b2^2 - 47/189*b2 - 91/54),)
        sage: chi = ArtinRepresentation(G, [2, 0, -1])
        sage: chi.conductor()
        108
        sage: chi.kernel()
        Subgroup [Ring endomorphism of Number Field in b2 with defining polynomial x^6 + 40*x^3 + 1372
          Defn: b2 |--> b2] of Galois group of Galois closure in b2 of Number Field in a with defining polynomial x^3 - 2 v3
        sage: chi.ramified_primes()
        (Fractional ideal (2, -1/2646*b2^5 + 1/189*b2^4 - 1/54*b2^3 - 118/1323*b2^2 + 47/189*b2 + 17/27),
         Fractional ideal (3, 1/2646*b2^5 - 1/189*b2^4 - 1/108*b2^3 + 118/1323*b2^2 - 47/189*b2 - 91/54))
        sage: chi.ramified_primes_base()
        (2, 3)
        sage: K5 = NumberField(x^5 - 5, 'a')
        sage: G5 = GaloisGroup_v3(K5, names='b')
        sage: chi = ArtinRepresentation(G5, [4, 0, 0, 0, -1])
        sage: chi.conductor()
        1953125
        sage: chi.ramified_primes_base()
        (5,)
        sage: chi = ArtinRepresentation(G5, [1, 1, -1, -1, 1])
        sage: chi.conductor()
        5
        sage: K35 = NumberField(x^3 - 35, 'a')
        sage: G35 = GaloisGroup_v3(K35, names='b')
        sage: L35 = G35.splitting_field()
        sage: chi = ArtinRepresentation(G35, [2,0,-1])
        sage: chi.euler_factor(5)
        1
        sage: chi.euler_factor(7)
        1
        sage: IP = G35.inertia_group(L35.primes_above(3)[0])
        sage: chi.average_value(IP)
        1
    """
    def restrict(self, H):
        rest = self._gap_classfunction.RestrictedClassFunction(H._gap_())
        return ArtinRepresentation(H, rest)
    
    @cached_method
    def frobenius_schur_indicator(self):
        """
        EXAMPLES::
        
            sage: from sage.rings.number_field.galois_group import GaloisGroup_v3
            sage: from sage.rings.number_field.artin_representation import ArtinRepresentation
            sage: f = x^8 + 24*x^6 + 144*x^4 + 288*x^2 + 144
            sage: K = NumberField(f, 'a')
            sage: G = GaloisGroup_v3(K)
            sage: chi = G.character([2, -2, 0, 0, 0])
            sage: chi.frobenius_schur_indicator()
            -1
            sage: g = x^8 - 12*x^6 + 36*x^4 - 36*x^2 + 9
            sage: M = NumberField(g, 'b')
            sage: G = GaloisGroup_v3(M)
            sage: chi = G.character([2, -2, 0, 0, 0])
            sage: chi.frobenius_schur_indicator()
            -1
        """
        return sum([self(g**2) for g in self.domain()]) / self.domain().order()
    
    @cached_method
    def kernel(self):
        G = self.domain()
        deg = self.degree()
        elts = [g for g in G if self(g) == deg]
        return G.subgroup(elts)
    
    @cached_method
    def ramified_primes(self):
        deg = self.degree()
        ram = []
        for P in self._nf_ram_primes():
            IP = self.domain().inertia_group(P)
            for g in IP:
                if self(g) != deg:
                    ram.append(P)
                    break
        return tuple(ram)
    
    @cached_method
    def ramified_primes_base(self):
        L = self.domain().splitting_field()
        deg = self.degree()
        ram = []
        for p in self._nf_ram_primes_base():
            P = L.primes_above(p)[0]
            IP = self.domain().inertia_group(P)
            for g in IP:
                if self(g) != deg:
                    ram.append(p)
                    break
        return tuple(ram)
    
    @cached_method
    def _nf_ram_primes(self):
        L = self.domain().splitting_field()
        ram = []
        for p, _ in L.absolute_discriminant().factor():
            for P, e in L.ideal(p).factor():
                if e > 1:
                    ram.append(P)
        return tuple(ram)
    
    @cached_method
    def _nf_ram_primes_base(self):
        L = self.domain().splitting_field()
        ram = []
        for p, _ in L.absolute_discriminant().factor():
            e = L.ideal(p).factor()[0][1]
            if e > 1:
                ram.append(p)
        return tuple(ram)
    
    @cached_method
    def average_value(self, H=None):
        if H is None:
            #return ZZ(0)  # QQ(0)? (Is this true?)
            H = self.domain()
        return sum(self(sigma) for sigma in H) / H.order()
    
    @cached_method
    def conductor(self, P=None):
        G = self.domain()
        L = G.splitting_field()
        if P is None:
            return prod(p ** self.conductor(L.primes_above(p)[0]) for p in self.ramified_primes_base())
        ram_breaks = sorted(G.ramification_breaks(P))
        n = max(ram_breaks)
        if n == -1:
            return ZZ(0)
        if ram_breaks[0] != -1:
            ram_breaks = [-1] + ram_breaks
        deg = self.degree()
        ram_groups = [G.ramification_group(P, i) for i in ram_breaks[1:]]
        if ram_breaks[1] != 0:
            g0 = G.ramification_group(P, 0).order()
        else:
            g0 = ram_groups[0].order()
        f = ZZ(0)#deg * (n + 1)
        gi_sum = ZZ(0)
        for j in range(1, len(ram_breaks)):
            gi_sum += (ram_breaks[j] - ram_breaks[j-1]) * ram_groups[j-1].order()
            complement = Set(ram_groups[j-1]).difference(Set(ram_groups[j])) if j < len(ram_groups) else ram_groups[-1]
            f += (ram_breaks[j] + 1) * sum([self(sigma) for sigma in complement])
        return (deg * gi_sum - f) / g0
    
    @cached_method
    def euler_factor(self, p, var='x'):
        r"""
        This does not return the Euler factor a `p`. Rather, it returns a polynomial `P_p` (in the variable ``var``) such that the Euler factor at `p` is `1/P_p(p^{-s})`.
        EXAMPLES::
        
        sage: K35 = NumberField(x^3 - 35, 'a')
        sage: from sage.rings.number_field.galois_group import GaloisGroup_v3
        sage: from sage.rings.number_field.artin_representation import ArtinRepresentation
        sage: G35 = GaloisGroup_v3(K35, names='b')
        sage: L35 = G35.splitting_field()
        sage: chi = ArtinRepresentation(G35, [2,0,-1])
        sage: for p in prime_range(30):
        ...    print p, chi.euler_factor(p)
        2 -x^2 + 1
        3 -x + 1
        5 1
        7 1
        11 -x^2 + 1
        13 x^2 + x + 1
        17 -x^2 + 1
        19 x^2 + x + 1
        23 -x^2 + 1
        29 -x^2 + 1
        sage: K.<a> = NumberField(x^5 - 5)
        sage: G = GaloisGroup_v3(K, 'b')
        sage: L = G.splitting_field()
        sage: chi = G.character([4,0,0,0,-1])
        sage: for p in prime_range(50):
        ...    print p, chi.euler_factor(p)
        2 -x^4 + 1
        3 -x^4 + 1
        5 1
        7 -x^4 + 1
        11 x^4 + x^3 + x^2 + x + 1
        13 -x^4 + 1
        17 -x^4 + 1
        19 x^4 - 2*x^2 + 1
        23 -x^4 + 1
        29 x^4 - 2*x^2 + 1
        31 x^4 - 4*x^3 + 6*x^2 - 4*x + 1
        37 -x^4 + 1
        41 x^4 + x^3 + x^2 + x + 1
        43 -x^4 + 1
        47 -x^4 + 1
        """
        G = self.domain()
        L = G.splitting_field()
        P = L.primes_above(p)[0]
        if p not in self.ramified_primes_base():
            return self.charpoly_reverse(G.artin_symbol(P), var)
        DP = G.decomposition_group(P)
        IP = DP.inertia_group(P)
        chi_P = self.restrict(DP)
        VI = chi_P.invariant_subspace(IP)
        return VI.charpoly_reverse(DP.artin_symbol(P), var)
    
    @cached_method
    def dirichlet_coefficients(self, ncoeffs=20):
        from sage.rings.power_series_ring import PowerSeriesRing
        from sage.misc.misc import srange
        #from sage.misc.mrange import mrange
        ncoeffs = ZZ(ncoeffs)
        ps = prime_range(ncoeffs + 1)
        num_ps = len(ps)
        exps = [ncoeffs.exact_log(p) + 1 for p in ps]
        M = ncoeffs.exact_log(2) + 1
        #print ps, exps, M
        PS = PowerSeriesRing(QQ, 'x', M)
        euler_factors = dict([[ps[i], ~PS(self.euler_factor(ps[i]), exps[i] + 1)] for i in range(num_ps)])
        ans = []
        for n in srange(1, ncoeffs + 1):
            ans.append(prod([euler_factors[p][e] for p, e in n.factor()]))
        #ans = [0] * ncoeffs
        #is_zeroes = True
        #for e in mrange(exps):
        #    if is_zeroes:
        #        is_zeroes = False
        #        ans[0] = QQ.one()
        #        continue
        #    n = 1
        #    an = QQ.one()
        #    breaker = False
        #    for i in range(num_ps):
        #        if exps[i] == 0:
        #            continue
        #        n *= ps[i] ** e[i]
        #        if n > ncoeffs:
        #            breaker = True
        #            break
        #        an *= euler_factors[i][e[i]]
        #    #print n, an, e
        #    if breaker:
        #        continue
        #    ans[n-1] = an
        return ans
    
    @cached_method
    def charpoly(self, g, var='x'):
        r"""
        Determines the characteristic polynomial `\det(I-gT)`
        """
        if self.degree() == 0:
            return QQ.one()
        from sage.combinat.sf.sf import SymmetricFunctions
        S = SymmetricFunctions(QQ)
        p = S.powersum()
        e = S.elementary()
        deg = self.degree()
        traces = [self(g ** n) for n in range(1, deg+1)]
        x = PolynomialRing(QQ, var).gen()
        cp = x ** deg
        for n in range(deg):
            mc = p(e[n+1]).monomial_coefficients()
            cp += (-1) ** (n+1) * x ** (deg-1-n) * sum(mc[k] * prod(traces[j-1] for j in k) for k in mc.keys())
        return cp
    
    @cached_method
    def charpoly_reverse(self, g, var='x'):
        r"""
        Determines the characteristic polynomial `\det(I-gT)`
        
        sage: from sage.rings.number_field.galois_group import GaloisGroup_v3
        sage: from sage.rings.number_field.artin_representation import ArtinRepresentation
        sage: K = NumberField(x^3 - 2, 'a')
        sage: G = GaloisGroup_v3(K, names='b2')
        sage: chi = ArtinRepresentation(G, [2, 0, -1])
        sage: L = G.splitting_field()
        sage: for p in prime_range(5, 50):
        ...    print p, chi.charpoly_reverse(G.artin_symbol(L.primes_above(p)[0]))
        5 -x^2 + 1
        7 x^2 + x + 1
        11 -x^2 + 1
        13 x^2 + x + 1
        17 -x^2 + 1
        19 x^2 + x + 1
        23 -x^2 + 1
        29 -x^2 + 1
        31 x^2 - 2*x + 1
        37 x^2 + x + 1
        41 -x^2 + 1
        43 x^2 - 2*x + 1
        47 -x^2 + 1
        """
        if self.degree() == 0:
            return QQ.one()
        from sage.combinat.sf.sf import SymmetricFunctions
        S = SymmetricFunctions(QQ)
        p = S.powersum()
        e = S.elementary()
        deg = self.degree()
        traces = [self(g ** n) for n in range(1, deg+1)]
        x = PolynomialRing(QQ, var).gen()
        cp = QQ.one()
        for n in range(deg):
            mc = p(e[n+1]).monomial_coefficients()
            cp += (-1) ** (n+1) * x ** (n+1) * sum(mc[k] * prod(traces[j-1] for j in k) for k in mc.keys())
        return cp
    
    def invariant_subspace(self, H):
        r"""
        Find the maximal subcharacter on which H acts trivially.
        """
        G = self.domain()
        pieces = self.decompose() #todo: change to irreducible_constituents and take inner product later if needed
        inv = ArtinRepresentation(G, [QQ(0)] * len(G.conjugacy_classes()))
        for mult, theta in pieces:
            add = True
            deg = theta.degree()
            for h in H:
                if theta(h) != deg:
                    add = False
                    break
            if add:
                inv += mult * theta
        return ArtinRepresentation(G, inv)
    
    @cached_method
    def root_number(self, p=None):
        r"""
        If ``p`` is ``None``, return the global root number. Otherwise, return the local root number at ``p``.
        
        EXAMPLES::
        
            sage: from sage.rings.number_field.galois_group import GaloisGroup_v3
            sage: from sage.rings.number_field.artin_representation import ArtinRepresentation
            sage: f = x^8 + 24*x^6 + 144*x^4 + 288*x^2 + 144
            sage: K = NumberField(f, 'a')
            sage: G = GaloisGroup_v3(K)
            sage: chi = G.character([2, -2, 0, 0, 0])
            sage: chi.root_number()
            -1
            sage: g = x^8 - 12*x^6 + 36*x^4 - 36*x^2 + 9
            sage: M = NumberField(g, 'b')
            sage: G = GaloisGroup_v3(M)
            sage: chi = G.character([2, -2, 0, 0, 0])
            sage: chi.root_number()
            1
        """
        if not  p is None:
            return NotImplementedError
        try:
            return self._root_number
        except AttributeError:
            pass
        if not self.is_irreducible():
            raise NotImplementedError
        F = self._base_ring
        sfi = self.frobenius_schur_indicator()
        if sfi == 1:
            return F.one()
        if sfi == -1:
            m = 2
            #temp
            for W in [F.one(), -F.one()]:
                if self._lfunction(W) is not None:
                    return self._root_number
        else:
            raise NotImplementedError
        raise NotImplementedError
    
    def _lfunction(self, W, prec=53, threshold=1e-10):
        from sage.lfunctions.all import Dokchitser
        G = self.domain()
        LG = G.splitting_field()
        deg = self.degree()
        
        #Determine the Gamma factors
        if LG.is_totally_real():
            gammaV = [0] * deg
        else:
            H = G.subgroup([G.complex_conjugation(LG.places()[0])])
            deg_plus = ZZ(self.restrict(H).scalar_product(H.trivial_character()))
            gammaV = [0] * deg_plus + [1] * (deg - deg_plus)
        
        if self.scalar_product(G.trivial_character()) > 0:
            raise NotImplementedError
        L = Dokchitser(conductor=self.conductor(), gammaV=gammaV, weight=1, eps=W, prec=prec)
        coeffs = 'coeff = %s'%(self.dirichlet_coefficients(L.num_coeffs(1.2)))
        L.init_coeffs('coeff[k]', pari_precode=coeffs)
        if L.check_functional_equation().abs() > threshold:
            return None
        self._root_number = W
        return True
        #self._lfunction = L
        pass
    
    def lfunction(self):
        raise NotImplementedError
    
    @cached_method
    def is_orthogonal(self):
        if not self.is_irreducible():
            raise NotImplementedError
        return self.frobenius_schur_indicator() == 1
    
    @cached_method
    def is_symplectic(self):
        if not self.is_irreducible():
            raise NotImplementedError
        return self.frobenius_schur_indicator() == -1
    
    @cached_method
    def is_unitary(self):
        if not self.is_irreducible():
            raise NotImplementedError
        return self.frobenius_schur_indicator() != 1 and self.frobenius_schur_indicator() != -1
