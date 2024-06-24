import random
import hashlib
import base64
import hashlib
# base64.b64encode(hashlib.sha1("test").digest())

class SchnorrSP:
    def __init__(self, p, q):
        self.p = p
        self.q = q

    def Relation(self, s, w):
        return (pow(s[0], w, self.p) == s[1])

    def Prover_0(self, s,w,r):
        return pow(s[0], r, self.p)
    
    def Statement(self, s1):
        s2 = pow(s1, self.w, self.p)
        self.s = (s1, s2)
        return self.s
    
    def Challenge(self, c):
        strc = str(c)
        strcencode = strc.encode('utf-8')
        e16 = hashlib.sha256(strcencode)
        e10 = int(e16.hexdigest(), 16) % self.q
        self.e = e10
        return self.e

    def Prover_1(self, s,w,r,c,e):
        self.t = e*w+ r
        return self.t

    def HonestVerifier(self, s,c,e,t):
        LHS = pow(s[0], t, self.p)
        RHS = (pow(s[1], e, self.p) * c) % self.p
        return (LHS == RHS)

    def Witness(self, w):
        self.w = w
        return w
    
    def RandomCoin(self):
        self.random_coin = random.randint(1, self.q-1)
        return self.random_coin

    def Extractor(self, t1, t2, e1, e2):
        if e1 == e2:
            return 0
        else:
            return (t1 - t2) * pow((e1 - e2), -1, self.q)

    def Simulator(self, s, t, e):
        c = (pow(s[0], t, self.p) * pow(s[1], -e, self.p)) % self.p
        return ((s[0], s[1]), c, e, t)

    def SimulatorMap(self, s, w, e, r):
        return (e*w + r)

    def SimulatorMapInverse(self, s, w, e, t):
        return t - e * w
            


class EqualitySP(SchnorrSP):
    
    def __init__(self, sp):
        self.sp = sp
        self.p = sp.p
        self.q = sp.q

    def Statement(self, s1):
        s12 = pow(s1[0], self.w, self.p)
        s22 = pow(s1[1], self.w, self.p)
        self.s = ((s1[0], s12), (s1[1], s22))
        return self.s
    
    def Challenge(self, c):
        self.e = self.sp.Challenge(c[0] + c[1])
        return self.e

    def Relation(self, s, w):
        return (self.sp.Relation(s[0], w) and self.sp.Relation(s[1], w))

    def Prover_0(self, s, w, r):
        return (self.sp.Prover_0(s[0], w, r), self.sp.Prover_0(s[1], w, r))
    
    def Prover_1(self, s, w, r, c, e):
        return self.sp.Prover_1(s[0], w, r, c, e)

    def HonestVerifier(self, s, c, e, t):
        x = (self.sp.HonestVerifier(s[0], c[0], e, t))
        y =  (self.sp.HonestVerifier(s[1], c[1], e, t))
        # print(x)
        # print(y)
        return x and y

    def Witness(self, w):
        self.w = self.sp.Witness(w)
        return self.w

    def RandomCoin(self):
        self.r = self.sp.RandomCoin()
        return self.r

    def Extractor(self, t1, t2, e1, e2):
        return self.sp.Extractor(t1, t2, e1, e2)

    def Simulator(self, s, t, e):
        (s1, c1, e1, t1) = self.sp.Simulator(s[0], t, e)
        (s2, c2, e2, t2) = self.sp.Simulator(s[1], t, e)
        return ((s1, s2), (c1, c2), e1, t1)

    def SimulatorMap(self, s, w, e, r):
        return self.sp.SimulatorMap(s[0], w, e, r)

    def SimulatorMapInverse(self, s, w, e, t):
        return self.sp.SimulatorMapInverse(s[0], w, e, t)
    
        

class DisjunctionSP(EqualitySP):
    def __init__(self, sp):
        self.sp = sp
        self.p = sp.p
        self.q = sp.q

    def Witness(self, w):
        self.w = self.sp.Witness(w)
        return self.w

    def Statement(self, s):
        # need to pass a statement of the form (((s1,s2),(s3,s4)),((s5,s6),(s7,s8)))
        s1 = s[0][0]
        s3 = s[0][1]
        s5 = s[1][0]
        s7 = s[1][1]
        s6 = pow(s5, self.w+1, self.p)
        s8 = pow(s7, self.w+2, self.p)
        self.s = (self.sp.Statement((s1, s3)), ((s5, s6), (s7, s8)))
        return self.s

    def Relation(self, s, w):
        return (self.sp.Relation(s[0], w) or self.sp.Relation(s[1], w))


    def RandomCoin(self):
        # RandomCoins:= ((sp.RandomCoins × sp.Responses) × sp.Challenges.carrier);
        r = self.sp.RandomCoin()
        c1 = self.sp.Prover_0(self.s[0], self.w, r)
        c2 = self.sp.Prover_0(self.s[1], self.w, r)
        e = self.sp.Challenge(c1 + c2)
        t = self.w * e + self.sp.r
        self.r = ((r, t), e)
        return self.r

    def Prover_0(self, s, w, xr): # r = ((r, t) e)
        if self.sp.Relation(s[0], w):
            r = xr[0][0]
            t = xr[0][1]
            e = xr[1]
            c1 = self.sp.Prover_0(s[0], w, r)
            (s2, c2, e2, t2) = self.sp.Simulator(s[1], t, e)
            return (c1, c2)
        else:
            (s1, c1, e1, t1) = self.sp.Simulator(s[0], t, e)
            c2 = self.sp.Prover_0(s[1], w, r)
            return (c1, c2)

    def Prover_1(self, s, w, xr, xc, e1): #   Prover_1:= (λ (s1, s2) w ((r,t1),e2) (c1, c2) e1.
        # Responses:= ((sp.Responses × sp.Challenges.carrier) × sp.Responses);
        s1 = s[0]
        s2 = s[1]
        r = xr[0][0]
        t1 = xr[0][1]
        e2 = xr[1]
        c1 = xc[0]
        c2 = xc[1]
        e3 = e1 - e2
        if self.sp.Relation(s1, w):
            (s_2, c_2, e_2, t_2) = self.sp.Simulator(s2, t1, e2)
            t_1 = self.sp.Prover_1(s1, w, r, c1, e3)
            return ((t_1, e3), t_2)
        else:
            (s_1, c_1, e_1, t_1) = self.sp.Simulator(s1, t1, e2)
            t_2 = self.sp.Prover_1(s2, w, r, c2, e3)
            return ((t_1, e2), t_2)

    def HonestVerifier(self, s, c, e1, xt): #    HonestVerifier:= (λ ((s1, s2), (c1, c2), e1, ((t1,e2),t2)).
        s1 = s[0]
        s2 = s[1]
        t1 = xt[0][0]
        e2 = xt[0][1]
        t2 = xt[1]
        e3 = e1 - e2
        x = self.sp.HonestVerifier(s1, c[0], e2, t1)
        y = self.sp.HonestVerifier(s2, c[1], e3, t2)
        # print("x: ", x)
        # print("y: ", y)
        return x and y

    def Extractor(self, xt1, xt2, xe1, xe2): #       Extractor:= (λ ((t1,e1),t2) ((t3,e3),t4) e5 e6.  
        t1 = xt1[0][0]
        e1 = xt1[0][1]
        t2 = xt1[1]
        t3 = xt2[0][0]
        e3 = xt2[0][1]
        t4 = xt2[1]
        e5 = xe1
        e6 = xe2
        if e1 != e3:
            return self.sp.Extractor(t1, t3, e1, e3)
        else:
            e2 = e5 - e1
            e4 = e6 - e3
            return self.sp.Extractor(t2, t4, e2, e4)


    def Simulator(self, s, xt, xe):
        s1 = s[0]
        s2 = s[1]
        t1 = xt[0][0]
        e1 = xt[0][1]
        t2 = xt[1]
        e2 = xe
        (s_1, c_1, e_1, t_1) = self.sp.Simulator(s[0], t1, e1)
        e3 = e2 - e1
        (s_2, c_2, e_2, t_2) = self.sp.Simulator(s[1], t2, e3)
        return ((s1, s2), (c_1, c_2), e2, ((t_1, e1), t_2))

    def SimulatorMap(self, s, w, e1, xr):
        s1 = s[0]
        s2 = s[1]
        r = xr[0][0]
        t = xr[0][1]
        e2 = xr[1]
        e3 = e1 - e2
        if self.sp.Relation(s1, w):
            t1 = self.sp.SimulatorMap(s1, w, e3, r)
            return ((t1, e3), t)
        else:
            t2 = self.sp.SimulatorMap(s2, w, e3, r)
            return ((t, e2), t2)
                                             
 
    def SimulatorMapInverse(self, s, w, e1, t):
        s1 = s[0]
        s2 = s[1]
        t1 = t[0][0]
        e2 = t[0][1]
        t2 = t[1]
        e3 = e1 - e2
        if self.sp.Relation(s1, w):
            r = self.sp.SimulatorMapInverse(s1, w, e2, t1)
            return ((r, t2), e3)
        else:
            r = self.sp.SimulatorMapInverse(s2, w, e3, t2)
            return ((r, t1), e2)


# Testing
if __name__ == "__main__":
    import random
    import json
    import functools

    # get global election variables
    with open(f'trustees.json') as f:
        json_data = f.read()
    trustees = json.loads(json_data)
    trustee = trustees[0]
    public_key = trustee['public_key']
    p = int(public_key['p'])
    q = int(public_key['q'])
    y = int(public_key['y'])
    g = int(public_key['g'])

    # get one voter answer
    uuid = "0a3ab828-040e-490c-b12b-01575ccfbf71"
    with open(f'ballots/{uuid}.json') as f:
        json_data = f.read()
    voter = json.loads(json_data)
    vote = voter['vote']
    answers = vote['answers']
    answer = answers[0]
    choices = answer['choices']
    choice = choices[0]
    alpha = int(choice['alpha'])
    beta = int(choice['beta'])
    individual_proofs = answer['individual_proofs']
    individual_proof = individual_proofs[0]

    sp = SchnorrSP(p,q)

    # correctness
    result = True
    for w in range(1000):
        sp.Witness(w)
        s = sp.Statement(g)
        r = sp.RandomCoin()
        c = sp.Prover_0(s, w, r)
        e = sp.Challenge(c)
        t = sp.Prover_1(s, w, r, c, e)
        x = sp.HonestVerifier(s, c, e, t)
        result = result and x
    print(f'schnorr correctness {result}')

    # Simulator correctness
    result = True
    for i in range(1000):
        w = random.randint(1, sp.q-1)
        s1 = random.randint(1, sp.p-1)
        s2 = random.randint(1, sp.p-1)
        s = (s1, s2)
        t = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        x = sp.Simulator(s, t, e)
        z = sp.HonestVerifier(x[0], x[1], x[2], x[3])
        result = result and z
    print(f'schnorr simulator correctness {result}')

    # ZK
    import functools
    result = True
    for i in range(1000):
        r = random.randint(1, sp.q-1)
        t = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        w = random.randint(1, sp.q-1)
        s1 = random.randint(1, sp.p-1)
        s2 = pow(s1, w, sp.p)
        s = (s1, s2)

        c = sp.Prover_0(s, w, r)
        spm = functools.partial(lambda x1, x2, x3, x4: sp.SimulatorMap(x1, x2, x3, x4), s, w, e)
        spmi = functools.partial(lambda x1, x2, x3, x4: sp.SimulatorMapInverse(x1, x2, x3, x4), s, w, e)
        
        result1 = (sp.Simulator(s, spm(r), e) == (s, c, e, sp.Prover_1(s,w,r,c,e)))
        result2 = (spmi(spm(r)) == r)
        result3 = (spm(spmi(t)) == t)

        result = result1 and result2 and result3 and result

    print(f'schnorr ZK {result}')


    sp = EqualitySP(SchnorrSP(p,q))
    # correctness
    result = True
    for w in range(1000):
        sp.Witness(w)
        s = sp.Statement((g,y))
        r = sp.RandomCoin()
        c = sp.Prover_0(s, w, r)
        e = sp.Challenge(c)
        t = sp.Prover_1(s, w, r, c, e)
        x = sp.HonestVerifier(s, c, e, t)
        result = result and x
    print(f'equality correctness {result}')


 
    # Simulator correctness
    result = True
    for i in range(1000):
        w = random.randint(1, sp.q-1)
        s1 = random.randint(1, sp.p-1)
        s2 = random.randint(1, sp.p-1)
        s3 = random.randint(1, sp.p-1)
        s4 = random.randint(1, sp.p-1)
        s = ((s1, s2),(s3, s4))
        t = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        x = sp.Simulator(s, t, e)
        z = sp.HonestVerifier(x[0], x[1], x[2], x[3])
        result = result and z
    print(f'equality simulator correctness {result}')

    # ZK
    import functools
    result = True
    for i in range(1000):
        r = random.randint(1, sp.q-1)
        t = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        w = random.randint(1, sp.q-1)
        s1 = random.randint(1, sp.p-1)
        s3 = random.randint(1, sp.p-1)
        s2 = pow(s1, w, sp.p)
        s4 = pow(s3, w, sp.p)
        s = ((s1, s2),(s3, s4))

        c = sp.Prover_0(s, w, r)
        spm = functools.partial(lambda x1, x2, x3, x4: sp.SimulatorMap(x1, x2, x3, x4), s, w, e)
        spmi = functools.partial(lambda x1, x2, x3, x4: sp.SimulatorMapInverse(x1, x2, x3, x4), s, w, e)
        
        result1 = (sp.Simulator(s, spm(r), e) == (s, c, e, sp.Prover_1(s,w,r,c,e)))
        result2 = (spmi(spm(r)) == r)
        result3 = (spm(spmi(t)) == t)

        result = result1 and result2 and result3 and result
    print(f'equality ZK {result}')


    sp = DisjunctionSP(EqualitySP(SchnorrSP(p,q)))
    # correctness
    result = True
    for w in range(1000):
        w = sp.Witness(10)
        s = sp.Statement(((g,y), (g,y)))
        r = sp.RandomCoin()
        c = sp.Prover_0(s, w, r)
        e = sp.Challenge(c)
        t = sp.Prover_1(s, w, r, c, e)
        x = sp.HonestVerifier(s, c, e, t)
        result = result and x
    print(f'disjunction correctness {result}')

    # Simulator correctness
    result = True
    for i in range(1000):
        w = random.randint(1, sp.q-1)

        s1 = random.randint(1, sp.p-1)
        s2 = random.randint(1, sp.p-1)
        s3 = random.randint(1, sp.p-1)
        s4 = random.randint(1, sp.p-1)

        s5 = random.randint(1, sp.p-1)
        s6 = random.randint(1, sp.p-1)
        s7 = random.randint(1, sp.p-1)
        s8 = random.randint(1, sp.p-1)

        s = (((s1,s2),(s3,s4)),((s5,s6),(s7,s8)))
        t1 = random.randint(1, sp.q-1)
        t2 = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        t = ((t1,e),t2)

        x = sp.Simulator(s, t, e)
        z = sp.HonestVerifier(x[0], x[1], x[2], x[3])
        result = result and z
    print(f'disjunction simulator correctness {result}')

    # ZK
    result = True
    for i in range(1000):
        
        r = random.randint(1, sp.q-1)
        t = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        rte = ((r,t),e)

        t1 = random.randint(1, sp.q-1)
        e = random.randint(1, sp.q-1)
        t2 = random.randint(1, sp.q-1)

        tet = ((t1,e),t2)

        w = random.randint(1, sp.q-1)

        s1 = random.randint(1, sp.p-1)
        s3 = random.randint(1, sp.p-1)
        s2 = pow(s1, w, sp.p)
        s4 = pow(s3, w, sp.p)

        s5 = random.randint(1, sp.p-1)
        s6 = random.randint(1, sp.p-1)
        s7 = random.randint(1, sp.p-1)
        s8 = random.randint(1, sp.p-1)

        s = (((s1, s2),(s3, s4)), ((s5,s6),(s7,s8)))

        c = sp.Prover_0(s, w, rte)
        spm = functools.partial(lambda x1, x2, x3, x4: sp.SimulatorMap(x1, x2, x3, x4), s, w, e)
        spmi = functools.partial(lambda x1, x2, x3, x4: sp.SimulatorMapInverse(x1, x2, x3, x4), s, w, e)
        
        result1 = (sp.Simulator(s, spm(rte), e) == (s, c, e, sp.Prover_1(s,w,rte,c,e)))
        result2 = (spmi(spm(rte)) == rte)
        result3 = (spm(spmi(tet)) == tet)

        result = result1 and result2 and result3 and result

    print(f'disjunction ZK {result}')