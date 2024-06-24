from protocols import *
from math import prod

def verify_encryption(proofs, alphas, betas, trustees_public_keys): 

    p = trustees_public_keys['p']
    q = trustees_public_keys['q']
    g = trustees_public_keys['g']
    ys = [y for y in trustees_public_keys['ys']]

    if proofs is None:
        return True
    
    election_pk = prod(ys) % p
    alpha = prod(alphas) % p
    beta = prod(betas) % p

    e1 = proofs[0]['challenge']
    e2 = proofs[1]['challenge']

    t1 = proofs[0]['response']
    t2 = proofs[1]['response']

    A1 = proofs[0]['commitment']['A']
    A2 = proofs[1]['commitment']['A']

    B1 = proofs[0]['commitment']['B']
    B2 = proofs[1]['commitment']['B']

    c = ((A1,B1),(A2,B2))

    tet = ((t1,e1),t2)

    s = (((g, alpha),(election_pk,beta)), ((g,alpha), (election_pk, beta * pow(g, -1, p))))

    sp = DisjunctionSP(EqualitySP(SchnorrSP(p,q)))
    result = sp.HonestVerifier(s, c, e1+e2, tet)

    return result


def verify_decryption(trustee_public_key, trustee_decryption_factor, trustee_decryption_proof, alphas):
    p = trustee_public_key['p']
    q = trustee_public_key['q']
    y = trustee_public_key['y']
    g = trustee_public_key['g']

    d = trustee_decryption_factorhe 
    e = trustee_decryption_proof['challenge']
    t = trustee_decryption_proof['response']
    A = trustee_decryption_proof['commitment']['A']
    B = trustee_decryption_proof['commitment']['B']
    c = (A, B)

    alpha = prod(alphas) % p
    s = ((g, y),(alpha,d))

    sp = EqualitySP(SchnorrSP(p,q))
    result = sp.HonestVerifier(s, c, e, t )

    return result


# def verify_result(result_data):
#     p = result_data['trustees_public_keys']['p']
#     q = result_data['trustees_public_keys']['q']
#     g = result_data['trustees_public_keys']['g']
#     question_result = result_data['result']
#     betas = result_data['betas']
#     decryption_factors = result_data['decryption_factors']

#     c = prod(betas) % p
#     e = -1
#     s1 = g
#     s2 = prod(decryption_factors) % p
#     s = (s1,s2)
#     t = question_result

#     sp = SchnorrSP(p,q)
#     result = sp.HonestVerifier(s, c, e, t)
#     return result


def verify_result(result_data):
    p = result_data['trustees_public_keys']['p']
    q = result_data['trustees_public_keys']['q']
    g = result_data['trustees_public_keys']['g']
    question_result = result_data['result']
    betas = result_data['betas']
    decryption_factors = result_data['decryption_factors']

    c = prod(betas) % p
    e = 1
    s1 = g
    s2 = prod(decryption_factors) % p
    s3 = pow(s2, -1, p)
    s = (s1,s3)
    t = question_result

    sp = SchnorrSP(p,q)
    result = sp.HonestVerifier(s, c, e, t)
    return result