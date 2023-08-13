from __future__ import division
from collections import defaultdict
from mwmatching import maxWeightMatching
import string
import math
from numpy.matlib import zeros

def read_complex1(complex):
    complexes = defaultdict(list)
    read_point = open(complex,"r");
    com = defaultdict(list)
    k = 1
    averagesize = 0.0
    for line in read_point.readlines():
        line_interaction = line.split()
        complexes = line_interaction[1:]
        #print("complexes =",len(complexes))
        averagesize = averagesize+len(complexes)
        com[k] = complexes
        k = k + 1
    print("averagesize =",averagesize/len(com))
    return com

def strtolist(com):
    for id in com:
        #print "com[id]=",com[id].split()
        com[id] = com[id].split()
    #print "com=",com
    return com

def refilter_complex(complex):
    for id in complex:
        print (id)
        print(complex[id])
        complex[id].remove(str(id))
    return complex

def NA(a,b):
    set_a = set(a)
    set_b = set(b)
    comm = float(len(set_a & set_b))
    union = len(set_a) * len(set_b)
    return (comm * comm) / union
###########################################################################
def Recall(reference,predicted,a):
    length = len(reference)
    num = 0.0
    for id in reference:
        w = 0.0
        for it in predicted:
            w = NA(reference[id],predicted[it])
            if w >= a:
                num = num + 1
                break
            else:
                continue
    recall = num /length
    print("recall=",recall)
    return recall

def Precision(reference,predicted,a):
    length = len(predicted)
    num = 0.0
    for id in predicted:
        w = 0.0
        for it in reference:
            w = NA(reference[it],predicted[id])
            if w >= a:
                num = num + 1
                break
            else:
                continue
    precision = float(num) / length
    print("precision =", precision)
    return precision

def F_measure(reference_complexes1,predicted_complexes1,a):
    recall = Recall(reference_complexes1,predicted_complexes1,a)
    precision = Precision(reference_complexes1,predicted_complexes1,a)
    f_measure = (2*recall*precision) / (precision + recall)
    print("F-measure=",f_measure)
    return f_measure,recall,precision

def Coverage(reference,predict):
    score = 0.0
    top = 0.0
    down = 0.0
    for i in reference:
        number_i = set(reference[i])
        max_com = 0.0
        for j in predict:
            number_j = set(predict[j])
            common_ij = number_i & number_j
            if len(common_ij) > max_com:
                max_com = len(common_ij)
            else:
                continue
        top = top + float(max_com)
        down = down + float(len(reference[i]))
    score = top / down
    print("score=",score)
    return score


def T_ij(prediction,reference):
    T_ij = len(set(prediction) & set(reference))
    return T_ij


def Sep_ij(Ts,i,j,reference_complex,predicted_complex):
    top = Ts*Ts
    T_nj = 0.0
    for id in reference_complex:
        predicted_complex1 = predicted_complex[j]
        T = T_ij(predicted_complex1,reference_complex[id])
        T_nj = T_nj + T
    T_im =0.0
    for it in predicted_complex:
        reference_complex1 = reference_complex[i]
        T1 = T_ij(reference_complex1,predicted_complex[it])
        T_im = T_im + T1
    down = T_nj*T_im
    return  top/ down
###########################################################################
def Sep_g(reference_complexes,predicted_complexes):
    Sep_g = 0.0
    sep_sum =0.0
    for i_n in reference_complexes:
        for j_m in predicted_complexes:
            Ts = T_ij(predicted_complexes[j_m],reference_complexes[i_n])
            if Ts == 0:
                Sep_ijs = 0.0
            else:
                Sep_ijs = Sep_ij(Ts,i_n,j_m,reference_complexes,predicted_complexes)
            sep_sum = sep_sum + Sep_ijs
    Sep_g = sep_sum / len(reference_complexes)
    return Sep_g

def Sep_p(reference_complexes,predicted_complexes):
    Sep_p = 0.0
    sep_sum =0.0
    for j_m in predicted_complexes:
        for i_n in reference_complexes:
            Ts = T_ij(predicted_complexes[j_m],reference_complexes[i_n])
            if Ts == 0:
                Sep_ijs = 0.0
            else:
                Sep_ijs = Sep_ij(Ts,i_n,j_m,reference_complexes,predicted_complexes)
            sep_sum = sep_sum + Sep_ijs
    Sep_p = sep_sum / len(predicted_complexes)
    return Sep_p

def Sep(Sep_g,Sep_p):
    sep = Sep_g * Sep_p
    return math.sqrt(sep)

def matching_score(set1, set2):
    """Calculates the matching score between two sets (e.g., a cluster and a complex)
    using the approach of Bader et al, 2001"""
    return len(set1.intersection(set2))**2 / (float(len(set1)) * len(set2))

def accuracy(reference, predicted):
    return (clusteringwise_sensitivity(reference, predicted) * \
            positive_predictive_value(reference, predicted)) ** 0.5

def clusteringwise_sensitivity(reference, predicted):
    num, den = 0., 0.
    for complex in reference:
        den += len(complex)
        num += max(len(complex.intersection(cluster)) for cluster in predicted)
    if den == 0.:
        return 0.
    return num / den

def clusteringwise_separation(reference, predicted):
    intersections = {}
    marginal_sums = [0.] * len(predicted), [0.] * len(reference)
    for i, cluster in enumerate(predicted):
        for j, complex in enumerate(reference):
            isect = len(cluster.intersection(complex))
            if isect > 0:
                intersections[i, j] = isect
            marginal_sums[0][i] += isect
            marginal_sums[1][j] += isect

    separations_complex = [0.] * len(reference)
    separations_cluster = [0.] * len(predicted)
    for i, cluster in enumerate(predicted):
        s = marginal_sums[0][i]
        for j, complex in enumerate(reference):
            isect = intersections.get((i, j), 0)
            if isect == 0:
                continue
            val = float(isect * isect) / (s * marginal_sums[1][j])
            separations_complex[j] += val
            separations_cluster[i] += val

    avg_sep_complex = sum(separations_complex) / len(separations_complex)
    avg_sep_cluster = sum(separations_cluster) / len(separations_cluster)
    return (avg_sep_complex * avg_sep_cluster) ** 0.5

def fraction_matched(reference,predicted,score_threshold=0.20):
    result = 0
    for id1, c1 in enumerate(reference):
        for id2, c2 in enumerate(predicted):
            score = matching_score(c1, c2)
            if score > score_threshold:
                result += 1
                break
    return result / len(reference)

def maximum_matching_ratio(reference, predicted, score_threshold=0.25):
    scores = {}
    n = len(reference)
    for id1, c1 in enumerate(reference):
        for id2, c2 in enumerate(predicted):
            score = matching_score(c1, c2)
            if score <= score_threshold:
                continue
            scores[id1, id2+n] = score
    input = [(v1, v2, w) for (v1, v2), w in scores.items()]
    mates = maxWeightMatching(input)
    score = sum(scores[i, mate] for i, mate in enumerate(mates) if i < mate)
    return score / n

def positive_predictive_value(reference, predicted):
    num, den = 0., 0.
    for cluster in predicted:
        isects = [len(cluster.intersection(complex)) for complex in reference]
        isects.append(0.)
        num += max(isects)
        den += sum(isects)
    if den == 0.:
        return 0.
    return num / den

def Jaccard_index(a,b):
    set_a = set(a)
    set_b = set(b)
    comm = float(len(set_a & set_b))
    union = float(len(set_a | set_b))
    return comm / union

def Complex_wise_Jaccard_index(reference,predicted):
    top_score = 0.0
    down_score = 0.0
    for id in reference:
        w = 0.0
        Max_Jaccard_score = 0.0
        for it in predicted:
            w = Jaccard_index(reference[id],predicted[it])
            if w > Max_Jaccard_score:
                Max_Jaccard_score = w
            else:
                continue
        top_score = top_score + Max_Jaccard_score * len(reference[id])
        down_score = down_score +len(reference[id])
    return top_score/down_score

def Cluster_wise_Jaccard_index(reference,predicted):
    top_score = 0.0
    down_score = 0.0
    for id in predicted:
        w = 0.0
        Max_Jaccard_score = 0.0
        for it in reference:
            w = Jaccard_index(reference[it],predicted[id])
            if w > Max_Jaccard_score:
                Max_Jaccard_score = w
            else:
                continue
        top_score = top_score + Max_Jaccard_score * len(predicted[id])
        down_score = down_score + len(predicted[id])
    return top_score/down_score

def Jaccard_Fmeasure(reference_complexes1,predicted_complexes1):
    Complex_wise_Jaccard_indexs = Complex_wise_Jaccard_index(reference_complexes1,predicted_complexes1)
    Cluster_wise_Jaccard_indexs = Cluster_wise_Jaccard_index(reference_complexes1,predicted_complexes1)
    Jaccard_Fmeasures = (2*Complex_wise_Jaccard_indexs*Cluster_wise_Jaccard_indexs) / (Cluster_wise_Jaccard_indexs + Complex_wise_Jaccard_indexs)
    return Jaccard_Fmeasures,Complex_wise_Jaccard_indexs,Cluster_wise_Jaccard_indexs

def Common_proteins(a,b):
    set_a = set(a)
    set_b = set(b)
    comm = float(len(set_a & set_b))
    return comm

def complex_wise_homogeneity(reference,predicted):
    HM = 0.0
    Sum_n = {}
    for ir in reference:
        sum_ir = 0.0
        for ip in predicted:
            sum_ir = sum_ir + Common_proteins(reference[ir],predicted[ip])
        Sum_n[ir] = sum_ir
    Sum_m = {}
    for ip1 in predicted:
        sum_ip = 0.0
        for ir1 in reference:
            sum_ip = sum_ip + Common_proteins(reference[ir1], predicted[ip1])
        Sum_m[ip1] = sum_ip
    sum_reference = 0.0
    for i in reference:
        sum = 0.0
        for j in predicted:
            w = Common_proteins(reference[i],predicted[j])
            #print Sum_m[j],Sum_n[i]
            sum = sum + (w / Sum_n[i]) * (w / Sum_m[j])
        sum_reference = sum + sum_reference
    HM = sum_reference/len(reference)
    return HM

def clustering_wise_homogeneity(reference,predicted):
    HC = 0.0
    Sum_n = {}
    for ir in reference:
        sum_ir = 0.0
        for ip in predicted:
            sum_ir = sum_ir + Common_proteins(reference[ir],predicted[ip])
        Sum_n[ir] = sum_ir
    Sum_m = {}
    for ip1 in predicted:
        sum_ip = 0.0
        for ir1 in reference:
            sum_ip = sum_ip + Common_proteins(reference[ir1], predicted[ip1])
        Sum_m[ip1] = sum_ip
    sum_reference = 0.0
    for i in predicted:
        sum = 0.0
        for j in reference:
            w = Common_proteins(reference[j],predicted[i])
            sum = sum + (w / Sum_n[j]) * (w / Sum_m[i])
        sum_reference = sum + sum_reference
    HC = sum_reference/len(predicted)
    return HC

def HG(reference_complexes1,predicted_complexes1):
    complex_wise_homogeneitys = complex_wise_homogeneity(reference_complexes1,predicted_complexes1)
    #print "recall=",recall
    clustering_wise_homogeneitys = clustering_wise_homogeneity(reference_complexes1,predicted_complexes1)
    #print "precision=",precision
    HGs = (2*complex_wise_homogeneitys*clustering_wise_homogeneitys) / (clustering_wise_homogeneitys + complex_wise_homogeneitys)
    #print "F-measure=",f_measure
    return HGs,complex_wise_homogeneitys,clustering_wise_homogeneitys

def canonical_protein_name(name):
    """Returns the canonical name of a protein by performing a few simple
    transformations on the name."""
    return name.strip().upper()

def is_numeric(x):
    """Returns whether the given string can be interpreted as a number."""
    try:
        float(x)
        return True
    except:
        return False

def read_complexes(fname, known_proteins=None, strictness=0.5,min_size=3, max_size=1000):
        result = []
        for line in open(fname):
            ps = set(canonical_protein_name(x) for x in line.strip().split() if x)
            if known_proteins is not None:
                isect = ps.intersection(known_proteins)
                if len(isect) < max(min_size, len(ps) * strictness):
                    continue
                if len(isect) > max_size:
                    continue
                ps = isect
            result.append(ps)

        to_delete = set()
        for idx, cluster in enumerate(result):
            for idx2, cluster2 in enumerate(result):
                if idx == idx2 or idx2 in to_delete:
                    continue
                if cluster == cluster2:
                    to_delete.add(idx2)

        result = [r for i, r in enumerate(result) if i not in to_delete]
        return result

def read_network(fname):
        known_proteins = set()
        for line in open(fname):
            parts = [canonical_protein_name(part) for part in line.strip().split()
                    if not is_numeric(part)]
            known_proteins.update(parts)
        return known_proteins

def justcount(one_data):
    del_just = False
    count = 0.0
    for i in one_data:
        # print "id[i]=",id[i]
        if one_data[i] == 0.0:
            count = count + 1
    # print count,len(id)
    if count / len(one_data) >= 0.8:
        del_just = True
    return del_just

def read_complexesp(fname):
        result = []
        for line in open(fname):
            line_1 = line.split()
            complexes = set(line_1[1:])
            #print("line=",complexes)
            result.append(complexes)

        to_delete = set()
        for idx, cluster in enumerate(result):
            for idx2, cluster2 in enumerate(result):
                if idx == idx2 or idx2 in to_delete:
                    continue
                if cluster == cluster2:
                    to_delete.add(idx2)

        result = [r for i, r in enumerate(result) if i not in to_delete]
        return result

def read_complexesp1(fname):
        result = []
        for id in fname:
            cluster = fname[id]
            complexes = set(cluster)
            result.append(complexes)

        to_delete = set()
        for idx, cluster in enumerate(result):
            for idx2, cluster2 in enumerate(result):
                if idx == idx2 or idx2 in to_delete:
                    continue
                if cluster == cluster2:
                    to_delete.add(idx2)

        result = [r for i, r in enumerate(result) if i not in to_delete]
        return result

def evaluation(fileurl,prediction,reference,output_file):
    predicted_complexes1 = prediction
    reference_complexes1 = read_complex1(reference)
    known_proteins = read_network(fileurl)
    reference_complexes_N = read_complexes(reference,known_proteins)
    predicted_complexes_N = read_complexesp1(predicted_complexes1)
    a = 0.20
    f_measure, recall, precision =F_measure(reference_complexes1, predicted_complexes1,a)
    CR = Coverage(reference_complexes1, predicted_complexes1)
    cws = clusteringwise_sensitivity(reference_complexes_N, predicted_complexes_N)
    print("cws(聚类灵敏度):",cws)
    ppv = positive_predictive_value (reference_complexes_N, predicted_complexes_N)
    acc = accuracy(reference_complexes_N, predicted_complexes_N)
    mmr = maximum_matching_ratio(reference_complexes_N, predicted_complexes_N, score_threshold=0.2)
    print("mmr(最大匹配率)：", mmr)
    sep = clusteringwise_separation(reference_complexes_N, predicted_complexes_N)
    print("sep(聚类分离度)：",sep)
    frac = fraction_matched(reference_complexes_N,predicted_complexes_N, score_threshold=0.25)
    print ("F分数;",f_measure)
    print ("acc:",acc)
    with open(output_file, 'w') as f:
        f.write("F-measure: {}\n".format(f_measure))
        f.write("MMR: {}\n".format(mmr))
        f.write("Accuracy: {}\n".format(acc))
    return (precision, recall, f_measure, mmr, acc)

def evaluation1(fileurl,prediction,reference):
    predicted_complexes1 = prediction
    reference_complexes1 = read_complex1(reference)
    known_proteins = read_network(fileurl)
    reference_complexes_N = read_complexes(reference,known_proteins)
    predicted_complexes_N = read_complexesp1(predicted_complexes1)
    a = 0.20
    f_measure, recall, precision =F_measure(reference_complexes1, predicted_complexes1,a)
    CR = Coverage(reference_complexes1, predicted_complexes1)
    print("CR(覆盖率)：",CR)
    cws = clusteringwise_sensitivity(reference_complexes_N, predicted_complexes_N)
    print("cws(聚类敏感性):", cws)
    ppv = positive_predictive_value (reference_complexes_N, predicted_complexes_N)
    print("ppv:",ppv)
    acc = accuracy(reference_complexes_N, predicted_complexes_N)
    print("acc:", acc)
    mmr = maximum_matching_ratio(reference_complexes_N, predicted_complexes_N, score_threshold=0.2)
    print("mmr:", mmr)
    sep = clusteringwise_separation(reference_complexes_N, predicted_complexes_N)
    print("sep(聚类分离度):", sep)
    frac = fraction_matched(reference_complexes_N,predicted_complexes_N, score_threshold=0.25)
    print("frac(匹配的分数):", frac)
    Jaccard_Fmeasures, Complex_wise_Jaccard_indexs, Cluster_wise_Jaccard_indexs = Jaccard_Fmeasure(reference_complexes1, predicted_complexes1)
    print("Jaccard_measures=", Jaccard_Fmeasures)
    print ("F分数;",f_measure)
    print ("acc:",acc)
    return (f_measure+ acc + mmr +frac+ Jaccard_Fmeasures)