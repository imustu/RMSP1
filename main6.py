# 编辑时间：2023/3/28   16:35
# 编辑时间：2023/3/23   9:48
import time
from collections import defaultdict

import networkx as nx
from numpy.matlib import zeros
import math
import random
import string
import numpy as np
import copy

from sklearn.cluster import SpectralClustering


def multipl(a,b):
    sumofab=0.0
    for i in range(len(a)):
        temp=a[i]*b[i]
        sumofab+=temp
    return sumofab

def protein_protein_PCC(node1, node2):
    timenode1 = np.array(node1)
    # print "timenode1 =",timenode1
    timenode2 = np.array(node2)
    # print "timenode2 =", timenode2
    n = len(timenode1)
    sumnode1 = sum(timenode1)
    sumnode2 = sum(timenode2)
    sumofxy = multipl(timenode1,timenode2)
    sumofx2 = sum([pow(i,2) for i in timenode1])
    sumofy2 = sum([pow(j,2) for j in timenode2])
    num = sumofxy-(float(sumnode1)*float(sumnode2)/n)
    corrcoef = math.sqrt((sumofx2-float(sumnode1**2)/n)*(sumofy2-float(sumnode2**2)/n))
    pcc = float(num)/corrcoef
    pcc = float(pcc + 1.0) / 2
    # print("pcc:",pcc)
    return pcc
    # print "graph=",graph
    sum_weight = 0.0
    if len(graph) >= 2:
        for id in graph:
            neighbors = relations[id]
            for it in neighbors:
                # print "id,it=",id,it
                if it > id and it in graph:
                    sum_weight = sum_weight + weights[id, it]
        density = 2 * sum_weight * math.sqrt(len(graph)) / (len(graph) * (len(graph) - 1))
    else:
        density = 0.0
    return density
# ****************************************************************

def density(graph, relations, weights):
    # print "graph=",graph
    sum_weight = 0.0
    if len(graph) >= 2:
        for id in graph:
            neighbors = relations[id]
            for it in neighbors:
                # print "id,it=",id,it
                if it > id and it in graph:
                    sum_weight = sum_weight + weights[id, it]
        density = 2 * sum_weight / (len(graph) * (len(graph) - 1))
    else:
        density = 0.0
    return density
# ****************************************************************
def Cohesiveness(graph, weights, relations):
    sum_weight = 0.0
    node_dict = {}
    k = 1
    for id in graph:
        node_dict[k] = id
        k = k + 1
    for it in node_dict:
        for ih in node_dict:
            if ih > it and weights[node_dict[it], node_dict[ih]] > 0.0:
                sum_weight = sum_weight + weights[node_dict[it], node_dict[ih]]
    sum_out_weight = 0.0
    for id1 in node_dict:
        neighbors = relations[node_dict[id1]]
        for iw in neighbors:
            if iw not in graph:
                sum_out_weight = sum_out_weight + weights[node_dict[id1], iw]
    modularitys = 0.0
    if (sum_weight + sum_out_weight) == 0.0 or len(graph) <= 2:
        modularitys = 0.0
    else:
        weightin = sum_weight
        weightout = sum_out_weight
        modularitys = weightin / (weightin + weightout)
    return modularitys
# ****************************************************************

def modularity(graph, relations, weight):
    sum_weight = 0.0
    node_dict = {}
    k = 1
    for id in graph:
        node_dict[k] = id
        k = k + 1
    for it in node_dict:
        for ih in node_dict:
            if ih <= it:
                continue
            else:
                if weight[node_dict[it], node_dict[ih]] > 0.0:
                    sum_weight = sum_weight + weight[node_dict[it], node_dict[ih]]
    sum_out_weight = 0.0
    neighbors_nodes = []
    for id1 in node_dict:
        neighbors = relations[node_dict[id1]]
        for iw in neighbors:
            if iw not in graph:
                sum_out_weight = sum_out_weight + weight[node_dict[id1], iw]
                if iw not in neighbors_nodes:
                   neighbors_nodes.append(iw)
            else:
                continue
    modularitys = 0.0
    if len(neighbors_nodes) < 1 or len(graph) <= 2:
        modularitys = 0.0
    else:
        avgdensity = 2 * sum_weight / len(graph)
        avg_out_weight = sum_out_weight / len(neighbors_nodes)
        modularitys = avgdensity / (avgdensity + avg_out_weight)
    return modularitys
# ****************************************************************
def densitymodularitys(graph, relations, weight):
    sum_weight = 0.0
    node_dict = {}
    k = 1
    for id in graph:
        node_dict[k] = id
        k = k + 1
    for it in node_dict:
        for ih in node_dict:
            if ih > it and weight[node_dict[it], node_dict[ih]] > 0.0:
               sum_weight = sum_weight + weight[node_dict[it], node_dict[ih]]
    sum_out_weight = 0.0
    neighbors_nodes = []
    for id1 in node_dict:
        neighbors = relations[node_dict[id1]]
        for iw in neighbors:
            if iw not in graph:
                sum_out_weight = sum_out_weight + weight[node_dict[id1], iw]
                if iw not in neighbors_nodes:
                   neighbors_nodes.append(iw)

    if len(neighbors_nodes) < 1 or len(graph) <= 2:
        modularitys = 0.0
    else:
        modularitys = (2 * sum_weight-sum_out_weight) / len(graph)
    return modularitys
# ****************************************************************
def AWM(graph,relations,weight):
    if len(graph) >= 2:
        weight_in = 0.0
        weight_out = 0.0
        edge_in = 0.0
        edge_out = 0.0
        for id in graph:
            neighbor = relations[id]
            inner_sum_weighted = 0.0
            outer_sum_weighted = 0.0
            for it in neighbor:
                if it in graph and it > id:
                    inner_sum_weighted = inner_sum_weighted + weight[id, it]
                    edge_in = edge_in + 1
                else:
                    outer_sum_weighted = outer_sum_weighted + weight[id, it]
                    edge_out = edge_out + 1
            weight_in = weight_in + inner_sum_weighted
            weight_out = weight_out + outer_sum_weighted
            if edge_in != 0:
               sum_up = weight_in / edge_in
            else:
               sum_up = 0.0
            if edge_out != 0:
                sum_down = weight_out / edge_out
            else:
                sum_down = 0.0
        if weight_in + weight_out > 0.0 and sum_down + sum_up > 0:
            score = sum_up / (sum_down + sum_up)
        else:
            score = 0.0
    else:
        score = 0.0
    return score
# ****************************************************************

def fitnessfunction(graph, relations, weights):
    densitys = density(graph, relations, weights)
    cohesiveness = Cohesiveness(graph, weights, relations)
    #densitymodularity = densitymodularitys(graph, relations, weights)
    #print("densitymodularity =",densitymodularity)
    AWMs = AWM(graph,relations,weights)
    #score = densitys*max(cohesiveness,AWMs)
    score = densitys+cohesiveness+AWMs
    #score = max(densitys, cohesiveness, AWMs)
    #score = cohesiveness
    return score
# ****************************************************************
def Selectingseeds(id_label, relations, weights,ratio):
    seeds = id_label.keys()
    #print("seed:", seeds)
    seedscore = {}
    for ib in seeds:
        scoreib = sqrtdensity(relations[ib] + [ib], relations, weights)
        seedscore[ib] = scoreib
    d2 = sorted(seedscore.items(), key=lambda seedscore: seedscore[1], reverse=True)
    #print("d2:",d2)
    num = ratio*len(seeds)
    Seedslist = []
    count = 0
    for ih in d2:
        count = count + 1
        if count < num:
           Seedslist.append(ih[0])

    #print("Seed:",Seedslist)
    Seedslist1 = [id_label[id] for id in Seedslist]
    #print("Seedlist1:", Seedslist1)
    #return Seedslist
    return d2

def generate_feature_matrix(G, Seeds):
    n = len(G.nodes())
    feature_matrix = np.zeros((n, len(Seeds)))
    for i, seed in enumerate(Seeds):
        p = np.zeros(n)
        p[seed] = 1
        walks = dict(nx.single_source_shortest_path(G, seed, 2))
        for node in walks:
            for w in walks[node]:
                p[w] = p[w] + 1
        p = p / p.sum()
        feature_matrix[:, i] = p
    return feature_matrix

def identify_complex(G, Seeds, n_clusters):
    feature_matrix = generate_feature_matrix(G, Seeds)
    labels = SpectralClustering(n_clusters=n_clusters, affinity='precomputed').fit_predict(feature_matrix)
    cluster_names = {}
    for i in range(n_clusters):
        nodes_in_cluster = [str(node) for node, label in zip(G.nodes(), labels) if label == i]
        #cluster_names[f'Cluster {i+1} ({len(nodes_in_cluster)} nodes)'] = nodes_in_cluster
        cluster_names[f'Cluster {i + 1} ({len(nodes_in_cluster)} nodes)'] = nodes_in_cluster
    return cluster_names
    #return nodes_in_cluster
#"------------------------------------------------------------"
# 采样邻居
def random_walk_sampling(G, seeds, p=0.5, q=0.5, r=2, num_samples=100):
    feature_matrix = []
    for seed in seeds:
        # 初始化概率分布，以种子节点为中心
        probs = dict(zip(G.nodes(), [0] * G.number_of_nodes()))
        probs[seed] = 1
        # 开始随机游走采样
        for i in range(num_samples):
            # 以当前节点为中心，随机选择下一个节点
            current_node = list(probs.keys())[list(probs.values()).index(1)]
            neighbors = list(G.neighbors(current_node))
            if len(neighbors) == 0:
                continue
            probs = dict(zip(G.nodes(), [0] * G.number_of_nodes()))
            probs[current_node] = 1 - p - q
            for neighbor in neighbors:
                if neighbor in seeds:
                    probs[neighbor] = p
                else:
                    probs[neighbor] = q
            # 保留前r步的概率分布平均值
            if i >= num_samples - r:
                if len(feature_matrix) <= i - num_samples + r:
                    feature_matrix.append(list(probs.values()))
                else:
                    feature_matrix[i - num_samples + r] = \
                        [a + b for a, b in zip(feature_matrix[i - num_samples + r], list(probs.values()))]
        # 取平均值
        feature_matrix[-1] = [v / r for v in feature_matrix[-1]]
    return np.array(feature_matrix)
