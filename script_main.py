# 编辑时间：2023/5/12   8:30
# 编辑时间：2023/5/13   10:41
# 编辑时间：2023/5/12   14:24
# 编辑时间：2023/4/17   13:32
# 编辑时间：2023/4/15   16:29
# 编辑时间：2023/4/1   15:16
import csv
from turtle import pd

import networkx as nx
import numpy
from numpy.matlib import zeros
from scipy.sparse import csr_matrix, diags, coo_matrix
import Measure
import main6
from sklearn.cluster import KMeans
from sklearn.preprocessing import StandardScaler
from sklearn.metrics.pairwise import cosine_similarity
import numpy as np
import numpy as np
from sklearn.cluster import SpectralClustering
from collections import defaultdict
import numpy as np
from sklearn.cluster import KMeans
from sklearn.metrics import pairwise_distances
from sklearn.neighbors import kneighbors_graph
from sklearn.preprocessing import normalize, StandardScaler
import numpy as np
import pandas as pd
from scipy.sparse import csc_matrix
from scipy.sparse.linalg import expm
import networkx as nx
from sklearn.manifold import TSNE
from scipy.sparse import csc_matrix
import umap
from collections import defaultdict
from sklearn.manifold import SpectralEmbedding
from sklearn.cluster import KMeans
from sklearn.decomposition import PCA
from scipy.sparse import  csc_matrix
import scipy.sparse as sp
from scipy.linalg import expm
import copy
from sklearn.metrics.pairwise import cosine_similarity

def Read_interactionfile(filename):
    relations = defaultdict(list)
    label_id = {}
    id_label = {}
    total = 0
    read_point = open(filename, "r");
    for line in read_point.readlines():
        line_interaction = line.strip().split()
        start_name = line_interaction[0].strip();
        # print "start_name =",start_name
        end_name = line_interaction[1].strip();
        # print "end_name =",end_name
        # weightid = line_interaction[2].strip();
        if start_name not in label_id:
            label_id[start_name] = len(label_id);
            id_label[len(id_label)] = start_name
        if end_name not in label_id:
            label_id[end_name] = len(label_id);
            id_label[len(id_label)] = end_name
        if ((not label_id[start_name] in relations[label_id[end_name]]) and start_name != end_name):
            total = total + 1
            relations[label_id[end_name]].append(label_id[start_name]);
            relations[label_id[start_name]].append(label_id[end_name]);
    print("Total number of interactions(duplications are removed):", total)
    print("Total number of proteins:", len(label_id))

    N = len(label_id)
    weight = zeros((N, N))
    num = 1
    read_point = open(filename, "r");
    for line in read_point.readlines():
        line_interaction = line.strip().split()
        start_name = line_interaction[0].strip();
        end_name = line_interaction[1].strip();
        weightid2 = line_interaction[2].strip();
        weightid3 = line_interaction[3].strip();
        weightid4 = line_interaction[4].strip();
        weightid = (float(weightid2)+float(weightid3)+float(weightid4))/3
        #print "start_name,end_name,weight =", start_name,end_name,weightid,num
        num = num + 1
        weight[label_id[start_name], label_id[end_name]] = weightid
        weight[label_id[end_name], label_id[start_name]] = weightid
    return relations, label_id, id_label, weight


def GO_slims(GO_url):
    GOlists = []
    relationsGO = defaultdict(list)
    label_id = {}
    id_label = {}
    read_point = open(GO_url, "r");
    for line in read_point.readlines():
        line_interaction = line.split()
        # print("line_interaction =",line_interaction)
        name1 = line_interaction[0]
        go_exact = line_interaction[2]
        # print("name=", name1,go_exact)
        if go_exact not in GOlists:
            GOlists.append(go_exact)
        if name1 not in label_id:
            label_id[name1] = len(label_id)
            id_label[len(label_id)] = name1
            if go_exact not in relationsGO[name1] and go_exact != '':
                relationsGO[name1].append(go_exact)
        else:
            # id = label_id[name1]
            if go_exact not in relationsGO[name1] and go_exact != '':
                relationsGO[name1].append(go_exact)
    #print("relationsGO=",relationsGO)
    return relationsGO

def Read_subcellularlocalization(filename):
  #print "you are reading interaction file!"
  relationsGO = defaultdict(list)
  relationsSL = defaultdict (list)
  label_id = {}
  id_label = {}
  fes = []
  read_point = open (filename, "r");
  for line in read_point.readlines():
      #line_interaction = string.split(line, "\t")
      line_interaction = line.split()
      #print("line_interaction =", line_interaction)
      name1 = line_interaction[0]
      name3 = line_interaction[2]
      name4 = line_interaction[3]
      #print "name1=",name1
      #print "name3=", name3
      #print "name4=", name4
      if name4 not in fes:
          fes.append(name4)
      if name1 not in label_id:
          label_id[name1] = len(label_id)
          id_label[len(label_id)] = name1
          if name3 not in relationsGO[len(label_id)]:
             relationsGO[len(label_id)].append(name3)
          if name4 not in relationsSL[len(label_id)]:
             relationsSL[len(label_id)].append(name4)
      else:
          id = label_id[name1]
          if name3 not in relationsGO[id]:
             relationsGO[id].append(name3)
          if name4 not in relationsSL[id]:
             relationsSL[id].append(name4)
  return label_id,id_label,relationsGO,relationsSL

def subcellular_localization(filesl, id_label_ppi):
    N = len(id_label_ppi)
    label_id, id_label, relationsGO, relationsSL = Read_subcellularlocalization(filesl)
    relationsGO1 = defaultdict(list)
    id_ppi = {}
    for id in id_label_ppi:
        if id_label_ppi[id] in label_id:
            id_ppi[id] = label_id[id_label_ppi[id]]
            relationsGO1[id] = relationsGO[label_id[id_label_ppi[id]]]
    return relationsGO1

def Read_genefile(filename):
    gene_time = defaultdict(list)
    read_point = open(filename,"r");
    for line in read_point.readlines():
        line_interaction = line.split()
        name = line_interaction[0]
        time_value = line_interaction[1:]
        gene_time[name] = time_value
    for index in gene_time:
        time_list = []
        str_float = gene_time[index]
        for id in str_float:
            id = float(id)
            time_list.append(id)
        gene_time[index] = time_list
    return gene_time
# ****************************************************************

def name_to_id(lable_id,gene_times):
    gene = defaultdict(list)
    for id in lable_id:
        if id in gene_times:
            gene[lable_id[id]] = gene_times[id]
        else:
            continue
    return gene
# ****************************************************************

def gene_expression_weight(label_id, GE_url):
    gene_time = Read_genefile(GE_url)
    gene_time = name_to_id(label_id,gene_time)
    return gene_time

####
##利用随机游走提取特征

def generate_node_embeddings1(G, seed=None, num_walks=10, walk_length=80, embedding_method='spectral', embedding_dim=128):
    num_nodes = len(G.nodes())

    # 使用随机游走提取节点特征
    walks = []
    for i in range(num_walks):
        nodes = list(G.nodes())
        np.random.shuffle(nodes)
        for node in nodes:
            walk = [node]
            for j in range(walk_length - 1):
                neighbors = list(G.neighbors(walk[-1]))
                if len(neighbors) == 0:
                    break
                # 使用二阶随机游走
                if np.random.rand() < 0.5 and len(walk) > 1:
                    walk.append(walk[-2])
                else:
                    next_node = np.random.choice(neighbors)
                    walk.append(next_node)
            walks.append(walk)

    # 构建节点邻接矩阵
    A = nx.to_numpy_array(G)

    # 节点嵌入
    if embedding_method == 'spectral':
        se = SpectralEmbedding(n_components=embedding_dim)
        node_embeddings = se.fit_transform(A)
    elif embedding_method == 'tsne':
        tsne = TSNE(n_components=embedding_dim)
        node_embeddings = tsne.fit_transform(A)
    elif embedding_method == 'umap':
        um = umap.UMAP(n_components=embedding_dim)
        node_embeddings = um.fit_transform(A)

    node_idx_map = {n: i for i, n in enumerate(G.nodes())}

    # 构建节点特征矩阵
    features = np.zeros((len(G.nodes()), num_walks * len(G.nodes())))
    # 将特征矩阵的值设置为每个节点被遍历的次数
    for i, walk in enumerate(walks):
        for node in walk:
            if node in node_idx_map:
                features[node_idx_map[node], i] += 1

    # 添加种子节点的评分特征
    if seed is not None:
        for node, score in seed:
            if node in node_idx_map:
                features[node_idx_map[node], :] += score

    # 对特征矩阵进行归一化
    features = features / np.linalg.norm(features, axis=1, keepdims=True)

    # 对节点嵌入进行归一化
    node_embeddings = node_embeddings / np.linalg.norm(node_embeddings, axis=1, keepdims=True)

    # 将特征矩阵和节点嵌入进行拼接
    node_features = np.concatenate((node_embeddings, features), axis=1)

    return node_features

##输出为蛋白质
def improved_spectral_clustering(data, n_clusters,id_label):
    # 计算相似度矩阵
    similarity_matrix = cosine_similarity(data)

    # 进行PCA降维操作
    pca = PCA(n_components=2)
    data = pca.fit_transform(data)

    # 进行谱聚类
    eigenvalues, eigenvectors = np.linalg.eig(similarity_matrix)
    indices = eigenvalues.argsort()[::-1]
    k_smallest_eigenvectors = eigenvectors[:, indices[:n_clusters]]
    k_means = KMeans(n_clusters=n_clusters)
    k_smallest_eigenvectors = np.real(k_smallest_eigenvectors)  # 将特征向量中的复数元素去除
    k_means.fit(k_smallest_eigenvectors)

    # 获取聚类结果
    labels = k_means.labels_
    clusters = {}
    for i in range(len(labels)):
        if labels[i] not in clusters:
            clusters[labels[i]] = []
        clusters[labels[i]].append(i)

    # 将节点ID转换为蛋白质名称
    protein_clusters = {}
    for cluster, nodes in clusters.items():
        protein_names = [id_label[protein_id] for protein_id in nodes]
        protein_clusters["Cluster {} ({} nodes)".format(cluster, len(nodes))] = protein_names

    return protein_clusters


##k++
def improved_spectral_clustering1(data, n_clusters, id_label):
    scaler = StandardScaler()
    data = scaler.fit_transform(data)

    # 计算相似度矩阵
    similarity_matrix = cosine_similarity(data)

    # 进行谱聚类
    eigenvalues, eigenvectors = np.linalg.eig(similarity_matrix)
    indices = eigenvalues.argsort()[::-1]
    k_smallest_eigenvectors = eigenvectors[:, indices[:n_clusters]]
    kmeans = KMeans(n_clusters=n_clusters, init='k-means++')
    k_smallest_eigenvectors = np.real(k_smallest_eigenvectors)  # 将特征向量中的复数元素去除
    kmeans.fit(k_smallest_eigenvectors)

    # 获取聚类结果
    labels = kmeans.labels_
    clusters = {}
    for i in range(len(labels)):
        if labels[i] not in clusters:
            clusters[labels[i]] = []
        clusters[labels[i]].append(i)

    print(clusters)
    return clusters


def Filteringcomplexes(Proteincomplexes,id_label,relationsGO):
    i = 0
    Finallycomplexes = defaultdict(list)
    for id in Proteincomplexes:
        leftcluster = []
        GOlist = []
        clusterid = Proteincomplexes[id]
        for it in clusterid:
            name = id_label[it]
            GOlists_name = relationsGO[name]
            GOlist = GOlist + GOlists_name
        #print("GOlist=",GOlist)
        GOlist1 = copy.deepcopy(GOlist)

        GOtermscount = {}
        for io in GOlist1:
            GOtermscount[io] = GOlist.count(io)
        if len(GOtermscount) == 0:
            leftcluster = clusterid
        else:
            maximum = max(GOtermscount, key=GOtermscount.get)
            #print("maximum =", maximum)
            for it in clusterid:
                name = id_label[it]
                GOlists_name = relationsGO[name]
                if maximum in GOlists_name:
                    leftcluster.append(it)
        #print "leftcluster=",leftcluster
        if len(leftcluster) >= 3:
           Finallycomplexes[i] = leftcluster
           i = i + 1
    return Finallycomplexes

if __name__ == '__main__':
    #dataset = 'CollinsW'
    dataset = 'GavinW'
    # print "***************************************************************"
    print (" runing " + dataset + "!")
    lists = '.\datasets/'
    filename = lists + dataset + '.txt'
    print('filename:',filename,"\n")
    relations, label_id, id_label,weight = Read_interactionfile(filename)
    #print('relations:',relations,'\n','label_id:',label_id,'\n','id_label:',id_label,'\n','weight:',weight,'\n')
    #print('relations:', relations)
    print("1***************************************************************")
    GO_url = '.\datasets/Go_slim_mapping1.txt'
    relationsGO = GO_slims(GO_url)
    # print("relationsGO=",relationsGO)
    print("2***************************************************************")
    SL_url = lists + 'Subcellular_localization.txt'
    relationsSL = subcellular_localization(SL_url, id_label)
    #print("relationsSL=",relationsSL)
    print("3***************************************************************")
    GE_url = lists + 'gene_expression_data.txt'
    gene_expressionfiles = gene_expression_weight(label_id, GE_url)
    Seeds = main6.Selectingseeds(id_label, relations, weight, ratio=0.9)
    #print("Seeds:",Seeds)

###############
    # n_clusters =170   #CollinsW
    # n_walks = 60
    # walk_length = 100
    #
    # # 构建网络
    # G = nx.read_edgelist('datasets/Collinsw_edgelist.txt')

    n_clusters =170      #GavinW
    n_walks = 30
    walk_length = 100

    # 构建网络
    G = nx.read_edgelist('datasets/GavinW_edgelist.txt')

    # 构建图
    G = nx.Graph()
    for node in id_label:
        G.add_node(node, label=id_label[node])
    for node1 in relations:
        for node2 in relations[node1]:
            if node1 < node2:
                G.add_edge(node1, node2)
    reference = 'datasets/standardcomplexes1.txt'
    walk = generate_node_embeddings1(G, Seeds, num_walks=n_walks, walk_length=walk_length,embedding_method='spectral', embedding_dim=128)
    cluster = improved_spectral_clustering1(walk, n_clusters, id_label)
    filtercluster = Filteringcomplexes(cluster, id_label, relationsGO)
    protein_clusters = {}
    for cluster, nodes in filtercluster.items():
        protein_names = [id_label[protein_id] for protein_id in nodes]
        protein_clusters["Cluster {} ({} nodes)".format(cluster, len(nodes))] = protein_names
    print(protein_clusters)
    metricsscore = Measure.evaluation1(filename,protein_clusters, reference)

    print("metricsscore =", metricsscore)