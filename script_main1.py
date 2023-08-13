# 编辑时间：2023/5/14   21:23
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
# ****************************************************************
# 该函数Read_subcellularlocalization接受一个文件名作为输入，并读取一个包含蛋白质亚细胞定位信息的文件。
# 它创建了两个字典relationsGO和relationsSL，分别存储每个蛋白质的基因本体论（Gene Ontology，GO）术语和亚细胞定位信息。
# 它还创建了两个字典label_id和id_label，将蛋白质名称映射到其对应的ID，反之亦然。
# 该函数读取输入文件中的每一行，并提取蛋白质名称、GO术语和亚细胞定位信息。
# 如果蛋白质名称尚未在label_id中，则将其与其相应的ID一起添加到字典中。如果GO术语或亚细胞定位信息尚未与相应字典中的蛋白质ID关联，
# 则将其添加到字典中。该函数返回label_id、id_label、relationsGO和relationsSL字典作为输出。
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
      #print "===================================="
  #print "The total number of protein is ",len(label_id)
  #print "label_id=",label_id
  #print "id_label=",id_label
  #print "len(fes)=",len(fes)
  #print "fes=",fes
  return label_id,id_label,relationsGO,relationsSL
# ****************************************************************
# subcellular_localization函数接受两个输入:filesl和id_label_ppi，并返回一个名为relationsGO1的字典。
# filesl输入表示包含蛋白质亚细胞定位信息的文件，id_label_ppi输入表示将蛋白质id映射到其相应名称的字典。
# 该函数首先在filesl上调用Read_subcellularlocalization函数，以提取每个蛋白质的亚细胞定位信息，
# 并创建字典label_id、id_label、relationsGO和relationsSL。
# 接下来，该函数创建一个空字典id_ppi，并循环id_label_ppi中的蛋白质id。对于每个ID，它检查对应的蛋白质名称是否在label_id中。
# 如果是，函数将ID映射到其在label_id中对应的ID，并将其存储在id_ppi字典中。此外，它在relationsGO1中创建一个具有相同ID的新条目，
# 并从relationsGO中添加相应的GO术语。最后，该函数返回relationsGO1字典。
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
# ****************************************************************# 这个函数Read_genefile以文件名作为输入，读取包含基因表达时间序列数据的文件。它创建了一个字典gene_time，用于存储每个基因的时间序列数据。
# 该函数读取输入文件中的每一行，并提取基因名称和时间值列表。它将基因名称和时间值添加到gene_time字典中。
# 然后，它将时间值从字符串转换为浮点数，并用新的浮点数列表替换原来的字符串列表。
# 该函数返回gene_time字典作为输出。
def Read_genefile(filename):
    gene_time = defaultdict(list)
    read_point = open(filename,"r");
    for line in read_point.readlines():
        #print(line)
        #line_interaction = string.split(line,"\t")
        line_interaction = line.split()
        #print("line_interaction =",line_interaction)
        name = line_interaction[0]
        #print "type(name)=",type(name):str
        #gene = name.split(" ")
        #print "gene=",gene
        #protein_name = gene[0]
        #print "protein_name =", protein_name
        time_value = line_interaction[1:]
        gene_time[name] = time_value
        #print("gene_time[name]=",gene_time[name])
    for index in gene_time:
        #print index
        #print (gene_time[index])
        time_list = []
        str_float = gene_time[index]
        #print("str_float=",str_float)
        #print type(str_float)
        for id in str_float:
            id = float(id)
            #value = string.atof(id)
            time_list.append(id)
        gene_time[index] = time_list
        #print ("gene_time[index]",time_list)
    #print "gene_time=",gene_time
    return gene_time
# ****************************************************************
# 函数"name_to_id"以两个字典"lable_id"和"gene_times"作为输入。“lable_id”是将蛋白质名称映射到其对应id的字典，
# “gene_times”是包含基因表达时间序列数据的字典。该函数创建一个名为“gene”的空字典。
# 它遍历“lable_id”中的每个ID，并检查对应的蛋白质名称是否在“gene_times”中。如果是，它将该蛋白质的时间序列数据添加到相应ID下的“基因”字典中。
# 如果不是，则继续到下一个ID。最后，该函数返回包含每个蛋白质ID的基因表达时间序列数据的“基因”字典。
def name_to_id(lable_id,gene_times):
    gene = defaultdict(list)
    for id in lable_id:
        if id in gene_times:
            gene[lable_id[id]] = gene_times[id]
        else:
            continue
    return gene
# ****************************************************************
# 这个函数gene_expression_weight接受两个输入:label_id和GE_url。label_id是将蛋白质名称映射到其对应id的字典，
# 而GE_url是包含基因表达数据的URL或本地文件路径。该函数使用Read_genefile函数从输入文件中读取基因表达数据，
# 然后使用name_to_id函数将蛋白质id映射到其相应的基因表达数据。生成的字典将蛋白质id映射到随时间变化的相应基因表达值。
# 该函数以字典的形式返回基因表达数据。
def gene_expression_weight(label_id, GE_url):
    #fileg = 'C:\Users\Wang-PC\Desktop\MCGEDP\gene_coexpress_data.txt'
    gene_time = Read_genefile(GE_url)
    # print "len(gene_time)=", len(gene_time)
    gene_time = name_to_id(label_id,gene_time)
    return gene_time

####
##利用随机游走提取特征

def generate_node_embeddings(G, seed=None, num_walks=20, walk_length=80, embedding_method='spectral',embedding_dim=128):
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
                next_node = np.random.choice(neighbors)
                walk.append(next_node)
            walks.append(walk)

    # 构建节点邻接矩阵
        A = nx.convert_matrix.to_numpy_array(G)
        #print("A2:", A)
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

    features = np.zeros((len(G.nodes()), num_walks*len(G.nodes())))
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

    features = features / np.linalg.norm(features, axis=1, keepdims=True)
    node_embeddings = node_embeddings / np.linalg.norm(node_embeddings, axis=1, keepdims=True)

    return node_embeddings

##改进
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


##原始随机游走提取特征矩阵
def random_walk_feature(G, num_walks=10, walk_length=5, n=10):
    """
    对PPI网络进行随机游走特征提取

    参数：
    G: networkx图对象，表示PPI网络
    num_walks: 随机游走次数
    walk_length: 每次随机游走
    返回值：
    features: numpy数组，表示每个节点的特征向量
    """
    # 进行随机游走
    walks = []
    for i in range(num_walks):
     for node in G.nodes():
        walk = [node]
        for j in range(walk_length):
            neighbors = list(G.neighbors(walk[-1]))
            if len(neighbors) > 0:
                next_node = np.random.choice(neighbors)
                walk.append(next_node)
            else:
                break
        walks.append(walk)

     # 统计节点的特征向量
     node2id = {node: i for i, node in enumerate(G.nodes())}
     n = len(G.nodes())
     features = np.zeros((n, n))
     for walk in walks:
       for i, node in enumerate(walk):
         if i < n:
            features[node2id[node], node2id[walk[i]]] += 1

    return features


####kmeans
def kmeans_clustering(data, n_clusters, id_label):
    # 数据标准化
    scaler = StandardScaler()
    data = scaler.fit_transform(data)

    # 计算相似度矩阵
    similarity_matrix = cosine_similarity(data)

    # 进行 K-Means 聚类
    k_means = KMeans(n_clusters=n_clusters)
    k_means.fit(similarity_matrix)

    # 获取聚类结果
    labels = k_means.labels_
    clusters = {}
    for i in range(len(labels)):
        if labels[i] not in clusters:
            clusters[labels[i]] = []
        clusters[labels[i]].append(i)
    return clusters


##层次
from scipy.cluster import hierarchy
from scipy.spatial.distance import pdist

def hierarchical_clustering(data, n_clusters):
    # 计算距离矩阵
    dist_matrix = pdist(data, metric='euclidean')

    # 构建层次聚类树
    linkage_matrix = hierarchy.linkage(dist_matrix, method='ward')

    # 切割聚类树
    labels = hierarchy.cut_tree(linkage_matrix, n_clusters=n_clusters).flatten()

    # 获取聚类结果
    clusters = {}
    for i in range(len(labels)):
        if labels[i] not in clusters:
            clusters[labels[i]] = []
        clusters[labels[i]].append(i)
    return clusters



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

# ##输出为ID结果，不是蛋白质名称
# def improved_spectral_clustering1(data, n_clusters,id_label):
#     scaler = StandardScaler()
#     data = scaler.fit_transform(data)
#
#
#     # 计算相似度矩阵
#     similarity_matrix = cosine_similarity(data)
#
#     # 进行谱聚类
#     eigenvalues, eigenvectors = np.linalg.eig(similarity_matrix)
#     indices = eigenvalues.argsort()[::-1]
#     k_smallest_eigenvectors = eigenvectors[:, indices[:n_clusters]]
#     k_means = KMeans(n_clusters=n_clusters)
#     k_smallest_eigenvectors = np.real(k_smallest_eigenvectors)  # 将特征向量中的复数元素去除
#     k_means.fit(k_smallest_eigenvectors)
#
#     # 获取聚类结果
#     labels = k_means.labels_
#     clusters = {}
#     for i in range(len(labels)):
#         if labels[i] not in clusters:
#             clusters[labels[i]] = []
#         clusters[labels[i]].append(i)
#
#     print(clusters)
#     return clusters

from sklearn.cluster import KMeans
from sklearn.preprocessing import StandardScaler
from sklearn.metrics.pairwise import cosine_similarity
import numpy as np
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
            #print("GOtermscount[io] =",GOtermscount[io])
        #print(" GOtermscount=", GOtermscount)
        #d2 = sorted(GOtermscount.items(), key=lambda GOtermscount: GOtermscount[1], reverse=True)
        #print("GOtermscount=", len(GOtermscount), GOtermscount)
        #print("type(maximum)=", type(maximum))
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
    dataset = 'CollinsW'
    #dataset = 'GavinW'
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
    n_clusters =370   #CollinsW
    n_walks = 60
    walk_length = 100

    # 构建网络
    G = nx.read_edgelist('datasets/Collinsw_edgelist.txt')

    # n_clusters =170      #GavinW
    # n_walks = 30
    # walk_length = 100
    #
    # # 构建网络
    # G = nx.read_edgelist('datasets/GavinW_edgelist.txt')

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
    # ##原始随机游走
    # walk = random_walk_feature(G, num_walks=n_walks, walk_length=walk_length,n=100)
    # print(walk)
    ###kmeans
    #cluster = kmeans_clustering(walk, n_clusters, id_label)
    ##层次
    #cluster = hierarchical_clustering(walk, n_clusters)
    ##谱聚类
    cluster = improved_spectral_clustering1(walk, n_clusters, id_label)
    filtercluster = Filteringcomplexes(cluster, id_label, relationsGO)
    protein_clusters = {}
    for cluster, nodes in filtercluster.items():
        protein_names = [id_label[protein_id] for protein_id in nodes]
        protein_clusters["Cluster {} ({} nodes)".format(cluster, len(nodes))] = protein_names
    print(protein_clusters)
    metricsscore = Measure.evaluation1(filename,protein_clusters, reference)

    print("metricsscore =", metricsscore)