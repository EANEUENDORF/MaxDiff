
#############################################################
#############################################################
# 0. Standard project set up
### Library ###
Sys.setenv(LANG = "en")

# Define path and create library
# pathLib <- "C:/RLibrary"
pathLib <- "C:/R_2/R-3.5.1/library"
dir.create(pathLib, showWarnings = FALSE)

# Set path to library
.libPaths(pathLib)

# Load 'checkpoint' package
library(checkpoint)

# Check package versions and install them if necessary
checkpoint("2016-06-20", checkpointLocation = pathLib)

# Load packages
library(RColorBrewer)
library(xlsx)
library(RODBC)
library(sqldf)
library(dplyr)
library(data.table)
library(sas7bdat)
library(bestglm)
library(combinat)
library(glmnet)
library(stringr)
library(RCurl)
library(tidyr)
library(readxl)
library(earth)
library(DMwR)
library(rJava)
library(stringi)

### Set general options ###
options(stringsAsFactors = FALSE)
options(scipen = 30)

### Subdirectories and Paths ###

# Create subfolders in project folder
dir.create("02 R Data", showWarnings = FALSE)
dir.create("03 Output", showWarnings = FALSE)

# Define paths to store results
path0 <- paste(getwd(), sep = "/")
path1 <- paste(getwd(), "02 R Data", sep = "/")
path2 <- paste(getwd(), "03 Output", sep = "/")

### Load data ###

# Lists with filenames
filenames1 <- list.files(path1, pattern = "*.rda", full.names = TRUE, ignore.case = TRUE)
filenames2 <- list.files("P:/Consulting/7. Data/Daten R", pattern = "*.rda", full.names = TRUE, ignore.case = TRUE)

# Import .RData files
invisible(sapply(filenames1, load, .GlobalEnv))
invisible(sapply(filenames2, load, .GlobalEnv))

############################################################################################
# Import your data
############################################################################################
itData = df

# Selecting the variables containing the max-diff data, for example
z = itData[,-1:-3]
# stacking the data (one set per row)
alternativeNames = c("select relevant variable names")
nAlternatives = length(alternativeNames)
nBlocks = ncol(z) / nAlternatives
nAltsPerSet = 5
n = nrow(z)
nObservations = n * nBlocks 
itMaxDiffData = matrix(as.numeric(t(z)),ncol = nAlternatives,byrow = TRUE, dimnames = list(1:nObservations, alternativeNames))

# Counts for sample
counts = apply(itMaxDiffData, 2, mean, na.rm = TRUE)
ranks = nAlternatives + 1 - rank(counts)
cbind(Counts = counts, Ranks = ranks)

# Individual level counts
id = rep(1:n,rep(nBlocks,n))
individualCounts = aggregate(itMaxDiffData,list(id),mean, na.rm = TRUE)[,-1]
round(individualCounts[1:10,],1) #show at data for first 10 respondents

# Individual level ranks
set.seed(0) # setting the random number seed to enhance comparability
indidualCountsNoTies = individualCounts + matrix(runif(n * nAlternatives)/100000, n) #adding random numbers to break ties
ranks = nAlternatives + 1 - apply(indidualCountsNoTies,1,rank) #ranks
rankProportions = t(apply(ranks,1,table) / n * 100)
round(rankProportions,1)

# Cum sum 
rankCumProportions = t(apply(rankProportions,1,cumsum))
round(rankCumProportions,1)

# Avg rank
aveRank = rankProportions %*% (1:14)/100
cbind(aveRank, Rank = rank(aveRank))

############################################################################################
# Logit model
############################################################################################
nRows = sum(!is.na(itMaxDiffData)) * 2
longData = matrix(0, nRows,nAlternatives + 3)
counter = 0
setCounter = 0
for (rr in 1:nObservations){
   # rr=11
  nAlts = 0
  alternatives = NULL
  respondent = floor((rr-0.1)/nBlocks) + 1
  for (cc in 1:nAlternatives){
    # cc=2
    v = itMaxDiffData[rr,cc]
    if (!is.na(v)){
      nAlts = nAlts + 1
      alternatives[nAlts] = cc
      if (v == 1)
        best = cc
      if (v == -1)
        worst = cc
    }
  }
  setCounter = setCounter + 1
  for (a in 1:nAlts){
    # a=1
    counter = counter + 1
    this_a = alternatives[a]
    if (this_a == best) 
      longData[counter,3] = 1
    else if (this_a == worst)
      longData[counter + nAlts,3] = 1
    longData[counter, 1] = respondent 
    longData[counter + nAlts,1] = respondent 
    longData[counter, 2] = setCounter 
    longData[counter + nAlts, 2] = setCounter + 1
    longData[counter,3 + this_a] = 1
    longData[counter + nAlts,3 + this_a] = -1 
  }
  setCounter = setCounter + 1
  counter = counter + nAlts
}
longData[1:20,]
longData = as.data.frame(longData)
names(longData) = c("ID","Set","Choice",alternativeNames)


# Respondent-level rank-ordered logit model with ties
# Set up 
setup.flat.data = function(x, number.alternatives){
  n = nrow(x)
  number.sets = ncol(x) / number.alternatives
  data = vector("list",n)
  for (i in 1:n)
  {
    temp.respondent.data = matrix(x[i,],byrow=TRUE,ncol = number.alternatives)
    respondent.data = vector("list",number.sets)
    for (s in 1:number.sets)
      respondent.data[[s]] = as.numeric(temp.respondent.data[s,])
    data[[i]] = respondent.data
  }
  compress.data(data)}

compress.data = function(x){#Creates a vector for each set where the first entry was best and the last worst
  compress = function(x){
    x.valid = !is.na(x)
    x.position = (1:length(x))[x.valid]
    x.position[order(x[x.valid], decreasing = TRUE)]
  }
  n = length(x)
  number.sets = length(x[[1]])
  number.alternatives = length(x[[1]][[1]])
  data = vector("list",n)
  for (i in 1:n)
  {
    respondent.data = vector("list",number.sets)
    for (s in 1:number.sets)
      respondent.data[[s]] = compress(x[[i]][[s]])
    data[[i]] = respondent.data
  }
  class(data) = "maxdiffData"
  data}

d.marley = function(b,x){
  b.vector = b[x]
  k = length(b.vector)
  ediffs = exp(matrix(b.vector,k,k,byrow=FALSE) - matrix(b.vector,k,k,byrow=TRUE))
  ediffs[1,k] / (sum(ediffs) - sum(diag(ediffs)))}

d.rlogit = function(b,x){
  eb = exp(b[x])
  k = length(eb)
  d.best = eb[1]/sum(eb)
  d.not.worst = dMWNCHypergeo(c(rep(1,k-2),0), rep(1,k-1),k-2,eb[-1], precision = 1E-7)
  d.best * d.not.worst}

d.repeated.maxdiff = function(b,x, method){
  prod(as.numeric(lapply(x,b = b,switch(method,marley=d.marley, rlogit = d.rlogit))))}

ll.max.diff = function(b,x, maxdiff.method = c("marley","rlogit")[1]){
  b[b > 100] = 100
  b[b < -100] = -100
  sum(log(as.numeric(lapply(x,b = c(0,b),method=maxdiff.method, d.repeated.maxdiff))))
}

max.diff.rank.ordered.logit.with.ties = function(stacked.data){
  flat.data = setup.flat.data(stacked.data, ncol(stacked.data))
  solution = optim(seq(.01,.02, length.out = ncol(stacked.data)-1), ll.max.diff,  maxdiff.method  = "rlogit", gr = NULL, x = flat.data, method =  "BFGS", control = list(fnscale  = -1, maxit = 1000, trace = FALSE), hessian = FALSE)
  pars = c(0, solution$par)
  names(pars) = dimnames(stacked.data)[[2]]
  list(log.likelihood = solution$value, coef = pars)}


# Actual model
individualRankLogit = individualCounts
stackedID = rep(1:n,rep(nBlocks,n))
getRankCoefficients = function(id){max.diff.rank.ordered.logit.with.ties(itMaxDiffData[stackedID == id,])$coef}
nAlts  = 14
for (i in 1:n)
  tryCatch({
  individualRankLogit[i,] = getRankCoefficients(i)},  error = function(err){message(err); return(NA)} )
set.seed(0) #setting the random number seed so that random numbers are consistently applied across the examples
ranks = nAlts + 1 - t(apply(individualRankLogit+ matrix(runif(n * nAlts)/100000, n),1,rank)) #ranks
rankProportions = t(apply(t(ranks),1,table) / n * 100)
round(rankProportions,1)

# Avg rank
aveRank = rankProportions %*% (1:14)/100
# aveRank = rankProportions %*% (1:10)/100
sf <- cbind(aveRank, Rank = rank(aveRank)) %>% as.data.frame() 
MaxDiffImportanceScoreandRanks <- tibble::rownames_to_column(sf) %>% arrange(Rank)

########## Write results ##########
write.xlsx(MaxDiffImportanceScoreandRanks, paste(path2,"MaxDiffLATAMSegment1.xlsx", sep="/"))








