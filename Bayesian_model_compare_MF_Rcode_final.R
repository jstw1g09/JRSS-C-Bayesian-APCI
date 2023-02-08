
#Load libraries 

library(truncnorm)
library(mvtnorm)
library(smoothmest)
library(tmvtnorm)
library(demography)
library(VGAM)
library(scoringRules)

#################
##Some functions 
#################

percentile.fn<-function(x){
quantile(x,c(0.025,0.5,0.975))
}

quantile.025<-function(x) quantile(x,probs=0.025)
quantile.50<-function(x) quantile(x,probs=0.5)
quantile.975<-function(x) quantile(x,probs=0.975)

dtrunc <- function(x, spec, a = -Inf, b = Inf, ...)
{
tt <- rep(0, length(x))
g <- get(paste("d", spec, sep = ""), mode = "function")
G <- get(paste("p", spec, sep = ""), mode = "function")
tt[x>=a & x<=b] <- g(x[x>=a&x<=b], ...)/(G(b, ...) - G(a, ...))
return(tt)
}

qtrunc <- function(p, spec, a = -Inf, b = Inf, ...)
{
tt <- p
G <- get(paste("p", spec, sep = ""), mode = "function")
Gin <- get(paste("q", spec, sep = ""), mode = "function")
tt <- Gin(G(a, ...) + p*(G(b, ...) - G(a, ...)), ...)
return(tt)
}

rtrunc <- function(n, spec, a = -Inf, b = Inf, ...)
{
x <- u <- runif(n, min = 0, max = 1)
x <- qtrunc(u, spec, a = a, b = b,...)
return(x)
}

rmvnorm.tol<-function (n, mean = rep(0, nrow(sigma)), sigma = diag(length(mean)), 
    method = c("eigen", "svd", "chol"), pre0.9_9994 = FALSE) 
{
    if (!isSymmetric(sigma, tol = (1e16)*(.Machine$double.eps), 
        check.attributes = FALSE)) {
        stop("sigma must be a symmetric matrix")
    }
    if (length(mean) != nrow(sigma)) {
        stop("mean and sigma have non-conforming size")
    }
    sigma1 <- sigma
    dimnames(sigma1) <- NULL
    if (!isTRUE(all.equal(sigma1, t(sigma1)))) {
        warning("sigma is numerically not symmetric")
    }
    method <- match.arg(method)
    if (method == "eigen") {
        ev <- eigen(sigma, symmetric = TRUE)
        if (!all(ev$values >= -sqrt(.Machine$double.eps) * abs(ev$values[1]))) {
            warning("sigma is numerically not positive definite")
        }
        retval <- ev$vectors %*% diag(sqrt(ev$values), length(ev$values)) %*% 
            t(ev$vectors)
    }
    else if (method == "svd") {
        sigsvd <- svd(sigma)
        if (!all(sigsvd$d >= -sqrt(.Machine$double.eps) * abs(sigsvd$d[1]))) {
            warning("sigma is numerically not positive definite")
        }
        retval <- t(sigsvd$v %*% (t(sigsvd$u) * sqrt(sigsvd$d)))
    }
    else if (method == "chol") {
        retval <- chol(sigma, pivot = TRUE)
        o <- order(attr(retval, "pivot"))
        retval <- retval[, o]
    }
    retval <- matrix(rnorm(n * ncol(sigma)), nrow = n, byrow = !pre0.9_9994) %*% 
        retval
    retval <- sweep(retval, 2, mean, "+")
    colnames(retval) <- names(mean)
    retval
}
 
dmvnorm.tol<-function(x, mean, sigma, log = FALSE){
    if (is.vector(x)) {
        x <- matrix(x, ncol = length(x))
    }
    if (missing(mean)) {
        mean <- rep(0, length = ncol(x))
    }
    if (missing(sigma)) {
        sigma <- diag(ncol(x))
    }
    if (NCOL(x) != NCOL(sigma)) {
        stop("x and sigma have non-conforming size")
    }
    if (!isSymmetric(sigma, tol = (1e16)*sqrt(.Machine$double.eps), 
        check.attributes = FALSE)) {
        stop("sigma must be a symmetric matrix")
    }
    if (length(mean) != NROW(sigma)) {
        stop("mean and sigma have non-conforming size")
    }
    distval <- mahalanobis(x, center = mean, cov = sigma)
    logdet <- sum(log(eigen(sigma, only.values = TRUE)$values))
    logretval <- -(ncol(x) * log(2 * pi) + logdet + distval)/2
    if (log) 
        return(logretval)
    exp(logretval)
}

dmvnorm.manual<-function(x,mean.vec,sigma,log=TRUE){
p<-length(x)
chol.sigma<-chol(sigma)
#order.chol.sigma<-order(attr(chol.sigma,"pivot"))
#chol.sigma<-chol.sigma[,order.chol.sigma]
i.t.chol.sigma<-forwardsolve(t(chol.sigma),diag(rep(1,p)))
#i.t.chol.sigma<-solve(t(chol.sigma))
log.det.Jacobian.chol<-determinant(i.t.chol.sigma)$modulus
z<-i.t.chol.sigma%*%(x-mean.vec)
log.pdf.z<-sum(dnorm(z,log=TRUE))
log.pdf.x<-log.pdf.z+log.det.Jacobian.chol
if (log) return(log.pdf.x)
else return(exp(log.pdf.x))
}

rmvnorm.manual<-function(n,mean.vec,sigma){
p<-length(mean.vec)
chol.sigma<-chol(sigma)
Z<-matrix(rnorm(n*p),nrow=p,ncol=n)
M<-matrix(rep(mean.vec,n),nrow=p,ncol=n,byrow=FALSE)
t(M+t(chol.sigma)%*%Z)
}

transformation.dmvnorm<-function(x,mean.vec,rij,log.det.Jacobian){
n<-length(x)
z<-rij%*%(x-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.x<-log.pdf.z+log.det.Jacobian
log.pdf.x
}

transformation.dmvnorm.loglinear<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho,A,T){
n<-length(x)
y<-x[-(2*A+T+1)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.y<-log(dtruncnorm(x[2*A+T+1],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.y
log.pdf.x
}

transformation.dmvnorm.match.prior<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho,mean.log.epsilon,variance.log.epsilon){
y<-x[-c(244,245)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.y<-log(dtruncnorm(x[244],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.v<-log(dtruncnorm(x[245],a=log(1),b=log(50000),mean=mean.log.epsilon,sd=sqrt(variance.log.epsilon)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.y+log.pdf.v
log.pdf.x
}

transformation.dmvnorm.match.prior.2<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho){
y<-x[-c(244)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.y<-log(dtruncnorm(x[244],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.y
log.pdf.x
}

transformation.dmvnorm.loglinear.match.prior.cohort<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho){
n<-length(x)
y<-x[-c(382)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.v<-log(dtruncnorm(x[382],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.v
log.pdf.x
}

transformation.dmvnorm.loglinear.match.prior.cohort.RW<-function(x,mean.vec,rij,log.det.Jacobian){
n<-length(x)
y<-x[-c(382)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.x<-log.pdf.z+log.det.Jacobian
log.pdf.x
}

transformation.dmvnorm.match.prior.cohort.2<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho){
y<-x[-c(382)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.y<-log(dtruncnorm(x[382],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.y
log.pdf.x
}

transformation.dmvnorm.match.prior.cohort.RW<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho){
y<-x[-c(382)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.x<-log.pdf.z+log.det.Jacobian 
log.pdf.x
}

project.expectancy.fn<-function(rates,Ext,time){
rates<-matrix(rates,nrow=100,ncol=length(time),byrow=FALSE)
rates.demog<-demogdata(rates,pop=matrix(rep(Ext[,10],length(time)),nrow=100,ncol=length(time)),ages=0:99,years=time,label="EW",type="mortality",name="female")
e0(rates.demog,type="period")
} 

bridge<-function(initial,m,sample1,sample2,n1,n2,l,l.tilda){
r<-vector(length=m)
r[1]<-initial
#rand<-seq(1000,m,by=1000)
for (i in 1:m){
r[i+1]<-(1/n2*sum((l.tilda)/(n1*l.tilda+n2*r[i])))/(1/n1*sum(1/(n1*l+n2*r[i])))
#if (i %in% rand) {gc()}
}
r
}

###########
##Data
###########
EWdeath<-read.table("1x1EWdeath.txt")
EWdeath.female<-as.numeric(as.vector(EWdeath[,3]))
EWdeath.female.mat<-matrix(EWdeath.female,nrow=111)
EWdeath.female.mat.ex<-EWdeath.female.mat[(1:100),(121:162)]
EWdeath.female.vec.ex<-as.vector(EWdeath.female.mat.ex)

EWexpo<-read.table("1x1EWexposure.txt")
EWexpo.female<-as.numeric(as.vector(EWexpo[,3]))
EWexpo.female.mat<-matrix(EWexpo.female,nrow=111)
EWexpo.female.mat.ex<-EWexpo.female.mat[(1:100),(121:162)]
EWexpo.female.vec.ex<-as.vector(EWexpo.female.mat.ex)

A<-dim(EWdeath.female.mat.ex)[1];T<-dim(EWdeath.female.mat.ex)[2]

###############
##Holdout data
###############

EWdeath.validation<-read.table("1x1EWdeath_validation_correct.txt")
EWdeath.female.validation<-as.numeric(as.vector(EWdeath.validation[,3]))
EWdeath.female.mat.validation<-matrix(EWdeath.female.validation,nrow=111)
EWdeath.female.mat.ex.validation<-EWdeath.female.mat.validation[(1:100),]
EWdeath.female.mat.ex.validation<-round(EWdeath.female.mat.ex.validation)

EWexpo.validation<-read.table("1x1EWexposure_validation_correct.txt")
EWexpo.female.validation<-as.numeric(as.vector(EWexpo.validation[,3]))
EWexpo.female.mat.validation<-matrix(EWexpo.female.validation,nrow=111)
EWexpo.female.mat.ex.validation<-EWexpo.female.mat.validation[(1:100),]
EWexpo.female.mat.ex.validation<-round(EWexpo.female.mat.ex.validation)


#######################
##Implied priors on log mu_xt
#######################

##Naive prior specification

prior.logmiuxt11.ng.block.fn<-function(n,A,T,t0,lx,sigma2.l,ak,bk,a.beta,b.beta,a.epsilon,b.epsilon,gamma.0,sigma.mat.0,sigma2.rho){ 
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
I<-diag(rep(1,A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))
for (j in 1:n){
sigma2.beta<-1/rgamma(1,a.beta,b.beta)
sigma2.k<-1/rgamma(1,ak,bk)
rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
alpha<-rnorm(A,mean=lx,sd=sqrt(sigma2.l))
beta<-rmvnorm(1,mean=rep(1/A,(A-1)),sigma=(sigma2.beta*(I-1/A*K)),method="chol")
beta<-c(1-sum(beta),beta)
gamma<-rmvnorm(1,mean=gamma.0,sigma=sigma.mat.0)
gamma1<-gamma[1]
gamma2<-gamma[2]
epsilon<-rgamma(1,a.epsilon,b.epsilon) 
kappa<-rep(0,T)
for (i in 2:T){
kappa[i]<-rnorm(1,mean=(gamma1+gamma2*t[i]+rho*(kappa[i-1]-gamma1-gamma2*t[i-1])),sd=sqrt(sigma2.k))
}
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(kappa)+log(matrix(rgamma(A*T,epsilon,epsilon),nrow=A,ncol=T))
logmiuxt[j,]<-as.vector(logmiuxt.temp)
}
logmiuxt
}

prior.logmiuxt11.ng.block<-prior.logmiuxt11.ng.block.fn(n=50000,A=A,T=T,t0=-21,lx=rep(0,100),sigma2.l=100,ak=0.1,bk=0.1,a.beta=0.1,b.beta=0.1,a.epsilon=2,b.epsilon=2,gamma.0=c(0,0),sigma.mat.0=matrix(c(1000,0,0,10),nrow=2),sigma2.rho=100)

prior.logmiuxt11.ng.loglinear.block.2.fn<-function(n,A,T,t0,lx,sigma2.l,ak,bk,a.beta,b.beta,a.epsilon,b.epsilon,sigma2.rho){ 
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
for (k in 1:n){
sigma2.beta<-1/rgamma(1,a.beta,b.beta)
sigma2.k<-1/rgamma(1,ak,bk)
rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
alpha<-rnorm(A,mean=lx,sd=sqrt(sigma2.l))
beta<-rnorm(A,mean=rep(0,A),sd=sqrt(sigma2.beta))
epsilon<-rgamma(1,a.epsilon,b.epsilon)
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
Q<-t(R)%*%R
J<-diag(rep(1,T))
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-sigma2.k*D 

kappa<-vector(length=T)
kappa[3:T]<-rmvnorm(1,mean=rep(0,(T-2)),sigma=S,method="chol")
kappa[1]<-sum((1:(T-2))*(kappa[3:T]))
kappa[2]<--sum((2:(T-1))*(kappa[3:T]))
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(kappa,A),nrow=A,ncol=T,byrow=TRUE)+log(matrix(rgamma(A*T,epsilon,epsilon),nrow=A,ncol=T))
logmiuxt[k,]<-as.vector(logmiuxt.temp)
}
logmiuxt
}

prior.logmiuxt11.ng.loglinear.block.2<-prior.logmiuxt11.ng.loglinear.block.2.fn(n=50000,A=A,T=T,t0=-21,lx=rep(0,100),sigma2.l=100,ak=0.1,bk=0.1,a.beta=0.1,b.beta=0.1,a.epsilon=2,b.epsilon=2,sigma2.rho=100)
 
par(mfrow=c(2,2))
plot(density(prior.logmiuxt11.ng.block[,1],n=50000),xlab="",main="Age 0 Year 1961",xlim=c(-600,100),cex.main=1.25,cex.lab=1.2,cex.axis=1.15)
lines(density(prior.logmiuxt11.ng.loglinear.block.2[,1],n=50000),col=2)
plot(density((prior.logmiuxt11.ng.block[,1000])[prior.logmiuxt11.ng.block[,1000]!=-Inf],n=50000),xlim=c(-600,100),ylim=c(0,0.01),xlab="",main="Age 99 Year 1970",cex.main=1.25,cex.lab=1.2,cex.axis=1.15)
lines(density((prior.logmiuxt11.ng.loglinear.block.2[,1000])[prior.logmiuxt11.ng.loglinear.block.2[,1000]!=-Inf],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block[,2901],n=50000),xlim=c(-600,100),ylim=c(0,0.017),xlab="",main="Age 0 Year 1990",cex.main=1.25,cex.lab=1.2,cex.axis=1.15)
lines(density(prior.logmiuxt11.ng.loglinear.block.2[,2901],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block[,4200],n=50000),xlim=c(-600,100),ylim=c(0,0.017),xlab="",main="Age 99 Year 2002",cex.main=1.25,cex.lab=1.2,cex.axis=1.15)
lines(density(prior.logmiuxt11.ng.loglinear.block.2[,4200],n=50000),col=2)

##sensible prior specification (moments matched)

prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc.fn<-function(n,A,T,t0,lx,sigma2.l,ak,bk,a.epsilon,b.epsilon,gamma.0,sigma.mat.0,sigma2.rho){ 
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
theta<-matrix(0,nrow=n,ncol=(2*A+T+6))
nu<-matrix(0,nrow=n,ncol=(A*T))
I<-diag(rep(1,A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))

for (k in 1:n){
sigma2.beta<-0.0050
#repeat{
#sigma2.k<-1/rgamma(1,ak,bk)
#if (sigma2.k<10) break
#}
sigma2.k<-1/rgamma(1,ak,bk)
#rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
rho<-2*rbeta(1,3,2)-1 
alpha<-rnorm(A,mean=lx,sd=sqrt(sigma2.l))
beta<-rmvnorm(1,mean=rep(1/A,(A-1)),sigma=(sigma2.beta*(I-1/A*K)),method="chol")
beta<-c(1-sum(beta),beta)
#epsilon<-rtrunc(1,spec="gamma",shape=a.epsilon,rate=b.epsilon,a=1,b=50000)
epsilon<-rgamma(1,shape=a.epsilon,rate=b.epsilon)
gamma<-c(rmvnorm(1,mean=gamma.0,sigma=sigma.mat.0))
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
i.R<-forwardsolve(R,diag(rep(1,T)))
i.Q<-i.R%*%t(i.R)
J<-diag(rep(1,T))
J[1,]<-rep(1,T)
C<-J%*%i.Q%*%t(J)
D<-C[(2:T),(2:T)]- (C[(2:T),1]/C[1,1])%*%t(C[1,(2:T)])
S<-sigma2.k*D
S<-(S+t(S))/2
mean.kappa<-(cbind(rep(1,T),t)%*%gamma)[-1]-C[(2:T),1]/C[1,1]*sum(cbind(rep(1,T),t)%*%gamma) 
kappa<-rmvnorm(1,mean=mean.kappa,sigma=S,method="chol")
kappa<-c(-sum(kappa),kappa)
nu.temp<-log(rgamma(A*T,epsilon,epsilon))
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(kappa)+matrix(nu.temp,nrow=A,ncol=T)
logmiuxt[k,]<-as.vector(logmiuxt.temp)
theta[k,]<-c(kappa,beta,alpha,sigma2.k,sigma2.beta,gamma,rho,epsilon)
nu[k,]<-nu.temp
}

cbind(logmiuxt,theta,nu)
}

prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc<-prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc.fn(n=50000,A=100,T=42,t0=-21,lx=rep(-5,100),sigma2.l=4,ak=1,bk=0.0001,a.epsilon=25,b.epsilon=0.05,gamma.0=c(0,0),sigma.mat.0=matrix(c(2000,0,0,2),nrow=2),sigma2.rho=100)

#moments-matched priors for loglinear model, but still normal priors for alpha,beta,kappa

prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc.fn<-function(n,A,T,t0,lx,sigma2.l,ak,bk,a.epsilon,b.epsilon,sigma2.rho){
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
theta<-matrix(0,nrow=n,ncol=(2*A+T+4))
for (k in 1:n){
sigma2.beta<-0.005*2
#repeat{
sigma2.k<-0.005*1/rgamma(1,ak,bk)
#if (sigma2.k<((0.99*0.005+0.0154^2)*10)) break
#}
#rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
rho<-2*rbeta(1,3,2)-1
alpha<-rnorm(A,mean=lx,sd=sqrt(2000*0.005+sigma2.l))
beta<-rnorm(A,mean=rep(0,A),sd=sqrt(0.005*2))
#epsilon<-rtrunc(1,spec="gamma",shape=a.epsilon,rate=b.epsilon,a=1,b=50000)
epsilon<-rgamma(1,a.epsilon,b.epsilon)
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
Q<-t(R)%*%R
J<-diag(rep(1,T))
J[1,]<-1
J[2,]<-0:(T-1)
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-sigma2.k*D

kappa<-vector(length=T)
kappa[3:T]<-rmvnorm(1,mean=rep(0,(T-2)),sigma=S,method="chol")
kappa[1]<-sum((1:(T-2))*kappa[3:T])
kappa[2]<--sum((2:(T-1))*kappa[3:T])
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(kappa,A),nrow=A,ncol=T,byrow=TRUE)+log(matrix(rgamma(A*T,epsilon,epsilon),nrow=A,ncol=T))
logmiuxt[k,]<-as.vector(logmiuxt.temp)
theta[k,]<-c(kappa,beta,alpha,sigma2.k,sigma2.beta,rho,epsilon)
}
cbind(logmiuxt,theta)
}

prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc<-prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc.fn(n=50000,A=100,T=42,t0=-21,lx=rep(-5,100),sigma2.l=4,ak=1,bk=0.0001,a.epsilon=25,b.epsilon=0.05,sigma2.rho=100)
gc()

par(mfrow=c(2,2))
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,1],n=50000),main="Age 0 Year 1961",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc[,1],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,1000],n=50000),xlim=c(-30,20),main="Age 99 Year 1970",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc[,1000],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,2901],n=50000),xlim=c(-30,20),main="Age 0 Year 1990",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc[,2901],n=50000),xlim=c(-30,20),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4200],n=50000),xlim=c(-30,20),main="Age 99 Year 2002",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.naive.notrunc[,4200],n=50000),xlim=c(-30,20),col=2)

##################
###Extra: simulation study using Czado's prior for alpha
###################

b<-0.001;a<-b*exp(-5)
alpha.lc<-log(rgamma(10000,a,b))
rlgamma(10000,scale=1/b,shape=a)
mean(alpha.lc);var(alpha.lc)
#too vague and heavy tail, will induce Bartlett's Paradox

a<-0.1;b<-0.1
x<-log(rgamma(10000,a,b))
mean(x);var(x)
digamma(a)-log(b);trigamma(a)

#change parameters a,b such that they are "sensible"
a.lc<-0.55;b.lc<-26.155
alpha.lc<-log(rgamma(10000,a.lc,b.lc))
mean(alpha.lc);var(alpha.lc);range(alpha.lc)
plot(density(alpha.lc)) #more negatively skewed

a.api<-0.28;b.api<-3.443
alpha.api<-log(rgamma(10000,a.api,b.api))
mean(alpha.api);var(alpha.api);range(alpha.api)
plot(density(alpha.api)) #more negatively skewed

#NBLC: log-gamma prior on alpha (sensible prior specificationm,moments matched),but still normal priors for beta,kappa

prior.logmiuxt11.ng.block.match.czado.fn<-function(n,A,T,t0,a.alpha,b.alpha,ak,bk,a.epsilon,b.epsilon,gamma.0,sigma.mat.0,sigma2.rho){ 
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
theta<-matrix(0,nrow=n,ncol=(2*A+T+6))
nu<-matrix(0,nrow=n,ncol=(A*T))
I<-diag(rep(1,A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))

for (k in 1:n){
sigma2.beta<-0.0050
#repeat{
#sigma2.k<-1/rgamma(1,ak,bk)
#if (sigma2.k<10) break
#}
sigma2.k<-1/rgamma(1,ak,bk)
#rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
rho<-2*rbeta(1,3,2)-1 
alpha<-log(rgamma(A,shape=a.alpha,rate=b.alpha))
beta<-rmvnorm(1,mean=rep(1/A,(A-1)),sigma=(sigma2.beta*(I-1/A*K)),method="chol")
beta<-c(1-sum(beta),beta)
#epsilon<-rtrunc(1,spec="gamma",shape=a.epsilon,rate=b.epsilon,a=1,b=50000)
epsilon<-rgamma(1,shape=a.epsilon,rate=b.epsilon)
gamma<-c(rmvnorm(1,mean=gamma.0,sigma=sigma.mat.0))
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
i.R<-forwardsolve(R,diag(rep(1,T)))
i.Q<-i.R%*%t(i.R)
J<-diag(rep(1,T))
J[1,]<-rep(1,T)
C<-J%*%i.Q%*%t(J)
D<-C[(2:T),(2:T)]- (C[(2:T),1]/C[1,1])%*%t(C[1,(2:T)])
S<-sigma2.k*D
S<-(S+t(S))/2
mean.kappa<-(cbind(rep(1,T),t)%*%gamma)[-1]-C[(2:T),1]/C[1,1]*sum(cbind(rep(1,T),t)%*%gamma) 
kappa<-rmvnorm(1,mean=mean.kappa,sigma=S,method="chol")
kappa<-c(-sum(kappa),kappa)
nu.temp<-log(rgamma(A*T,epsilon,epsilon))
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(kappa)+matrix(nu.temp,nrow=A,ncol=T)
logmiuxt[k,]<-as.vector(logmiuxt.temp)
theta[k,]<-c(kappa,beta,alpha,sigma2.k,sigma2.beta,gamma,rho,epsilon)
nu[k,]<-nu.temp
}

cbind(logmiuxt,theta,nu)
}

prior.logmiuxt11.ng.block.match.czado<-prior.logmiuxt11.ng.block.match.czado.fn(n=50000,A=100,T=42,t0=-21,a.alpha=0.55,b.alpha=26.155,ak=1,bk=0.0001,a.epsilon=25,b.epsilon=0.05,gamma.0=c(0,0),sigma.mat.0=matrix(c(2000,0,0,2),nrow=2),sigma2.rho=100)

#NBLC: log-gamma prior on alpha (sensible prior specificationm,moments matched),but still normal priors for beta,kappa

prior.logmiuxt11.ng.loglinear.block.2.czado.fn<-function(n,A,T,t0,a.alpha,b.alpha,ak,bk,a.epsilon,b.epsilon,sigma2.rho){
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
theta<-matrix(0,nrow=n,ncol=(2*A+T+4))
for (k in 1:n){
sigma2.beta<-0.005*2
#repeat{
sigma2.k<-0.005*1/rgamma(1,ak,bk)
#if (sigma2.k<((0.99*0.005+0.0154^2)*10)) break
#}
#rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
rho<-2*rbeta(1,3,2)-1
alpha<-log(rgamma(A,shape=a.alpha,rate=b.alpha))
beta<-rnorm(A,mean=rep(0,A),sd=sqrt(0.005*2))
#epsilon<-rtrunc(1,spec="gamma",shape=a.epsilon,rate=b.epsilon,a=1,b=50000)
epsilon<-rgamma(1,a.epsilon,b.epsilon)
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
Q<-t(R)%*%R
J<-diag(rep(1,T))
J[1,]<-1
J[2,]<-0:(T-1)
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-sigma2.k*D

kappa<-vector(length=T)
kappa[3:T]<-rmvnorm(1,mean=rep(0,(T-2)),sigma=S,method="chol")
kappa[1]<-sum((1:(T-2))*kappa[3:T])
kappa[2]<--sum((2:(T-1))*kappa[3:T])
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(kappa,A),nrow=A,ncol=T,byrow=TRUE)+log(matrix(rgamma(A*T,epsilon,epsilon),nrow=A,ncol=T))
logmiuxt[k,]<-as.vector(logmiuxt.temp)
theta[k,]<-c(kappa,beta,alpha,sigma2.k,sigma2.beta,rho,epsilon)
}
cbind(logmiuxt,theta)
}

prior.logmiuxt11.ng.loglinear.block.2.czado<-prior.logmiuxt11.ng.loglinear.block.2.czado.fn(n=50000,A=100,T=42,t0=-21,a.alpha=0.28,b.alpha=3.443,ak=1,bk=0.0001,a.epsilon=25,b.epsilon=0.05,sigma2.rho=100)
gc()

par(mfrow=c(2,2))
plot(density(prior.logmiuxt11.ng.block.match.czado[,1],n=50000),main="Age 0 Year 1961",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.czado[,1],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.czado[,1000],n=50000),xlim=c(-30,20),main="Age 99 Year 1970",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.czado[,1000],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.czado[,2901],n=50000),xlim=c(-30,20),main="Age 0 Year 1990",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.czado[,2901],n=50000),xlim=c(-30,20),col=2)
plot(density(prior.logmiuxt11.ng.block.match.czado[,4200],n=50000),xlim=c(-30,20),main="Age 99 Year 2002",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.czado[,4200],n=50000),xlim=c(-30,20),col=2)
legend("topright",c("NBLC","NBAPI"),lty=1,col=c(1,2))


###Compatible prior specification (Laplace priors)

#alpha
alpha.ng.LC.LQ.0.05<-apply((prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4343:4442]+prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4445]*prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4243:4342]),2,quantile,p=0.05)

lambda.alpha<--(-5-alpha.ng.LC.LQ.0.05)/(log(0.1)) #2.6
#lambda.alpha<-rep(2,100)

beta.ng.LC.LQ.0.45<-apply(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4446]*prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4243:4342],2,quantile,p=0.45)

lambda.beta<-beta.ng.LC.LQ.0.45/log(0.9) #around 0.03
#lambda.beta<-rep(0.03,100)


prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile.notrunc.fn<-function(n,A,T,t0,lx,lambda.alpha,lambda.beta,sigma2.l,ak,bk,a.epsilon,b.epsilon,sigma2.rho){
t<-t0:(t0+T-1)
logmiuxt<-matrix(0,nrow=n,ncol=(A*T))
theta<-matrix(0,nrow=n,ncol=(2*A+T+4))
nu<-matrix(0,nrow=n,ncol=(A*T))
for (k in 1:n){
#repeat{
#lambda<-2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(2000))*rgamma(1,ak,bk)
#if (lambda>(0.1*2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(2000)))) break
lambda<-2/(0.005)*rgamma(1,ak,bk)
#if (lambda>(0.1*2/(0.005*2000))) break
#}
sigma2.k<-rexp(1,rate=lambda) 
rho<-2*rbeta(1,3,2)-1
#rho<-rtruncnorm(1,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho))
alpha<-rdoublex(A,mu=lx,lambda=lambda.alpha)
beta<-rdoublex(A,mu=0,lambda=lambda.beta)
#epsilon<-rtrunc(1,spec="gamma",shape=a.epsilon,rate=b.epsilon,a=1,b=5000)
epsilon<-rgamma(1,shape=a.epsilon,rate=b.epsilon)
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
Q<-t(R)%*%R
J<-diag(rep(1,T))
J[1,]<-1
J[2,]<-0:(T-1)
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-2*sigma2.k*D

kappa<-vector(length=T)
kappa[3:T]<-rmvnorm(1,mean=rep(0,(T-2)),sigma=S,method="chol")
kappa[1]<-sum((1:(T-2))*kappa[3:T])
kappa[2]<--sum((2:(T-1))*kappa[3:T])
nu.temp<-log(rgamma(A*T,epsilon,epsilon))
logmiuxt.temp<-matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(kappa,A),nrow=A,ncol=T,byrow=TRUE)+matrix(nu.temp,nrow=A,ncol=T)
logmiuxt[k,]<-as.vector(logmiuxt.temp)
theta[k,]<-c(kappa,beta,alpha,sigma2.k,lambda,rho,epsilon)
nu[k,]<-nu.temp
}
cbind(logmiuxt,theta,nu)
}

prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile<-prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile.notrunc.fn(n=50000,A=100,T=42,t0=-21,lx=rep(-5,100),lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,sigma2.l=4,ak=1,bk=0.0001,a.epsilon=25,b.epsilon=0.05,sigma2.rho=100) 

par(mfrow=c(4,3))
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,1],n=50000),xlim=c(-20,10),main="Age 0 Year 1961",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,1],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,10],n=50000),xlim=c(-10,0),main="log miu_10,1")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,10],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,100],n=50000),xlim=c(-10,0),main="log miu_100,1")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,100],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,500],n=50000),xlim=c(-10,0),main="log miu_100,5")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,500],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,1000],n=50000),xlim=c(-20,10),main="Age 99 Year 1970",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,1000],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,2000],n=50000),xlim=c(-10,0),main="log miu_100,20")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,2000],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,2500],n=50000),xlim=c(-10,0),main="log miu_100,25")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,2500],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,2901],n=50000),xlim=c(-20,10),main="Age 0 Year 1990",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,2901],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,3500],n=50000),xlim=c(-10,0),main="log miu_100,35")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,3500],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4000],n=50000),xlim=c(-10,0),main="log miu_100,40")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,4000],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4186],n=50000),xlim=c(-10,0),main="log miu_86,42")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,4186],n=50000),col=2)
plot(density(prior.logmiuxt11.ng.block.match.remove.lowvar.notrunc[,4200],n=50000),xlim=c(-20,10),main="Age 99 Year 2002",xlab="")
lines(density(prior.logmiuxt11.ng.loglinear.block.2.remove.laplace.2.lowvar.quantile[,4200],n=50000),col=2)

############################
##Naive priors MCMC samples (for illustration)
############################
 
MCMC.deathrates.over.negbin.int.AR1.normal<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k.new,alpha.new,beta.new,sigma2.beta,gamma.new,sigma2.k,rho.new,lx,sigma2.l,epsilon,a.beta,b.beta,ak,bk,sigma2.rho,gamma.0,sigma.mat.0,prior.epsilon.gamma=FALSE,a.epsilon,b.epsilon,prior.epsilon.normal=FALSE,miu.epsilon,sigma2.epsilon,sigma2.t,sigma2.x,sigma2.x.alpha,sigma2.prop.epsilon){

Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha.new)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=2*A+T+6)
loglikelihood.store<-vector(length=n)

Y.tmin<-matrix(c(rep(1,(T-1)),(t0+1):(t0+T-1)),byrow=F,ncol=2)
Z<-matrix(0,nrow=(T-1),ncol=2)
Z[1,1]<-1
Z[1,2]<-t0
isigma.mat.0<-solve(sigma.mat.0)
I<-diag(1,nrow=(A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))
inverse<-solve(I-1/A*K)

accept.epsilon<-0
accept<-rep(0,T)
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)

iter<-0
g<-seq(thin,n-burnin,by=thin)

for (m in 1:n){

k.new[1]<-0
for (i in 2:T){

if (i==T){
p.nbinom<-epsilon/(epsilon+Ext[,i]*exp(alpha.new+beta.new*k.new[i]))
k.star<-rnorm(1,k.new[i],sqrt(sigma2.t[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[,i]*exp(alpha.new+beta.new*k.star))
prob.accept.k<-(sum(dnbinom(Dxt[,i],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.k)*(k.star-gamma.new[1]-gamma.new[2]*(t0+i-1)-rho.new*(k.new[i-1]-gamma.new[1]-gamma.new[2]*(t0+i-2)))^2
-sum(dnbinom(Dxt[,i],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.k)*(k.new[i]-gamma.new[1]-gamma.new[2]*(t0+i-1)-rho.new*(k.new[i-1]-gamma.new[1]-gamma.new[2]*(t0+i-2)))^2)
if (log(runif(1))<=prob.accept.k) {k.new[i]<-k.star} & {accept[i]<-accept[i]+1}
}

if (i!=T){
p.nbinom<-epsilon/(epsilon+Ext[,i]*exp(alpha.new+beta.new*k.new[i]))
k.star<-rnorm(1,k.new[i],sqrt(sigma2.t[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[,i]*exp(alpha.new+beta.new*k.star))
prob.accept.k<-(sum(dnbinom(Dxt[,i],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.k)*(k.star-gamma.new[1]-gamma.new[2]*(t0+i-1)-rho.new*(k.new[i-1]-gamma.new[1]-gamma.new[2]*(t0+i-2)))^2-1/(2*sigma2.k)*(k.new[i+1]-gamma.new[1]-gamma.new[2]*(t0+i)-rho.new*(k.star-gamma.new[1]-gamma.new[2]*(t0+i-1)))^2
-sum(dnbinom(Dxt[,i],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.k)*(k.new[i]-gamma.new[1]-gamma.new[2]*(t0+i-1)-rho.new*(k.new[i-1]-gamma.new[1]-gamma.new[2]*(t0+i-2)))^2+1/(2*sigma2.k)*(k.new[i+1]-gamma.new[1]-gamma.new[2]*(t0+i)-rho.new*(k.new[i]-gamma.new[1]-gamma.new[2]*(t0+i-1)))^2)
if (log(runif(1))<=prob.accept.k) {k.new[i]<-k.star} & {accept[i]<-accept[i]+1}
}
}

for (i in 2:A){
beta.star<-rnorm(1,beta.new[i],sqrt(sigma2.x[i]))
beta.star.vec<-beta.new;beta.star.vec[i]<-beta.star;beta.star.vec[1]<-1-sum(beta.star.vec[-1])
prob.accept.beta<-sum(Dxt[i,]*k.new*(beta.star-beta.new[i]))+sum(Dxt[1,]*k.new*(beta.star.vec[1]-beta.new[1]))-sum((Dxt[i,]+epsilon)*(log(Ext[i,]*exp(alpha.new[i]+beta.star*k.new)+epsilon)-log(Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new)+epsilon)))-
sum((Dxt[1,]+epsilon)*(log(Ext[1,]*exp(alpha.new[1]+beta.star.vec[1]*k.new)+epsilon)-log(Ext[1,]*exp(alpha.new[1]+beta.new[1]*k.new)+epsilon)))-(beta.star.vec[1]^2)/(2*sigma2.beta)-(beta.star^2)/(2*sigma2.beta)+(beta.new[1]^2)/(2*sigma2.beta)+(beta.new[i]^2)/(2*sigma2.beta)
if (log(runif(1))<=prob.accept.beta) {beta.new[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
beta.new[1]<-1-sum(beta.new[-1])
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new))
alpha.star<-rnorm(1,alpha.new[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta.new[i]*k.new))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.l)*(alpha.star-lx[i])^2-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.l)*(alpha.new[i]-lx[i])^2
if (log(runif(1))<=prob.accept.alpha) {alpha.new[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

ita.t<-gamma.new[1]+gamma.new[2]*(t0:(t0+T-1))
a.rho<-sum((k.new[-T]-ita.t[-T])^2)
b.rho<-sum((k.new-ita.t)*c(0,(k.new[-T]-ita.t[-T])))
miu.rho<-b.rho/(a.rho+sigma2.k/sigma2.rho)
sigma2.rho.star<-sigma2.k/(a.rho+sigma2.k/sigma2.rho)

rho.new<-rnorm(1,mean=miu.rho,sd=sqrt(sigma2.rho.star))

isigma2.k<-rgamma(1,ak+(T-1)/2,bk+0.5*sum((k.new[-1]-ita.t[-1]-rho.new*(k.new[-T]-ita.t[-T]))^2))
sigma2.k<-isigma2.k^-1

isigma2.beta<-rgamma(1,a.beta+(A-1)/2,b.beta+0.5*t(beta.new[-1]-rep(1/A,(A-1)))%*%inverse%*%(beta.new[-1]-rep(1/A,(A-1))))
sigma2.beta<-isigma2.beta^-1

R<-matrix(0,nrow=(T-1),ncol=(T-1))
for (i in 1:(T-1)){
for (j in 1:(T-1)){
if ((i-j)==1) R[i,j]<--rho.new
if ((i-j)==0) R[i,j]<-1
}
}
i.R<-solve(R)
Q<-t(R)%*%R

sigma.mat.star<-solve(t(Y.tmin-rho.new*i.R%*%Z)%*%Q%*%(Y.tmin-rho.new*i.R%*%Z)+sigma2.k*isigma.mat.0)
gamma.star<-sigma.mat.star%*%(t(Y.tmin-rho.new*i.R%*%Z)%*%Q%*%k.new[-1]+sigma2.k*isigma.mat.0%*%gamma.0)
gamma.new<-rmvnorm.tol(1,mean=gamma.star,sigma=sigma2.k*sigma.mat.star,method="chol")
#should update ita.t here, but it is still OK since I did not use ita.t until just before Gibbs rho.

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
}

if (prior.epsilon.normal){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.epsilon)*(epsilon.star-miu.epsilon)^2-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.epsilon)*(epsilon-miu.epsilon)^2+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
}

loglikelihood<-sum(dpois(Dxt,exp(matrix(rep(alpha.new,T),nrow=A,ncol=T)+beta.new%*%t(k.new)),log=TRUE))

if ((m>burnin) & ((m-burnin) %in% g)){
iter<-iter+1
result[iter,]<-c(k.new,beta.new,alpha.new,rho.new,sigma2.k,sigma2.beta,gamma.new,epsilon)
}

loglikelihood.store[m]<-loglikelihood
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],rho.1=result[,(2*A+T+1)],sigma2.k=result[,(2*A+T+2)],sigma2.beta=result[,(2*A+T+3)],gamma.new=result[,(2*A+T+4):(2*A+T+5)],epsilon=result[,(2*A+T+6)],loglikelihood=loglikelihood.store[g],accept,accept.beta,accept.alpha,accept.epsilon)
}

#classical fitting for initialisation
iteration.LC.poisson2<-function(deaths,exposure,m,alpha.initial,beta.initial,kappa.initial,A,T){
alpha.new<-alpha.initial
beta.new<-beta.initial
kappa.new<-kappa.initial
kappa.new.matrix<-matrix(kappa.new,ncol=length(kappa.initial))
Deviance<-NULL

for (i in 1:m){

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

alpha.new<-alpha.new+apply((deaths-fitted.y),1,sum)/apply(fitted.y,1,sum)

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

kappa.new<-kappa.new+apply((deaths-fitted.y)*beta.new,2,sum)/apply(fitted.y*(beta.new^2),2,sum)
kappa.new<-kappa.new-(kappa.new[1])
kappa.new.matrix<-matrix(kappa.new,ncol=length(kappa.initial))

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

beta.new<-beta.new+apply(t(t(deaths-fitted.y)*kappa.new),1,sum)/apply(t(t(fitted.y)*kappa.new^2),1,sum)
beta.new<-beta.new/(sum(beta.new))

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

Deviance[i]<-sum(2*(deaths*log(deaths/fitted.y)-(deaths-fitted.y)))
}
list(Deviance,alpha.new,beta.new,kappa.new)
}

result5.female.2<-iteration.LC.poisson2(round(EWdeath.female.mat.ex),EWexpo.female.mat.ex,50,alpha.initial=apply((EWdeath.female.mat.ex/EWexpo.female.mat.ex),1,mean),beta.initial=rep(1/A,A),kappa.initial=rep(0,T),A=A,T=T)

Ext<-round(EWexpo.female.mat.ex)
Dxt<-round(EWdeath.female.mat.ex)
t0<--21
k.new<-unlist(result5.female.2[[4]])
t<-t0:(t0+T-1)
Y<-matrix(c(rep(1,length(k.new)),t),byrow=F,ncol=2)
sigma.mat.0<-matrix(c(1000,0,0,10),nrow=2)
alpha.new<-unlist(result5.female.2[[2]])
beta.new<-unlist(result5.female.2[[3]])
gamma.new<-c(0,0)
sigma2.k<-arima(k.new-Y%*%gamma.new,order=c(1,0,0))$sigma2
sigma2.beta=var(beta.new)
rho.new<-arima(k.new-Y%*%gamma.new,order=c(1,0,0))$coef[1]
lx<-rep(0,A)
sigma2.l<-100
a.beta<-0.001
b.beta<-0.001
ak<-0.001
bk<-0.001 

##automated search for optimal acceptance rate
sigma.x.alpha<-rep(0.001,100)
sigma2.x<-rep(0.0000001,100)
sigma2.t=rep(4.5,length(k.new))

repeat{
system.time(rates.MCMC.over.negbin.int.AR1.y0.normal<-MCMC.deathrates.over.negbin.int.AR1.normal(n=100,burnin=0000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=T,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=var(beta.new),gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,a.beta=a.beta,b.beta=b.beta,ak=ak,bk=bk,sigma2.rho=100,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=0.0001,b.epsilon=0.0001,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma2.t=sigma2.t,sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08))
sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]<20]/2
if (sum((rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]<40) & (rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="Age",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(rates.MCMC.over.negbin.int.AR1.y0.normal[[12]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)

repeat{
system.time(rates.MCMC.over.negbin.int.AR1.y0.normal<-MCMC.deathrates.over.negbin.int.AR1.normal(n=100,burnin=0000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=T,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=var(beta.new),gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,a.beta=a.beta,b.beta=b.beta,ak=ak,bk=bk,sigma2.rho=100,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=0.0001,b.epsilon=0.0001,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma2.t=sigma2.t,sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08))
sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.normal[[11]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.normal[[11]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.normal[[11]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.normal[[11]]<20]/2
if (sum((rates.MCMC.over.negbin.int.AR1.y0.normal[[11]]<40) & (rates.MCMC.over.negbin.int.AR1.y0.normal[[11]]>20))==99) break
}
sigma2.x<-c(0.0000001,sigma2.x[-1])
par(mfrow=c(1,2))
plot(sigma2.x*1e7,mgp=c(2.25,1,0),ylim=c(0,10),xlab="Age",ylab=expression(paste("Proposal Variance ",(1%*% 10^-7))),main=expression(sigma[beta[x]]^2),cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(rates.MCMC.over.negbin.int.AR1.y0.normal[[11]][-1]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)

par(mfrow=c(1,2))
plot(2:42,sigma2.t[-1],ylim=c(0,6),main=expression(sigma[kappa[t]]^2),xlab="Year",ylab="Proposal Variance",cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(2:42,rates.MCMC.over.negbin.int.AR1.y0.normal[[10]][-1]/100,ylim=c(0,1),xlab="Year",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)


system.time(rates.MCMC.over.negbin.int.AR1.y0.normal<-MCMC.deathrates.over.negbin.int.AR1.normal(n=201000,burnin=1000,thin=20,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=T,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=var(beta.new),gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,a.beta=a.beta,b.beta=b.beta,ak=ak,bk=bk,sigma2.rho=100,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=0.0001,b.epsilon=0.0001,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma2.t=sigma2.t,sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08))
theta.AR1.over.negbin.int.y0.normal<-cbind(rates.MCMC.over.negbin.int.AR1.y0.normal$k.new,rates.MCMC.over.negbin.int.AR1.y0.normal$beta.new,rates.MCMC.over.negbin.int.AR1.y0.normal$alpha.new,log(rates.MCMC.over.negbin.int.AR1.y0.normal$sigma2.k),log(rates.MCMC.over.negbin.int.AR1.y0.normal$sigma2.beta),rates.MCMC.over.negbin.int.AR1.y0.normal$gamma.new,rates.MCMC.over.negbin.int.AR1.y0.normal$rho.1,rates.MCMC.over.negbin.int.AR1.y0.normal$epsilon)

#Marginal likelihood of NBLC-AR1 with naive priors

like.prior.negbin.lca<-function(param,Dxt,Ext,A,T,t,lx,sigma2.l,sigma2.rho,gamma.0,sigma.mat.0,ak,bk,a.beta,b.beta,a.epsilon,b.epsilon){#supply param=c(k,beta,alpha,log.sigma2.k,log.sigma2.beta,gamma1,gamma2,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
sigma2.k<-exp(param[2*A+T+1])
sigma2.beta<-exp(param[2*A+T+2])
rho<-param[2*A+T+5]
gamma1<-param[2*A+T+3]
gamma2<-param[2*A+T+4]
gamma<-c(gamma1,gamma2)
ita.t<-gamma1+gamma2*t
epsilon<-param[2*A+T+6]
I<-diag(rep(1,A-1))
K<-matrix(1,nrow=A-1,ncol=A-1)
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(k))+epsilon)	

sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+sum(dnorm(k[-1],mean=ita.t[-1]+rho*(k[-T]-ita.t[-T]),sd=sqrt(sigma2.k),log=TRUE))+dmvnorm(beta[-1],mean=rep(1/A,A-1),sigma=sigma2.beta*(I-1/A*K),log=TRUE)+
sum(dnorm(alpha,mean=lx,sd=sqrt(sigma2.l),log=TRUE))+dnorm(rho,mean=0,sd=sqrt(sigma2.rho),log=TRUE)+dmvnorm(gamma,mean=gamma.0,sigma=sigma.mat.0,log=TRUE)+ak*log(bk)-lgamma(ak)-ak*log(sigma2.k)-bk/sigma2.k+a.beta*log(b.beta)-lgamma(a.beta)-a.beta*log(sigma2.beta)-b.beta/sigma2.beta+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon
}

sigma2.rho<-100
gamma.0<-c(0,0)
a.epsilon<-0.0001
b.epsilon<-0.0001

like.prior.negbin.lca(param=theta.AR1.over.negbin.int.y0.normal[1,],Dxt=Dxt,Ext=Ext,A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,sigma2.rho=sigma2.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.beta=a.beta,b.beta=b.beta,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.negbin<-apply(theta.AR1.over.negbin.int.y0.normal,1,like.prior.negbin.lca,Dxt=Dxt,Ext=Ext,A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,sigma2.rho=sigma2.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.beta=a.beta,b.beta=b.beta,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.negbin.vec<-apply(cbind(theta.AR1.over.negbin.int.y0.normal[,-c(1,T+1,2*A+T+6)],log(theta.AR1.over.negbin.int.y0.normal[,2*A+T+6])),2,mean)
covariance.negbin.mat<-cov(cbind(theta.AR1.over.negbin.int.y0.normal[,-c(1,T+1,2*A+T+6)],log(theta.AR1.over.negbin.int.y0.normal[,2*A+T+6])))

sample.bridge.negbin.lca<-rmvnorm(10000,mean=mean.negbin.vec,sigma=covariance.negbin.mat,method="chol")
sample.bridge.negbin.lca<-cbind(rep(0,10000),sample.bridge.negbin.lca[,1:(T-1)],1-apply(sample.bridge.negbin.lca[,(T):(A+T-2)],1,sum),sample.bridge.negbin.lca[,(T):(2*A+T+3)],exp(sample.bridge.negbin.lca[,2*A+T+4]))
likelihood.bridge<-apply(sample.bridge.negbin.lca,1,like.prior.negbin.lca,Dxt=Dxt,Ext=Ext,A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,sigma2.rho=sigma2.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.beta=a.beta,b.beta=b.beta,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

chol.cov.negbin.mat<-chol(covariance.negbin.mat)
inverse.t.chol.cov.negbin.mat<-solve(t(chol.cov.negbin.mat))

log.det.Jacobian.negbin<-determinant(inverse.t.chol.cov.negbin.mat,logarithm=TRUE)$modulus

q2.negbin<-apply(cbind(theta.AR1.over.negbin.int.y0.normal[,-c(1,T+1,2*A+T+6)],log(theta.AR1.over.negbin.int.y0.normal[,2*A+T+6])),1,transformation.dmvnorm,mean.vec=mean.negbin.vec,rij=inverse.t.chol.cov.negbin.mat,log.det.Jacobian=log.det.Jacobian.negbin)
q2.negbin.bridge<-apply(cbind(sample.bridge.negbin.lca[,-c(1,T+1,2*A+T+6)],log(sample.bridge.negbin.lca[,2*A+T+6])),1,transformation.dmvnorm,mean.vec=mean.negbin.vec,rij=inverse.t.chol.cov.negbin.mat,log.det.Jacobian=log.det.Jacobian.negbin)

log.l<-likelihood.negbin-q2.negbin
log.l.tilda<-likelihood.bridge-q2.negbin.bridge

log.l.tilda<-log.l.tilda+24000
log.l<-log.l+24000
l<-exp(log.l)
l.tilda<-exp(log.l.tilda)

nc.negbin.lca<-bridge(initial=100,m=100,sample1=theta.AR1.over.negbin.int.y0.normal,sample2=sample.bridge.negbin.lca,n1=10000,n2=10000,l=l,l.tilda=l.tilda)[101] 
log(nc.negbin.lca)-24000 #approx -23729.06


MCMC.rates.new.over.negbin.int.AR1.trunc.block<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k,alpha,beta,sigma2.beta,sigma2.k,rho,lx,sigma2.l,epsilon,a.beta,b.beta,ak,bk,sigma2.rho,prior.epsilon.gamma=TRUE,a.epsilon,b.epsilon,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.rho,sigma2.prop.epsilon){

Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha)
result<-matrix(0,nrow=n,ncol=(2*A+T+4))
loglikelihood.store<-vector(length=n)

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
Q<-t(R)%*%R
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])

accept.epsilon<-0
accept.rho<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)

for (m in 1:n){

S<-sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
k.star.vec<-rmvnorm.tol(1,mean=k[-c(1,2)],sigma=sigma.prop.k)
k.temp.star.vec<-k;k.temp.star.vec[3:T]<-k.star.vec
k.temp.star.vec[1]<-sum((1:(T-2))*k.temp.star.vec[3:T]);k.temp.star.vec[2]<--sum((2:(T-1))*k.temp.star.vec[3:T])
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k.temp.star.vec,A),nrow=A,ncol=T,byrow=TRUE)))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.temp.star.vec[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k<-k.temp.star.vec
accept<-accept+1}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k))
beta.star<-rnorm(1,beta[i],sqrt(sigma2.x[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta.star*t+k))
prob.accept.beta<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-beta.star^2/(2*sigma2.beta)-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+beta[i]^2/(2*sigma2.beta)
if (log(runif(1))<=prob.accept.beta) {beta[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k))
alpha.star<-rnorm(1,alpha[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta[i]*t+k))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-((alpha.star-lx[i])^2)/(2*sigma2.l)-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+((alpha[i]-lx[i])^2)/(2*sigma2.l)
if (log(runif(1))<=prob.accept.alpha) {alpha[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

rho.star<-rnorm(1,mean=rho,sd=sqrt(sigma2.prop.rho))#could straightaway use rtruncnorm, although this does required us to change the MH acceptance/rejection ratio
if ((rho.star>-1) & (rho.star<1)){
R.star<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R.star[i,j]<--rho.star
if ((i-j)==0) R.star[i,j]<-1
}
}
Q.star<-t(R.star)%*%R.star
C.star<-J%*%solve(Q.star)%*%t(J) 
D.star<-C.star[(3:T),(3:T)]-(C.star[(3:T),(1:2)])%*%solve(C.star[(1:2),(1:2)])%*%(C.star[(1:2),(3:T)])
S.star<-sigma2.k*D.star #always gives warning on symmetry, investigate and if necessary, create dmvnorm.tol to alter the tolerance. And why is S.star ever be unsymmetric? It isnt possible unless it is numerically unsymmetric.
prob.accept.rho<-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)-(rho.star^2)/(2*sigma2.rho)-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)+(rho^2)/(2*sigma2.rho)
if (log(runif(1))<=prob.accept.rho){
(rho<-rho.star)  
(Q<-Q.star) 
(R<-R.star) 
(C<-C.star) 
(D<-D.star) 
(S<-S.star) 
(accept.rho<-accept.rho+1)}
}

isigma2.k<-rgamma(1,ak+(T-2)/2,bk+0.5*(t(k[3:T])%*%solve(D)%*%k[3:T]))
sigma2.k<-isigma2.k^-1

isigma2.beta<-rgamma(1,a.beta+A/2,b.beta+sum(beta^2)/2)
sigma2.beta<-isigma2.beta^-1

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
}

p.nbinom<-epsilon/(epsilon+exp(matrix(rep(alpha,T),nrow=A,ncol=T)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
loglikelihood<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))

result[m,]<-c(k,beta,alpha,rho,sigma2.k,sigma2.beta,epsilon)
loglikelihood.store[m]<-loglikelihood
}
result<-result[(burnin+1):n,]
loglikelihood.store<-loglikelihood.store[(burnin+1):n]
g<-seq(thin,n-burnin,by=thin)
result<-result[g,]
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],rho.1=result[,(2*A+T+1)],sigma2.k=result[,(2*A+T+2)],sigma2.beta=result[,(2*A+T+3)],epsilon=result[,(2*A+T+4)],loglikelihood=loglikelihood.store[g],accept,accept.beta,accept.alpha,accept.epsilon,accept.rho)
}

#classical fitting for initialisation
GLM.poisson.cons7<-function(dxt.vec,log.ext.vec,t0,A,T){
x<-matrix(0,nrow=(A*T),ncol=A)
x[,1]<-rep(c(1,rep(0,A-1)),T)
for (i in 2:A){
x[,i]<-c(0,(x[,(i-1)])[-(A*T)])
}
t<-rep(t0,A)
for (i in 1:(T-1)){
t<-c(t,rep(t0+i,A))
}
beta.x<-x*t
k<-matrix(0,nrow=(A*T),ncol=T)
for (i in 1:T){
k[,i]<-c(rep(rep(0,A),(i-1)),rep(1,A),rep(rep(0,A),(T-i)))
}

for (i in 3:T){
k[,i]<-k[,i]+(i-2)*k[,1]-(i-1)*k[,2]
}

fit<-glm(formula=(dxt.vec~x[,1]+x[,2]+x[,3]+x[,4]+x[,5]+x[,6]+x[,7]+x[,8]+x[,9]+x[,10]+x[,11]+x[,12]+x[,13]+x[,14]+x[,15]+x[,16]+x[,17]+x[,18]+x[,19]+x[,20]+x[,21]+x[,22]+x[,23]+x[,24]+x[,25]+x[,26]+x[,27]+x[,28]+x[,29]+x[,30]+x[,31]+x[,32]+x[,33]+x[,34]+x[,35]+x[,36]+x[,37]+x[,38]+x[,39]+x[,40]+x[,41]+x[,42]+x[,43]+x[,44]+x[,45]+x[,46]+x[,47]+x[,48]+x[,49]+x[,50]+x[,51]+x[,52]+x[,53]+x[,54]+x[,55]+x[,56]+x[,57]+x[,58]+x[,59]+x[,60]+x[,61]+x[,62]+x[,63]+x[,64]+x[,65]+x[,66]+x[,67]+x[,68]+x[,69]+x[,70]+x[,71]+x[,72]+x[,73]+x[,74]+x[,75]+x[,76]+x[,77]+x[,78]+x[,79]+x[,80]+x[,81]+x[,82]+x[,83]+x[,84]+x[,85]+x[,86]+x[,87]+x[,88]+x[,89]+x[,90]+x[,91]+x[,92]+x[,93]+x[,94]+x[,95]+x[,96]+x[,97]+x[,98]+x[,99]+x[,100]+beta.x[,1]+beta.x[,2]+beta.x[,3]+beta.x[,4]+beta.x[,5]+beta.x[,6]+beta.x[,7]+beta.x[,8]+beta.x[,9]+beta.x[,10]+beta.x[,11]+beta.x[,12]+beta.x[,13]+beta.x[,14]+beta.x[,15]+beta.x[,16]+beta.x[,17]+beta.x[,18]+beta.x[,19]+beta.x[,20]+beta.x[,21]+beta.x[,22]+beta.x[,23]+beta.x[,24]+beta.x[,25]+beta.x[,26]+beta.x[,27]+beta.x[,28]+beta.x[,29]+beta.x[,30]+beta.x[,31]+beta.x[,32]+beta.x[,33]+beta.x[,34]+beta.x[,35]+beta.x[,36]+beta.x[,37]+beta.x[,38]+beta.x[,39]+beta.x[,40]+
beta.x[,41]+beta.x[,42]+beta.x[,43]+beta.x[,44]+beta.x[,45]+beta.x[,46]+beta.x[,47]+beta.x[,48]+beta.x[,49]+beta.x[,50]+beta.x[,51]+beta.x[,52]+beta.x[,53]+beta.x[,54]+beta.x[,55]+beta.x[,56]+beta.x[,57]+beta.x[,58]+beta.x[,59]+beta.x[,60]+beta.x[,61]+beta.x[,62]+beta.x[,63]+beta.x[,64]+beta.x[,65]+beta.x[,66]+beta.x[,67]+beta.x[,68]+beta.x[,69]+beta.x[,70]+beta.x[,71]+beta.x[,72]+beta.x[,73]+beta.x[,74]+beta.x[,75]+beta.x[,76]+beta.x[,77]+beta.x[,78]+beta.x[,79]+beta.x[,80]+beta.x[,81]+beta.x[,82]+beta.x[,83]+beta.x[,84]+beta.x[,85]+beta.x[,86]+beta.x[,87]+beta.x[,88]+beta.x[,89]+beta.x[,90]+beta.x[,91]+beta.x[,92]+beta.x[,93]+beta.x[,94]+beta.x[,95]+beta.x[,96]+beta.x[,97]+beta.x[,98]+beta.x[,99]+beta.x[,100]+k[,3]+k[,4]+k[,5]+k[,6]+k[,7]+k[,8]+k[,9]+k[,10]+k[,11]+k[,12]+k[,13]+k[,14]+k[,15]+k[,16]+k[,17]+k[,18]+k[,19]+k[,20]+k[,21]+k[,22]+k[,23]+k[,24]+k[,25]+k[,26]+k[,27]+k[,28]+k[,29]+k[,30]+k[,31]+k[,32]+k[,33]+k[,34]+k[,35]+k[,36]+k[,37]+k[,38]+k[,39]+k[,40]+k[,41]+k[,42]-1),offset=log.ext.vec,family=poisson)
return(fit)
}

result.poisson.cons7.glm<-GLM.poisson.cons7(dxt.vec=(round(EWdeath.female.vec.ex)),log.ext.vec=log(round(EWexpo.female.vec.ex)),t0=t0,A=A,T=T)

k.new<-c(sum((1:40)*result.poisson.cons7.glm$coef[201:240]),-sum((2:41)*result.poisson.cons7.glm$coef[201:240]),result.poisson.cons7.glm$coef[201:240])
alpha.new<-result.poisson.cons7.glm$coef[1:100]
beta.new<-result.poisson.cons7.glm$coef[101:200]
sigma2.k<-arima(k.new,order=c(1,0,0))$sigma2
sigma2.beta=var(beta.new)
rho.new<-arima(k.new,order=c(1,0,0))$coef[1]
lx<-rep(0,100)
sigma2.l<-100
a.beta<-0.001
b.beta<-0.001
ak<-0.001
bk<-0.001

marg.var.k<-summary.glm(result.poisson.cons7.glm)$cov.unscaled[201:240,201:240]
cond.var.k<-solve(-solve(-summary.glm(result.poisson.cons7.glm)$cov.unscaled)[201:240,201:240])

system.time(rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg<-MCMC.rates.new.over.negbin.int.AR1.trunc.block(n=101000,burnin=1000,thin=10,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,sigma2.beta=sigma2.beta,sigma2.k=sigma2.k,
rho=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,a.beta=a.beta,b.beta=b.beta,ak=ak,bk=bk,sigma2.rho=100,prior.epsilon.gamma=TRUE,a.epsilon=0.0001,b.epsilon=0.0001,sigma.prop.k=(6.38^2/41*marg.var.k),sigma2.x=c(0.00001,0.00001,0.00001,0.00001,rep(0.00005,26),rep(0.00002,7),rep(0.00001,8),rep(0.00001,27),rep(0.000007,24),rep(0.00001,4)),sigma2.x.alpha=c(0.0015,0.003,0.003,rep(0.006,14),rep(0.003,21),rep(0.0008,62)),sigma2.prop.epsilon=0.05,sigma2.prop.rho=0.8))
theta.AR1.over.negbin.int.y0.new.trunc.block.marg<-cbind(rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$k.new,rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$beta.new,rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$alpha.new,log(rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$sigma2.k),log(rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$sigma2.beta),rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$rho.1,rates.MCMC.over.negbin.int.AR1.y0.new.trunc.block.marg$epsilon)

#Marginal likelihood of NBAPI-AR1 with naive priors

like.prior.loglinear.lca<-function(param,Dxt,Ext,A,T,t,lx,sigma2.l,sigma2.rho,ak,bk,a.beta,b.beta,a.epsilon,b.epsilon){#supply param=c(k,beta,alpha,log.sigma2.k,log.sigma2.beta,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
sigma2.k<-exp(param[2*A+T+1])
sigma2.beta<-exp(param[2*A+T+2])
rho<-param[2*A+T+3]
epsilon<-param[2*A+T+4]

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
Q<-t(R)%*%R
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-sigma2.k*D 
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE))+epsilon)	

sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+sum(dnorm(beta,mean=rep(0,A),sd=sqrt(sigma2.beta),log=TRUE))+dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)+
sum(dnorm(alpha,mean=lx,sd=sqrt(sigma2.l),log=TRUE))+log(dtruncnorm(rho,a=-1,b=1,mean=0,sd=sqrt(sigma2.rho)))+ak*log(bk)-lgamma(ak)-ak*log(sigma2.k)-bk/sigma2.k+a.beta*log(b.beta)-lgamma(a.beta)-a.beta*log(sigma2.beta)-b.beta/sigma2.beta+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon
}

sigma2.rho<-100
gamma.0<-c(0,0)
a.epsilon<-0.0001
b.epsilon<-0.0001

theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess<-theta.AR1.over.negbin.int.y0.new.trunc.block.marg
like.prior.loglinear.lca(param=theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[1,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,sigma2.rho=sigma2.rho,ak=ak,bk=bk,a.beta=a.beta,b.beta=b.beta,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.loglinear.group<-apply(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess,1,like.prior.loglinear.lca,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,sigma2.rho=sigma2.rho,ak=ak,bk=bk,a.beta=a.beta,b.beta=b.beta,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec<-apply(cbind(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,-c(1,2,245,246)],log(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,246])),2,mean)
covariance.loglinear.mat<-cov(cbind(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,-c(1,2,245,246)],log(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,246])))
mean.rho.loglinear<-mean(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,245])
variance.rho.loglinear<-var(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,245])

chol.cov.loglinear.group<-chol(covariance.loglinear.mat)
inverse.t.chol.cov.loglinear.group<-solve(t(chol.cov.loglinear.group))
 
find.k1<-function(x,T){
sum((1:(T-2))*x)
}
find.k2<-function(x,T){
-sum((2:(T-1))*x)
}

M<-matrix(rep(mean.loglinear.vec),nrow=243,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(243*10000),nrow=243,ncol=10000)
sample.bridge.loglinear.group<-M+t(chol.cov.loglinear.group)%*%Z
sample.bridge.loglinear.group<-t(sample.bridge.loglinear.group)
sample.rho.bridge.loglinear<-rtruncnorm(10000,a=-1,b=1,mean=mean.rho.loglinear,sd=sqrt(variance.rho.loglinear))
full.sample.bridge.loglinear.group<-cbind(apply(sample.bridge.loglinear.group[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group[,-243],sample.rho.bridge.loglinear,sample.bridge.loglinear.group[,243])
rm(M);rm(Z);rm(sample.rho.bridge.loglinear);rm(sample.bridge.loglinear.group);gc()
likelihood.bridge.loglinear.group<-apply(cbind(full.sample.bridge.loglinear.group[,-246],exp(full.sample.bridge.loglinear.group[,246])),1,like.prior.loglinear.lca,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,sigma2.rho=sigma2.rho,ak=ak,bk=bk,a.beta=a.beta,b.beta=b.beta,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
    
log.det.Jacobian.loglinear.group<-determinant(inverse.t.chol.cov.loglinear.group,logarithm=TRUE)$modulus

q2.loglinear.group<-apply(cbind(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,-c(1,2,246)],log(theta.AR1.over.negbin.int.y0.new.trunc.block.cond.hess[,246])),1,transformation.dmvnorm.loglinear,mean.vec=mean.loglinear.vec,rij=inverse.t.chol.cov.loglinear.group,log.det.Jacobian=log.det.Jacobian.loglinear.group,mean.rho=mean.rho.loglinear,variance.rho=variance.rho.loglinear,A=100,T=42)
q2.bridge.loglinear.group<-apply(full.sample.bridge.loglinear.group[,-c(1,2)],1,transformation.dmvnorm.loglinear,mean.vec=mean.loglinear.vec,rij=inverse.t.chol.cov.loglinear.group,log.det.Jacobian=log.det.Jacobian.loglinear.group,mean.rho=mean.rho.loglinear,variance.rho=variance.rho.loglinear,A=100,T=42)   
log.l.loglinear.group<-likelihood.loglinear.group-q2.loglinear.group
log.l.tilda.loglinear.group<-likelihood.bridge.loglinear.group-q2.bridge.loglinear.group

log.l.tilda.loglinear.group<-log.l.tilda.loglinear.group+24400
log.l.loglinear.group<-log.l.loglinear.group+24400
l.loglinear.group<-exp(log.l.loglinear.group)
l.tilda.loglinear.group<-exp(log.l.tilda.loglinear.group)
 
nc.loglinear.group<-bridge(initial=100,m=1000,sample1=theta.AR1.over.negbin.int.y0.new.trunc.block.hess,sample2=full.sample.bridge.loglinear.group,n1=10000,n2=10000,l=l.loglinear.group,l.tilda=l.tilda.loglinear.group) 
log(nc.loglinear.group)-24400 #approx -23769.77

######################
##Compatible prior specification
######################

##NBLC AR1

iteration.LC.poisson<-function(deaths,exposure,m,alpha.initial,beta.initial,kappa.initial,A,T){
alpha.new<-alpha.initial
beta.new<-beta.initial
kappa.new<-kappa.initial
kappa.new.matrix<-matrix(kappa.new,ncol=length(kappa.initial))
Deviance<-NULL

for (i in 1:m){

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

alpha.new<-alpha.new+apply((deaths-fitted.y),1,sum)/apply(fitted.y,1,sum)

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

kappa.new<-kappa.new+apply((deaths-fitted.y)*beta.new,2,sum)/apply(fitted.y*(beta.new^2),2,sum)
kappa.new<-kappa.new-mean(kappa.new)
kappa.new.matrix<-matrix(kappa.new,ncol=length(kappa.initial))

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

beta.new<-beta.new+apply(t(t(deaths-fitted.y)*kappa.new),1,sum)/apply(t(t(fitted.y)*kappa.new^2),1,sum)
beta.new<-beta.new/(sum(beta.new))

fitted.y<-exposure*exp(alpha.new+beta.new%*%kappa.new.matrix)

Deviance[i]<-sum(2*(deaths*log(deaths/fitted.y)-(deaths-fitted.y)))
}
list(Deviance,alpha.new,beta.new,kappa.new)
}

deaths.female<-EWdeath.female.mat.ex
result5.female<-iteration.LC.poisson(round(EWdeath.female.mat.ex),round(EWexpo.female.mat.ex),m=50,alpha.initial=apply((EWdeath.female.mat.ex/EWexpo.female.mat.ex),1,mean),beta.initial=rep(1/A,A),kappa.initial=rep(0,T))

MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k.new,alpha.new,beta.new,sigma2.beta,gamma.new,sigma2.k,rho.new,lx,sigma2.l,epsilon,a.beta,b.beta,ak,bk,a.rho,b.rho,gamma.0,sigma.mat.0,prior.epsilon.gamma=FALSE,a.epsilon,b.epsilon,prior.epsilon.normal=FALSE,miu.epsilon,sigma2.epsilon,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.epsilon,sigma2.prop.rho){

Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha.new)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=2*A+T+6)

X<-matrix(c(rep(1,T),t0:(t0+T-1)),byrow=F,ncol=2)
X.1<-matrix(c(rep(1,(T-1)),(t0+1):(t0+T-1)),byrow=F,ncol=2)
isigma.mat.0<-solve(sigma.mat.0)
I<-diag(1,nrow=(A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))
inverse<-solve(I-1/A*K)

J<-diag(rep(1,T))
J[1,]<-rep(1,T)
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho.new
}
}
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])

accept.epsilon<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)
accept.rho<-0
iter<-0
g<-seq(thin,n,by=thin)

for (m in 1:n){

S<-sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
k.star.vec<-rmvnorm.tol(1,mean=k.new[-1],sigma=sigma.prop.k,method="chol")
k.star.vec<-c(-sum(k.star.vec),k.star.vec)
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.star.vec)))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.star.vec[-1],mean=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k.new[-1],mean=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k.new<-k.star.vec
accept<-accept+1}

for (i in 2:A){
beta.star<-rnorm(1,beta.new[i],sqrt(sigma2.x[i]))
beta.star.vec<-beta.new;beta.star.vec[i]<-beta.star;beta.star.vec[1]<-1-sum(beta.star.vec[-1])
prob.accept.beta<-sum(Dxt[i,]*k.new*(beta.star-beta.new[i]))+sum(Dxt[1,]*k.new*(beta.star.vec[1]-beta.new[1]))-sum((Dxt[i,]+epsilon)*(log(Ext[i,]*exp(alpha.new[i]+beta.star*k.new)+epsilon)-log(Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new)+epsilon)))-
sum((Dxt[1,]+epsilon)*(log(Ext[1,]*exp(alpha.new[1]+beta.star.vec[1]*k.new)+epsilon)-log(Ext[1,]*exp(alpha.new[1]+beta.new[1]*k.new)+epsilon)))-(beta.star.vec[1]^2)/(2*sigma2.beta)-(beta.star^2)/(2*sigma2.beta)+(beta.new[1]^2)/(2*sigma2.beta)+(beta.new[i]^2)/(2*sigma2.beta)
if (log(runif(1))<=prob.accept.beta) {beta.new[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
beta.new[1]<-1-sum(beta.new[-1])
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new))
alpha.star<-rnorm(1,alpha.new[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta.new[i]*k.new))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.l)*(alpha.star-lx[i])^2-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.l)*(alpha.new[i]-lx[i])^2
if (log(runif(1))<=prob.accept.alpha) {alpha.new[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

rho.star<-rnorm(1,mean=rho.new,sd=sqrt(sigma2.prop.rho))
if ((rho.star>-1) & (rho.star<1)){
R.star<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R.star[i,j]<--rho.star
}
}
Q.star<-t(R.star)%*%R.star
B.star<-J%*%solve(Q.star)%*%t(J)
D.star<-B.star[2:T,2:T]-(B.star[2:T,1]/B.star[1,1])%*%t(B.star[1,2:T]) 
S.star<-sigma2.k*D.star
prob.accept.rho<-dmvnorm.tol(k.new[-1],mean=(X.1%*%gamma.new-B.star[2:T,1]/B.star[1,1]*sum(X%*%gamma.new)),sigma=S.star,log=TRUE)+(a.rho-1)*log(1+rho.star)+(b.rho-1)*log(1-rho.star)-dmvnorm.tol(k.new[-1],mean=(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)-(a.rho-1)*log(1+rho.new)-(b.rho-1)*log(1-rho.new)
if (log(runif(1))<=prob.accept.rho){
(rho.new<-rho.star)  
(Q<-Q.star) 
(R<-R.star) 
(B<-B.star) 
(D<-D.star) 
(S<-S.star) 
(accept.rho<-accept.rho+1)} 
}

#isigma2.k<-rtrunc(1,spec="gamma",shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))),a=0.1,b=Inf)
isigma2.k<-rgamma(1,shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))))
sigma2.k<-isigma2.k^-1

sigma2.beta<-0.005

S<-sigma2.k*D 
chol.S<-chol(S)
i.chol.S<-backsolve(chol.S,diag(rep(1,T-1)))
i.S<-i.chol.S%*%t(i.chol.S)

sigma.mat.star<-solve(isigma.mat.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X))
gamma.star<-sigma.mat.star%*%(isigma.mat.0%*%gamma.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%k.new[-1])
gamma.new<-c(rmvnorm.tol(1,mean=gamma.star,sigma=sigma.mat.star,method="chol"))

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if (prior.epsilon.normal){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<5000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.epsilon)*(epsilon.star-miu.epsilon)^2-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.epsilon)*(epsilon-miu.epsilon)^2+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if ((m>burnin) & (m %in% g)){
iter<-iter+1
result[iter,]<-c(k.new,beta.new,alpha.new,rho.new,sigma2.k,sigma2.beta,gamma.new,epsilon)
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],rho.1=result[,(2*A+T+1)],sigma2.k=result[,(2*A+T+2)],sigma2.beta=result[,(2*A+T+3)],gamma.new=result[,(2*A+T+4):(2*A+T+5)],epsilon=result[,(2*A+T+6)],accept,accept.beta,accept.alpha,accept.epsilon,accept.rho)
}

result5.female<-iteration.LC.poisson(round(EWdeath.female.mat.ex),round(EWexpo.female.mat.ex),m=50,alpha.initial=apply((EWdeath.female.mat.ex/EWexpo.female.mat.ex),1,mean),beta.initial=rep(1/A,A),kappa.initial=rep(0,T))
Ext<-EWexpo.female.mat.ex
Dxt<-EWdeath.female.mat.ex
k.new<-unlist(result5.female[[4]])
Y<-matrix(c(rep(1,length(k.new)),t0:(t0+length(k.new)-1)),byrow=F,ncol=2)
sigma.mat.0<-matrix(c(2000,0,0,2),nrow=2)
alpha.new<-unlist(result5.female[[2]])
beta.new<-unlist(result5.female[[3]])  
gamma.new<-c(0,0)
sigma2.k<-arima(k.new-Y%*%gamma.new,order=c(1,0,0))$sigma2
sigma2.beta<-0.005
rho.new<-arima(k.new-Y%*%gamma.new,order=c(1,0,0))$coef[1]
lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001 

iteration.methodB.LC.poisson<-function(deaths,exposure,m,beta.initial){
beta.new<-beta.initial
alpha.new<-NULL
k.new<-NULL
Deviance<-vector(length=m)
deaths.vec<-as.vector(deaths)
exposure.vec<-as.vector(exposure)
design.matrix.alpha<-kronecker(X=matrix(rep(1,T),ncol=1),Y=diag(rep(1,A)))

for (i in 1:m){
design.matrix.kappa<-kronecker(X=diag(rep(1,T)),Y=beta.new)
design.matrix.kappa<-design.matrix.kappa-design.matrix.kappa[,1]
design.matrix.kappa<-design.matrix.kappa[,-1]
design.matrix.1<-cbind(design.matrix.alpha,design.matrix.kappa)
fit<-glm.fit(x=design.matrix.1,y=deaths.vec,family=poisson(),offset=log(exposure.vec))
alpha.new<-fit$coef[1:A]
k.new<-fit$coef[-(1:A)]
k.new<-c(-sum(k.new),k.new)

design.matrix.beta<-kronecker(X=k.new,Y=diag(rep(1,A)))
design.matrix.beta<-design.matrix.beta-design.matrix.beta[,1]
design.matrix.beta<-design.matrix.beta[,-1]
design.matrix.2<-cbind(design.matrix.alpha,design.matrix.beta)
fit2<-glm.fit(x=design.matrix.2,y=deaths.vec,family=poisson(),offset=(log(exposure.vec)+1.54*c(kronecker(X=k.new,Y=c(1,rep(0,(A-1)))))))
alpha.new<-fit2$coef[1:A]
beta.new<-fit2$coef[-(1:A)]
beta.new<-c(1.54-sum(beta.new),beta.new)
Deviance[i]<-fit2$deviance
}
marg.var.k<-summary.glm(fit)$cov.unscaled[(A+1):(A+T-1),(A+1):(A+T-1)]
cond.var.k<-solve(-solve(-summary.glm(fit)$cov.unscaled)[(A+1):(A+T-1),(A+1):(A+T-1)])
list(alpha.new,beta.new,k.new,Deviance,marg.var.k,cond.var.k)
}

result.poisson.glm<-iteration.methodB.LC.poisson(deaths=round(Dxt),exposure=round(Ext),m=100,beta.initial=rep(0.01,A))

result.poisson.glm[[4]] #deviance=15349.54

##automated search for optimal acceptance rate
sigma.x.alpha<-rep(0.001,100)
sigma2.x<-rep(0.00001,100)
sigma2.x<-c(0.0000001,sigma2.x[-1])

repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior<-MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.k=((6.38^2)/41*result.poisson.glm[[5]]),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25))
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]<40) & (rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="Age",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[11]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)

repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior<-MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.k=((6.38^2)/41*result.poisson.glm[[5]]),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25))
sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]<40) & (rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]>20))==99) break
}

par(mfrow=c(1,2))
plot(sigma2.x,mgp=c(2.25,1,0),xlab="Age",ylab=expression(paste("Proposal Variance ",(1%*% 10^-7))),main=expression(sigma[beta[x]]^2),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior[[10]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)


##frequentist marginal variance of kappa as group proposal
 
system.time(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior<-MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior(n=5001000,burnin=1000,thin=500,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.k=((8.38^2)/41*result.poisson.glm[[5]]),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25))
gc()
theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior<-cbind(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$k.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$beta.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$alpha.new,log(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$sigma2.k),log(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$sigma2.beta),rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$gamma.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$rho.1,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior$epsilon)
gc()

par(mfrow=c(4,4))
plot(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243]),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,244]),xlab="iterations",ylab="",main="sigma2_beta",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,245],xlab="iterations",ylab="",main="gamma_1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,246],xlab="iterations",ylab="",main="gamma_2",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247],xlab="iterations",ylab="",main="rho",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248],xlab="iterations",ylab="",main="phi",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,143],xlab="iterations",ylab="",main="alpha_0",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,153],xlab="iterations",ylab="",main="alpha_50",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,242],xlab="iterations",ylab="",main="alpha_99",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,43],xlab="iterations",ylab="",main="beta_0",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,93],xlab="iterations",ylab="",main="beta_50",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,142],xlab="iterations",ylab="",main="beta_99",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,2],xlab="iterations",ylab="",main="kappa_1962",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,20],xlab="iterations",ylab="",main="kappa_1980",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,30],xlab="iterations",ylab="",main="kappa_1990",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,40],xlab="iterations",ylab="",main="kappa_2000",type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243])),main="sigma2_k",xlab="")
plot(density(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,244])),main="sigma2_beta",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,245]),main="gamma_1",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,246]),main="gamma_2",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247]),main="rho",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248]),main="phi",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,143]),main="alpha_0",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,193]),main="alpha_50",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,242]),main="alpha_99",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,43]),main="beta_0",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,93]),main="beta_50",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,142]),main="beta_99",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,2]),main="kappa_1962",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,20]),main="kappa_1980",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,30]),main="kappa_1990",xlab="")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,40]),main="kappa_2000",xlab="")

par(mfrow=c(4,4))
acf(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243]),ylab="",main="sigma2_k")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,245],ylab="",main="gamma_1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,246],ylab="",main="gamma_2")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247],ylab="",main="rho")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248],ylab="",main="phi")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,143],ylab="",main="alpha_0")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,153],ylab="",main="alpha_50")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,242],ylab="",main="alpha_99")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,43],ylab="",main="beta_0")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,93],ylab="",main="beta_50")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,142],ylab="",main="beta_99")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,2],ylab="",main="kappa_1962")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,20],ylab="",main="kappa_1980")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,30],ylab="",main="kappa_1990")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,40],ylab="",main="kappa_2000")

##NBLC RW

MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k.new,alpha.new,beta.new,sigma2.beta,gamma.new,sigma2.k,rho.new,lx,sigma2.l,epsilon,a.beta,b.beta,ak,bk,sigma2.rho,gamma.0,sigma.mat.0,prior.epsilon.gamma=FALSE,a.epsilon,b.epsilon,prior.epsilon.normal=FALSE,miu.epsilon,sigma2.epsilon,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.epsilon,sigma2.prop.rho){

Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha.new)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=2*A+T+6)

X<-matrix(c(rep(1,T),t0:(t0+T-1)),byrow=F,ncol=2)
X.1<-matrix(c(rep(1,(T-1)),(t0+1):(t0+T-1)),byrow=F,ncol=2)
isigma.mat.0<-solve(sigma.mat.0)
I<-diag(1,nrow=(A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))
inverse<-solve(I-1/A*K)

J<-diag(rep(1,T))
J[1,]<-rep(1,T)
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho.new
}
}
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])

accept.epsilon<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)
accept.rho<-0
iter<-0
g<-seq(thin,n,by=thin)

for (m in 1:n){

S<-sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
k.star.vec<-rmvnorm.tol(1,mean=k.new[-1],sigma=sigma.prop.k,method="chol")
k.star.vec<-c(-sum(k.star.vec),k.star.vec)
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.star.vec)))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.star.vec[-1],mean=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k.new[-1],mean=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k.new<-k.star.vec
accept<-accept+1}

for (i in 2:A){
beta.star<-rnorm(1,beta.new[i],sqrt(sigma2.x[i]))
beta.star.vec<-beta.new;beta.star.vec[i]<-beta.star;beta.star.vec[1]<-1-sum(beta.star.vec[-1])
prob.accept.beta<-sum(Dxt[i,]*k.new*(beta.star-beta.new[i]))+sum(Dxt[1,]*k.new*(beta.star.vec[1]-beta.new[1]))-sum((Dxt[i,]+epsilon)*(log(Ext[i,]*exp(alpha.new[i]+beta.star*k.new)+epsilon)-log(Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new)+epsilon)))-
sum((Dxt[1,]+epsilon)*(log(Ext[1,]*exp(alpha.new[1]+beta.star.vec[1]*k.new)+epsilon)-log(Ext[1,]*exp(alpha.new[1]+beta.new[1]*k.new)+epsilon)))-(beta.star.vec[1]^2)/(2*sigma2.beta)-(beta.star^2)/(2*sigma2.beta)+(beta.new[1]^2)/(2*sigma2.beta)+(beta.new[i]^2)/(2*sigma2.beta)
if (log(runif(1))<=prob.accept.beta) {beta.new[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
beta.new[1]<-1-sum(beta.new[-1])
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new))
alpha.star<-rnorm(1,alpha.new[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta.new[i]*k.new))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.l)*(alpha.star-lx[i])^2-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.l)*(alpha.new[i]-lx[i])^2
if (log(runif(1))<=prob.accept.alpha) {alpha.new[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

#isigma2.k<-rtrunc(1,spec="gamma",shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))),a=0.1,b=Inf)
isigma2.k<-rgamma(1,shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))))
sigma2.k<-isigma2.k^-1

sigma2.beta<-0.005

S<-sigma2.k*D 
chol.S<-chol(S)
i.chol.S<-backsolve(chol.S,diag(rep(1,T-1)))
i.S<-i.chol.S%*%t(i.chol.S)

sigma.mat.star<-solve(isigma.mat.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X))
gamma.star<-sigma.mat.star%*%(isigma.mat.0%*%gamma.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%k.new[-1])
gamma.new<-c(rmvnorm.tol(1,mean=gamma.star,sigma=sigma.mat.star,method="chol"))

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if (prior.epsilon.normal){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
if ((epsilon.star>1) & (epsilon.star<5000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.epsilon)*(epsilon.star-miu.epsilon)^2-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.epsilon)*(epsilon-miu.epsilon)^2+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
}
}

if ((m>burnin) & (m %in% g)){
iter<-iter+1
result[iter,]<-c(k.new,beta.new,alpha.new,rho.new,sigma2.k,sigma2.beta,gamma.new,epsilon)
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],rho.1=result[,(2*A+T+1)],sigma2.k=result[,(2*A+T+2)],sigma2.beta=result[,(2*A+T+3)],gamma.new=result[,(2*A+T+4):(2*A+T+5)],epsilon=result[,(2*A+T+6)],accept,accept.beta,accept.alpha,accept.epsilon,accept.rho)
}

##automated search for optimal acceptance rate
sigma.x.alpha<-rep(0.001,100)
sigma2.x<-rep(0.00001,100)
sigma2.x<-c(0.0000001,sigma2.x[-1])

repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior<-MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.k=((6.38^2)/41*result.poisson.glm[[5]]),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25))
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]<40) & (rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="Age",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[11]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)

repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior<-MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.k=((6.38^2)/41*result.poisson.glm[[5]]),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25))
sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]<40) & (rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]>20))==99) break
}

par(mfrow=c(1,2))
plot(sigma2.x,mgp=c(2.25,1,0),xlab="Age",ylab=expression(paste("Proposal Variance ",(1%*% 10^-7))),main=expression(sigma[beta[x]]^2),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior[[10]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)


system.time(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior<-MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior(n=5001000,burnin=1000,thin=500,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.k=((8.38^2)/41*result.poisson.glm[[5]]),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25))
gc()
theta.RW.over.negbin.int.group.marg.y0.normal.match.prior<-cbind(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$k.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$beta.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$alpha.new,log(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$sigma2.k),log(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$sigma2.beta),rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$gamma.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$rho.1,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior$epsilon)
gc()

par(mfrow=c(4,4))
plot(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,243]),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,244]),xlab="iterations",ylab="",main="sigma2_beta",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,245],xlab="iterations",ylab="",main="gamma_1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,246],xlab="iterations",ylab="",main="gamma_2",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,247],xlab="iterations",ylab="",main="rho",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,248],xlab="iterations",ylab="",main="phi",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,143],xlab="iterations",ylab="",main="alpha_0",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,153],xlab="iterations",ylab="",main="alpha_50",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,242],xlab="iterations",ylab="",main="alpha_99",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,43],xlab="iterations",ylab="",main="beta_0",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,93],xlab="iterations",ylab="",main="beta_50",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,142],xlab="iterations",ylab="",main="beta_99",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,2],xlab="iterations",ylab="",main="kappa_1962",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,20],xlab="iterations",ylab="",main="kappa_1980",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,30],xlab="iterations",ylab="",main="kappa_1990",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,40],xlab="iterations",ylab="",main="kappa_2000",type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,243])),main="sigma2_k",xlab="")
plot(density(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,244])),main="sigma2_beta",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,245]),main="gamma_1",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,246]),main="gamma_2",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,247]),main="rho",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,248]),main="phi",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,143]),main="alpha_0",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,193]),main="alpha_50",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,242]),main="alpha_99",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,43]),main="beta_0",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,93]),main="beta_50",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,142]),main="beta_99",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,2]),main="kappa_1962",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,20]),main="kappa_1980",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,30]),main="kappa_1990",xlab="")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,40]),main="kappa_2000",xlab="")


###############
##Laplace priors for NBAPI
##############

##NBAPI-AR1

MCMC.rates.new.over.negbin.int.AR1.notrunc.fast.group.matchprior<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k,alpha,beta,sigma2.k,rho,lx,lambda.alpha,lambda.beta,sigma2.l,lambda,epsilon,a.beta,b.beta,ak,bk,sigma2.rho,a.rho,b.rho,prior.epsilon.gamma=TRUE,a.epsilon,b.epsilon,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.rho,sigma2.prop.epsilon,sigma2.k.prop){
	
Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=(2*A+T+4))
loglikelihood.store<-vector(length=round((n-burnin)/thin))

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
Q<-t(R)%*%R
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])

accept.epsilon<-0
accept.rho<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)
accept.sigma2.k<-0
iter<-0
g<-seq(thin,n,by=thin)

for (m in 1:n){

S<-2*sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
k.star.vec<-rmvnorm.tol(1,mean=k[-c(1,2)],sigma=sigma.prop.k)
k.temp.star.vec<-k;k.temp.star.vec[3:T]<-k.star.vec
k.temp.star.vec[1]<-sum((1:(T-2))*k.temp.star.vec[3:T]);k.temp.star.vec[2]<--sum((2:(T-1))*k.temp.star.vec[3:T])
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k.temp.star.vec,A),nrow=A,ncol=T,byrow=TRUE)))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.temp.star.vec[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k<-k.temp.star.vec
accept<-accept+1}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k))
beta.star<-rnorm(1,beta[i],sqrt(sigma2.x[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta.star*t+k))
prob.accept.beta<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(beta.star,mu=0,lambda=lambda.beta[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(beta[i],mu=0,lambda=lambda.beta[i]))
if (log(runif(1))<=prob.accept.beta) {beta[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k))
alpha.star<-rnorm(1,alpha[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta[i]*t+k))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(alpha.star,mu=lx[i],lambda=lambda.alpha[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(alpha[i],mu=lx[i],lambda=lambda.alpha[i]))
if (log(runif(1))<=prob.accept.alpha) {alpha[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

rho.star<-rnorm(1,mean=rho,sd=sqrt(sigma2.prop.rho))
if ((rho.star>-1) & (rho.star<1)){
R.star<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R.star[i,j]<--rho.star
if ((i-j)==0) R.star[i,j]<-1
}
}
Q.star<-t(R.star)%*%R.star
C.star<-J%*%solve(Q.star)%*%t(J) 
D.star<-C.star[(3:T),(3:T)]-(C.star[(3:T),(1:2)])%*%solve(C.star[(1:2),(1:2)])%*%(C.star[(1:2),(3:T)])
S.star<-2*sigma2.k*D.star #always gives warning on symmetry, investigate and if necessary, create dmvnorm.tol to alter the tolerance. And why would S.star ever be unsymmetric? It isnt possible unless it is numerically unsymmetric.
#prob.accept.rho<-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)-(rho.star^2)/(2*sigma2.rho)-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)+(rho^2)/(2*sigma2.rho)
prob.accept.rho<-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)+(a.rho-1)*log(1+rho.star)+(b.rho-1)*log(1-rho.star)-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)-(a.rho-1)*log(1+rho)-(b.rho-1)*log(1-rho)
if (log(runif(1))<=prob.accept.rho){
(rho<-rho.star)  
(Q<-Q.star) 
(R<-R.star) 
(C<-C.star) 
(D<-D.star) 
(S<-S.star) 
(accept.rho<-accept.rho+1)}
}

sigma2.k.star<-exp(rnorm(1,mean=log(sigma2.k),sd=sqrt(sigma2.k.prop)))
S.star<-2*sigma2.k.star*D
prob.accept.sigma2.k<-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)+dexp(sigma2.k.star,rate=lambda,log=TRUE)-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)-dexp(sigma2.k,rate=lambda,log=TRUE)+log(sigma2.k.star)-log(sigma2.k)
if (log (runif(1))<=prob.accept.sigma2.k){
sigma2.k<-sigma2.k.star
S<-S.star
accept.sigma2.k<-accept.sigma2.k+1 
}

#lambda<-rtrunc(1,spec="gamma",a=(0.1*2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1))),b=Inf,shape=(ak+1),rate=(bk/(2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1)))+sigma2.k))
#lambda<-rtrunc(1,spec="gamma",a=0.0001,b=Inf,shape=(ak+1),rate=(bk/0.001+sigma2.k))
lambda<-rgamma(1,shape=(ak+1),rate=(bk/400+sigma2.k))

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

p.nbinom<-epsilon/(epsilon+exp(matrix(rep(alpha,T),nrow=A,ncol=T)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
loglikelihood<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))

if ((m>burnin) & (m %in% g)){
iter<-iter+1
result[iter,]<-c(k,beta,alpha,rho,sigma2.k,lambda,epsilon)
loglikelihood.store[iter]<-loglikelihood
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],rho.1=result[,(2*A+T+1)],sigma2.k=result[,(2*A+T+2)],lambda=result[,(2*A+T+3)],epsilon=result[,(2*A+T+4)],loglikelihood=loglikelihood.store[g],accept,accept.beta,accept.alpha,accept.epsilon,accept.rho,accept.sigma2.k)
}

k.new<-c(sum((1:40)*result.poisson.cons7.glm$coef[201:240]),-sum((2:41)*result.poisson.cons7.glm$coef[201:240]),result.poisson.cons7.glm$coef[201:240])
alpha.new<-result.poisson.cons7.glm$coef[1:100]
beta.new<-result.poisson.cons7.glm$coef[101:200]
sigma2.k<-arima(k.new,order=c(1,0,0))$sigma2
rho.new<-arima(k.new,order=c(1,0,0))$coef[1]
lx<-rep(-5,100)
ak<-1
bk<-0.0001
lambda.alpha<-rep(2.6,A)
lambda.beta<-rep(0.03,A)

hess.cond.kappa.loglinear.matchprior<-function(x,A,T,Dxt,Ext,t0,alpha,beta,rho,sigma2.k.prime,epsilon){#x=c(k_3,k_4,...,k_T)
k<-c(sum((1:(T-2))*x),-sum((2:(T-1))*x),x)
t<-t0:(t0+T-1)
I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)
R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
Q<-t(R)%*%R
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
i.D<-solve(D)

hess<-matrix(0,nrow=T-2,ncol=T-2)
for (i in 3:T){
for (j in 3:T){
if ((i-j)==0) {hess[i-2,j-2]<--sum(((Dxt[,i]+epsilon)*epsilon*Ext[,i]*exp(alpha+beta*t[i]+k[i]))/((Ext[,i]*exp(alpha+beta*t[i]+k[i])+epsilon)^2))-((i-2)^2)*sum(((Dxt[,1]+epsilon)*epsilon*Ext[,1]*exp(alpha+beta*t[1]+k[1]))/((Ext[,1]*exp(alpha+beta*t[1]+k[1])+epsilon)^2))-((i-1)^2)*sum(((Dxt[,2]+epsilon)*epsilon*Ext[,2]*exp(alpha+beta*t[2]+k[2]))/((Ext[,2]*exp(alpha+beta*t[2]+k[2])+epsilon)^2))-1/(2*exp(sigma2.k.prime))*i.D[i-2,i-2]}
else {hess[i-2,j-2]<--(i-2)*(j-2)*sum(((Dxt[,1]+epsilon)*epsilon*Ext[,1]*exp(alpha+beta*t[1]+k[1]))/((Ext[,1]*exp(alpha+beta*t[1]+k[1])+epsilon)^2))-(i-1)*(j-1)*sum(((Dxt[,2]+epsilon)*epsilon*Ext[,2]*exp(alpha+beta*t[2]+k[2]))/((Ext[,2]*exp(alpha+beta*t[2]+k[2])+epsilon)^2))-1/(2*exp(sigma2.k.prime))*i.D[i-2,j-2]}
}
}
hess
}

median.sigma2.k<-median(exp(theta.AR1.over.negbin.int.y0.new.trunc.fast.group.marg.matchprior[,243])) #0.0001982217
median.rho<-median((theta.AR1.over.negbin.int.y0.new.trunc.fast.group.marg.matchprior[,245])) #0.6143724
median.epsilon<-median((theta.AR1.over.negbin.int.y0.new.trunc.fast.group.marg.matchprior[,246])) #713.7118
hess.cond.kappa.matchprior<-hess.cond.kappa.loglinear.matchprior(x=result.poisson.cons7.glm$coef[201:240],A=100,T=42,Dxt=round(Dxt),Ext=round(Ext),t0=-21,alpha=result.poisson.cons7.glm$coef[1:100],beta=result.poisson.cons7.glm$coef[101:200],rho=0.6143724,sigma2.k.prime=log(0.0001982217),epsilon=713.7118)
eigen(-hess.cond.kappa.matchprior)$values
eigen(solve(-hess.cond.kappa.matchprior))$values
negative.i.hess.cond.kappa.matchprior<-solve(-hess.cond.kappa.matchprior)

##automated search for optimal acceptance rate
sigma.x.alpha<-rep(0.001,100)
sigma2.x<-rep(0.0001,100)

repeat{
system.time(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior<-MCMC.rates.new.over.negbin.int.AR1.notrunc.fast.group.matchprior(n=100,burnin=0,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=-21,t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,lambda=1,sigma2.k=sigma2.k,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
rho=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,sigma2.rho=100,a.rho=3,b.rho=2,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,sigma.prop.k=((2.38^2)/41*negative.i.hess.cond.kappa.matchprior),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.10,sigma2.prop.rho=0.5,sigma2.k.prop=1))
sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]<20]/2
if (sum((rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]<40) & (rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="x",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]/100,ylim=c(0,1),xlab="x",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)

repeat{
system.time(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior<-MCMC.rates.new.over.negbin.int.AR1.notrunc.fast.group.matchprior(n=100,burnin=00,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=-21,t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,lambda=1,sigma2.k=sigma2.k,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
rho=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,sigma2.rho=100,a.rho=3,b.rho=2,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,sigma.prop.k=((2.38^2)/41*negative.i.hess.cond.kappa.matchprior),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.10,sigma2.prop.rho=0.5,sigma2.k.prop=1))
sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]<20]/2
if (sum((rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]<40) & (rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]>20))==99) break
}
par(mfrow=c(1,2))
plot(sigma2.x*1e5,mgp=c(2.25,1,0),xlab="x",ylab=expression(paste("Proposal Variance ",(1%*% 10^-5))),main=expression(sigma[beta[x]]^2),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]/100,ylim=c(0,1),xlab="x",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)

system.time(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior<-MCMC.rates.new.over.negbin.int.AR1.notrunc.fast.group.matchprior(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=-21,t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,lambda=1,sigma2.k=sigma2.k,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
rho=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,sigma2.rho=100,a.rho=3,b.rho=2,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,sigma.prop.k=((2.38^2)/41*negative.i.hess.cond.kappa.matchprior),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.10,sigma2.prop.rho=0.5,sigma2.k.prop=1))
theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior<-cbind(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$k.new,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$beta.new,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$alpha.new,log(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$sigma2.k),log(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$lambda),rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$rho.1,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.fast.group.cond.hess.matchprior$epsilon)
gc()

par(mfrow=c(4,4))
plot(exp(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243]),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(exp(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244]),xlab="iterations",ylab="",main="lambda",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245],xlab="iterations",ylab="",main="rho",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],xlab="iterations",ylab="",main="epsilon",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143],xlab="iterations",ylab="",main="alpha_1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,193],xlab="iterations",ylab="",main="alpha_51",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,242],xlab="iterations",ylab="",main="alpha_100",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43],xlab="iterations",ylab="",main="beta_1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,93],xlab="iterations",ylab="",main="beta_51",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,142],xlab="iterations",ylab="",main="beta_100",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1],xlab="iterations",ylab="",main=expression(kappa[1]),type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,2],xlab="iterations",ylab="",main=expression(kappa[2]),type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,10],xlab="iterations",ylab="",main=expression(kappa[10]),type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,20],xlab="iterations",ylab="",main=expression(kappa[20]),type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,30],xlab="iterations",ylab="",main=expression(kappa[30]),type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,42],xlab="iterations",ylab="",main=expression(kappa[42]),type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243]),n=50000),main="sigma2_k")
plot(density(exp(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244]),n=50000),main="lambda")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245],n=50000),main="rho")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],n=50000),main="epsilon")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143],n=50000),main="alpha_1")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,193],n=50000),main="alpha_51")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,242],n=50000),main="alpha_100")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43],n=50000),main="beta_1")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,93],n=50000),main="beta_51")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,142],n=50000),main="beta_100")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1],n=50000),main="kappa_1")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,2],n=50000),main="kappa_2")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,20],n=50000),main="kappa_20")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,30],n=50000),main="kappa_30")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,40],n=50000),main="kappa_40")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,42],n=50000),main="kappa_42")

##NBAPI-RW

MCMC.rates.new.over.negbin.int.RW.notrunc.fast.group.matchprior<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k,alpha,beta,sigma2.k,rho,lx,lambda.alpha,lambda.beta,sigma2.l,lambda,epsilon,a.beta,b.beta,ak,bk,prior.epsilon.gamma=TRUE,a.epsilon,b.epsilon,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.rho,sigma2.prop.epsilon,sigma2.k.prop){
	
Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=(2*A+T+4))
loglikelihood.store<-vector(length=round((n-burnin)/thin))

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
i.R<-forwardsolve(R,diag(rep(1,T)))
i.Q<-i.R%*%t(i.R)
C<-J%*%i.Q%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])

accept.epsilon<-0
accept.rho<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)
accept.sigma2.k<-0
iter<-0
g<-seq(thin,n,by=thin)

for (m in 1:n){

S<-2*sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
k.star.vec<-rmvnorm.tol(1,mean=k[-c(1,2)],sigma=sigma.prop.k)
k.temp.star.vec<-k;k.temp.star.vec[3:T]<-k.star.vec
k.temp.star.vec[1]<-sum((1:(T-2))*k.temp.star.vec[3:T]);k.temp.star.vec[2]<--sum((2:(T-1))*k.temp.star.vec[3:T])
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k.temp.star.vec,A),nrow=A,ncol=T,byrow=TRUE)))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.temp.star.vec[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k<-k.temp.star.vec
accept<-accept+1}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k))
beta.star<-rnorm(1,beta[i],sqrt(sigma2.x[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta.star*t+k))
prob.accept.beta<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(beta.star,mu=0,lambda=lambda.beta[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(beta[i],mu=0,lambda=lambda.beta[i]))
if (log(runif(1))<=prob.accept.beta) {beta[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k))
alpha.star<-rnorm(1,alpha[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta[i]*t+k))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(alpha.star,mu=lx[i],lambda=lambda.alpha[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(alpha[i],mu=lx[i],lambda=lambda.alpha[i]))
if (log(runif(1))<=prob.accept.alpha) {alpha[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

sigma2.k.star<-exp(rnorm(1,mean=log(sigma2.k),sd=sqrt(sigma2.k.prop)))
S.star<-2*sigma2.k.star*D
prob.accept.sigma2.k<-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)+dexp(sigma2.k.star,rate=lambda,log=TRUE)-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)-dexp(sigma2.k,rate=lambda,log=TRUE)+log(sigma2.k.star)-log(sigma2.k)
if (log (runif(1))<=prob.accept.sigma2.k){
sigma2.k<-sigma2.k.star
S<-S.star
accept.sigma2.k<-accept.sigma2.k+1 
}

#lambda<-rtrunc(1,spec="gamma",a=(0.1*2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1))),b=Inf,shape=(ak+1),rate=(bk/(2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1)))+sigma2.k))
#lambda<-rtrunc(1,spec="gamma",a=0.0001,b=Inf,shape=(ak+1),rate=(bk/0.001+sigma2.k))
lambda<-rgamma(1,shape=(ak+1),rate=(bk/400+sigma2.k))

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

p.nbinom<-epsilon/(epsilon+exp(matrix(rep(alpha,T),nrow=A,ncol=T)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)))
loglikelihood<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))

if ((m>burnin) & (m %in% g)){
iter<-iter+1
result[iter,]<-c(k,beta,alpha,rho,sigma2.k,lambda,epsilon)
loglikelihood.store[iter]<-loglikelihood
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],rho.1=result[,(2*A+T+1)],sigma2.k=result[,(2*A+T+2)],lambda=result[,(2*A+T+3)],epsilon=result[,(2*A+T+4)],loglikelihood=loglikelihood.store[g],accept,accept.beta,accept.alpha,accept.epsilon,accept.rho,accept.sigma2.k)
}

k.new<-c(sum((1:40)*result.poisson.cons7.glm$coef[201:240]),-sum((2:41)*result.poisson.cons7.glm$coef[201:240]),result.poisson.cons7.glm$coef[201:240])
alpha.new<-result.poisson.cons7.glm$coef[1:100]
beta.new<-result.poisson.cons7.glm$coef[101:200]
sigma2.k<-arima(k.new,order=c(1,0,0))$sigma2
rho.new<-arima(k.new,order=c(1,0,0))$coef[1]
lx<-rep(-5,100)
ak<-1
bk<-0.0001
lambda.alpha<-rep(2.6,100)
lambda.beta<-rep(0.03,100)

##automated search for optimal acceptance rate
sigma.x.alpha<-rep(0.001,100)
repeat{
system.time(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior<-MCMC.rates.new.over.negbin.int.RW.notrunc.fast.group.matchprior(n=100,burnin=0,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=-21,t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,lambda=1,sigma2.k=sigma2.k,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
rho=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,sigma.prop.k=((2.38^2)/41*negative.i.hess.cond.kappa.matchprior),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.10,sigma2.prop.rho=0.5,sigma2.k.prop=1))
sigma.x.alpha[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]<20]/2
if (sum((rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]<40) & (rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="Age",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[11]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)

sigma2.x<-rep(0.0001,100)
repeat{
system.time(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior<-MCMC.rates.new.over.negbin.int.RW.notrunc.fast.group.matchprior(n=100,burnin=00,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=-21,t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,lambda=1,sigma2.k=sigma2.k,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
rho=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,sigma.prop.k=((2.38^2)/41*negative.i.hess.cond.kappa.matchprior),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.10,sigma2.prop.rho=0.5,sigma2.k.prop=1))
sigma2.x[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]<20]/2
if (sum((rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]<40) & (rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]>20))==99) break
}
par(mfrow=c(1,2))
plot(sigma2.x*1e5,mgp=c(2.25,1,0),xlab="Age",ylab=expression(paste("Proposal Variance ",(1%*% 10^-5))),main=expression(sigma[beta[x]]^2),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior[[10]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)

system.time(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior<-MCMC.rates.new.over.negbin.int.RW.notrunc.fast.group.matchprior(n=5001000,burnin=1000,thin=500,exposures=round(Ext),deaths=round(Dxt),t0=-21,t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,lambda=1,sigma2.k=sigma2.k,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
rho=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,prior.epsilon.gamma=TRUE,a.epsilon=25,b.epsilon=0.05,sigma.prop.k=((2.38^2)/41*negative.i.hess.cond.kappa.matchprior),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.10,sigma2.prop.rho=0.5,sigma2.k.prop=1))
theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior<-cbind(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$k.new,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$beta.new,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$alpha.new,log(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$sigma2.k),log(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$lambda),rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$rho.1,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.fast.group.cond.hess.matchprior$epsilon)
gc()

par(mfrow=c(4,4))
plot(exp(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243]),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(exp(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244]),xlab="iterations",ylab="",main="lambda",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245],xlab="iterations",ylab="",main="rho",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],xlab="iterations",ylab="",main="epsilon",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143],xlab="iterations",ylab="",main="alpha_1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,193],xlab="iterations",ylab="",main="alpha_51",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,242],xlab="iterations",ylab="",main="alpha_100",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43],xlab="iterations",ylab="",main="beta_1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,93],xlab="iterations",ylab="",main="beta_51",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,142],xlab="iterations",ylab="",main="beta_100",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1],xlab="iterations",ylab="",main=expression(kappa[1]),type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,2],xlab="iterations",ylab="",main=expression(kappa[2]),type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,10],xlab="iterations",ylab="",main=expression(kappa[10]),type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,20],xlab="iterations",ylab="",main=expression(kappa[20]),type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,30],xlab="iterations",ylab="",main=expression(kappa[30]),type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,42],xlab="iterations",ylab="",main=expression(kappa[42]),type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243]),n=50000),main="sigma2_k")
plot(density(exp(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244]),n=50000),main="lambda")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245],n=50000),main="rho")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],n=50000),main="epsilon")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143],n=50000),main="alpha_1")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,193],n=50000),main="alpha_51")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,242],n=50000),main="alpha_100")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43],n=50000),main="beta_1")
plot(density(theta.RW.over.negbin.int.y0.new.nnotrunc.fast.group.cond.hess.matchprior[,93],n=50000),main="beta_51")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,142],n=50000),main="beta_100")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1],n=50000),main="kappa_1")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,2],n=50000),main="kappa_2")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,20],n=50000),main="kappa_20")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,30],n=50000),main="kappa_30")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,40],n=50000),main="kappa_40")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,42],n=50000),main="kappa_42")



##################################
##classical poisson LC with cohort with constraints: sum(beta)=1,sum(kt=0),sum(cohort)=sum(c*cohort)=sum(c^2*cohort)=0 
##################################

iteration.methodB.LC.cohort.poisson.cons5<-function(deaths,exposure,m,beta.initial,C){
beta.new<-beta.initial
alpha.new<-NULL
k.new<-NULL
Deviance<-vector(length=m)
deaths.vec<-as.vector(deaths)
exposure.vec<-as.vector(exposure)
design.matrix.alpha<-kronecker(X=matrix(rep(1,42),ncol=1),Y=diag(rep(1,100)))

cohort.dummy<-matrix(NA,nrow=A*T,ncol=length(C))
for (k in C){
mat.temp<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
if ((j-i)==k) mat.temp[i,j]<-1
}}
cohort.dummy[,k+A]<-as.vector(mat.temp)
}

for (k in (C+A)[-(1:3)]){
cohort.dummy[,k]<-cohort.dummy[,k]-0.5*(k-2)*(k-3)*cohort.dummy[,1]
}
for (k in (C+A)[-(1:3)]){
cohort.dummy[,k]<-cohort.dummy[,k]+(k-1)*(k-3)*cohort.dummy[,2]
}
for (k in (C+A)[-(1:3)]){
cohort.dummy[,k]<-cohort.dummy[,k]-0.5*(k-1)*(k-2)*cohort.dummy[,3]
}
cohort.dummy<-cohort.dummy[,-c(1:3)]

for (i in 1:m){
design.matrix.kappa<-kronecker(X=diag(rep(1,42)),Y=beta.new)
design.matrix.kappa<-design.matrix.kappa-design.matrix.kappa[,1]
design.matrix.kappa<-design.matrix.kappa[,-1]
design.matrix.1<-cbind(design.matrix.alpha,design.matrix.kappa,cohort.dummy)
fit<-glm.fit(x=design.matrix.1,y=deaths.vec,family=poisson(),offset=log(exposure.vec))
alpha.new<-fit$coef[1:100]
k.new<-fit$coef[101:141]
k.new<-c(-sum(k.new),k.new)
cohort.new<-fit$coef[-(1:141)]
cohort.new<-c(-0.5*sum((2:(length(C)-2))*(1:(length(C)-3))*cohort.new),sum((1:(length(C)-3))*(3:(length(C)-1))*cohort.new),-0.5*sum((2:(length(C)-2))*(3:(length(C)-1))*cohort.new),cohort.new)

design.matrix.beta<-kronecker(X=k.new,Y=diag(rep(1,100)))
design.matrix.beta<-design.matrix.beta-design.matrix.beta[,1]
design.matrix.beta<-design.matrix.beta[,-1]
design.matrix.2<-cbind(design.matrix.alpha,design.matrix.beta,cohort.dummy)
fit2<-glm.fit(x=design.matrix.2,y=deaths.vec,family=poisson(),offset=(log(exposure.vec)+1*c(kronecker(X=k.new,Y=c(1,rep(0,99))))))
alpha.new<-fit2$coef[1:100]
beta.new<-fit2$coef[101:199]
beta.new<-c(1-sum(beta.new),beta.new)
cohort.new<-fit2$coef[-(1:199)]
cohort.new<-c(-0.5*sum((2:(length(C)-2))*(1:(length(C)-3))*cohort.new),sum((1:(length(C)-3))*(3:(length(C)-1))*cohort.new),-0.5*sum((2:(length(C)-2))*(3:(length(C)-1))*cohort.new),cohort.new)
Deviance[i]<-fit2$deviance
}
marg.var.k<-summary.glm(fit)$cov.unscaled[101:141,101:141]
#cond.var.k<-solve(-solve(-summary.glm(fit)$cov.unscaled)[101:141,101:141])
marg.var.cohort<-summary.glm(fit)$cov.unscaled[142:279,142:279]
#cond.var.cohort<-solve(-solve(-summary.glm(fit)$cov.unscaled)[142:279,142:279])
list(alpha.new,beta.new,k.new,cohort.new,Deviance,marg.var.k,marg.var.cohort)
}

C<-(1-A):(T-1)
system.time(result.poisson.LC.cohort.cons5.glm<-iteration.methodB.LC.cohort.poisson.cons5(deaths=round(Dxt),exposure=round(Ext),m=100,beta.initial=rep(0.01,100),C=C))

##############
##NBLCC-AR1 with grouping on kappa and with compatible priors etc
##Constraints:sum(beta)=1,sum(kappa)=0,sum(gamma)=sum(c*gamma)=sum(c^2*gamma)=0
##UNIFORM(0,0.1) PRIOR ON SIGMA.GAMMA
##############

MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior.cohort.unif<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k.new,alpha.new,beta.new,cohort,sigma2.cohort,rho.cohort,sigma2.rho.cohort,sigma2.beta,gamma.new,sigma2.k,rho.new,lx,sigma2.l,epsilon,a.beta,b.beta,ak,bk,a.rho,b.rho,gamma.0,sigma.mat.0,prior.epsilon.gamma=FALSE,a.epsilon,b.epsilon,prior.epsilon.normal=FALSE,miu.epsilon,sigma2.epsilon,a.cohort,b.cohort,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.epsilon,sigma2.prop.rho,sigma.prop.cohort,sigma2.prop.rho.cohort,sigma2.prop.sigma2.cohort){

Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha.new)
C<-length(cohort)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=3*A+2*T+7)

X<-matrix(c(rep(1,T),t0:(t0+T-1)),byrow=F,ncol=2)
X.1<-matrix(c(rep(1,(T-1)),(t0+1):(t0+T-1)),byrow=F,ncol=2)
isigma.mat.0<-solve(sigma.mat.0)
I<-diag(1,nrow=(A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))
inverse<-solve(I-1/A*K)

J<-diag(rep(1,T))
J[1,]<-rep(1/sqrt(T),T)
R<-diag(rep(1,T))
R[1,1]<-sqrt(1-rho.new^2)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho.new
}
}
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])

J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1
I.cohort<-diag(rep(1,C))

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic
S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}


accept.epsilon<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)
accept.cohort<-0
accept.rho<-0
accept.rho.cohort<-0
accept.sigma2.cohort<-0
iter<-0
g<-seq(thin,n,by=thin)

for (m in 1:n){

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
cohort.star.vec<-c(rmvnorm.manual(1,mean.vec=cohort[-c(1,72,C)],sigma=sigma.prop.cohort))
cohort.temp.star.vec<-cohort;cohort.temp.star.vec[-c(1,72,C)]<-cohort.star.vec
cohort.temp.star.vec[1]<-1/(71*140)*sum(c((-70):(-1),1:68)*c(139:70,68:1)*cohort.star.vec);cohort.temp.star.vec[72]<-1/(69*71)*sum(-c(139:70,68:1)*c(1:70,72:139)*cohort.star.vec);cohort.temp.star.vec[C]<-1/(69*140)*sum(c(1:70,72:139)*c(70:1,(-1):(-68))*cohort.star.vec)
cohort.star.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.star.mat[i,j]<-cohort.temp.star.vec[j-i+A]
}
}
p.nbinom.star.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.star.mat))
prob.accept.cohort<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.star.mat,log=TRUE))+dmvnorm.manual(cohort.temp.star.vec[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)
if (log(runif(1))<=prob.accept.cohort) {cohort<-cohort.temp.star.vec
cohort.mat<-cohort.star.mat
accept.cohort<-accept.cohort+1
}	



S<-sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
k.star.vec<-rmvnorm.tol(1,mean=k.new[-1],sigma=sigma.prop.k,method="chol")
k.star.vec<-c(-sum(k.star.vec),k.star.vec)
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.star.vec)+cohort.mat))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.manual(k.star.vec[-1],mean.vec=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.manual(k.new[-1],mean.vec=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k.new<-k.star.vec
accept<-accept+1}

for (i in 2:A){
beta.star<-rnorm(1,beta.new[i],sqrt(sigma2.x[i]))
beta.star.vec<-beta.new;beta.star.vec[i]<-beta.star;beta.star.vec[1]<-1-sum(beta.star.vec[-1])
prob.accept.beta<-sum(Dxt[i,]*k.new*(beta.star-beta.new[i]))+sum(Dxt[1,]*k.new*(beta.star.vec[1]-beta.new[1]))-sum((Dxt[i,]+epsilon)*(log(Ext[i,]*exp(alpha.new[i]+beta.star*k.new+cohort.mat[i,])+epsilon)-log(Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new+cohort.mat[i,])+epsilon)))-
sum((Dxt[1,]+epsilon)*(log(Ext[1,]*exp(alpha.new[1]+beta.star.vec[1]*k.new+cohort.mat[1,])+epsilon)-log(Ext[1,]*exp(alpha.new[1]+beta.new[1]*k.new+cohort.mat[1,])+epsilon)))-(beta.star.vec[1]^2)/(2*sigma2.beta)-(beta.star^2)/(2*sigma2.beta)+(beta.new[1]^2)/(2*sigma2.beta)+(beta.new[i]^2)/(2*sigma2.beta)
if (log(runif(1))<=prob.accept.beta) {beta.new[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
beta.new[1]<-1-sum(beta.new[-1])
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new+cohort.mat[i,]))
alpha.star<-rnorm(1,alpha.new[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta.new[i]*k.new+cohort.mat[i,]))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.l)*(alpha.star-lx[i])^2-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.l)*(alpha.new[i]-lx[i])^2
if (log(runif(1))<=prob.accept.alpha) {alpha.new[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

repeat{
rho.cohort.star<-rtruncnorm(1,a=-1,b=1,mean=rho.cohort,sd=sqrt(sigma2.prop.rho.cohort))
R.cohort.star<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort.star[i,j]<--(1+rho.cohort.star)
if ((i-j)==2) R.cohort.star[i,j]<-rho.cohort.star
}
}
R.cohort.star[2,1]<--1*sqrt(1-rho.cohort.star^2)
R.cohort.star[2,2]<-sqrt(1-rho.cohort.star^2)
R.cohort.star[1,1]<-1/100 
i.R.cohort.star<-forwardsolve(R.cohort.star,I.cohort)
i.Q.cohort.star<-i.R.cohort.star%*%t(i.R.cohort.star)
B.cohort.star<-J.cohort%*%i.Q.cohort.star%*%t(J.cohort)
ic.star<-(B.cohort.star[(4:C),(1:3)])%*%solve(B.cohort.star[(1:3),(1:3)])%*%(B.cohort.star[(1:3),(4:C)])
D.cohort.star<-B.cohort.star[(4:C),(4:C)]-ic.star
S.cohort.star<-sigma2.cohort*D.cohort.star
S.cohort.star<-0.5*(S.cohort.star+t(S.cohort.star))
if (prod(sign(eigen(S.cohort.star)$val))==1){
break}
}
 
prob.accept.rho.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dnorm(rho.cohort.star,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)
if (log(runif(1))<=prob.accept.rho.cohort){
(rho.cohort<-rho.cohort.star)
(R.cohort<-R.cohort.star)
(B.cohort<-B.cohort.star)
(D.cohort<-D.cohort.star)
(S.cohort<-S.cohort.star)
(accept.rho.cohort<-accept.rho.cohort+1)
}

chol.D.cohort<-chol(D.cohort)
i.chol.D.cohort<-backsolve(chol.D.cohort,diag(rep(1,C-3)))
i.D.cohort<-i.chol.D.cohort%*%t(i.chol.D.cohort)
#sigma2.cohort<-1/rgamma(1,a.cohort+(C-3)/2,b.cohort+0.5*t(cohort[-c(1,72,C)])%*%i.D.cohort%*%cohort[-c(1,72,C)])

sigma2.cohort.star<-(rnorm(1,sqrt(sigma2.cohort),sqrt(sigma2.prop.sigma2.cohort)))^2
if (sigma2.cohort.star<0.01){
S.cohort.star<-sigma2.cohort.star*D.cohort
prob.accept.sigma2.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dunif(sqrt(sigma2.cohort.star),max=0.1,log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dunif(sqrt(sigma2.cohort),max=0.1,log=TRUE)
if (log(runif(1))<=prob.accept.sigma2.cohort){
sigma2.cohort<-sigma2.cohort.star;S.cohort<-S.cohort.star;accept.sigma2.cohort<-accept.sigma2.cohort+1
}
}

S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))

rho.star<-rnorm(1,mean=rho.new,sd=sqrt(sigma2.prop.rho))
if ((rho.star>-1) & (rho.star<1)){
R.star<-diag(rep(1,T))
R.star[1,1]<-sqrt(1-rho.star^2)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R.star[i,j]<--rho.star
}
}
Q.star<-t(R.star)%*%R.star
B.star<-J%*%solve(Q.star)%*%t(J)
D.star<-B.star[2:T,2:T]-(B.star[2:T,1]/B.star[1,1])%*%t(B.star[1,2:T]) 
S.star<-sigma2.k*D.star
prob.accept.rho<-dmvnorm.manual(k.new[-1],mean.vec=(X.1%*%gamma.new-B.star[2:T,1]/B.star[1,1]*sum(X%*%gamma.new)),sigma=S.star,log=TRUE)+(a.rho-1)*log(1+rho.star)+(b.rho-1)*log(1-rho.star)-dmvnorm.manual(k.new[-1],mean.vec=(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)-(a.rho-1)*log(1+rho.new)-(b.rho-1)*log(1-rho.new)
if (log(runif(1))<=prob.accept.rho){
(rho.new<-rho.star)  
(Q<-Q.star) 
(R<-R.star) 
(B<-B.star) 
(D<-D.star) 
(S<-S.star) 
(accept.rho<-accept.rho+1)} 
}

#isigma2.k<-rtrunc(1,spec="gamma",shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))),a=0.1,b=Inf)
isigma2.k<-rgamma(1,shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))))

sigma2.k<-isigma2.k^-1

sigma2.beta<-0.005

S<-sigma2.k*D 
chol.S<-chol(S)
i.chol.S<-backsolve(chol.S,diag(rep(1,T-1)))
i.S<-i.chol.S%*%t(i.chol.S)

sigma.mat.star<-solve(isigma.mat.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X))
gamma.star<-sigma.mat.star%*%(isigma.mat.0%*%gamma.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%k.new[-1])
gamma.new<-c(rmvnorm.manual(1,mean.vec=gamma.star,sigma=sigma.mat.star))

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if (prior.epsilon.normal){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<5000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.epsilon)*(epsilon.star-miu.epsilon)^2-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.epsilon)*(epsilon-miu.epsilon)^2+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if ((m>burnin) & (m %in% g)){
iter<-iter+1
result[iter,]<-c(k.new,beta.new,alpha.new,cohort,rho.new,sigma2.k,sigma2.beta,gamma.new,rho.cohort,sigma2.cohort,epsilon)
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],cohort=result[,(2*A+T+1):(3*A+2*T-1)],rho.1=result[,(3*A+2*T)],sigma2.k=result[,(3*A+2*T+1)],sigma2.beta=result[,(3*A+2*T+2)],gamma.new=result[,(3*A+2*T+3):(3*A+2*T+4)],rho.cohort=result[,(3*A+2*T+5)],sigma2.cohort=result[,(3*A+2*T+6)],epsilon=result[,(3*A+2*T+7)],accept,accept.beta,accept.alpha,accept.cohort,accept.epsilon,accept.rho,accept.rho.cohort,accept.sigma2.cohort)
}

Ext<-round(EWexpo.female.mat.ex)
Dxt<-round(EWdeath.female.mat.ex)
t0<--21
k.new<-(result.poisson.LC.cohort.cons5.glm[[3]])
t<-t0:(t0+length(k.new)-1)
Y<-matrix(c(rep(1,length(k.new)),t0:(t0+length(k.new)-1)),byrow=F,ncol=2)
sigma.mat.0<-matrix(c(400,0,0,2),nrow=2)
alpha.new<-(result.poisson.LC.cohort.cons5.glm[[1]])
beta.new<-(result.poisson.LC.cohort.cons5.glm[[2]])  
gamma.new<-c(0,0)
sigma2.k<-arima(k.new-Y%*%gamma.new,order=c(1,0,0))$sigma2
sigma2.beta<-0.005
rho.new<-arima(k.new-Y%*%gamma.new,order=c(1,0,0))$coef[1]
lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001 
a.cohort<-100
b.cohort<-0.001
cohort<-(result.poisson.LC.cohort.cons5.glm[[4]])
rho.cohort<-arima(cohort,order=c(1,1,0))$coef
sigma2.cohort<-arima(cohort,order=c(1,1,0))$sigma2

marg.var.k.LC<-result.poisson.LC.cohort.cons5.glm[[6]]
marg.var.cohort.LC<-result.poisson.LC.cohort.cons5.glm[[7]]


#automated tuning of proposal variances

sigma.x.alpha<-rep(0.001,100)
repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif<-MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior.cohort.unif(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,cohort=cohort,sigma2.cohort=sigma2.cohort,rho.cohort=rho.cohort,sigma2.rho.cohort=1,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.cohort=a.cohort,b.cohort=b.cohort,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.cohort=((2.38^2)/138*marg.var.cohort.LC),sigma.prop.k=((3.38^2)/40*marg.var.k.LC),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25,sigma2.prop.rho.cohort=0.1,sigma2.prop.sigma2.cohort=0.01))
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]<40) & (rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="Age",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[14]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)

sigma2.x<-rep(0.0000001,100)
repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif<-MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior.cohort.unif(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,cohort=cohort,sigma2.cohort=sigma2.cohort,rho.cohort=rho.cohort,sigma2.rho.cohort=1,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.cohort=a.cohort,b.cohort=b.cohort,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.cohort=((2.38^2)/138*marg.var.cohort.LC),sigma.prop.k=((3.38^2)/40*marg.var.k.LC),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25,sigma2.prop.rho.cohort=0.1,sigma2.prop.sigma2.cohort=0.01))
sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]]<40) & (rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]]>20))==99) break
}
sigma2.x<-c(0.0000001,sigma2.x[-1])
par(mfrow=c(1,2))
plot(sigma2.x*1e7,mgp=c(2.25,1,0),ylim=c(0,10),xlab="Age",ylab=expression(paste("Proposal Variance ",(1%*% 10^-7))),main=expression(sigma[beta[x]]^2),cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif[[13]][-1]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)


																							
system.time(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif<-MCMC.deathrates.over.negbin.int.group.AR1.normal.match.prior.cohort.unif(n=100000,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,cohort=cohort,sigma2.cohort=sigma2.cohort,rho.cohort=rho.cohort,sigma2.rho.cohort=1,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=rho.new,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.cohort=a.cohort,b.cohort=b.cohort,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.cohort=((2.38^2)/138*marg.var.cohort.LC),sigma.prop.k=((3.38^2)/40*marg.var.k.LC),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25,sigma2.prop.rho.cohort=0.1,sigma2.prop.sigma2.cohort=0.00001))
gc()
theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif<-cbind(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$k.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$beta.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$alpha.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$cohort,log(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$sigma2.k),log(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$sigma2.beta),rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$gamma.new,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$rho.1,rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$rho.cohort,log(rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$sigma2.cohort),rates.MCMC.over.negbin.int.group.marg.AR1.y0.normal.match.prior.cohort.unif$epsilon)
gc()

par(mfrow=c(4,4))
plot(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,384]),xlab="iterations",ylab="",main="sigma2_k",type="l")
#plot(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,385]),xlab="iterations",ylab="",main="sigma2.beta",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,386],xlab="iterations",ylab="",main="gamma.1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,387],xlab="iterations",ylab="",main="gamma.2",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388],xlab="iterations",ylab="",main="rho.1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,389],xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,390]),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391],xlab="iterations",ylab="",main="epsilon",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,143],xlab="iterations",ylab="",main="alpha_1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,242],xlab="iterations",ylab="",main="alpha_100",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,43],xlab="iterations",ylab="",main="beta_1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,142],xlab="iterations",ylab="",main="beta_100",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,1],xlab="iterations",ylab="",main="kappa_1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,20],xlab="iterations",ylab="",main="kappa_20",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,243],xlab="iterations",ylab="",main="cohort_1",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,277],xlab="iterations",ylab="",main="cohort_35",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,314],xlab="iterations",ylab="",main="cohort_72",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,342],xlab="iterations",ylab="",main="cohort_100",type="l")
plot(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,383],xlab="iterations",ylab="",main="cohort_141",type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,384])),xlab="iterations",ylab="",main="sigma2_k",type="l")
#plot(density(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,385])),xlab="iterations",ylab="",main="sigma2.beta",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,386]),xlab="iterations",ylab="",main="gamma.1",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,387]),xlab="iterations",ylab="",main="gamma.2",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388]),xlab="iterations",ylab="",main="rho.1",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,389]),xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(density(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,390])),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391]),xlab="iterations",ylab="",main="epsilon",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,143]),xlab="iterations",ylab="",main="alpha_1",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,242]),xlab="iterations",ylab="",main="alpha_100",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,43]),xlab="iterations",ylab="",main="beta_1",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,142]),xlab="iterations",ylab="",main="beta_100",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,1]),xlab="iterations",ylab="",main="kappa_1",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,20]),xlab="iterations",ylab="",main="kappa_20",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,243]),xlab="iterations",ylab="",main="cohort_1",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,277]),xlab="iterations",ylab="",main="cohort_35",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,314]),xlab="iterations",ylab="",main="cohort_72",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,342]),xlab="iterations",ylab="",main="cohort_100",type="l")
plot(density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,383]),xlab="iterations",ylab="",main="cohort_141",type="l")

par(mfrow=c(4,4))
acf(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,384]),ylab="",main="sigma2_k")
#acf(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,385]),ylab="",main="sigma2.beta")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,386],ylab="",main="gamma.1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,387],ylab="",main="gamma.2")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388],ylab="",main="rho.1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,389],ylab="",main="rho.cohort")
acf(exp(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,390]),ylab="",main="sigma2.cohort")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391],ylab="",main="epsilon")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,143],ylab="",main="alpha_1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,242],ylab="",main="alpha_100")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,43],ylab="",main="beta_1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,142],ylab="",main="beta_100")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,1],ylab="",main="kappa_1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,20],ylab="",main="kappa_20")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,243],ylab="",main="cohort_1")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,277],ylab="",main="cohort_35")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,314],ylab="",main="cohort_72")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,342],ylab="",main="cohort_100")
acf(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,383],ylab="",main="cohort_141")

##############
##NBLCC-RW (RANDOM WALK) with grouping on kappa 
##Constraints:sum(beta)=1,sum(kappa)=0,sum(gamma)=sum(c*gamma)=sum(c^2*gamma)=0
##UNIFORM(0,0.1) PRIOR ON SIGMA.GAMMA
##############

MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior.cohort.unif<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k.new,alpha.new,beta.new,cohort,sigma2.cohort,rho.cohort,sigma2.rho.cohort,sigma2.beta,gamma.new,sigma2.k,rho.new,lx,sigma2.l,epsilon,a.beta,b.beta,ak,bk,a.rho,b.rho,gamma.0,sigma.mat.0,prior.epsilon.gamma=FALSE,a.epsilon,b.epsilon,prior.epsilon.normal=FALSE,miu.epsilon,sigma2.epsilon,a.cohort,b.cohort,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.epsilon,sigma2.prop.rho,sigma.prop.cohort,sigma2.prop.rho.cohort,sigma2.prop.sigma2.cohort){

Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha.new)
C<-length(cohort)
result<-matrix(0,nrow=round((n-burnin)/thin),ncol=3*A+2*T+7)

X<-matrix(c(rep(1,T),t0:(t0+T-1)),byrow=F,ncol=2)
X.1<-matrix(c(rep(1,(T-1)),(t0+1):(t0+T-1)),byrow=F,ncol=2)
isigma.mat.0<-solve(sigma.mat.0)
I<-diag(1,nrow=(A-1))
K<-matrix(1,nrow=(A-1),ncol=(A-1))
inverse<-solve(I-1/A*K)

J<-diag(rep(1,T))
J[1,]<-rep(1/sqrt(T),T)
R<-diag(rep(1,T))
#R[1,1]<-sqrt(1-rho.new^2)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho.new
}
}
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])

J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1
I.cohort<-diag(rep(1,C))

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic
S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

rho.new<-1
accept.epsilon<-0
accept<-0
accept.beta<-rep(0,A)
accept.alpha<-rep(0,A)
accept.cohort<-0
accept.rho<-0
accept.rho.cohort<-0
accept.sigma2.cohort<-0
iter<-0
g<-seq(thin,n,by=thin)

for (m in 1:n){

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
cohort.star.vec<-c(rmvnorm.manual(1,mean.vec=cohort[-c(1,72,C)],sigma=sigma.prop.cohort))
cohort.temp.star.vec<-cohort;cohort.temp.star.vec[-c(1,72,C)]<-cohort.star.vec
cohort.temp.star.vec[1]<-1/(71*140)*sum(c((-70):(-1),1:68)*c(139:70,68:1)*cohort.star.vec);cohort.temp.star.vec[72]<-1/(69*71)*sum(-c(139:70,68:1)*c(1:70,72:139)*cohort.star.vec);cohort.temp.star.vec[C]<-1/(69*140)*sum(c(1:70,72:139)*c(70:1,(-1):(-68))*cohort.star.vec)
cohort.star.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.star.mat[i,j]<-cohort.temp.star.vec[j-i+A]
}
}
p.nbinom.star.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.star.mat))
prob.accept.cohort<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.star.mat,log=TRUE))+dmvnorm.manual(cohort.temp.star.vec[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)
if (log(runif(1))<=prob.accept.cohort) {cohort<-cohort.temp.star.vec
cohort.mat<-cohort.star.mat
accept.cohort<-accept.cohort+1
}	



S<-sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
k.star.vec<-rmvnorm.tol(1,mean=k.new[-1],sigma=sigma.prop.k,method="chol")
k.star.vec<-c(-sum(k.star.vec),k.star.vec)
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.star.vec)+cohort.mat))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.manual(k.star.vec[-1],mean.vec=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.manual(k.new[-1],mean.vec=((X%*%gamma.new)[-1]-B[(2:T),1]/B[1,1]*sum(X%*%gamma.new)),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k.new<-k.star.vec
accept<-accept+1}

for (i in 2:A){
beta.star<-rnorm(1,beta.new[i],sqrt(sigma2.x[i]))
beta.star.vec<-beta.new;beta.star.vec[i]<-beta.star;beta.star.vec[1]<-1-sum(beta.star.vec[-1])
prob.accept.beta<-sum(Dxt[i,]*k.new*(beta.star-beta.new[i]))+sum(Dxt[1,]*k.new*(beta.star.vec[1]-beta.new[1]))-sum((Dxt[i,]+epsilon)*(log(Ext[i,]*exp(alpha.new[i]+beta.star*k.new+cohort.mat[i,])+epsilon)-log(Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new+cohort.mat[i,])+epsilon)))-
sum((Dxt[1,]+epsilon)*(log(Ext[1,]*exp(alpha.new[1]+beta.star.vec[1]*k.new+cohort.mat[1,])+epsilon)-log(Ext[1,]*exp(alpha.new[1]+beta.new[1]*k.new+cohort.mat[1,])+epsilon)))-(beta.star.vec[1]^2)/(2*sigma2.beta)-(beta.star^2)/(2*sigma2.beta)+(beta.new[1]^2)/(2*sigma2.beta)+(beta.new[i]^2)/(2*sigma2.beta)
if (log(runif(1))<=prob.accept.beta) {beta.new[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
beta.new[1]<-1-sum(beta.new[-1])
}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha.new[i]+beta.new[i]*k.new+cohort.mat[i,]))
alpha.star<-rnorm(1,alpha.new[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta.new[i]*k.new+cohort.mat[i,]))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.l)*(alpha.star-lx[i])^2-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.l)*(alpha.new[i]-lx[i])^2
if (log(runif(1))<=prob.accept.alpha) {alpha.new[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

repeat{
rho.cohort.star<-rtruncnorm(1,a=-1,b=1,mean=rho.cohort,sd=sqrt(sigma2.prop.rho.cohort))
R.cohort.star<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort.star[i,j]<--(1+rho.cohort.star)
if ((i-j)==2) R.cohort.star[i,j]<-rho.cohort.star
}
}
R.cohort.star[2,1]<--1*sqrt(1-rho.cohort.star^2)
R.cohort.star[2,2]<-sqrt(1-rho.cohort.star^2)
R.cohort.star[1,1]<-1/100 
i.R.cohort.star<-forwardsolve(R.cohort.star,I.cohort)
i.Q.cohort.star<-i.R.cohort.star%*%t(i.R.cohort.star)
B.cohort.star<-J.cohort%*%i.Q.cohort.star%*%t(J.cohort)
ic.star<-(B.cohort.star[(4:C),(1:3)])%*%solve(B.cohort.star[(1:3),(1:3)])%*%(B.cohort.star[(1:3),(4:C)])
D.cohort.star<-B.cohort.star[(4:C),(4:C)]-ic.star
S.cohort.star<-sigma2.cohort*D.cohort.star
S.cohort.star<-0.5*(S.cohort.star+t(S.cohort.star))
if (prod(sign(eigen(S.cohort.star)$val))==1){
break}
}
 
prob.accept.rho.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dnorm(rho.cohort.star,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)
if (log(runif(1))<=prob.accept.rho.cohort){
(rho.cohort<-rho.cohort.star)
(R.cohort<-R.cohort.star)
(B.cohort<-B.cohort.star)
(D.cohort<-D.cohort.star)
(S.cohort<-S.cohort.star)
(accept.rho.cohort<-accept.rho.cohort+1)
}

chol.D.cohort<-chol(D.cohort)
i.chol.D.cohort<-backsolve(chol.D.cohort,diag(rep(1,C-3)))
i.D.cohort<-i.chol.D.cohort%*%t(i.chol.D.cohort)
#sigma2.cohort<-1/rgamma(1,a.cohort+(C-3)/2,b.cohort+0.5*t(cohort[-c(1,72,C)])%*%i.D.cohort%*%cohort[-c(1,72,C)])

sigma2.cohort.star<-(rnorm(1,sqrt(sigma2.cohort),sqrt(sigma2.prop.sigma2.cohort)))^2
if (sigma2.cohort.star<0.01){
S.cohort.star<-sigma2.cohort.star*D.cohort
prob.accept.sigma2.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dunif(sqrt(sigma2.cohort.star),max=0.1,log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dunif(sqrt(sigma2.cohort),max=0.1,log=TRUE)
if (log(runif(1))<=prob.accept.sigma2.cohort){
sigma2.cohort<-sigma2.cohort.star;S.cohort<-S.cohort.star;accept.sigma2.cohort<-accept.sigma2.cohort+1
}
}

S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))

#isigma2.k<-rtrunc(1,spec="gamma",shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))),a=0.1,b=Inf)
isigma2.k<-rgamma(1,shape=ak+(T-1)/2,rate=bk+0.5*t(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new)))%*%solve(D)%*%(k.new[-1]-(X.1%*%gamma.new-B[2:T,1]/B[1,1]*sum(X%*%gamma.new))))

sigma2.k<-isigma2.k^-1

sigma2.beta<-0.005

S<-sigma2.k*D 
chol.S<-chol(S)
i.chol.S<-backsolve(chol.S,diag(rep(1,T-1)))
i.S<-i.chol.S%*%t(i.chol.S)

sigma.mat.star<-solve(isigma.mat.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X))
gamma.star<-sigma.mat.star%*%(isigma.mat.0%*%gamma.0+t(X.1-(B[2:T,1]/B[1,1])%*%t(rep(1,T))%*%X)%*%i.S%*%k.new[-1])
gamma.new<-c(rmvnorm.manual(1,mean.vec=gamma.star,sigma=sigma.mat.star))

if (prior.epsilon.gamma){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if (prior.epsilon.normal){
p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<5000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha.new,T),nrow=A,ncol=T,byrow=FALSE)+beta.new%*%t(k.new)+cohort.mat))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))-1/(2*sigma2.epsilon)*(epsilon.star-miu.epsilon)^2-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))+1/(2*sigma2.epsilon)*(epsilon-miu.epsilon)^2+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}
}

if ((m>burnin) & (m %in% g)){
iter<-iter+1
result[iter,]<-c(k.new,beta.new,alpha.new,cohort,rho.new,sigma2.k,sigma2.beta,gamma.new,rho.cohort,sigma2.cohort,epsilon)
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],cohort=result[,(2*A+T+1):(3*A+2*T-1)],rho.1=result[,(3*A+2*T)],sigma2.k=result[,(3*A+2*T+1)],sigma2.beta=result[,(3*A+2*T+2)],gamma.new=result[,(3*A+2*T+3):(3*A+2*T+4)],rho.cohort=result[,(3*A+2*T+5)],sigma2.cohort=result[,(3*A+2*T+6)],epsilon=result[,(3*A+2*T+7)],accept,accept.beta,accept.alpha,accept.cohort,accept.epsilon,accept.rho,accept.rho.cohort,accept.sigma2.cohort)
}

Ext<-round(EWexpo.female.mat.ex)
Dxt<-round(EWdeath.female.mat.ex)
t0<--21
k.new<-(result.poisson.LC.cohort.cons5.glm[[3]])
t<-t0:(t0+length(k.new)-1)
Y<-matrix(c(rep(1,length(k.new)),t0:(t0+length(k.new)-1)),byrow=F,ncol=2)
sigma.mat.0<-matrix(c(400,0,0,2),nrow=2)
alpha.new<-(result.poisson.LC.cohort.cons5.glm[[1]])
beta.new<-(result.poisson.LC.cohort.cons5.glm[[2]])  
gamma.new<-c(0,0)
sigma2.k<-arima(k.new-Y%*%gamma.new,order=c(0,1,0))$sigma2
sigma2.beta<-0.005

lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001 
a.cohort<-100
b.cohort<-0.001
cohort<-(result.poisson.LC.cohort.cons5.glm[[4]])
rho.cohort<-arima(cohort,order=c(1,1,0))$coef
sigma2.cohort<-arima(cohort,order=c(1,1,0))$sigma2

marg.var.k.LC<-result.poisson.LC.cohort.cons5.glm[[6]]
marg.var.cohort.LC<-result.poisson.LC.cohort.cons5.glm[[7]]

#automated tuning of proposal variances

sigma.x.alpha<-rep(0.001,100)
repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif<-MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior.cohort.unif(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,cohort=cohort,sigma2.cohort=sigma2.cohort,rho.cohort=rho.cohort,sigma2.rho.cohort=1,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.cohort=a.cohort,b.cohort=b.cohort,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.cohort=((2.38^2)/138*marg.var.cohort.LC),sigma.prop.k=((3.38^2)/40*marg.var.k.LC),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25,sigma2.prop.rho.cohort=0.1,sigma2.prop.sigma2.cohort=0.01))
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]>40]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]>40]*2
sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]<20]<-sigma.x.alpha[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]<40) & (rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]>20))==100) break
}
par(mfrow=c(1,2))
plot(sigma.x.alpha,ylim=c(0,0.009),xlab="Age",main=expression(sigma[alpha[x]]^2),ylab="Proposal Variance",cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[14]]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)

sigma2.x<-rep(0.0000001,100)
repeat{
system.time(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif<-MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior.cohort.unif(n=100,burnin=000,thin=1,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,cohort=cohort,sigma2.cohort=sigma2.cohort,rho.cohort=rho.cohort,sigma2.rho.cohort=1,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.cohort=a.cohort,b.cohort=b.cohort,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.cohort=((2.38^2)/138*marg.var.cohort.LC),sigma.prop.k=((3.38^2)/40*marg.var.k.LC),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25,sigma2.prop.rho.cohort=0.1,sigma2.prop.sigma2.cohort=0.01))
sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]]>40]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]]>40]*2
sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]]<20]<-sigma2.x[rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]]<20]/2
if (sum((rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]]<40) & (rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]]>20))==99) break
}
sigma2.x<-c(0.0000001,sigma2.x[-1])
par(mfrow=c(1,2))
plot(sigma2.x*1e7,mgp=c(2.25,1,0),ylim=c(0,10),xlab="Age",ylab=expression(paste("Proposal Variance ",(1%*% 10^-7))),main=expression(sigma[beta[x]]^2),cex.axis=1.5,cex.lab=1.5,cex.main=2)
plot(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif[[13]][-1]/100,ylim=c(0,1),xlab="Age",ylab="Acceptance Rate",cex.axis=1.5,cex.lab=1.5,cex.main=2)

																							
system.time(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif<-MCMC.deathrates.over.negbin.int.group.RW.normal.match.prior.cohort.unif(n=80000,burnin=000,thin=4,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k.new=k.new,alpha.new=alpha.new,beta.new=beta.new,cohort=cohort,sigma2.cohort=sigma2.cohort,rho.cohort=rho.cohort,sigma2.rho.cohort=1,sigma2.beta=sigma2.beta,gamma.new=gamma.new,sigma2.k=sigma2.k,
rho.new=1,lx=lx,sigma2.l=sigma2.l,epsilon=100,ak=ak,bk=bk,a.rho=3,b.rho=2,gamma.0=gamma.new,sigma.mat.0=sigma.mat.0,prior.epsilon.gamma=TRUE,a.cohort=a.cohort,b.cohort=b.cohort,a.epsilon=25,b.epsilon=0.05,prior.epsilon.normal=FALSE,miu.epsilon=0,sigma2.epsilon=100,sigma.prop.cohort=((2.38^2)/138*marg.var.cohort.LC),sigma.prop.k=((3.38^2)/40*marg.var.k.LC),sigma2.x=sigma2.x,sigma2.x.alpha=sigma.x.alpha,sigma2.prop.epsilon=0.08,sigma2.prop.rho=0.25,sigma2.prop.rho.cohort=0.1,sigma2.prop.sigma2.cohort=0.0001))
gc()
theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif<-cbind(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$k.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$beta.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$alpha.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$cohort,log(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$sigma2.k),log(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$sigma2.beta),rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$gamma.new,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$rho.1,rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$rho.cohort,log(rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$sigma2.cohort),rates.MCMC.over.negbin.int.group.marg.RW.y0.normal.match.prior.cohort.unif$epsilon)
gc()

par(mfrow=c(4,4))
plot(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,384]),xlab="iterations",ylab="",main="sigma2_k",type="l")
#plot(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,385]),xlab="iterations",ylab="",main="sigma2.beta",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,386],xlab="iterations",ylab="",main="gamma.1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,387],xlab="iterations",ylab="",main="gamma.2",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388],xlab="iterations",ylab="",main="rho.1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,389],xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,390]),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391],xlab="iterations",ylab="",main="epsilon",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,143],xlab="iterations",ylab="",main="alpha_1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,242],xlab="iterations",ylab="",main="alpha_100",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,43],xlab="iterations",ylab="",main="beta_1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,142],xlab="iterations",ylab="",main="beta_100",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,1],xlab="iterations",ylab="",main="kappa_1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,20],xlab="iterations",ylab="",main="kappa_20",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,243],xlab="iterations",ylab="",main="cohort_1",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,277],xlab="iterations",ylab="",main="cohort_35",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,314],xlab="iterations",ylab="",main="cohort_72",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,342],xlab="iterations",ylab="",main="cohort_100",type="l")
plot(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,383],xlab="iterations",ylab="",main="cohort_141",type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,384])),xlab="iterations",ylab="",main="sigma2_k",type="l")
#plot(density(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,385])),xlab="iterations",ylab="",main="sigma2.beta",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,386]),xlab="iterations",ylab="",main="gamma.1",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,387]),xlab="iterations",ylab="",main="gamma.2",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388]),xlab="iterations",ylab="",main="rho.1",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,389]),xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(density(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,390])),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391]),xlab="iterations",ylab="",main="epsilon",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,143]),xlab="iterations",ylab="",main="alpha_1",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,242]),xlab="iterations",ylab="",main="alpha_100",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,43]),xlab="iterations",ylab="",main="beta_1",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,142]),xlab="iterations",ylab="",main="beta_100",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,1]),xlab="iterations",ylab="",main="kappa_1",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,20]),xlab="iterations",ylab="",main="kappa_20",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,243]),xlab="iterations",ylab="",main="cohort_1",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,277]),xlab="iterations",ylab="",main="cohort_35",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,314]),xlab="iterations",ylab="",main="cohort_72",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,342]),xlab="iterations",ylab="",main="cohort_100",type="l")
plot(density(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,383]),xlab="iterations",ylab="",main="cohort_141",type="l")

par(mfrow=c(4,4))
acf(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,384]),ylab="",main="sigma2_k")
#acf(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,385]),ylab="",main="sigma2.beta")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,386],ylab="",main="gamma.1")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,387],ylab="",main="gamma.2")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388],ylab="",main="rho.1")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,389],ylab="",main="rho.cohort")
acf(exp(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,390]),ylab="",main="sigma2.cohort")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391],ylab="",main="epsilon")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,143],ylab="",main="alpha_1")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,242],ylab="",main="alpha_100")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,43],ylab="",main="beta_1")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,142],ylab="",main="beta_100")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,1],ylab="",main="kappa_1")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,20],ylab="",main="kappa_20")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,243],ylab="",main="cohort_1")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,277],ylab="",main="cohort_35")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,314],ylab="",main="cohort_72")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,342],ylab="",main="cohort_100")
acf(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,383],ylab="",main="cohort_141")

###########################
###Marginal likelihoods
###########################

#######################################
##NBLC-AR1 sum(beta_x)=1,sum(k_t)=0
#######################################

like.prior.negbin.lca.match.prior<-function(param,Dxt,Ext,A,T,t,lx,sigma2.l,a.rho,b.rho,gamma.0,sigma.mat.0,ak,bk,a.epsilon,b.epsilon,I=diag(rep(1,A-1)),K=matrix(1,nrow=A-1,ncol=A-1),J,X=matrix(c(rep(1,T),(-21):21),byrow=FALSE,ncol=2)){#supply param=c(k,beta,alpha,log.sigma2.k,log.sigma2.beta,gamma1,gamma2,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
sigma2.k<-exp(param[2*A+T+1])
sigma2.beta<-exp(param[2*A+T+2])
rho<-param[2*A+T+5]
gamma1<-param[2*A+T+3]
gamma2<-param[2*A+T+4]
gamma<-c(gamma1,gamma2)
ita.t<-gamma1+gamma2*t
epsilon<-(param[2*A+T+6])
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<- -rho
}
}
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(k))+epsilon)	
X<-cbind(rep(1,T),t)


{result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+dmvnorm.tol(k[-1],mean=((X%*%gamma)[-1]-B[2:T,1]/B[1,1]*sum(X%*%gamma)),sigma=(sigma2.k*D),log=TRUE)+dmvnorm.tol(beta[-1],mean=rep(1/A,A-1),sigma=sigma2.beta*(I-1/A*K),log=TRUE)+
sum(dnorm(alpha,mean=lx,sd=sqrt(sigma2.l),log=TRUE))+log(0.5)+dbeta((rho+1)/2,a.rho,b.rho,log=TRUE)+dmvnorm(gamma,mean=gamma.0,sigma=sigma.mat.0,log=TRUE)+ak*log(bk)-lgamma(ak)-ak*log(sigma2.k)-bk/sigma2.k+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon}
return(result)
}

Ext<-round(EWexpo.female.mat.ex)
Dxt<-round(EWdeath.female.mat.ex)
t0<--21
t<-t0:(t0+T-1)
lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001
a.rho<-3
b.rho<-2
gamma.0<-c(0,0)
sigma.mat.0<-matrix(c(2000,0,0,2),nrow=2)
a.epsilon<-25
b.epsilon<-0.05
J<-diag(rep(1,T))
J[1,]<-rep(1,T)

like.prior.negbin.lca.match.prior(param=as.numeric(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[100,]),Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.negbin.match.prior<-apply(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior,1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

mean.negbin.vec.match.prior<-apply((theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,247,248)]),2,mean)
covariance.negbin.mat.match.prior<-cov((theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,247,248)]))
mean.rho.negbin.match.prior<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247])
mean.log.epsilon.negbin.match.prior<-mean(log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248]))
variance.rho.negbin.match.prior<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247])
variance.log.epsilon.negbin.match.prior<-var(log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248]))
	
chol.cov.negbin.match.prior<-chol(covariance.negbin.mat.match.prior)
inverse.t.chol.cov.negbin.match.prior<-solve(t(chol.cov.negbin.match.prior))

M<-matrix(rep(mean.negbin.vec.match.prior,10000),nrow=243,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(243*10000),nrow=243,ncol=10000)
sample.bridge.negbin.match.prior<-M+t(chol.cov.negbin.match.prior)%*%Z
sample.bridge.negbin.match.prior<-t(sample.bridge.negbin.match.prior)
gc()
sample.rho.bridge.negbin.match.prior<-rtruncnorm(10000,a=-1,b=1,mean=mean.rho.negbin.match.prior,sd=sqrt(variance.rho.negbin.match.prior))
sample.log.epsilon.bridge.negbin.match.prior<-rtruncnorm(10000,a=log(1),b=log(50000),mean=mean.log.epsilon.negbin.match.prior,sd=sqrt(variance.log.epsilon.negbin.match.prior))
full.sample.bridge.negbin.match.prior<-cbind(-apply(sample.bridge.negbin.match.prior[,1:41],1,sum),sample.bridge.negbin.match.prior[,1:41],1-apply(sample.bridge.negbin.match.prior[,42:140],1,sum),sample.bridge.negbin.match.prior[,42:241],rep(log(0.005),10000),sample.bridge.negbin.match.prior[,242:243],sample.rho.bridge.negbin.match.prior,exp(sample.log.epsilon.bridge.negbin.match.prior))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior);rm(sample.log.epsilon.bridge.negbin.match.prior);rm(sample.bridge.negbin.match.prior);gc()
like.prior.negbin.lca.match.prior(full.sample.bridge.negbin.match.prior[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior<-apply(full.sample.bridge.negbin.match.prior,1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

log.det.Jacobian.negbin.match.prior<-determinant(inverse.t.chol.cov.negbin.match.prior,logarithm=TRUE)$modulus

q2.negbin.match.prior<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248])),1,transformation.dmvnorm.match.prior,mean.vec=mean.negbin.vec.match.prior,rij=inverse.t.chol.cov.negbin.match.prior,log.det.Jacobian=log.det.Jacobian.negbin.match.prior,mean.rho=mean.rho.negbin.match.prior,variance.rho=variance.rho.negbin.match.prior,mean.log.epsilon=mean.log.epsilon.negbin.match.prior,variance.log.epsilon=variance.log.epsilon.negbin.match.prior)
q2.bridge.match.prior<-apply(cbind(full.sample.bridge.negbin.match.prior[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior[,248])),1,transformation.dmvnorm.match.prior,mean.vec=mean.negbin.vec.match.prior,rij=inverse.t.chol.cov.negbin.match.prior,log.det.Jacobian=log.det.Jacobian.negbin.match.prior,mean.rho=mean.rho.negbin.match.prior,variance.rho=variance.rho.negbin.match.prior,mean.log.epsilon=mean.log.epsilon.negbin.match.prior,variance.log.epsilon=variance.log.epsilon.negbin.match.prior)
 
log.l.match.prior<-likelihood.negbin.match.prior-q2.negbin.match.prior
log.l.tilda.match.prior<-likelihood.bridge.match.prior-q2.bridge.match.prior
 
log.l.tilda.match.prior<-log.l.tilda.match.prior+24300
log.l.match.prior<-log.l.match.prior+24300
l.match.prior<-exp(log.l.match.prior)
l.tilda.match.prior<-exp(log.l.tilda.match.prior)

nc.negbin.lca.match.prior<-bridge(initial=100,m=1000,sample1=theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior,sample2=full.sample.bridge.negbin.lca.match.prior,n1=10000,n2=10000,l=l.match.prior,l.tilda=l.tilda.match.prior)  
log(nc.negbin.lca.match.prior)-24300 						
						 #-23801.74 (thin by 500, n1=n2=10000)
						 #-23801.45 (thin by 500, n2=2*n1=20000)

##no truncation on epsilon

mean.negbin.vec.match.prior<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,247,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248])),2,mean)
covariance.negbin.mat.match.prior<-cov(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,247,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248])))
mean.rho.negbin.match.prior<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247])
variance.rho.negbin.match.prior<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,247])
	
chol.cov.negbin.match.prior<-chol(covariance.negbin.mat.match.prior)
inverse.t.chol.cov.negbin.match.prior<-solve(t(chol.cov.negbin.match.prior))

M<-matrix(rep(mean.negbin.vec.match.prior,20000),nrow=244,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(244*20000),nrow=244,ncol=20000)
sample.bridge.negbin.match.prior<-M+t(chol.cov.negbin.match.prior)%*%Z
sample.bridge.negbin.match.prior<-t(sample.bridge.negbin.match.prior)
gc()
sample.rho.bridge.negbin.match.prior<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.negbin.match.prior,sd=sqrt(variance.rho.negbin.match.prior))
full.sample.bridge.negbin.match.prior<-cbind(-apply(sample.bridge.negbin.match.prior[,1:41],1,sum),sample.bridge.negbin.match.prior[,1:41],1-apply(sample.bridge.negbin.match.prior[,42:140],1,sum),sample.bridge.negbin.match.prior[,42:241],rep(log(0.005),20000),sample.bridge.negbin.match.prior[,242:243],sample.rho.bridge.negbin.match.prior,exp(sample.bridge.negbin.match.prior[,244]))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior);rm(sample.bridge.negbin.match.prior);gc()
like.prior.negbin.lca.match.prior(full.sample.bridge.negbin.match.prior[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior<-apply(full.sample.bridge.negbin.match.prior,1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

log.det.Jacobian.negbin.match.prior<-determinant(inverse.t.chol.cov.negbin.match.prior,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.2(x=c(full.sample.bridge.negbin.match.prior[1000,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior[1000,248])),mean.vec=mean.negbin.vec.match.prior,rij=inverse.t.chol.cov.negbin.match.prior,log.det.Jacobian=log.det.Jacobian.negbin.match.prior,mean.rho=mean.rho.negbin.match.prior,variance.rho=variance.rho.negbin.match.prior)
dmvnorm(c(full.sample.bridge.negbin.match.prior[1000,-c(1,43,244,247,248)],log(full.sample.bridge.negbin.match.prior[1000,248])),mean=mean.negbin.vec.match.prior,sigma=covariance.negbin.mat.match.prior,log=TRUE)+log(dtruncnorm(full.sample.bridge.negbin.match.prior[1000,247],a=-1,b=1,mean=mean.rho.negbin.match.prior,sd=sqrt(variance.rho.negbin.match.prior)))

q2.negbin.match.prior<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248])),1,transformation.dmvnorm.match.prior.2,mean.vec=mean.negbin.vec.match.prior,rij=inverse.t.chol.cov.negbin.match.prior,log.det.Jacobian=log.det.Jacobian.negbin.match.prior,mean.rho=mean.rho.negbin.match.prior,variance.rho=variance.rho.negbin.match.prior)
q2.bridge.match.prior<-apply(cbind(full.sample.bridge.negbin.match.prior[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior[,248])),1,transformation.dmvnorm.match.prior.2,mean.vec=mean.negbin.vec.match.prior,rij=inverse.t.chol.cov.negbin.match.prior,log.det.Jacobian=log.det.Jacobian.negbin.match.prior,mean.rho=mean.rho.negbin.match.prior,variance.rho=variance.rho.negbin.match.prior)
 
log.l.match.prior<-likelihood.negbin.match.prior-q2.negbin.match.prior
log.l.tilda.match.prior<-likelihood.bridge.match.prior-q2.bridge.match.prior
 
log.l.tilda.match.prior<-log.l.tilda.match.prior+24300
log.l.match.prior<-log.l.match.prior+24300
l.match.prior<-exp(log.l.match.prior)
l.tilda.match.prior<-exp(log.l.tilda.match.prior)

nc.negbin.lca.match.prior<-bridge(initial=100,m=1000,sample1=theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior,sample2=full.sample.bridge.negbin.lca.match.prior,n1=10000,n2=20000,l=l.match.prior,l.tilda=l.tilda.match.prior)  
log(nc.negbin.lca.match.prior)-24300 #-23801.75 (thin by 500, n1=n2=10000)
						 #-23801.46 (thin by 500, n2=2*n1=20000)


#############
##splitting
#############

likelihood.negbin.match.prior.split<-apply(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,],1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

mean.negbin.vec.match.prior.split<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,-c(1,43,244,247,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,248])),2,mean)
covariance.negbin.mat.match.prior.split<-cov(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,-c(1,43,244,247,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,248])))
mean.rho.negbin.match.prior.split<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,247])
variance.rho.negbin.match.prior.split<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,247])
	
chol.cov.negbin.match.prior.split<-chol(covariance.negbin.mat.match.prior.split)
inverse.t.chol.cov.negbin.match.prior.split<-solve(t(chol.cov.negbin.match.prior.split))

M<-matrix(rep(mean.negbin.vec.match.prior.split,20000),nrow=244,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(244*20000),nrow=244,ncol=20000)
sample.bridge.negbin.match.prior.split<-M+t(chol.cov.negbin.match.prior.split)%*%Z
sample.bridge.negbin.match.prior.split<-t(sample.bridge.negbin.match.prior.split)
gc()
sample.rho.bridge.negbin.match.prior.split<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.negbin.match.prior.split,sd=sqrt(variance.rho.negbin.match.prior.split))
full.sample.bridge.negbin.match.prior.split<-cbind(-apply(sample.bridge.negbin.match.prior.split[,1:41],1,sum),sample.bridge.negbin.match.prior.split[,1:41],1-apply(sample.bridge.negbin.match.prior.split[,42:140],1,sum),sample.bridge.negbin.match.prior.split[,42:241],rep(log(0.005),20000),sample.bridge.negbin.match.prior.split[,242:243],sample.rho.bridge.negbin.match.prior.split,exp(sample.bridge.negbin.match.prior.split[,244]))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior.split);rm(sample.bridge.negbin.match.prior.split);gc()
like.prior.negbin.lca.match.prior(full.sample.bridge.negbin.match.prior.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior.split<-apply(full.sample.bridge.negbin.match.prior.split,1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
 
log.det.Jacobian.negbin.match.prior.split<-determinant(inverse.t.chol.cov.negbin.match.prior.split,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.2(x=c(full.sample.bridge.negbin.match.prior.split[1000,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.split[1000,248])),mean.vec=mean.negbin.vec.match.prior.split,rij=inverse.t.chol.cov.negbin.match.prior.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.split,mean.rho=mean.rho.negbin.match.prior.split,variance.rho=variance.rho.negbin.match.prior.split)
dmvnorm(c(full.sample.bridge.negbin.match.prior.split[1000,-c(1,43,244,247,248)],log(full.sample.bridge.negbin.match.prior.split[1000,248])),mean=mean.negbin.vec.match.prior.split,sigma=covariance.negbin.mat.match.prior.split,log=TRUE)+log(dtruncnorm(full.sample.bridge.negbin.match.prior.split[1000,247],a=-1,b=1,mean=mean.rho.negbin.match.prior.split,sd=sqrt(variance.rho.negbin.match.prior.split)))


q2.negbin.match.prior.split<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,-c(1,43,244,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,248])),1,transformation.dmvnorm.match.prior.2,mean.vec=mean.negbin.vec.match.prior.split,rij=inverse.t.chol.cov.negbin.match.prior.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.split,mean.rho=mean.rho.negbin.match.prior.split,variance.rho=variance.rho.negbin.match.prior.split)
q2.bridge.match.prior.split<-apply(cbind(full.sample.bridge.negbin.match.prior.split[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.split[,248])),1,transformation.dmvnorm.match.prior.2,mean.vec=mean.negbin.vec.match.prior.split,rij=inverse.t.chol.cov.negbin.match.prior.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.split,mean.rho=mean.rho.negbin.match.prior.split,variance.rho=variance.rho.negbin.match.prior.split)
 
log.l.match.prior.split<-likelihood.negbin.match.prior.split-q2.negbin.match.prior.split
log.l.tilda.match.prior.split<-likelihood.bridge.match.prior.split-q2.bridge.match.prior.split
 
log.l.tilda.match.prior.split<-log.l.tilda.match.prior.split+24300
log.l.match.prior.split<-log.l.match.prior.split+24300
l.match.prior.split<-exp(log.l.match.prior.split)
l.tilda.match.prior.split<-exp(log.l.tilda.match.prior.split)

nc.negbin.lca.match.prior.split<-bridge(initial=100,m=10000,sample1=theta.AR1.over.negbin.int.y0.normal.match.prior[5001:10000,],sample2=full.sample.bridge.negbin.lca.match.prior.split,n1=5000,n2=20000,l=l.match.prior.split,l.tilda=l.tilda.match.prior.split)  
log(nc.negbin.lca.match.prior.split)-24300 #-23800.25 (thin by 500,n2=5000,n1=5000)
							 #-23800.20 (thin by 500,n2=10000,n1=5000)
							 #-23800.22 (thin by 500,n2=20000,n1=5000)

#############
##cross-splitting
#############

likelihood.negbin.match.prior.split.2<-apply(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,],1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

mean.negbin.vec.match.prior.split.2<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,-c(1,43,244,247,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,248])),2,mean)
covariance.negbin.mat.match.prior.split.2<-cov(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,-c(1,43,244,247,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,248])))
mean.rho.negbin.match.prior.split.2<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,247])
variance.rho.negbin.match.prior.split.2<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,247])
	
chol.cov.negbin.match.prior.split.2<-chol(covariance.negbin.mat.match.prior.split.2)
inverse.t.chol.cov.negbin.match.prior.split.2<-solve(t(chol.cov.negbin.match.prior.split.2))

M<-matrix(rep(mean.negbin.vec.match.prior.split.2,10000),nrow=244,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(244*10000),nrow=244,ncol=10000)
sample.bridge.negbin.match.prior.split.2<-M+t(chol.cov.negbin.match.prior.split.2)%*%Z
sample.bridge.negbin.match.prior.split.2<-t(sample.bridge.negbin.match.prior.split.2)
gc()
sample.rho.bridge.negbin.match.prior.split.2<-rtruncnorm(10000,a=-1,b=1,mean=mean.rho.negbin.match.prior.split.2,sd=sqrt(variance.rho.negbin.match.prior.split.2))
full.sample.bridge.negbin.match.prior.split.2<-cbind(-apply(sample.bridge.negbin.match.prior.split.2[,1:41],1,sum),sample.bridge.negbin.match.prior.split.2[,1:41],1-apply(sample.bridge.negbin.match.prior.split.2[,42:140],1,sum),sample.bridge.negbin.match.prior.split.2[,42:241],rep(log(0.005),10000),sample.bridge.negbin.match.prior.split.2[,242:243],sample.rho.bridge.negbin.match.prior.split.2,exp(sample.bridge.negbin.match.prior.split.2[,244]))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior.split.2);rm(sample.bridge.negbin.match.prior.split.2);gc()
like.prior.negbin.lca.match.prior(full.sample.bridge.negbin.match.prior.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior.split.2<-apply(full.sample.bridge.negbin.match.prior.split.2,1,like.prior.negbin.lca.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
 
log.det.Jacobian.negbin.match.prior.split.2<-determinant(inverse.t.chol.cov.negbin.match.prior.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.2(x=c(full.sample.bridge.negbin.match.prior.split.2[1000,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.split.2[1000,248])),mean.vec=mean.negbin.vec.match.prior.split.2,rij=inverse.t.chol.cov.negbin.match.prior.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.split.2,mean.rho=mean.rho.negbin.match.prior.split.2,variance.rho=variance.rho.negbin.match.prior.split.2)
dmvnorm(c(full.sample.bridge.negbin.match.prior.split.2[1000,-c(1,43,244,247,248)],log(full.sample.bridge.negbin.match.prior.split.2[1000,248])),mean=mean.negbin.vec.match.prior.split.2,sigma=covariance.negbin.mat.match.prior.split.2,log=TRUE)+log(dtruncnorm(full.sample.bridge.negbin.match.prior.split.2[1000,247],a=-1,b=1,mean=mean.rho.negbin.match.prior.split.2,sd=sqrt(variance.rho.negbin.match.prior.split.2)))


q2.negbin.match.prior.split.2<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,-c(1,43,244,248)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,248])),1,transformation.dmvnorm.match.prior.2,mean.vec=mean.negbin.vec.match.prior.split.2,rij=inverse.t.chol.cov.negbin.match.prior.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.split.2,mean.rho=mean.rho.negbin.match.prior.split.2,variance.rho=variance.rho.negbin.match.prior.split.2)
q2.bridge.match.prior.split.2<-apply(cbind(full.sample.bridge.negbin.match.prior.split.2[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.split.2[,248])),1,transformation.dmvnorm.match.prior.2,mean.vec=mean.negbin.vec.match.prior.split.2,rij=inverse.t.chol.cov.negbin.match.prior.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.split.2,mean.rho=mean.rho.negbin.match.prior.split.2,variance.rho=variance.rho.negbin.match.prior.split.2)
 
log.l.match.prior.split.2<-likelihood.negbin.match.prior.split.2-q2.negbin.match.prior.split.2
log.l.tilda.match.prior.split.2<-likelihood.bridge.match.prior.split.2-q2.bridge.match.prior.split.2
 
log.l.tilda.match.prior.split.2<-log.l.tilda.match.prior.split.2+24300
log.l.match.prior.split.2<-log.l.match.prior.split.2+24300
l.match.prior.split.2<-exp(log.l.match.prior.split.2)
l.tilda.match.prior.split.2<-exp(log.l.tilda.match.prior.split.2)

nc.negbin.lca.match.prior.split.2<-bridge(initial=100,m=10000,sample1=theta.AR1.over.negbin.int.y0.normal.match.prior[1:5000,],sample2=full.sample.bridge.negbin.lca.match.prior.split.2,n1=5000,n2=10000,l=l.match.prior.split.2,l.tilda=l.tilda.match.prior.split.2)  
log(nc.negbin.lca.match.prior.split.2)-24300 #-23800.20 (thin by 500,n2=10000,n1=5000)
#so cross splitting estimate is 0.5*(-23800.20-23800.20)=-23800.20


#######################################
##NBLC-RW sum(beta_x)=1,sum(k_t)=0
#######################################

like.prior.negbin.lca.match.prior.RW<-function(param,Dxt,Ext,A,T,t,lx,sigma2.l,gamma.0,sigma.mat.0,ak,bk,a.epsilon,b.epsilon,I=diag(rep(1,A-1)),K=matrix(1,nrow=A-1,ncol=A-1),J,X=matrix(c(rep(1,T),(-21):21),byrow=FALSE,ncol=2)){#supply param=c(k,beta,alpha,log.sigma2.k,log.sigma2.beta,gamma1,gamma2,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
sigma2.k<-exp(param[2*A+T+1])
sigma2.beta<-exp(param[2*A+T+2])
rho<-param[2*A+T+5]
gamma1<-param[2*A+T+3]
gamma2<-param[2*A+T+4]
gamma<-c(gamma1,gamma2)
ita.t<-gamma1+gamma2*t
epsilon<-(param[2*A+T+6])
R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
i.R<-forwardsolve(R,diag(rep(1,T)))
i.Q<-i.R%*%t(i.R)
B<-J%*%i.Q%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(k))+epsilon)	
X<-cbind(rep(1,T),t)


{result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+dmvnorm.tol(k[-1],mean=((X%*%gamma)[-1]-B[2:T,1]/B[1,1]*sum(X%*%gamma)),sigma=(sigma2.k*D),log=TRUE)+dmvnorm.tol(beta[-1],mean=rep(1/A,A-1),sigma=sigma2.beta*(I-1/A*K),log=TRUE)+
sum(dnorm(alpha,mean=lx,sd=sqrt(sigma2.l),log=TRUE))+dmvnorm(gamma,mean=gamma.0,sigma=sigma.mat.0,log=TRUE)+ak*log(bk)-lgamma(ak)-ak*log(sigma2.k)-bk/sigma2.k+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001
gamma.0<-c(0,0)
sigma.mat.0<-matrix(c(2000,0,0,2),nrow=2)
a.epsilon<-25
b.epsilon<-0.05
J<-diag(rep(1,T))
J[1,]<-rep(1,T)

like.prior.negbin.lca.match.prior.RW(param=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1000,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.negbin.match.prior.RW<-apply(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior,1,like.prior.negbin.lca.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

mean.negbin.vec.match.prior.RW<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,247,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,248])),2,mean)
covariance.negbin.mat.match.prior.RW<-cov(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,247,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,248])))
	
chol.cov.negbin.match.prior.RW<-chol(covariance.negbin.mat.match.prior.RW)
inverse.t.chol.cov.negbin.match.prior.RW<-solve(t(chol.cov.negbin.match.prior.RW))

M<-matrix(rep(mean.negbin.vec.match.prior.RW,20000),nrow=244,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(244*20000),nrow=244,ncol=20000)
sample.bridge.negbin.match.prior.RW<-M+t(chol.cov.negbin.match.prior.RW)%*%Z
sample.bridge.negbin.match.prior.RW<-t(sample.bridge.negbin.match.prior.RW)
gc()
full.sample.bridge.negbin.match.prior.RW<-cbind(-apply(sample.bridge.negbin.match.prior.RW[,1:41],1,sum),sample.bridge.negbin.match.prior.RW[,1:41],1-apply(sample.bridge.negbin.match.prior.RW[,42:140],1,sum),sample.bridge.negbin.match.prior.RW[,42:241],rep(log(0.005),20000),sample.bridge.negbin.match.prior.RW[,242:243],rep(1,20000),exp(sample.bridge.negbin.match.prior.RW[,244]))
rm(M);rm(Z);rm(sample.bridge.negbin.match.prior.RW);gc()
like.prior.negbin.lca.match.prior.RW(full.sample.bridge.negbin.match.prior.RW[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior.RW<-apply(full.sample.bridge.negbin.match.prior.RW,1,like.prior.negbin.lca.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
 
transformation.dmvnorm.match.prior.RW<-function(x,mean.vec,rij,log.det.Jacobian){
y<-x[-c(244)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.x<-log.pdf.z+log.det.Jacobian
log.pdf.x
}

log.det.Jacobian.negbin.match.prior.RW<-determinant(inverse.t.chol.cov.negbin.match.prior.RW,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.RW(x=c(full.sample.bridge.negbin.match.prior.RW[1000,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.RW[1000,248])),mean.vec=mean.negbin.vec.match.prior.RW,rij=inverse.t.chol.cov.negbin.match.prior.RW,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW)
dmvnorm(c(full.sample.bridge.negbin.match.prior.RW[1000,-c(1,43,244,247,248)],log(full.sample.bridge.negbin.match.prior.RW[1000,248])),mean=mean.negbin.vec.match.prior.RW,sigma=covariance.negbin.mat.match.prior.RW,log=TRUE)

q2.negbin.match.prior.RW<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,-c(1,43,244,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[,248])),1,transformation.dmvnorm.match.prior.RW,mean.vec=mean.negbin.vec.match.prior.RW,rij=inverse.t.chol.cov.negbin.match.prior.RW,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW)
q2.bridge.match.prior.RW<-apply(cbind(full.sample.bridge.negbin.match.prior.RW[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.RW[,248])),1,transformation.dmvnorm.match.prior.RW,mean.vec=mean.negbin.vec.match.prior.RW,rij=inverse.t.chol.cov.negbin.match.prior.RW,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW)
 
log.l.match.prior.RW<-likelihood.negbin.match.prior.RW-q2.negbin.match.prior.RW
log.l.tilda.match.prior.RW<-likelihood.bridge.match.prior.RW-q2.bridge.match.prior.RW
 
log.l.tilda.match.prior.RW<-log.l.tilda.match.prior.RW+24300
log.l.match.prior.RW<-log.l.match.prior.RW+24300
l.match.prior.RW<-exp(log.l.match.prior.RW)
l.tilda.match.prior.RW<-exp(log.l.tilda.match.prior.RW)

nc.negbin.lca.match.prior.RW<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior,sample2=full.sample.bridge.negbin.lca.match.prior.RW,n1=10000,n2=20000,l=l.match.prior.RW,l.tilda=l.tilda.match.prior.RW)  
log(nc.negbin.lca.match.prior.RW)-24300  #-23800.16 (thin by 500, n1=n2=10000)
						     #-23799.82 (thin by 500, n2=2*n1=20000)

#################
##splitting
#################

likelihood.negbin.match.prior.RW.split<-apply(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,],1,like.prior.negbin.lca.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

mean.negbin.vec.match.prior.RW.split<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,-c(1,43,244,247,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,248])),2,mean)
covariance.negbin.mat.match.prior.RW.split<-cov(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,-c(1,43,244,247,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,248])))
	
chol.cov.negbin.match.prior.RW.split<-chol(covariance.negbin.mat.match.prior.RW.split)
inverse.t.chol.cov.negbin.match.prior.RW.split<-solve(t(chol.cov.negbin.match.prior.RW.split))

M<-matrix(rep(mean.negbin.vec.match.prior.RW.split,5000),nrow=244,ncol=5000,byrow=FALSE)
Z<-matrix(rnorm(244*5000),nrow=244,ncol=5000)
sample.bridge.negbin.match.prior.RW.split<-M+t(chol.cov.negbin.match.prior.RW.split)%*%Z
sample.bridge.negbin.match.prior.RW.split<-t(sample.bridge.negbin.match.prior.RW.split)
gc()
full.sample.bridge.negbin.match.prior.RW.split<-cbind(-apply(sample.bridge.negbin.match.prior.RW.split[,1:41],1,sum),sample.bridge.negbin.match.prior.RW.split[,1:41],1-apply(sample.bridge.negbin.match.prior.RW.split[,42:140],1,sum),sample.bridge.negbin.match.prior.RW.split[,42:241],rep(log(0.005),5000),sample.bridge.negbin.match.prior.RW.split[,242:243],rep(1,5000),exp(sample.bridge.negbin.match.prior.RW.split[,244]))
rm(M);rm(Z);rm(sample.bridge.negbin.match.prior.RW.split);gc()
like.prior.negbin.lca.match.prior.RW(full.sample.bridge.negbin.match.prior.RW.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior.RW.split<-apply(full.sample.bridge.negbin.match.prior.RW.split,1,like.prior.negbin.lca.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

log.det.Jacobian.negbin.match.prior.RW.split<-determinant(inverse.t.chol.cov.negbin.match.prior.RW.split,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.RW(x=c(full.sample.bridge.negbin.match.prior.RW.split[1000,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.RW.split[1000,248])),mean.vec=mean.negbin.vec.match.prior.RW.split,rij=inverse.t.chol.cov.negbin.match.prior.RW.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW.split)
dmvnorm(c(full.sample.bridge.negbin.match.prior.RW.split[1000,-c(1,43,244,247,248)],log(full.sample.bridge.negbin.match.prior.RW.split[1000,248])),mean=mean.negbin.vec.match.prior.RW.split,sigma=covariance.negbin.mat.match.prior.RW.split,log=TRUE)

q2.negbin.match.prior.RW.split<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,-c(1,43,244,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,248])),1,transformation.dmvnorm.match.prior.RW,mean.vec=mean.negbin.vec.match.prior.RW.split,rij=inverse.t.chol.cov.negbin.match.prior.RW.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW.split)
q2.bridge.match.prior.RW.split<-apply(cbind(full.sample.bridge.negbin.match.prior.RW.split[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.RW.split[,248])),1,transformation.dmvnorm.match.prior.RW,mean.vec=mean.negbin.vec.match.prior.RW.split,rij=inverse.t.chol.cov.negbin.match.prior.RW.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW.split)
 
log.l.match.prior.RW.split<-likelihood.negbin.match.prior.RW.split-q2.negbin.match.prior.RW.split
log.l.tilda.match.prior.RW.split<-likelihood.bridge.match.prior.RW.split-q2.bridge.match.prior.RW.split
 
log.l.tilda.match.prior.RW.split<-log.l.tilda.match.prior.RW.split+24300
log.l.match.prior.RW.split<-log.l.match.prior.RW.split+24300
l.match.prior.RW.split<-exp(log.l.match.prior.RW.split)
l.tilda.match.prior.RW.split<-exp(log.l.tilda.match.prior.RW.split)

nc.negbin.lca.match.prior.RW.split<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,],sample2=full.sample.bridge.negbin.lca.match.prior.RW.split,n1=5000,n2=5000,l=l.match.prior.RW.split,l.tilda=l.tilda.match.prior.RW.split)  
log(nc.negbin.lca.match.prior.RW.split)-24300    #-23798.61 (thin by 500,n1=5000,n2=5000)
								 #-23798.59 (thin by 500,n1=5000,n2=10000)
						    		 #-23798.62 (thin by 500,n1=5000,n2=20000) 
##cross-splitting

likelihood.negbin.match.prior.RW.split.2<-apply(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,],1,like.prior.negbin.lca.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

mean.negbin.vec.match.prior.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,-c(1,43,244,247,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,248])),2,mean)
covariance.negbin.mat.match.prior.RW.split.2<-cov(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,-c(1,43,244,247,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[5001:10000,248])))
	
chol.cov.negbin.match.prior.RW.split.2<-chol(covariance.negbin.mat.match.prior.RW.split.2)
inverse.t.chol.cov.negbin.match.prior.RW.split.2<-solve(t(chol.cov.negbin.match.prior.RW.split.2))

M<-matrix(rep(mean.negbin.vec.match.prior.RW.split.2,10000),nrow=244,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(244*10000),nrow=244,ncol=10000)
sample.bridge.negbin.match.prior.RW.split.2<-M+t(chol.cov.negbin.match.prior.RW.split.2)%*%Z
sample.bridge.negbin.match.prior.RW.split.2<-t(sample.bridge.negbin.match.prior.RW.split.2)
gc()
full.sample.bridge.negbin.match.prior.RW.split.2<-cbind(-apply(sample.bridge.negbin.match.prior.RW.split.2[,1:41],1,sum),sample.bridge.negbin.match.prior.RW.split.2[,1:41],1-apply(sample.bridge.negbin.match.prior.RW.split.2[,42:140],1,sum),sample.bridge.negbin.match.prior.RW.split.2[,42:241],rep(log(0.005),10000),sample.bridge.negbin.match.prior.RW.split.2[,242:243],rep(1,10000),exp(sample.bridge.negbin.match.prior.RW.split.2[,244]))
rm(M);rm(Z);rm(sample.bridge.negbin.match.prior.RW.split.2);gc()
like.prior.negbin.lca.match.prior.RW(full.sample.bridge.negbin.match.prior.RW.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)
likelihood.bridge.match.prior.RW.split.2<-apply(full.sample.bridge.negbin.match.prior.RW.split.2,1,like.prior.negbin.lca.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J)

log.det.Jacobian.negbin.match.prior.RW.split.2<-determinant(inverse.t.chol.cov.negbin.match.prior.RW.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.RW(x=c(full.sample.bridge.negbin.match.prior.RW.split.2[1000,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.RW.split.2[1000,248])),mean.vec=mean.negbin.vec.match.prior.RW.split.2,rij=inverse.t.chol.cov.negbin.match.prior.RW.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW.split.2)
dmvnorm(c(full.sample.bridge.negbin.match.prior.RW.split.2[1000,-c(1,43,244,247,248)],log(full.sample.bridge.negbin.match.prior.RW.split.2[1000,248])),mean=mean.negbin.vec.match.prior.RW.split.2,sigma=covariance.negbin.mat.match.prior.RW.split.2,log=TRUE)

q2.negbin.match.prior.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,-c(1,43,244,248)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,248])),1,transformation.dmvnorm.match.prior.RW,mean.vec=mean.negbin.vec.match.prior.RW.split.2,rij=inverse.t.chol.cov.negbin.match.prior.RW.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW.split.2)
q2.bridge.match.prior.RW.split.2<-apply(cbind(full.sample.bridge.negbin.match.prior.RW.split.2[,-c(1,43,244,248)],log(full.sample.bridge.negbin.match.prior.RW.split.2[,248])),1,transformation.dmvnorm.match.prior.RW,mean.vec=mean.negbin.vec.match.prior.RW.split.2,rij=inverse.t.chol.cov.negbin.match.prior.RW.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.RW.split.2)
 
log.l.match.prior.RW.split.2<-likelihood.negbin.match.prior.RW.split.2-q2.negbin.match.prior.RW.split.2
log.l.tilda.match.prior.RW.split.2<-likelihood.bridge.match.prior.RW.split.2-q2.bridge.match.prior.RW.split.2
 
log.l.tilda.match.prior.RW.split.2<-log.l.tilda.match.prior.RW.split.2+24300
log.l.match.prior.RW.split.2<-log.l.match.prior.RW.split.2+24300
l.match.prior.RW.split.2<-exp(log.l.match.prior.RW.split.2)
l.tilda.match.prior.RW.split.2<-exp(log.l.tilda.match.prior.RW.split.2)

nc.negbin.lca.match.prior.RW.split.2<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:5000,],sample2=full.sample.bridge.negbin.lca.match.prior.RW.split.2,n1=5000,n2=10000,l=l.match.prior.RW.split.2,l.tilda=l.tilda.match.prior.RW.split.2)  
log(nc.negbin.lca.match.prior.RW.split.2)-24300 #-23798.63 (thin by 500,n1=5000,n2=10000)

#so cross splitting estimate is 0.5*(-23798.59-23798.63)=-23798.61

######################
##NBAPI-AR1 (constraints: sum(k_t)=sum(tk_t)=0)
######################
	
like.prior.loglinear.negbin.match.prior<-function(param,Dxt,Ext,A,T,t,lx,lambda.alpha,lambda.beta,a.rho,b.rho,ak,bk,a.epsilon,b.epsilon){#supply param=c(k,beta,alpha,log.sigma2.k,log.lambda,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
sigma2.k<-exp(param[2*A+T+1])
lambda<-exp(param[2*A+T+2])
rho<-param[2*A+T+3]
epsilon<-param[2*A+T+4]

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
Q<-t(R)%*%R
C<-J%*%solve(Q)%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-2*sigma2.k*D 
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE))+epsilon)	

{result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+sum(log(ddoublex(beta,mu=0,lambda=lambda.beta)))+dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)+
sum(log(ddoublex(alpha,mu=lx,lambda=lambda.alpha)))+log(0.5)+dbeta((rho+1)/2,a.rho,b.rho,log=TRUE)+log(lambda)-lambda*sigma2.k+log(sigma2.k)+ak*log(bk/400)-lgamma(ak)+ak*log(lambda)-bk/400*lambda+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
ak<-1
bk<-0.0001
a.epsilon<-25
b.epsilon<-0.05
a.rho<-3
b.rho<-2
lambda.alpha<-rep(2.5,A)
lambda.beta<-rep(0.03,A)


like.prior.loglinear.negbin.match.prior(param=theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.loglinear.group.match.prior<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec.match.prior<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,244,245,246)]),2,mean)
covariance.loglinear.mat.match.prior<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,244,245,246)]))
mean.log.lambda.loglinear.match.prior<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244])
variance.log.lambda.loglinear.match.prior<-var(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244])
mean.rho.loglinear.match.prior<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245])
variance.rho.loglinear.match.prior<-var(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245])
mean.log.epsilon.loglinear.match.prior<-mean(log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246]))
variance.log.epsilon.loglinear.match.prior<-var(log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246]))

chol.cov.loglinear.group.match.prior<-chol(covariance.loglinear.mat.match.prior)
inverse.t.chol.cov.loglinear.group.match.prior<-solve(t(chol.cov.loglinear.group.match.prior))
 
find.k1<-function(x,T){
sum((1:(T-2))*x)
}
find.k2<-function(x,T){
-sum((2:(T-1))*x)
}

M<-matrix(rep(mean.loglinear.vec.match.prior,10000),nrow=241,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(241*10000),nrow=241,ncol=10000)
sample.bridge.loglinear.group.match.prior<-M+t(chol.cov.loglinear.group.match.prior)%*%Z
sample.bridge.loglinear.group.match.prior<-t(sample.bridge.loglinear.group.match.prior)
gc()
sample.log.lambda.bridge.loglinear.match.prior<-rtruncnorm(10000,a=log(0.0001),b=Inf,mean=mean.log.lambda.loglinear.match.prior,sd=sqrt(variance.log.lambda.loglinear.match.prior))
sample.rho.bridge.loglinear.match.prior<-rtruncnorm(10000,a=-1,b=1,mean=mean.rho.loglinear.match.prior,sd=sqrt(variance.rho.loglinear.match.prior))
sample.log.epsilon.bridge.loglinear.match.prior<-rtruncnorm(10000,a=log(1),b=log(5000),mean=mean.log.epsilon.loglinear.match.prior,sd=sqrt(variance.log.epsilon.loglinear.match.prior))
full.sample.bridge.loglinear.group.match.prior<-cbind(apply(sample.bridge.loglinear.group.match.prior[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior,sample.log.lambda.bridge.loglinear.match.prior,sample.rho.bridge.loglinear.match.prior,exp(sample.log.epsilon.bridge.loglinear.match.prior))
rm(M);rm(Z);rm(sample.log.lambda.bridge.loglinear.match.prior);rm(sample.rho.bridge.loglinear.match.prior);rm(sample.log.epsilon.bridge.loglinear.match.prior);rm(sample.bridge.loglinear.group.match.prior);gc()
like.prior.loglinear.negbin.match.prior(full.sample.bridge.loglinear.group.match.prior[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior<-apply(full.sample.bridge.loglinear.group.match.prior,1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

transformation.dmvnorm.loglinear.match.prior<-function(x,mean.vec,rij,log.det.Jacobian,mean.log.lambda,variance.log.lambda,mean.rho,variance.rho,mean.log.epsilon,variance.log.epsilon){
n<-length(x)
y<-x[-c(242,243,244)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.y<-log(dtruncnorm(x[242],a=log(0.0001),b=Inf,mean=mean.log.lambda,sd=sqrt(variance.log.lambda)))
log.pdf.v<-log(dtruncnorm(x[243],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.u<-log(dtruncnorm(x[244],a=log(1),b=log(50000),mean=mean.log.epsilon,sd=sqrt(variance.log.epsilon)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.y+log.pdf.v+log.pdf.u
log.pdf.x
}
    
log.det.Jacobian.loglinear.group.match.prior<-determinant(inverse.t.chol.cov.loglinear.group.match.prior,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior(x=c(full.sample.bridge.loglinear.group.match.prior[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior[1000,246])),mean.vec=mean.loglinear.vec.match.prior,rij=inverse.t.chol.cov.loglinear.group.match.prior,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior,mean.log.lambda=mean.log.lambda.loglinear.match.prior,variance.log.lambda=variance.log.lambda.loglinear.match.prior,mean.rho=mean.rho.loglinear.match.prior,variance.rho=variance.rho.loglinear.match.prior,mean.log.epsilon=mean.log.epsilon.loglinear.match.prior,variance.log.epsilon=variance.log.epsilon.loglinear.match.prior)
dmvnorm(full.sample.bridge.loglinear.group.match.prior[1000,-c(1,2,244,245,246)],mean=mean.loglinear.vec.match.prior,sigma=covariance.loglinear.mat.match.prior,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior[1000,244],a=log(0.0001),b=Inf,mean=mean.log.lambda.loglinear.match.prior,sd=sqrt(variance.log.lambda.loglinear.match.prior)))+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior[1000,245],a=-1,b=1,mean=mean.rho.loglinear.match.prior,sd=sqrt(variance.rho.loglinear.match.prior)))+log(dtruncnorm(log(full.sample.bridge.loglinear.group.match.prior[1000,246]),a=log(1),b=log(50000),mean=mean.log.epsilon.loglinear.match.prior,sd=sqrt(variance.log.epsilon.loglinear.match.prior)))
 
q2.loglinear.group.match.prior<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])),1,transformation.dmvnorm.loglinear.match.prior,mean.vec=mean.loglinear.vec.match.prior,rij=inverse.t.chol.cov.loglinear.group.match.prior,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior,mean.log.lambda=mean.log.lambda.loglinear.match.prior,variance.log.lambda=variance.log.lambda.loglinear.match.prior,mean.rho=mean.rho.loglinear.match.prior,variance.rho=variance.rho.loglinear.match.prior,mean.log.epsilon=mean.log.epsilon.loglinear.match.prior,variance.log.epsilon=variance.log.epsilon.loglinear.match.prior)
q2.bridge.loglinear.group.match.prior<-apply(cbind(full.sample.bridge.loglinear.group.match.prior[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior[,246])),1,transformation.dmvnorm.loglinear.match.prior,mean.vec=mean.loglinear.vec.match.prior,rij=inverse.t.chol.cov.loglinear.group.match.prior,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior,mean.log.lambda=mean.log.lambda.loglinear.match.prior,variance.log.lambda=variance.log.lambda.loglinear.match.prior,mean.rho=mean.rho.loglinear.match.prior,variance.rho=variance.rho.loglinear.match.prior,mean.log.epsilon=mean.log.epsilon.loglinear.match.prior,variance.log.epsilon=variance.log.epsilon.loglinear.match.prior)   
log.l.loglinear.group.match.prior<-likelihood.loglinear.group.match.prior-q2.loglinear.group.match.prior
log.l.tilda.loglinear.group.match.prior<-likelihood.bridge.loglinear.group.match.prior-q2.bridge.loglinear.group.match.prior

log.l.tilda.loglinear.group.match.prior<-log.l.tilda.loglinear.group.match.prior+24300
log.l.loglinear.group.match.prior<-log.l.loglinear.group.match.prior+24300
l.loglinear.group.match.prior<-exp(log.l.loglinear.group.match.prior)
l.tilda.loglinear.group.match.prior<-exp(log.l.tilda.loglinear.group.match.prior)
 
nc.loglinear.group.match.prior<-bridge(initial=100,m=1000,sample1=theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,sample2=full.sample.bridge.loglinear.group.match.prior,n1=10000,n2=20000,l=l.loglinear.group.match.prior,l.tilda=l.tilda.loglinear.group.match.prior) 
log(nc.loglinear.group.match.prior)-24300 #-23692.37 (thin by 500,n2=n1=10000)
							#-23691.36 (thin by 500,n2=2*n1=20000)

##no truncation on lambda and epsilon

mean.loglinear.vec.match.prior<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,244,245,246)],theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])),2,mean)
covariance.loglinear.mat.match.prior<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,244,245,246)],theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])))
mean.rho.loglinear.match.prior<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245])
variance.rho.loglinear.match.prior<-var(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,245])

chol.cov.loglinear.group.match.prior<-chol(covariance.loglinear.mat.match.prior)
inverse.t.chol.cov.loglinear.group.match.prior<-solve(t(chol.cov.loglinear.group.match.prior))
 
find.k1<-function(x,T){
sum((1:(T-2))*x)
}
find.k2<-function(x,T){
-sum((2:(T-1))*x)
}

M<-matrix(rep(mean.loglinear.vec.match.prior,20000),nrow=243,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(243*20000),nrow=243,ncol=20000)
sample.bridge.loglinear.group.match.prior<-M+t(chol.cov.loglinear.group.match.prior)%*%Z
sample.bridge.loglinear.group.match.prior<-t(sample.bridge.loglinear.group.match.prior)
gc()
sample.rho.bridge.loglinear.match.prior<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.loglinear.match.prior,sd=sqrt(variance.rho.loglinear.match.prior))
full.sample.bridge.loglinear.group.match.prior<-cbind(apply(sample.bridge.loglinear.group.match.prior[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior[,1:242],sample.rho.bridge.loglinear.match.prior,exp(sample.bridge.loglinear.group.match.prior[,243]))
rm(M);rm(Z);rm(sample.rho.bridge.loglinear.match.prior);rm(sample.bridge.loglinear.group.match.prior);gc()
like.prior.loglinear.negbin.match.prior(full.sample.bridge.loglinear.group.match.prior[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior<-apply(full.sample.bridge.loglinear.group.match.prior,1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

transformation.dmvnorm.loglinear.match.prior.2<-function(x,mean.vec,rij,log.det.Jacobian,mean.rho,variance.rho){
n<-length(x)
y<-x[-c(243)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.v<-log(dtruncnorm(x[243],a=-1,b=1,mean=mean.rho,sd=sqrt(variance.rho)))
log.pdf.x<-log.pdf.z+log.det.Jacobian+log.pdf.v
log.pdf.x
}
    
log.det.Jacobian.loglinear.group.match.prior<-determinant(inverse.t.chol.cov.loglinear.group.match.prior,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.2(x=c(full.sample.bridge.loglinear.group.match.prior[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior[1000,246])),mean.vec=mean.loglinear.vec.match.prior,rij=inverse.t.chol.cov.loglinear.group.match.prior,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior,mean.rho=mean.rho.loglinear.match.prior,variance.rho=variance.rho.loglinear.match.prior)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior[1000,-c(1,2,245,246)],log(full.sample.bridge.loglinear.group.match.prior[1000,246])),mean=mean.loglinear.vec.match.prior,sigma=covariance.loglinear.mat.match.prior,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior[1000,245],a=-1,b=1,mean=mean.rho.loglinear.match.prior,sd=sqrt(variance.rho.loglinear.match.prior)))
 
q2.loglinear.group.match.prior<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])),1,transformation.dmvnorm.loglinear.match.prior.2,mean.vec=mean.loglinear.vec.match.prior,rij=inverse.t.chol.cov.loglinear.group.match.prior,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior,mean.rho=mean.rho.loglinear.match.prior,variance.rho=variance.rho.loglinear.match.prior)
q2.bridge.loglinear.group.match.prior<-apply(cbind(full.sample.bridge.loglinear.group.match.prior[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior[,246])),1,transformation.dmvnorm.loglinear.match.prior.2,mean.vec=mean.loglinear.vec.match.prior,rij=inverse.t.chol.cov.loglinear.group.match.prior,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior,mean.rho=mean.rho.loglinear.match.prior,variance.rho=variance.rho.loglinear.match.prior)   
log.l.loglinear.group.match.prior<-likelihood.loglinear.group.match.prior-q2.loglinear.group.match.prior
log.l.tilda.loglinear.group.match.prior<-likelihood.bridge.loglinear.group.match.prior-q2.bridge.loglinear.group.match.prior

log.l.tilda.loglinear.group.match.prior<-log.l.tilda.loglinear.group.match.prior+24300
log.l.loglinear.group.match.prior<-log.l.loglinear.group.match.prior+24300
l.loglinear.group.match.prior<-exp(log.l.loglinear.group.match.prior)
l.tilda.loglinear.group.match.prior<-exp(log.l.tilda.loglinear.group.match.prior)
 
nc.loglinear.group.match.prior<-bridge(initial=100,m=1000,sample1=theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,sample2=full.sample.bridge.loglinear.group.match.prior,n1=10000,n2=10000,l=l.loglinear.group.match.prior,l.tilda=l.tilda.loglinear.group.match.prior) 
log(nc.loglinear.group.match.prior)-24300 #-23691.69 (thin by 500,n2=n1=10000)
							#-23690.68 (thin by 500,n2=2*n1=20000)

##splitting

likelihood.loglinear.group.match.prior.split<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,],1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec.match.prior.split<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,-c(1,2,245,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,246])),2,mean)
covariance.loglinear.mat.match.prior.split<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,-c(1,2,245,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,246])))
mean.rho.loglinear.match.prior.split<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,245])
variance.rho.loglinear.match.prior.split<-var(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,245])

chol.cov.loglinear.group.match.prior.split<-chol(covariance.loglinear.mat.match.prior.split)
inverse.t.chol.cov.loglinear.group.match.prior.split<-solve(t(chol.cov.loglinear.group.match.prior.split))

M<-matrix(rep(mean.loglinear.vec.match.prior.split,5000),nrow=243,ncol=5000,byrow=FALSE)
Z<-matrix(rnorm(243*5000),nrow=243,ncol=5000)
sample.bridge.loglinear.group.match.prior.split<-M+t(chol.cov.loglinear.group.match.prior.split)%*%Z
sample.bridge.loglinear.group.match.prior.split<-t(sample.bridge.loglinear.group.match.prior.split)
gc()
sample.rho.bridge.loglinear.match.prior.split<-rtruncnorm(5000,a=-1,b=1,mean=mean.rho.loglinear.match.prior.split,sd=sqrt(variance.rho.loglinear.match.prior.split))
full.sample.bridge.loglinear.group.match.prior.split<-cbind(apply(sample.bridge.loglinear.group.match.prior.split[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.split[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.split[,1:242],sample.rho.bridge.loglinear.match.prior.split,exp(sample.bridge.loglinear.group.match.prior.split[,243]))
rm(M);rm(Z);rm(sample.rho.bridge.loglinear.match.prior.split);rm(sample.bridge.loglinear.group.match.prior.split);gc()
like.prior.loglinear.negbin.match.prior(full.sample.bridge.loglinear.group.match.prior.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior.split<-apply(full.sample.bridge.loglinear.group.match.prior.split,1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
    
log.det.Jacobian.loglinear.group.match.prior.split<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.split,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.2(x=c(full.sample.bridge.loglinear.group.match.prior.split[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.split[1000,246])),mean.vec=mean.loglinear.vec.match.prior.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.split,mean.rho=mean.rho.loglinear.match.prior.split,variance.rho=variance.rho.loglinear.match.prior.split)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.split[1000,-c(1,2,245,246)],log(full.sample.bridge.loglinear.group.match.prior.split[1000,246])),mean=mean.loglinear.vec.match.prior.split,sigma=covariance.loglinear.mat.match.prior.split,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior.split[1000,245],a=-1,b=1,mean=mean.rho.loglinear.match.prior.split,sd=sqrt(variance.rho.loglinear.match.prior.split)))
 
q2.loglinear.group.match.prior.split<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,-c(1,2,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,246])),1,transformation.dmvnorm.loglinear.match.prior.2,mean.vec=mean.loglinear.vec.match.prior.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.split,mean.rho=mean.rho.loglinear.match.prior.split,variance.rho=variance.rho.loglinear.match.prior.split)
q2.bridge.loglinear.group.match.prior.split<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.split[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.split[,246])),1,transformation.dmvnorm.loglinear.match.prior.2,mean.vec=mean.loglinear.vec.match.prior.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.split,mean.rho=mean.rho.loglinear.match.prior.split,variance.rho=variance.rho.loglinear.match.prior.split)   
log.l.loglinear.group.match.prior.split<-likelihood.loglinear.group.match.prior.split-q2.loglinear.group.match.prior.split
log.l.tilda.loglinear.group.match.prior.split<-likelihood.bridge.loglinear.group.match.prior.split-q2.bridge.loglinear.group.match.prior.split

log.l.tilda.loglinear.group.match.prior.split<-log.l.tilda.loglinear.group.match.prior.split+24300
log.l.loglinear.group.match.prior.split<-log.l.loglinear.group.match.prior.split+24300
l.loglinear.group.match.prior.split<-exp(log.l.loglinear.group.match.prior.split)
l.tilda.loglinear.group.match.prior.split<-exp(log.l.tilda.loglinear.group.match.prior.split)
 
nc.loglinear.group.match.prior.split<-bridge(initial=100,m=10000,sample1=theta.AR1.over.negbin.int.y0.new.trunc.fast.group.hess.match.prior[5001:10000,],sample2=full.sample.bridge.loglinear.group.match.prior.split,n1=5000,n2=20000,l=l.loglinear.group.match.prior.split,l.tilda=l.tilda.loglinear.group.match.prior.split) 
log(nc.loglinear.group.match.prior.split)-24300 #-23691.59 (thin by 500,n2=n1=5000)
								#-23690.84 (thin by 500,n2=2*n1=10000)
								#-23690.15 (thin by 500,n2=4*n1=20000)

##cross-splitting

likelihood.loglinear.group.match.prior.split.2<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,],1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec.match.prior.split.2<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,-c(1,2,245,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,246])),2,mean)
covariance.loglinear.mat.match.prior.split.2<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,-c(1,2,245,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,246])))
mean.rho.loglinear.match.prior.split.2<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,245])
variance.rho.loglinear.match.prior.split.2<-var(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,245])

chol.cov.loglinear.group.match.prior.split.2<-chol(covariance.loglinear.mat.match.prior.split.2)
inverse.t.chol.cov.loglinear.group.match.prior.split.2<-solve(t(chol.cov.loglinear.group.match.prior.split.2))

M<-matrix(rep(mean.loglinear.vec.match.prior.split.2,10000),nrow=243,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(243*10000),nrow=243,ncol=10000)
sample.bridge.loglinear.group.match.prior.split.2<-M+t(chol.cov.loglinear.group.match.prior.split.2)%*%Z
sample.bridge.loglinear.group.match.prior.split.2<-t(sample.bridge.loglinear.group.match.prior.split.2)
gc()
sample.rho.bridge.loglinear.match.prior.split.2<-rtruncnorm(10000,a=-1,b=1,mean=mean.rho.loglinear.match.prior.split.2,sd=sqrt(variance.rho.loglinear.match.prior.split.2))
full.sample.bridge.loglinear.group.match.prior.split.2<-cbind(apply(sample.bridge.loglinear.group.match.prior.split.2[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.split.2[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.split.2[,1:242],sample.rho.bridge.loglinear.match.prior.split.2,exp(sample.bridge.loglinear.group.match.prior.split.2[,243]))
rm(M);rm(Z);rm(sample.rho.bridge.loglinear.match.prior.split.2);rm(sample.bridge.loglinear.group.match.prior.split.2);gc()
like.prior.loglinear.negbin.match.prior(full.sample.bridge.loglinear.group.match.prior.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior.split.2<-apply(full.sample.bridge.loglinear.group.match.prior.split.2,1,like.prior.loglinear.negbin.match.prior,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
    
log.det.Jacobian.loglinear.group.match.prior.split.2<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.2(x=c(full.sample.bridge.loglinear.group.match.prior.split.2[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.split.2[1000,246])),mean.vec=mean.loglinear.vec.match.prior.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.split.2,mean.rho=mean.rho.loglinear.match.prior.split.2,variance.rho=variance.rho.loglinear.match.prior.split.2)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.split.2[1000,-c(1,2,245,246)],log(full.sample.bridge.loglinear.group.match.prior.split.2[1000,246])),mean=mean.loglinear.vec.match.prior.split.2,sigma=covariance.loglinear.mat.match.prior.split.2,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior.split.2[1000,245],a=-1,b=1,mean=mean.rho.loglinear.match.prior.split.2,sd=sqrt(variance.rho.loglinear.match.prior.split.2)))
 
q2.loglinear.group.match.prior.split.2<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,-c(1,2,246)],log(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,246])),1,transformation.dmvnorm.loglinear.match.prior.2,mean.vec=mean.loglinear.vec.match.prior.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.split.2,mean.rho=mean.rho.loglinear.match.prior.split.2,variance.rho=variance.rho.loglinear.match.prior.split.2)
q2.bridge.loglinear.group.match.prior.split.2<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.split.2[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.split.2[,246])),1,transformation.dmvnorm.loglinear.match.prior.2,mean.vec=mean.loglinear.vec.match.prior.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.split.2,mean.rho=mean.rho.loglinear.match.prior.split.2,variance.rho=variance.rho.loglinear.match.prior.split.2)   
log.l.loglinear.group.match.prior.split.2<-likelihood.loglinear.group.match.prior.split.2-q2.loglinear.group.match.prior.split.2
log.l.tilda.loglinear.group.match.prior.split.2<-likelihood.bridge.loglinear.group.match.prior.split.2-q2.bridge.loglinear.group.match.prior.split.2

log.l.tilda.loglinear.group.match.prior.split.2<-log.l.tilda.loglinear.group.match.prior.split.2+24300
log.l.loglinear.group.match.prior.split.2<-log.l.loglinear.group.match.prior.split.2+24300
l.loglinear.group.match.prior.split.2<-exp(log.l.loglinear.group.match.prior.split.2)
l.tilda.loglinear.group.match.prior.split.2<-exp(log.l.tilda.loglinear.group.match.prior.split.2)
 
nc.loglinear.group.match.prior.split.2<-bridge(initial=100,m=10000,sample1=theta.AR1.over.negbin.int.y0.new.trunc.fast.group.hess.match.prior[1:5000,],sample2=full.sample.bridge.loglinear.group.match.prior.split.2,n1=5000,n2=10000,l=l.loglinear.group.match.prior.split.2,l.tilda=l.tilda.loglinear.group.match.prior.split.2) 
log(nc.loglinear.group.match.prior.split.2)-24300  #-23690.19 (thin by 500,n2=2*n1=10000)

so cross-splitting estimate is 0.5*(-23690.84-23690.19)=-23690.51


######################
##NBAPI-RW (constraints: sum(k_t)=sum(tk_t)=0)
######################

like.prior.loglinear.negbin.match.prior.RW<-function(param,Dxt,Ext,A,T,t,lx,lambda.alpha,lambda.beta,ak,bk,a.epsilon,b.epsilon){#supply param=c(k,beta,alpha,log.sigma2.k,log.lambda,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
sigma2.k<-exp(param[2*A+T+1])
lambda<-exp(param[2*A+T+2])
rho<-param[2*A+T+3]
epsilon<-param[2*A+T+4]

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-0:(T-1)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
i.R<-forwardsolve(R,diag(rep(1,T)))
i.Q<-i.R%*%t(i.R)
C<-J%*%i.Q%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-2*sigma2.k*D 
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE))+epsilon)	


{result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+sum(log(ddoublex(beta,mu=0,lambda=lambda.beta)))+dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)+
sum(log(ddoublex(alpha,mu=lx,lambda=lambda.alpha)))+log(lambda)-lambda*sigma2.k+log(sigma2.k)+ak*log(bk/400)-lgamma(ak)+ak*log(lambda)-bk/400*lambda+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
ak<-1
bk<-0.0001
a.epsilon<-25
b.epsilon<-0.05
lambda.alpha<-rep(2.5,A)
lambda.beta<-rep(0.03,A)
 
like.prior.loglinear.negbin.match.prior.RW(param=theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.loglinear.group.match.prior.RW<-apply(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,1,like.prior.loglinear.negbin.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec.match.prior.RW<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,245,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])),2,mean)
covariance.loglinear.mat.match.prior.RW<-cov(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,245,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])))

chol.cov.loglinear.group.match.prior.RW<-chol(covariance.loglinear.mat.match.prior.RW)
inverse.t.chol.cov.loglinear.group.match.prior.RW<-solve(t(chol.cov.loglinear.group.match.prior.RW))
 
find.k1<-function(x,T){
sum((1:(T-2))*x)
}
find.k2<-function(x,T){
-sum((2:(T-1))*x)
}

M<-matrix(rep(mean.loglinear.vec.match.prior.RW,10000),nrow=243,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(243*10000),nrow=243,ncol=10000)
sample.bridge.loglinear.group.match.prior.RW<-M+t(chol.cov.loglinear.group.match.prior.RW)%*%Z
sample.bridge.loglinear.group.match.prior.RW<-t(sample.bridge.loglinear.group.match.prior.RW)
gc()
full.sample.bridge.loglinear.group.match.prior.RW<-cbind(apply(sample.bridge.loglinear.group.match.prior.RW[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.RW[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.RW[,-243],rep(1,10000),exp(sample.bridge.loglinear.group.match.prior.RW[,243]))
rm(M);rm(Z);rm(sample.bridge.loglinear.group.match.prior.RW);gc()
like.prior.loglinear.negbin.match.prior.RW(full.sample.bridge.loglinear.group.match.prior.RW[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior.RW<-apply(full.sample.bridge.loglinear.group.match.prior.RW,1,like.prior.loglinear.negbin.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

transformation.dmvnorm.loglinear.match.prior.RW<-function(x,mean.vec,rij,log.det.Jacobian){
n<-length(x)
y<-x[-c(243)]
z<-rij%*%(y-mean.vec)
log.pdf.z<-sum(dnorm(z,mean=0,sd=1,log=TRUE))
log.pdf.x<-log.pdf.z+log.det.Jacobian
log.pdf.x
}
    
log.det.Jacobian.loglinear.group.match.prior.RW<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.RW,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.RW(x=c(full.sample.bridge.loglinear.group.match.prior.RW[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.RW[1000,246])),mean.vec=mean.loglinear.vec.match.prior.RW,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.RW[1000,-c(1,2,245,246)],log(full.sample.bridge.loglinear.group.match.prior.RW[1000,246])),mean=mean.loglinear.vec.match.prior.RW,sigma=covariance.loglinear.mat.match.prior.RW,log=TRUE)
 
q2.loglinear.group.match.prior.RW<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-c(1,2,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246])),1,transformation.dmvnorm.loglinear.match.prior.RW,mean.vec=mean.loglinear.vec.match.prior.RW,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW)
q2.bridge.loglinear.group.match.prior.RW<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.RW[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.RW[,246])),1,transformation.dmvnorm.loglinear.match.prior.RW,mean.vec=mean.loglinear.vec.match.prior.RW,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW)   
log.l.loglinear.group.match.prior.RW<-likelihood.loglinear.group.match.prior.RW-q2.loglinear.group.match.prior.RW
log.l.tilda.loglinear.group.match.prior.RW<-likelihood.bridge.loglinear.group.match.prior.RW-q2.bridge.loglinear.group.match.prior.RW

log.l.tilda.loglinear.group.match.prior.RW<-log.l.tilda.loglinear.group.match.prior.RW+24300
log.l.loglinear.group.match.prior.RW<-log.l.loglinear.group.match.prior.RW+24300
l.loglinear.group.match.prior.RW<-exp(log.l.loglinear.group.match.prior.RW)
l.tilda.loglinear.group.match.prior.RW<-exp(log.l.tilda.loglinear.group.match.prior.RW)
 
nc.loglinear.group.match.prior.RW<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,sample2=full.sample.bridge.loglinear.group.match.prior.RW,n1=10000,n2=10000,l=l.loglinear.group.match.prior.RW,l.tilda=l.tilda.loglinear.group.match.prior.RW) 
log(nc.loglinear.group.match.prior.RW)-24300 #-23691.63 (n1=10000,n2=10000, thin by 500)
							   #-23691.31 (n1=10000,n2=20000, thin by 500)

############
##splitting
############

likelihood.loglinear.group.match.prior.RW.split<-apply(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,],1,like.prior.loglinear.negbin.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec.match.prior.RW.split<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,-c(1,2,245,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,246])),2,mean)
covariance.loglinear.mat.match.prior.RW.split<-cov(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,-c(1,2,245,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,246])))

chol.cov.loglinear.group.match.prior.RW.split<-chol(covariance.loglinear.mat.match.prior.RW.split)
inverse.t.chol.cov.loglinear.group.match.prior.RW.split<-solve(t(chol.cov.loglinear.group.match.prior.RW.split))

M<-matrix(rep(mean.loglinear.vec.match.prior.RW.split,5000),nrow=243,ncol=5000,byrow=FALSE)
Z<-matrix(rnorm(243*5000),nrow=243,ncol=5000)
sample.bridge.loglinear.group.match.prior.RW.split<-M+t(chol.cov.loglinear.group.match.prior.RW.split)%*%Z
sample.bridge.loglinear.group.match.prior.RW.split<-t(sample.bridge.loglinear.group.match.prior.RW.split)
gc()
full.sample.bridge.loglinear.group.match.prior.RW.split<-cbind(apply(sample.bridge.loglinear.group.match.prior.RW.split[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.RW.split[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.RW.split[,-243],rep(1,5000),exp(sample.bridge.loglinear.group.match.prior.RW.split[,243]))
rm(M);rm(Z);rm(sample.bridge.loglinear.group.match.prior.RW.split);gc()
like.prior.loglinear.negbin.match.prior.RW(full.sample.bridge.loglinear.group.match.prior.RW.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior.RW.split<-apply(full.sample.bridge.loglinear.group.match.prior.RW.split,1,like.prior.loglinear.negbin.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
    
log.det.Jacobian.loglinear.group.match.prior.RW.split<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.RW.split,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.RW(x=c(full.sample.bridge.loglinear.group.match.prior.RW.split[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.RW.split[1000,246])),mean.vec=mean.loglinear.vec.match.prior.RW.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW.split)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.RW.split[1000,-c(1,2,245,246)],log(full.sample.bridge.loglinear.group.match.prior.RW.split[1000,246])),mean=mean.loglinear.vec.match.prior.RW.split,sigma=covariance.loglinear.mat.match.prior.RW.split,log=TRUE)

q2.loglinear.group.match.prior.RW.split<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,-c(1,2,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,246])),1,transformation.dmvnorm.loglinear.match.prior.RW,mean.vec=mean.loglinear.vec.match.prior.RW.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW.split)
q2.bridge.loglinear.group.match.prior.RW.split<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.RW.split[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.RW.split[,246])),1,transformation.dmvnorm.loglinear.match.prior.RW,mean.vec=mean.loglinear.vec.match.prior.RW.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW.split)   
log.l.loglinear.group.match.prior.RW.split<-likelihood.loglinear.group.match.prior.RW.split-q2.loglinear.group.match.prior.RW.split
log.l.tilda.loglinear.group.match.prior.RW.split<-likelihood.bridge.loglinear.group.match.prior.RW.split-q2.bridge.loglinear.group.match.prior.RW.split

log.l.tilda.loglinear.group.match.prior.RW.split<-log.l.tilda.loglinear.group.match.prior.RW.split+24300
log.l.loglinear.group.match.prior.RW.split<-log.l.loglinear.group.match.prior.RW.split+24300
l.loglinear.group.match.prior.RW.split<-exp(log.l.loglinear.group.match.prior.RW.split)
l.tilda.loglinear.group.match.prior.RW.split<-exp(log.l.tilda.loglinear.group.match.prior.RW.split)
 
nc.loglinear.group.match.prior.RW.split<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,],sample2=full.sample.bridge.loglinear.group.match.prior.RW.split,n1=5000,n2=5000,l=l.loglinear.group.match.prior.RW.split,l.tilda=l.tilda.loglinear.group.match.prior.RW.split) 
log(nc.loglinear.group.match.prior.RW.split)-24300    #-23690.20 (n1=5000,n2=5000, thin by 500)
									#-23690.17 (n1=5000,n2=10000, thin by 500)
									#-23690.15 (n1=5000,n2=20000, thin by 500)

############
##cross-splitting
############

likelihood.loglinear.group.match.prior.RW.split.2<-apply(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,],1,like.prior.loglinear.negbin.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)

mean.loglinear.vec.match.prior.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,-c(1,2,245,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,246])),2,mean)
covariance.loglinear.mat.match.prior.RW.split.2<-cov(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,-c(1,2,245,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[5001:10000,246])))

chol.cov.loglinear.group.match.prior.RW.split.2<-chol(covariance.loglinear.mat.match.prior.RW.split.2)
inverse.t.chol.cov.loglinear.group.match.prior.RW.split.2<-solve(t(chol.cov.loglinear.group.match.prior.RW.split.2))

M<-matrix(rep(mean.loglinear.vec.match.prior.RW.split.2,10000),nrow=243,ncol=10000,byrow=FALSE)
Z<-matrix(rnorm(243*10000),nrow=243,ncol=10000)
sample.bridge.loglinear.group.match.prior.RW.split.2<-M+t(chol.cov.loglinear.group.match.prior.RW.split.2)%*%Z
sample.bridge.loglinear.group.match.prior.RW.split.2<-t(sample.bridge.loglinear.group.match.prior.RW.split.2)
gc()
full.sample.bridge.loglinear.group.match.prior.RW.split.2<-cbind(apply(sample.bridge.loglinear.group.match.prior.RW.split.2[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.RW.split.2[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.RW.split.2[,-243],rep(1,10000),exp(sample.bridge.loglinear.group.match.prior.RW.split.2[,243]))
rm(M);rm(Z);rm(sample.bridge.loglinear.group.match.prior.RW.split.2);gc()
like.prior.loglinear.negbin.match.prior.RW(full.sample.bridge.loglinear.group.match.prior.RW.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
likelihood.bridge.loglinear.group.match.prior.RW.split.2<-apply(full.sample.bridge.loglinear.group.match.prior.RW.split.2,1,like.prior.loglinear.negbin.match.prior.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon)
    
log.det.Jacobian.loglinear.group.match.prior.RW.split.2<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.RW.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.RW(x=c(full.sample.bridge.loglinear.group.match.prior.RW.split.2[1000,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.RW.split.2[1000,246])),mean.vec=mean.loglinear.vec.match.prior.RW.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW.split.2)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.RW.split.2[1000,-c(1,2,245,246)],log(full.sample.bridge.loglinear.group.match.prior.RW.split.2[1000,246])),mean=mean.loglinear.vec.match.prior.RW.split.2,sigma=covariance.loglinear.mat.match.prior.RW.split.2,log=TRUE)

q2.loglinear.group.match.prior.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,-c(1,2,246)],log(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,246])),1,transformation.dmvnorm.loglinear.match.prior.RW,mean.vec=mean.loglinear.vec.match.prior.RW.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW.split.2)
q2.bridge.loglinear.group.match.prior.RW.split.2<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.RW.split.2[,-c(1,2,246)],log(full.sample.bridge.loglinear.group.match.prior.RW.split.2[,246])),1,transformation.dmvnorm.loglinear.match.prior.RW,mean.vec=mean.loglinear.vec.match.prior.RW.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.RW.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.RW.split.2)   
log.l.loglinear.group.match.prior.RW.split.2<-likelihood.loglinear.group.match.prior.RW.split.2-q2.loglinear.group.match.prior.RW.split.2
log.l.tilda.loglinear.group.match.prior.RW.split.2<-likelihood.bridge.loglinear.group.match.prior.RW.split.2-q2.bridge.loglinear.group.match.prior.RW.split.2

log.l.tilda.loglinear.group.match.prior.RW.split.2<-log.l.tilda.loglinear.group.match.prior.RW.split.2+24300
log.l.loglinear.group.match.prior.RW.split.2<-log.l.loglinear.group.match.prior.RW.split.2+24300
l.loglinear.group.match.prior.RW.split.2<-exp(log.l.loglinear.group.match.prior.RW.split.2)
l.tilda.loglinear.group.match.prior.RW.split.2<-exp(log.l.tilda.loglinear.group.match.prior.RW.split.2)
 
nc.loglinear.group.match.prior.RW.split.2<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:5000,],sample2=full.sample.bridge.loglinear.group.match.prior.RW.split.2,n1=5000,n2=10000,l=l.loglinear.group.match.prior.RW.split.2,l.tilda=l.tilda.loglinear.group.match.prior.RW.split.2) 
log(nc.loglinear.group.match.prior.RW.split.2)-24300 #-23690.12 (n1=5000,n2=10000, thin by 500)

so cross-splitting estimate is 0.5*(-23690.17-23690.12)=-23690.15

###################################
##Model Averaging
####################################

post.prob.RW.loglinear<-exp(-23690.15+23690.51)/(1+exp(-23690.15+23690.51)) #0.5890404
post.prob.RW.matchprior<-exp(-23798.61+23800.2)/(1+exp(-23798.61+23800.2))  #0.8306161

average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior<-rbind(theta.RW.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:round(post.prob.RW.loglinear*10000),],theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:round((1-post.prob.RW.loglinear)*10000),])
average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior<-rbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior[1:round(post.prob.RW.matchprior*10000),],theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:round((1-post.prob.RW.matchprior)*10000),])

alpha.loglinear.matchprior.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143:242]
alpha.loglinear.matchprior.average.percentile<-apply(alpha.loglinear.matchprior.average,2,percentile.fn)
beta.loglinear.matchprior.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43:142]
beta.loglinear.matchprior.average.percentile<-apply(beta.loglinear.matchprior.average,2,percentile.fn)

plot(alpha.loglinear.matchprior.average.percentile[2,],col=2,type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Age",ylab="",main=expression(alpha[x]))
lines(alpha.loglinear.matchprior.average.percentile[1,],col=2,lty=2)
lines(alpha.loglinear.matchprior.average.percentile[3,],col=2,lty=2)
plot(beta.loglinear.matchprior.average.percentile[2,],col=2,type="l",ylim=c(-0.04,0.025),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Age",ylab="",main=expression(beta[x]))
lines(beta.loglinear.matchprior.average.percentile[1,],col=2,lty=2)
lines(beta.loglinear.matchprior.average.percentile[3,],col=2,lty=2)
legend("bottomright",c("NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),lty=c(1,1,2,2),col=c(1,2,1,2))

k.loglinear.matchprior.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1:42]
k.loglinear.matchprior.average.percentile<-apply(k.loglinear.matchprior.average,2,percentile.fn)

NB.loglinear.projection<-function(posterior.param,h,A,T,t0){#note that sigma2.k and sigma2.beta are supplied with logarithm
t<-t0:(t0+T-1)
alpha<-posterior.param[(A+T+1):(2*A+T)]
beta<-posterior.param[(T+1):(A+T)]
kappa<-posterior.param[1:T]
rho<-posterior.param[2*A+T+3]
sigma2.k<-(exp(posterior.param[2*A+T+1]))
lambda<-(exp(posterior.param[2*A+T+2]))
epsilon<-posterior.param[2*A+T+4]
t.new<-(t0+T):(t0+T+h-1)
kappa.forecast<-rho*kappa[T]+rnorm(1,0,sqrt(2*sigma2.k))
for (i in 2:h){
kappa.forecast[i]<-rho*kappa.forecast[i-1]+rnorm(1,0,sqrt(2*sigma2.k))
}
logmiuxt.forecast<-matrix(rep(alpha,h),nrow=A,ncol=h,byrow=FALSE)+beta%*%t(t.new)+matrix(rep(kappa.forecast,A),nrow=A,ncol=h,byrow=TRUE)+matrix(log(rgamma(A*h,epsilon,epsilon)),nrow=A,ncol=h)
return(rbind(logmiuxt.forecast,kappa.forecast))
}


full.projected.ng.loglinear.average<-apply(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,1,NB.loglinear.projection,h=26,A=100,T=42,t0=-21)
k.forecast.ng.loglinear.average<-full.projected.ng.loglinear.average[(seq(from=101,to=2626,by=101)),]
full.projected.ng.loglinear.average<-full.projected.ng.loglinear.average[-(seq(from=101,to=2626,by=101)),];gc()

k.loglinear.forecast.matchprior.average.percentile<-apply(k.forecast.ng.loglinear.average,1,percentile.fn)
plot((-41):0,k.loglinear.matchprior.average.percentile[2,],col=2,xaxt="n",type="l",yaxt="n",xlim=c(-41,26),ylim=c(-0.2,0.16),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Year",ylab="",main=expression(kappa[t]))
axis(1,at=c(seq(-41,26,by=10)),label=c(seq(1961,2028,by=10)),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
axis(2,at=c(seq(-0.2,0.2,by=0.1)),label=c(seq(-0.2,0.2,by=0.1)),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines((-41):0,k.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines((-41):0,k.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
lines(1:26,k.loglinear.forecast.matchprior.average.percentile[2,],col=2)
lines(1:26,k.loglinear.forecast.matchprior.average.percentile[1,],lty=2,col=2)
lines(1:26,k.loglinear.forecast.matchprior.average.percentile[3,],lty=2,col=2)


alpha.ng.matchprior.average<-average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,143:242]
alpha.ng.matchprior.average.percentile<-apply(alpha.ng.matchprior.average,2,percentile.fn)
beta.ng.matchprior.average<-average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,43:142]
beta.ng.matchprior.average.percentile<-apply(beta.ng.matchprior.average,2,percentile.fn)

lines(alpha.ng.matchprior.average.percentile[2,],type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Age",ylab="",main=expression(alpha[x]))
lines(alpha.ng.matchprior.average.percentile[1,],lty=2)
lines(alpha.ng.matchprior.average.percentile[3,],lty=2)
lines(beta.ng.matchprior.average.percentile[2,],type="l",ylim=c(0,0.026),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Age",ylab="",main=expression(beta[x]))
lines(beta.ng.matchprior.average.percentile[1,],lty=2)
lines(beta.ng.matchprior.average.percentile[3,],lty=2)

k.ng.matchprior.average<-average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,1:42]
k.ng.matchprior.average.percentile<-apply(k.ng.matchprior.average,2,percentile.fn)

NB.matchprior.projection<-function(posterior.param,h,A,T,t0){#note that sigma2.k and sigma2.beta are supplied with logarithm
t<-t0:(t0+T-1)
alpha<-posterior.param[(A+T+1):(2*A+T)]
beta<-posterior.param[(T+1):(A+T)]
kappa<-posterior.param[1:T]
gamma1<-posterior.param[2*A+T+3]
gamma2<-posterior.param[2*A+T+4]
rho<-posterior.param[2*A+T+5]
sigma2.k<-(exp(posterior.param[2*A+T+1]))
sigma2.beta<-(exp(posterior.param[2*A+T+2]))
epsilon<-posterior.param[2*A+T+6]
t.new<-(t0+T):(t0+T+h-1)
kappa.forecast<-gamma1+gamma2*t.new[1]+rho*(kappa[T]-gamma1-gamma2*t[T])+rnorm(1,0,sqrt(sigma2.k))
for (i in 2:h){
kappa.forecast[i]<-gamma1+gamma2*t.new[i]+rho*(kappa.forecast[i-1]-gamma1-gamma2*t.new[i-1])+rnorm(1,0,sqrt(sigma2.k))
}
logmiuxt.forecast<-alpha+beta%*%t(kappa.forecast)+matrix(log(rgamma(A*h,epsilon,epsilon)),nrow=A,ncol=h)
return(rbind(logmiuxt.forecast,kappa.forecast))
}

full.projected.ng.matchprior.average<-apply(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior,1,NB.matchprior.projection,h=26,A=100,T=42,t0=-21)
k.forecast.ng.matchprior.average<-full.projected.ng.matchprior.average[(seq(from=101,to=2626,by=101)),]
full.projected.ng.matchprior.average<-full.projected.ng.matchprior.average[-(seq(from=101,to=2626,by=101)),];gc()

k.ng.forecast.matchprior.average.percentile<-apply(k.forecast.ng.matchprior.average,1,percentile.fn)
plot((-41):0,k.ng.matchprior.average.percentile[2,],xaxt="n",yaxt="n",type="l",xlim=c(-41,26),ylim=c(-105,30),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Year",ylab="",main=expression(kappa[t]))
axis(1,at=c(seq(-41,26,by=10)),label=c(seq(1961,2028,by=10)),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
axis(2,at=c(seq(-100,140,by=40)),labe=c(seq(-100,140,by=40)),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines((-41):0,k.ng.matchprior.average.percentile[1,],lty=2)
lines((-41):0,k.ng.matchprior.average.percentile[3,],lty=2)
lines(1:26,k.ng.forecast.matchprior.average.percentile[2,])
lines(1:26,k.ng.forecast.matchprior.average.percentile[1,],lty=2)
lines(1:26,k.ng.forecast.matchprior.average.percentile[3,],lty=2)

par(mfrow=c(2,2))
plot(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243])),main=expression(sigma[k]^2),xlab="",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244])),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(lambda),xlab="")
dens.rho.loglinear.AR1<-density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:4110,245],n=50000)
plot(dens.rho.loglinear.AR1$x,0.4109596*dens.rho.loglinear.AR1$y,main=expression(rho),ylab="Density",xlab="",xaxt="n",ylim=c(0,1.2),xlim=c(0,1.1),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
axis(1,at=c(0,0.25,0.5,0.75,1.055),label=c(0,0.25,0.5,0.75,1))
lines(c(1.055,1.055),c(0,0.5890404))
plot(density(1/average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],n=50000),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(1/phi),xlab="")

par(mfrow=c(3,2))
plot(density(exp(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243])),main=expression(sigma[k]^2),xlab="",xlim=c(0,11),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(density(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,245],n=50000),main=expression(psi[1]),xlab="",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(density(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,246]),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(psi[2]),xlim=c(-3,0),ylim=c(0,2),xlab="")
dens.rho.lc.matchprior.AR1<-density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:1694,247],n=50000)
plot(c(0,dens.rho.lc.matchprior.AR1$x),c(0,0.1693839*dens.rho.lc.matchprior.AR1$y),main=expression(rho),ylab="Density",xlab="",xaxt="n",xlim=c(0,1.1),ylim=c(0,1),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
axis(1,at=c(0,0.25,0.5,0.75,1.07),label=c(0,0.25,0.5,0.75,1))
lines(c(1.07,1.07),c(0,0.8306161))
plot(density(1/average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248],n=50000),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(1/phi),xlab="")

#combined kernel densities
par(mfrow=c(3,2))
plot(density(exp(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243])),main=expression(sigma[k]^2),xlab="",xlim=c(0,6),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243])),col=2,cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(density(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,245],n=50000),main=expression(psi[1]),xlab="",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(density(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,246]),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(psi[2]),xlim=c(-3,0),ylim=c(0,2),xlab="")
plot(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244])),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(lambda),xlab="",col=2)
dens.rho.lc.matchprior.AR1<-density(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[1:1694,247],n=50000)
plot(c(0,dens.rho.lc.matchprior.AR1$x),c(0,0.1693839*dens.rho.lc.matchprior.AR1$y),main=expression(rho),ylab="Density",xlab="",xaxt="n",xlim=c(0,1.1),ylim=c(0,1.2),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
axis(1,at=c(0,0.25,0.5,0.75,1.07),label=c(0,0.25,0.5,0.75,1))
lines(c(1.07,1.07),c(0,0.8306161))
dens.rho.loglinear.AR1<-density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:4110,245],n=50000)
lines(dens.rho.loglinear.AR1$x,0.4109596*dens.rho.loglinear.AR1$y,col=2,xaxt="n",ylim=c(0,1.2),xlim=c(0,1.1),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(c(1.07,1.07),c(0,0.5890404),col=2)
plot(density(1/average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248],n=50000),ylim=c(0,7100),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,main=expression(1/phi),xlab="")
lines(density(1/average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],n=50000),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,col=2)



#################
##Fitted and Projection of log rates
##################

full.projected.ng.matchprior.average<-apply(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior,1,NB.matchprior.projection,h=26,A=100,T=42,t0=-21)
k.forecast.ng.matchprior.average<-full.projected.ng.matchprior.average[(seq(from=101,to=2626,by=101)),]
full.projected.ng.matchprior.average<-full.projected.ng.matchprior.average[-(seq(from=101,to=2626,by=101)),];gc()

full.projected.ng.loglinear.average<-apply(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior,1,NB.loglinear.projection,h=26,A=100,T=42,t0=-21)
k.forecast.ng.loglinear.average<-full.projected.ng.loglinear.average[(seq(from=101,to=2626,by=101)),]
full.projected.ng.loglinear.average<-full.projected.ng.loglinear.average[-(seq(from=101,to=2626,by=101)),];gc()

generate.Dxt.ng.fn<-function(x,Ext.valid,A,h){
a<-x[(A+h+1):(2*A+h)]
b<-x[(h+1):(A+h)]
k<-x[1:h]
e<-x[2*A+h+6]
Ext.valid.vec<-as.vector(Ext.valid)
logmiuxt.vec<-as.vector(matrix(rep(a,h),nrow=A,ncol=h,byrow=FALSE)+b%*%t(k))
rnbinom(A*h,size=e,prob=(e/(e+Ext.valid.vec*exp(logmiuxt.vec))))
}

projected.Dxt.11yrs.ng.matchprior.average<-apply(cbind(t(k.forecast.ng.matchprior.average[1:14,]),average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,-(1:42)]),1,generate.Dxt.ng.fn,Ext.valid=EWexpo.female.mat.ex.validation,A=100,h=14)
EWexpo.female.mat.ex.validation.mat<-matrix(rep(as.vector(EWexpo.female.mat.ex.validation),10000),nrow=length(as.vector(EWexpo.female.mat.ex.validation)),ncol=10000,byrow=FALSE)
projected.miuxt.11yrs.ng.matchprior.average.withover<-projected.Dxt.11yrs.ng.matchprior.average/EWexpo.female.mat.ex.validation.mat 

fitted.Dxt.11yrs.ng.matchprior.average<-apply(cbind(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior),1,generate.Dxt.ng.fn,Ext.valid=Ext,A=100,h=42)
EWexpo.female.mat.ex.mat<-matrix(rep(as.vector(Ext),10000),nrow=length(as.vector(Ext)),ncol=10000,byrow=FALSE)
fitted.miuxt.11yrs.ng.matchprior.average.withover<-fitted.Dxt.11yrs.ng.matchprior.average/EWexpo.female.mat.ex.mat

generate.Dxt.ng.loglinear.fn<-function(x,Ext.valid,A,h,t0){
t<-t0:(t0+h-1)
a<-x[(A+h+1):(2*A+h)]
b<-x[(h+1):(A+h)]
k<-x[1:h]
e<-x[2*A+h+4]
Ext.valid.vec<-as.vector(Ext.valid)
logmiuxt.vec<-as.vector(matrix(rep(a,h),nrow=A,ncol=h,byrow=FALSE)+b%*%t(t)+matrix(rep(k,A),nrow=A,ncol=h,byrow=TRUE))
rnbinom(A*h,size=e,prob=(e/(e+Ext.valid.vec*exp(logmiuxt.vec))))
}

projected.Dxt.11yrs.ng.loglinear.average<-apply(cbind(t(k.forecast.ng.loglinear.average[1:14,]),average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,-(1:42)]),1,generate.Dxt.ng.loglinear.fn,Ext.valid=EWexpo.female.mat.ex.validation,A=100,h=14,t0=(-21+T))
EWexpo.female.mat.ex.validation.mat<-matrix(rep(as.vector(EWexpo.female.mat.ex.validation),10000),nrow=length(as.vector(EWexpo.female.mat.ex.validation)),ncol=10000,byrow=FALSE)
projected.miuxt.11yrs.ng.loglinear.average.withover<-projected.Dxt.11yrs.ng.loglinear.average/EWexpo.female.mat.ex.validation.mat 

fitted.Dxt.11yrs.ng.loglinear.average<-apply(cbind(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior),1,generate.Dxt.ng.loglinear.fn,Ext.valid=Ext,A=100,h=42,t0=-21)
EWexpo.female.mat.ex.mat<-matrix(rep(as.vector(Ext),10000),nrow=length(as.vector(Ext)),ncol=10000,byrow=FALSE)
fitted.miuxt.11yrs.ng.loglinear.average.withover<-fitted.Dxt.11yrs.ng.loglinear.average/EWexpo.female.mat.ex.mat


#age 0
ind.new<-seq(1,1400,by=100)
crude.logmiuxt.forecast.age0.ng.matchprior.average<-log(projected.miuxt.11yrs.ng.matchprior.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age0.ng.matchprior.average<-apply(crude.logmiuxt.forecast.age0.ng.matchprior.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[1,],pch=4,xlim=c(0,55),ylim=c(-6.45,-3.8),xaxt="n",xlab="Year",ylab="",main="Age 0",cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.matchprior.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.matchprior.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA),lty=c(NA,NA,1,4,2,3),col=c(1,1,1,2,1,2))
points(43:56,log(EWdeath.female.mat.ex.validation[1,]/EWexpo.female.mat.ex.validation[1,]),pch=20)

crude.logmiuxt.forecast.age0.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age0.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age0.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.average[3,],lty=3,type="l",col=2)

ind.fitted<-seq(1,4200,by=100)
crude.logmiuxt.fitted.age0.ng.matchprior.average<-log(fitted.miuxt.11yrs.ng.matchprior.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age0.ng.matchprior.average<-apply(crude.logmiuxt.fitted.age0.ng.matchprior.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.matchprior.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.matchprior.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age0.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age0.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age0.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.average[3,],lty=3,type="l",col=2)

#age 30
ind.new<-seq(31,1400,by=100)
crude.logmiuxt.forecast.age30.ng.matchprior.average<-log(projected.miuxt.11yrs.ng.matchprior.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age30.ng.matchprior.average<-apply(crude.logmiuxt.forecast.age30.ng.matchprior.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[31,],pch=4,xlim=c(0,55),ylim=c(-8.4,-7.05),xaxt="n",xlab="Year",ylab="",main="Age 30",cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.matchprior.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.matchprior.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA),lty=c(NA,NA,1,4,2,3),col=c(1,1,1,2,1,2))
points(43:56,log(EWdeath.female.mat.ex.validation[31,]/EWexpo.female.mat.ex.validation[31,]),pch=20)

crude.logmiuxt.forecast.age30.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age30.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age30.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.average[3,],lty=3,type="l",col=2)

ind.fitted<-seq(31,4200,by=100)
crude.logmiuxt.fitted.age30.ng.matchprior.average<-log(fitted.miuxt.11yrs.ng.matchprior.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age30.ng.matchprior.average<-apply(crude.logmiuxt.fitted.age30.ng.matchprior.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.matchprior.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.matchprior.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age30.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age30.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age30.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.average[3,],lty=3,type="l",col=2)


#age 60
ind.new<-seq(61,1400,by=100)
crude.logmiuxt.forecast.age60.ng.matchprior.average<-log(projected.miuxt.11yrs.ng.matchprior.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age60.ng.matchprior.average<-apply(crude.logmiuxt.forecast.age60.ng.matchprior.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[61,],pch=4,xlim=c(0,55),ylim=c(-5.3,-4.4),xaxt="n",xlab="Year",ylab="",main="Age 60",cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.matchprior.average[2,],type="l",col=4)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.matchprior.average[1,],type="l",lty=2,col=4)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.matchprior.average[3,],type="l",lty=2,col=4)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA),lty=c(NA,NA,1,4,2,3),col=c(1,1,1,2,1,2))
points(43:56,log(EWdeath.female.mat.ex.validation[61,]/EWexpo.female.mat.ex.validation[61,]),pch=20)

crude.logmiuxt.forecast.age60.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age60.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age60.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.average[3,],lty=3,type="l",col=2)

ind.fitted<-seq(61,4200,by=100)
crude.logmiuxt.fitted.age60.ng.matchprior.average<-log(fitted.miuxt.11yrs.ng.matchprior.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age60.ng.matchprior.average<-apply(crude.logmiuxt.fitted.age60.ng.matchprior.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.matchprior.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.matchprior.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age60.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age60.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age60.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.average[3,],lty=3,type="l",col=2)

#age 80
ind.new<-seq(81,1400,by=100)
crude.logmiuxt.forecast.age80.ng.matchprior.average<-log(projected.miuxt.11yrs.ng.matchprior.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age80.ng.matchprior.average<-apply(crude.logmiuxt.forecast.age80.ng.matchprior.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[81,],pch=4,xlim=c(0,55),ylim=c(-3.3,-2.25),xaxt="n",xlab="Year",ylab="",main="Age 80",cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.matchprior.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.matchprior.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA),lty=c(NA,NA,1,4,2,3),col=c(1,1,1,2,1,2))
points(43:56,log(EWdeath.female.mat.ex.validation[81,]/EWexpo.female.mat.ex.validation[81,]),pch=20)

crude.logmiuxt.forecast.age80.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age80.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age80.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.average[3,],lty=3,type="l",col=2)

ind.fitted<-seq(81,4200,by=100)
crude.logmiuxt.fitted.age80.ng.matchprior.average<-log(fitted.miuxt.11yrs.ng.matchprior.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age80.ng.matchprior.average<-apply(crude.logmiuxt.fitted.age80.ng.matchprior.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.matchprior.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.matchprior.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age80.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age80.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age80.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.average[3,],lty=3,type="l",col=2)


#age 65
ind.new<-seq(66,1400,by=100)
crude.logmiuxt.forecast.age65.ng.matchprior.average<-log(projected.miuxt.11yrs.ng.matchprior.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age65.ng.matchprior.average<-apply(crude.logmiuxt.forecast.age65.ng.matchprior.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[66,],pch=4,xlim=c(0,55),ylim=c(-4.9,-3.9),xaxt="n",xlab="Year",ylab="",main="Age 65",cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.matchprior.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.matchprior.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA),lty=c(NA,NA,1,4,2,3),col=c(1,1,1,2,1,2))
points(43:56,log(EWdeath.female.mat.ex.validation[66,]/EWexpo.female.mat.ex.validation[66,]),pch=20)

crude.logmiuxt.forecast.age65.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age65.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age65.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.average[3,],lty=3,type="l",col=2)

ind.fitted<-seq(66,4200,by=100)
crude.logmiuxt.fitted.age65.ng.matchprior.average<-log(fitted.miuxt.11yrs.ng.matchprior.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age65.ng.matchprior.average<-apply(crude.logmiuxt.fitted.age65.ng.matchprior.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.matchprior.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.matchprior.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.matchprior.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age65.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age65.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age65.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.average[2,],lty=4,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.average[1,],lty=3,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.average[3,],lty=3,type="l",col=2)

##################
##Projected life expectancy
##################

fitted.expectancy.ng.loglinear.average<-apply((fitted.miuxt.11yrs.ng.loglinear.average.withover),2,project.expectancy.fn,Ext=Ext,time=1961:2002)
fitted.expectancy.ng.matchprior.average<-apply((fitted.miuxt.11yrs.ng.matchprior.average.withover),2,project.expectancy.fn,Ext=Ext,time=1961:2002)

fitted.expectancy.ng.loglinear.average.withP.percentile<-apply(fitted.expectancy.ng.loglinear.average,1,percentile.fn)
fitted.expectancy.ng.matchprior.average.withP.percentile<-apply(fitted.expectancy.ng.matchprior.average,1,percentile.fn)

###With Poisson variation

project.expectancy.ng.loglinear.average.withP<-apply((projected.miuxt.11yrs.ng.loglinear.average.withover[1:1400,]),2,project.expectancy.fn,Ext=Ext,time=2003:2016)
project.expectancy.ng.matchprior.average.withP<-apply((projected.miuxt.11yrs.ng.matchprior.average.withover[1:1400,]),2,project.expectancy.fn,Ext=Ext,time=2003:2016)

project.expectancy.ng.loglinear.average.withP.percentile<-apply(project.expectancy.ng.loglinear.average.withP,1,percentile.fn)
project.expectancy.ng.matchprior.average.withP.percentile<-apply(project.expectancy.ng.matchprior.average.withP,1,percentile.fn)
plot((-41):0,e0(demogdata(Dxt/Ext,pop=Ext,ages=0:99,years=1961:2002,label="EW",type="mortality",name="female"),type="period"),pch=4,cex.axis=1.15,cex.lab=1.2,cex.main=1.25,ylim=c(73.5,83.65),xlim=c(-41,12.5),xlab="Years",ylab="Life Expectancy at Birth",main="",xaxt="n")
axis(1,at=c(-41,-32,-22,-12,-2,8,18,26),label=c(1961,1970,1980,1990,2000,2010,2020,2028),cex.axis=1.15)
lines(1:14,project.expectancy.ng.loglinear.average.withP.percentile[2,],lty=4,col=2)
lines(1:14,project.expectancy.ng.loglinear.average.withP.percentile[1,],lty=3,col=2)
lines(1:14,project.expectancy.ng.loglinear.average.withP.percentile[3,],lty=3,col=2)
lines(1:14,project.expectancy.ng.matchprior.average.withP.percentile[2,])
lines(1:14,project.expectancy.ng.matchprior.average.withP.percentile[1,],lty=2)
lines(1:14,project.expectancy.ng.matchprior.average.withP.percentile[3,],lty=2)
points(1:14,e0(demogdata(round(EWdeath.female.mat.ex.validation)/round(EWexpo.female.mat.ex.validation),pop=round(EWexpo.female.mat.ex.validation),ages=0:99,years=2003:2016,label="EW",type="mortality",name="female"),type="period"),pch=20)
legend("topleft",c("Observed Life Expectancy","Holdout Life expectancy","NBLC Median","NBAPI Median","NBLC 95% Intervals","NBAPI 95% Intervals"),pch=c(4,20,NA,NA,NA,NA),lty=c(NA,NA,1,4,2,3),col=c(1,1,1,2,1,2),cex=1.25)
lines((-41):0,fitted.expectancy.ng.loglinear.average.withP.percentile[2,],lty=4,col=2)
lines((-41):0,fitted.expectancy.ng.loglinear.average.withP.percentile[1,],lty=3,col=2)
lines((-41):0,fitted.expectancy.ng.loglinear.average.withP.percentile[3,],lty=3,col=2)
lines((-41):0,fitted.expectancy.ng.matchprior.average.withP.percentile[2,],lty=1)
lines((-41):0,fitted.expectancy.ng.matchprior.average.withP.percentile[1,],lty=2)
lines((-41):0,fitted.expectancy.ng.matchprior.average.withP.percentile[3,],lty=2)

#################################
##APCI with cohort models
#################################

##Classical APCI,constraints: sum(kt)=sum(t*kt)=0, sum(cohort)=sum(c*cohort)=sum(c^2*cohort)=0,remove points c(1,72,142) 

GLM.poisson.cohort.cons10.diff<-function(dxt.vec,log.ext.vec,t0,A,T,C){
x<-matrix(0,nrow=(A*T),ncol=A)
x[,1]<-rep(c(1,rep(0,A-1)),T)
for (i in 2:A){
x[,i]<-c(0,(x[,(i-1)])[-(A*T)])
}
t<-rep(t0,A)
for (i in 1:(T-1)){
t<-c(t,rep(t0+i,A))
}
beta.x<-x*t

cohort.dummy<-matrix(NA,nrow=A*T,ncol=length(C))
for (k in C){
mat.temp<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
if ((j-i)==k) mat.temp[i,j]<-1
}}
cohort.dummy[,k+A]<-as.vector(mat.temp)
}

for (k in (C+A)[-c(1,72,length(C))]){
cohort.dummy[,k]<-cohort.dummy[,k]+1/(70*139)*(k-72)*(141-k)*cohort.dummy[,1]
}
for (k in (C+A)[-c(1,72,length(C))]){
cohort.dummy[,k]<-cohort.dummy[,k]-1/(69*71)*(141-k)*(k-1)*cohort.dummy[,72]
}
for (k in (C+A)[-c(1,72,length(C))]){
cohort.dummy[,k]<-cohort.dummy[,k]+1/(69*140)*(k-1)*(72-k)*cohort.dummy[,length(C)]
}
cohort.dummy<-cohort.dummy[,-c(1,72,length(C))]

kappa<-matrix(0,nrow=(A*T),ncol=T)
for (i in 1:T){
kappa[,i]<-c(rep(rep(0,A),(i-1)),rep(1,A),rep(rep(0,A),(T-i)))
}

for (i in 3:T){
kappa[,i]<-kappa[,i]+(i-2)*kappa[,1]-(i-1)*kappa[,2]
}

covariate.dummy<-cbind(x,beta.x,kappa[,-(1:2)],cohort.dummy)

fit<-glm.fit(x=covariate.dummy,y=dxt.vec,family=poisson(),offset=log.ext.vec)
return(fit)
}

C<-(1-A):(T-1)
result.poisson.cohort.cons10.glm.diff<-GLM.poisson.cohort.cons10.diff(dxt.vec=round(EWdeath.female.vec.ex),log.ext.vec=log(round(EWexpo.female.vec.ex)),t0=-21,A=100,T=42,C=C)
alpha.loglinear<-result.poisson.cohort.cons10.glm.diff$coef[1:100]
beta.loglinear<-result.poisson.cohort.cons10.glm.diff$coef[101:200]
kappa.loglinear<-c(sum((1:40)*result.poisson.cohort.cons10.glm.diff$coef[201:240]),-sum((2:41)*result.poisson.cohort.cons10.glm.diff$coef[201:240]),result.poisson.cohort.cons10.glm.diff$coef[201:240])
cohort.loglinear<-c(1/(71*140)*sum(c((-70):(-1),1:68)*c(139:70,68:1)*result.poisson.cohort.cons10.glm.diff$coef[241:378]),result.poisson.cohort.cons10.glm.diff$coef[241:310],1/(69*71)*sum(-c(139:70,68:1)*c(1:70,72:139)*result.poisson.cohort.cons10.glm.diff$coef[241:378]),result.poisson.cohort.cons10.glm.diff$coef[311:378],1/(69*140)*sum(c(1:70,72:139)*c(70:1,(-1):(-68))*result.poisson.cohort.cons10.glm.diff$coef[241:378]))
plot(alpha.loglinear,type="l",ylab="",main="alpha")
plot(beta.loglinear,type="l",ylab="",main="beta")
plot(kappa.loglinear,type="l",ylab="",main="kappa")
par(mfrow=c(2,1))
plot(cohort.loglinear,type="l",ylab="",xlab="c",main=expression(gamma[c]))
plot(cohort.loglinear,type="l",ylab="",xlab="c",main=expression(gamma[c]-gamma[c-1]))
result.poisson.cohort.cons10.glm.diff$deviance 


##NBAPCI-AR1

MCMC.rates.new.over.negbin.int.AR1.notrunc.cohort.group.matchprior<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k,alpha,beta,cohort,sigma2.k,sigma2.cohort,rho,rho.cohort,sigma2.rho.cohort,lx,lambda.alpha,lambda.beta,lambda,epsilon,ak,bk,a.rho,b.rho,sigma2.rho,a.epsilon,b.epsilon,a.cohort,b.cohort,sigma.prop.cohort,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.rho,sigma2.prop.rho.cohort,sigma2.prop.epsilon,sigma2.k.prop,sigma2.prop.sigma2.cohort){
	
Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha)
C<-length(cohort)

result<-matrix(0,nrow=round((n-burnin)/thin),ncol=(2*A+T+4+C+2))

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1/sqrt(T),T)
J[2,]<-1/((T-1)/2)*((-(T-1)/2):((T-1)/2))

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
R[1,1]<-sqrt(1-rho^2)
i.R<-forwardsolve(R,I)
i.Q<-i.R%*%t(i.R)
B<-J%*%i.Q%*%t(J)
D<-B[(3:T),(3:T)]-(B[(3:T),(1:2)])%*%solve(B[(1:2),(1:2)])%*%(B[(1:2),(3:T)])

J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1
I.cohort<-diag(rep(1,C))

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

accept.epsilon<-0;accept.rho<-0;accept<-0;accept.beta<-rep(0,A);accept.alpha<-rep(0,A);accept.cohort<-0;accept.sigma2.k<-0;accept.rho.cohort<-0
accept.sigma2.cohort<-0
iter<-0
g<-seq(thin,n-burnin,by=thin)

for (m in 1:n){

S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))
p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
cohort.star.vec<-c(rmvnorm.manual(1,mean.vec=cohort[-c(1,72,C)],sigma=sigma.prop.cohort))
cohort.temp.star.vec<-cohort;cohort.temp.star.vec[-c(1,72,C)]<-cohort.star.vec
cohort.temp.star.vec[1]<-1/(71*140)*sum(c((-70):(-1),1:68)*c(139:70,68:1)*cohort.star.vec);cohort.temp.star.vec[72]<-1/(69*71)*sum(-c(139:70,68:1)*c(1:70,72:139)*cohort.star.vec);cohort.temp.star.vec[C]<-1/(69*140)*sum(c(1:70,72:139)*c(70:1,(-1):(-68))*cohort.star.vec)
cohort.star.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.star.mat[i,j]<-cohort.temp.star.vec[j-i+A]
}
}
p.nbinom.star.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.star.mat))
prob.accept.cohort<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.star.mat,log=TRUE))+dmvnorm.manual(cohort.temp.star.vec[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)
if (log(runif(1))<=prob.accept.cohort) {cohort<-cohort.temp.star.vec
cohort.mat<-cohort.star.mat
accept.cohort<-accept.cohort+1
}

S<-2*sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
k.star.vec<-rmvnorm.tol(1,mean=k[-c(1,2)],sigma=sigma.prop.k)
k.temp.star.vec<-k;k.temp.star.vec[3:T]<-k.star.vec
k.temp.star.vec[1]<-sum((1:(T-2))*k.temp.star.vec[3:T]);k.temp.star.vec[2]<--sum((2:(T-1))*k.temp.star.vec[3:T])
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k.temp.star.vec,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.temp.star.vec[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k<-k.temp.star.vec
accept<-accept+1}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k+cohort[(1:T)-i+A]))
beta.star<-rnorm(1,beta[i],sqrt(sigma2.x[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta.star*t+k+cohort[(1:T)-i+A]))
prob.accept.beta<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(beta.star,mu=0,lambda=lambda.beta[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(beta[i],mu=0,lambda=lambda.beta[i]))
if (log(runif(1))<=prob.accept.beta) {beta[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
}
 
for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k+cohort[(1:T)-i+A]))
alpha.star<-rnorm(1,alpha[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta[i]*t+k+cohort[(1:T)-i+A]))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(alpha.star,mu=lx[i],lambda=lambda.alpha[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(alpha[i],mu=lx[i],lambda=lambda.alpha[i]))
if (log(runif(1))<=prob.accept.alpha) {alpha[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

rho.cohort.star<-rnorm(1,mean=rho.cohort,sd=sqrt(sigma2.prop.rho.cohort))
if ((rho.cohort.star>-1) & (rho.cohort.star<1)){
R.cohort.star<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort.star[i,j]<--(1+rho.cohort.star)
if ((i-j)==2) R.cohort.star[i,j]<-rho.cohort.star
}
}
R.cohort.star[2,1]<--1*sqrt(1-rho.cohort.star^2)
R.cohort.star[2,2]<-sqrt(1-rho.cohort.star^2)
R.cohort.star[1,1]<-1/100 
i.R.cohort.star<-forwardsolve(R.cohort.star,I.cohort)
i.Q.cohort.star<-i.R.cohort.star%*%t(i.R.cohort.star)
B.cohort.star<-J.cohort%*%i.Q.cohort.star%*%t(J.cohort)
ic.star<-(B.cohort.star[(4:C),(1:3)])%*%solve(B.cohort.star[(1:3),(1:3)])%*%(B.cohort.star[(1:3),(4:C)])
D.cohort.star<-B.cohort.star[(4:C),(4:C)]-ic.star
S.cohort.star<-sigma2.cohort*D.cohort.star
S.cohort.star<-0.5*(S.cohort.star+t(S.cohort.star))
 
prob.accept.rho.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dnorm(rho.cohort.star,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)
if (log(runif(1))<=prob.accept.rho.cohort){
(rho.cohort<-rho.cohort.star)
(R.cohort<-R.cohort.star)
(B.cohort<-B.cohort.star)
(D.cohort<-D.cohort.star)
(S.cohort<-S.cohort.star)
(accept.rho.cohort<-accept.rho.cohort+1)
}
}

chol.D.cohort<-chol(D.cohort)
i.chol.D.cohort<-backsolve(chol.D.cohort,diag(rep(1,C-3)))
i.D.cohort<-i.chol.D.cohort%*%t(i.chol.D.cohort)
#sigma2.cohort<-1/rgamma(1,a.cohort+(C-3)/2,b.cohort+0.5*t(cohort[-c(1,72,C)])%*%i.D.cohort%*%cohort[-c(1,72,C)])
sigma2.cohort.star<-(rnorm(1,sqrt(sigma2.cohort),sqrt(sigma2.prop.sigma2.cohort)))^2
if (sigma2.cohort.star<0.01){
S.cohort.star<-sigma2.cohort.star*D.cohort
prob.accept.sigma2.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dunif(sqrt(sigma2.cohort.star),max=0.1,log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dunif(sqrt(sigma2.cohort),max=0.1,log=TRUE)
if (log(runif(1))<=prob.accept.sigma2.cohort){
sigma2.cohort<-sigma2.cohort.star;S.cohort<-S.cohort.star;accept.sigma2.cohort<-accept.sigma2.cohort+1
}
}

S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))

rho.star<-rnorm(1,mean=rho,sd=sqrt(sigma2.prop.rho))
if ((rho.star>-1) & (rho.star<1)){
R.star<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R.star[i,j]<--rho.star
if ((i-j)==0) R.star[i,j]<-1
}
}
R.star[1,1]<-sqrt(1-rho.star^2)
Q.star<-t(R.star)%*%R.star
B.star<-J%*%solve(Q.star)%*%t(J) 
D.star<-B.star[(3:T),(3:T)]-(B.star[(3:T),(1:2)])%*%solve(B.star[(1:2),(1:2)])%*%(B.star[(1:2),(3:T)])
S.star<-2*sigma2.k*D.star #always gives warning on symmetry, investigate and if necessary, create dmvnorm.tol to alter the tolerance. And why would S.star ever be unsymmetric? It isnt possible unless it is numerically unsymmetric.
#prob.accept.rho<-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)-(rho.star^2)/(2*sigma2.rho)-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)+(rho^2)/(2*sigma2.rho)
prob.accept.rho<-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)+(a.rho-1)*log(1+rho.star)+(b.rho-1)*log(1-rho.star)-dmvnorm.tol(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)-(a.rho-1)*log(1+rho)-(b.rho-1)*log(1-rho)
if (log(runif(1))<=prob.accept.rho){
(rho<-rho.star)  
(Q<-Q.star) 
(R<-R.star) 
(B<-B.star) 
(D<-D.star) 
(S<-S.star) 
(accept.rho<-accept.rho+1)}
}

sigma2.k.star<-exp(rnorm(1,mean=log(sigma2.k),sd=sqrt(sigma2.k.prop)))
S.star<-2*sigma2.k.star*D
prob.accept.sigma2.k<-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)+dexp(sigma2.k.star,rate=lambda,log=TRUE)-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)-dexp(sigma2.k,rate=lambda,log=TRUE)+log(sigma2.k.star)-log(sigma2.k)
if (log (runif(1))<=prob.accept.sigma2.k){
sigma2.k<-sigma2.k.star
S<-S.star
accept.sigma2.k<-accept.sigma2.k+1 
}

#lambda<-rtrunc(1,spec="gamma",a=(0.1*2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1))),b=Inf,shape=(ak+1),rate=(bk/(2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1)))+sigma2.k))
#lambda<-rtrunc(1,spec="gamma",a=0.0001,b=Inf,shape=(ak+1),rate=(bk/0.001+sigma2.k)) 
lambda<-rgamma(1,shape=(ak+1),rate=(bk/400+sigma2.k))

p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}

if ((m>burnin) & ((m-burnin) %in% g)){
iter<-iter+1
result[iter,]<-c(k,beta,alpha,cohort,rho,sigma2.k,lambda,rho.cohort,sigma2.cohort,epsilon)
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],cohort.new=result[,(2*A+T+1):(2*A+T+C)],rho.1=result[,(2*A+T+C+1)],sigma2.k=result[,(2*A+T+C+2)],lambda=result[,(2*A+T+C+3)],rho.cohort=result[,(2*A+T+C+4)],sigma2.cohort=result[,(2*A+T+C+5)],epsilon=result[,(2*A+T+C+6)],accept,accept.beta,accept.alpha,accept.cohort,accept.epsilon,accept.rho,accept.sigma2.k,accept.rho.cohort,accept.sigma2.cohort)
}

t0<--21
Ext<-round(EWexpo.female.mat.ex)
Dxt<-round(EWdeath.female.mat.ex)
k.new<-c(sum((1:40)*result.poisson.cohort.cons10.glm.diff$coef[201:240]),-sum((2:41)*result.poisson.cohort.cons10.glm.diff$coef[201:240]),result.poisson.cohort.cons10.glm.diff$coef[201:240])
t<-t0:(t0+length(k.new)-1)
alpha.new<-result.poisson.cohort.cons10.glm.diff$coef[1:100]
beta.new<-result.poisson.cohort.cons10.glm.diff$coef[101:200]
cohort.new<-c(1/(71*140)*sum(c((-70):(-1),1:68)*c(139:70,68:1)*result.poisson.cohort.cons10.glm.diff$coef[241:378]),result.poisson.cohort.cons10.glm.diff$coef[241:310],1/(69*71)*sum(-c(139:70,68:1)*c(1:70,72:139)*result.poisson.cohort.cons10.glm.diff$coef[241:378]),result.poisson.cohort.cons10.glm.diff$coef[311:378],1/(69*140)*sum(c(1:70,72:139)*c(70:1,(-1):(-68))*result.poisson.cohort.cons10.glm.diff$coef[241:378]))
sigma2.k<-arima(k.new,order=c(1,0,0),include.mean=FALSE)$sigma2
rho.new<-arima(k.new,order=c(1,0,0),include.mean=FALSE)$coef[1]
rho.cohort.new<-arima(cohort.new,order=c(1,1,0))$coef
sigma2.cohort<-arima(cohort.new,order=c(1,1,0))$sigma2
lx<-rep(-5,100)
ak<-1
bk<-0.0001
a.rho<-3
b.rho<-2
sigma2.rho<-1
lambda.alpha<-rep(2.5,A)
lambda.beta<-rep(0.03,A)
a.cohort<-100
b.cohort<-0.001

marg.var.k<-summary.glm(result.poisson.cohort.cons10.glm.diff)$cov.unscaled[201:240,201:240]
marg.var.cohort<-summary.glm(result.poisson.cohort.cons10.glm.diff)$cov.unscaled[241:378,241:378]
 
system.time(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-MCMC.rates.new.over.negbin.int.AR1.notrunc.cohort.group.matchprior(n=201000,burnin=1000,thin=10,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,cohort=cohort.new,sigma2.k=sigma2.k,sigma2.cohort=sigma2.cohort,rho=rho.new,rho.cohort=rho.cohort.new,sigma2.rho.cohort=1,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
lambda=1,epsilon=100,ak=ak,bk=bk,a.rho=a.rho,b.rho=b.rho,sigma2.rho=sigma2.rho,a.epsilon=25,b.epsilon=0.05,a.cohort=a.cohort,b.cohort=b.cohort,sigma.prop.cohort=((2.08^2)/138*marg.var.cohort),sigma.prop.k=((3.38^2)/40*marg.var.k),sigma2.x=c(0.000001,0.00001,0.00004,0.00002,rep(0.00004,10),rep(0.00002,16),rep(0.00003,7),rep(0.00001,8),rep(0.000007,27),rep(0.000007,24),rep(0.000005,4)),sigma2.x.alpha=c(0.0008,0.0008,0.003,rep(0.007,14),rep(0.002,21),rep(0.0005,62)),sigma2.prop.rho=0.5,sigma2.prop.rho.cohort=0.1,sigma2.prop.epsilon=0.1,sigma2.k.prop=1,sigma2.prop.sigma2.cohort=0.00005))


theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-cbind(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$k.new,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$beta.new,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$alpha.new,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$cohort.new,log(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$sigma2.k),log(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$lambda),log(rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$sigma2.cohort),rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$rho.1,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$rho.cohort,rates.MCMC.over.negbin.int.AR1.y0.new.notrunc.cohort.group.marg.matchprior.100.001$epsilon)
theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[seq(10,200000,by=10),] #further thinning

par(mfrow=c(4,4))
plot(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,384]),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,385]),xlab="iterations",ylab="",main="lambda",type="l")
plot(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,386]),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387],xlab="iterations",ylab="",main="rho.1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,388],xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389],xlab="iterations",ylab="",main="epsilon",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143],xlab="iterations",ylab="",main="alpha_1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,242],xlab="iterations",ylab="",main="alpha_100",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43],xlab="iterations",ylab="",main="beta_1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,142],xlab="iterations",ylab="",main="beta_100",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1],xlab="iterations",ylab="",main="kappa_1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,20],xlab="iterations",ylab="",main="kappa_20",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243],xlab="iterations",ylab="",main="cohort_1",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,277],xlab="iterations",ylab="",main="cohort_35",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,314],xlab="iterations",ylab="",main="cohort_72",type="l")
plot(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,342],xlab="iterations",ylab="",main="cohort_100",type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,384]),n=50000),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(density(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,385]),n=50000),xlab="iterations",ylab="",main="lambda",type="l")
plot(density(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,386]),n=50000),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387],n=50000),xlab="iterations",ylab="",main="rho.1",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,388],n=50000),xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(density(1/theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389],n=50000),xlab="iterations",ylab="",main="epsilon",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143],n=50000),xlab="iterations",ylab="",main="alpha_1",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,242],n=50000),xlab="iterations",ylab="",main="alpha_100",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43],n=50000),xlab="iterations",ylab="",main="beta_1",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,142],n=50000),xlab="iterations",ylab="",main="beta_100",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1],n=50000),xlab="iterations",ylab="",main="kappa_1",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,20],n=50000),xlab="iterations",ylab="",main="kappa_20",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243],n=50000),xlab="iterations",ylab="",main="cohort_1",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,277],n=50000),xlab="iterations",ylab="",main="cohort_35",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,314],n=50000),xlab="iterations",ylab="",main="cohort_72",type="l")
plot(density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,342],n=50000),xlab="iterations",ylab="",main="cohort_100",type="l")

par(mfrow=c(4,4))
acf(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,384]),main="sigma2_k")
acf(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,385]),main="lambda")
acf(exp(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,386]),main="sigma2.cohort")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387],main="rho.1")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,388],main="rho.cohort")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389],main="epsilon")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143],main="alpha_1")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,242],main="alpha_100")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43],main="beta_1")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,142],main="beta_100")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1],main="kappa_1")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,20],main="kappa_20")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243],main="cohort_1")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,277],main="cohort_35")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,314],main="cohort_72")
acf(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,342],main="cohort_100")

alpha.AR1.over.negbin.int.loglinear.cohort.025<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143:242],2,quantile.025)
alpha.AR1.over.negbin.int.loglinear.cohort.50<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143:242],2,quantile.50)
alpha.AR1.over.negbin.int.loglinear.cohort.975<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143:242],2,quantile.975)
beta.AR1.over.negbin.int.loglinear.cohort.025<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43:142],2,quantile.025)
beta.AR1.over.negbin.int.loglinear.cohort.50<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43:142],2,quantile.50)
beta.AR1.over.negbin.int.loglinear.cohort.975<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43:142],2,quantile.975)
kappa.AR1.over.negbin.int.loglinear.cohort.025<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1:42],2,quantile.025)
kappa.AR1.over.negbin.int.loglinear.cohort.50<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1:42],2,quantile.50)
kappa.AR1.over.negbin.int.loglinear.cohort.975<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1:42],2,quantile.975)
cohort.AR1.over.negbin.int.loglinear.cohort.025<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243:383],2,quantile.025)
cohort.AR1.over.negbin.int.loglinear.cohort.50<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243:383],2,quantile.50)
cohort.AR1.over.negbin.int.loglinear.cohort.975<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243:383],2,quantile.975)
k.forecast.ng.loglinear.cohort.025<-apply(t(k.forecast.ng.loglinear.cohort),2,quantile.025)
k.forecast.ng.loglinear.cohort.50<-apply(t(k.forecast.ng.loglinear.cohort),2,quantile.50)
k.forecast.ng.loglinear.cohort.975<-apply(t(k.forecast.ng.loglinear.cohort),2,quantile.975)
cohort.forecast.ng.loglinear.cohort.025<-apply(t(cohort.forecast.ng.loglinear.cohort),2,quantile.025)
cohort.forecast.ng.loglinear.cohort.50<-apply(t(cohort.forecast.ng.loglinear.cohort),2,quantile.50)
cohort.forecast.ng.loglinear.cohort.975<-apply(t(cohort.forecast.ng.loglinear.cohort),2,quantile.975)

plot(alpha.AR1.over.negbin.int.loglinear.cohort.50,type="l",xlab="Age,x",main=expression(alpha[x]),ylab="",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
lines(alpha.AR1.over.negbin.int.loglinear.cohort.025,type="l",lty=2)
lines(alpha.AR1.over.negbin.int.loglinear.cohort.975,type="l",lty=2)
lines(alpha.loglinear.matchprior.average.percentile[2,],col=2)
lines(alpha.loglinear.matchprior.average.percentile[1,],col=2,lty=2)
lines(alpha.loglinear.matchprior.average.percentile[3,],col=2,lty=2)
legend("bottomright",c("Median under NBLL-C","Median under NBLL","95% Intervals under NBLL-C","95% Intervals under NBLL"),lty=c(1,1,2,2),col=c(1,2,1,2))
plot(beta.AR1.over.negbin.int.loglinear.cohort.50,type="l",xlab="Age,x",ylab="",main=expression(beta[x]),ylim=c(-0.045,0.001),cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
lines(beta.AR1.over.negbin.int.loglinear.cohort.025,type="l",lty=2)
lines(beta.AR1.over.negbin.int.loglinear.cohort.975,type="l",lty=2)
lines(beta.loglinear.matchprior.average.percentile[2,],col=2)
lines(beta.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines(beta.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
plot((-41:0),kappa.AR1.over.negbin.int.loglinear.cohort.50,type="l",xlab="Year,t",ylab="",main=expression(kappa[t]),xlim=c(-41,26),ylim=c(-0.2,0.16),xaxt="n",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,c(seq(-41,19,by=10),26),c(seq(1961,2021,by=10),2028),cex.axis=1.15)
lines((-41:0),kappa.AR1.over.negbin.int.loglinear.cohort.025,type="l",lty=2)
lines((-41:0),kappa.AR1.over.negbin.int.loglinear.cohort.975,type="l",lty=2)
lines(1:26,k.forecast.ng.loglinear.cohort.50,type="l")
lines(1:26,k.forecast.ng.loglinear.cohort.025,type="l",lty=2)
lines(1:26,k.forecast.ng.loglinear.cohort.975,type="l",lty=2)
lines((-41):0,k.loglinear.matchprior.average.percentile[2,],col=2)
lines((-41):0,k.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines((-41):0,k.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
lines(1:26,k.forecast.ng.loglinear.matchprior.average.percentile[2,],col=2)
lines(1:26,k.forecast.ng.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines(1:26,k.forecast.ng.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
legend("bottomleft",c("Median under NBLL-C","Median under NBLL","95% Intervals under NBLL-C","95% Intervals under NBLL"),lty=c(1,1,2,2),col=c(1,2,1,2))
plot((-140:0),cohort.AR1.over.negbin.int.loglinear.cohort.50,type="l",xlab="Cohort",ylab="",main=expression(gamma[c]),ylim=c(-0.12,0.25),xlim=c(-140,26),xaxt="n",cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,c(seq(-140,19,by=20),26),c(seq(1861,2020,by=20),2028),cex.axis=1.15)
lines((-140:0),cohort.AR1.over.negbin.int.loglinear.cohort.025,type="l",lty=2)
lines((-140:0),cohort.AR1.over.negbin.int.loglinear.cohort.975,type="l",lty=2)
lines(1:26,cohort.forecast.ng.loglinear.cohort.50,type="l")
lines(1:26,cohort.forecast.ng.loglinear.cohort.025,type="l",lty=2)
lines(1:26,cohort.forecast.ng.loglinear.cohort.975,type="l",lty=2)

##NBAPCI-RW

MCMC.rates.new.over.negbin.int.RW.notrunc.cohort.group.matchprior<-function(n,burnin=0,thin,exposures,deaths,t0,t.interval,k,alpha,beta,cohort,sigma2.k,sigma2.cohort,rho,rho.cohort,sigma2.rho.cohort,lx,lambda.alpha,lambda.beta,lambda,epsilon,ak,bk,sigma2.rho,a.epsilon,b.epsilon,a.cohort,b.cohort,sigma.prop.cohort,sigma.prop.k,sigma2.x,sigma2.x.alpha,sigma2.prop.rho.cohort,sigma2.prop.epsilon,sigma2.k.prop,sigma2.prop.sigma2.cohort){
	
Ext<-exposures
Dxt<-deaths
t<-t0:(t0+t.interval-1)
T<-length(t)
A<-length(alpha)
C<-length(cohort)

result<-matrix(0,nrow=round((n-burnin)/thin),ncol=(2*A+T+4+C+2))

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1/sqrt(T),T)
J[2,]<-1/((T-1)/2)*((-(T-1)/2):((T-1)/2))

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
#R[1,1]<-sqrt(1-rho^2)
i.R<-forwardsolve(R,I)
i.Q<-i.R%*%t(i.R)
B<-J%*%i.Q%*%t(J)
D<-B[(3:T),(3:T)]-(B[(3:T),(1:2)])%*%solve(B[(1:2),(1:2)])%*%(B[(1:2),(3:T)])

J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1
I.cohort<-diag(rep(1,C))

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

accept.epsilon<-0;accept<-0;accept.beta<-rep(0,A);accept.alpha<-rep(0,A);accept.cohort<-0;accept.sigma2.k<-0;accept.rho.cohort<-0
accept.sigma2.cohort<-0
iter<-0
g<-seq(thin,n-burnin,by=thin)

for (m in 1:n){

S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))
p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
cohort.star.vec<-c(rmvnorm.manual(1,mean.vec=cohort[-c(1,72,C)],sigma=sigma.prop.cohort))
cohort.temp.star.vec<-cohort;cohort.temp.star.vec[-c(1,72,C)]<-cohort.star.vec
cohort.temp.star.vec[1]<-1/(71*140)*sum(c((-70):(-1),1:68)*c(139:70,68:1)*cohort.star.vec);cohort.temp.star.vec[72]<-1/(69*71)*sum(-c(139:70,68:1)*c(1:70,72:139)*cohort.star.vec);cohort.temp.star.vec[C]<-1/(69*140)*sum(c(1:70,72:139)*c(70:1,(-1):(-68))*cohort.star.vec)
cohort.star.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.star.mat[i,j]<-cohort.temp.star.vec[j-i+A]
}
}
p.nbinom.star.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.star.mat))
prob.accept.cohort<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.star.mat,log=TRUE))+dmvnorm.manual(cohort.temp.star.vec[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)
if (log(runif(1))<=prob.accept.cohort) {cohort<-cohort.temp.star.vec
cohort.mat<-cohort.star.mat
accept.cohort<-accept.cohort+1
}

S<-2*sigma2.k*D

p.nbinom.mat<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
k.star.vec<-rmvnorm.tol(1,mean=k[-c(1,2)],sigma=sigma.prop.k)
k.temp.star.vec<-k;k.temp.star.vec[3:T]<-k.star.vec
k.temp.star.vec[1]<-sum((1:(T-2))*k.temp.star.vec[3:T]);k.temp.star.vec[2]<--sum((2:(T-1))*k.temp.star.vec[3:T])
p.nbinom.mat.star<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k.temp.star.vec,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
prob.accept.k<-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat.star,log=TRUE))+dmvnorm.tol(k.temp.star.vec[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom.mat,log=TRUE))-dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)
if (log(runif(1))<=prob.accept.k) {k<-k.temp.star.vec
accept<-accept+1}

for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k+cohort[(1:T)-i+A]))
beta.star<-rnorm(1,beta[i],sqrt(sigma2.x[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta.star*t+k+cohort[(1:T)-i+A]))
prob.accept.beta<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(beta.star,mu=0,lambda=lambda.beta[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(beta[i],mu=0,lambda=lambda.beta[i]))
if (log(runif(1))<=prob.accept.beta) {beta[i]<-beta.star} & {accept.beta[i]<-accept.beta[i]+1}
}
 
for (i in 1:A){
p.nbinom<-epsilon/(epsilon+Ext[i,]*exp(alpha[i]+beta[i]*t+k+cohort[(1:T)-i+A]))
alpha.star<-rnorm(1,alpha[i],sqrt(sigma2.x.alpha[i]))
p.nbinom.star<-epsilon/(epsilon+Ext[i,]*exp(alpha.star+beta[i]*t+k+cohort[(1:T)-i+A]))
prob.accept.alpha<-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom.star,log=TRUE))+log(ddoublex(alpha.star,mu=lx[i],lambda=lambda.alpha[i]))-sum(dnbinom(Dxt[i,],size=epsilon,prob=p.nbinom,log=TRUE))-log(ddoublex(alpha[i],mu=lx[i],lambda=lambda.alpha[i]))
if (log(runif(1))<=prob.accept.alpha) {alpha[i]<-alpha.star} & {accept.alpha[i]<-accept.alpha[i]+1}
}	

rho.cohort.star<-rnorm(1,mean=rho.cohort,sd=sqrt(sigma2.prop.rho.cohort))
if ((rho.cohort.star>-1) & (rho.cohort.star<1)){
R.cohort.star<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort.star[i,j]<--(1+rho.cohort.star)
if ((i-j)==2) R.cohort.star[i,j]<-rho.cohort.star
}
}
R.cohort.star[2,1]<--1*sqrt(1-rho.cohort.star^2)
R.cohort.star[2,2]<-sqrt(1-rho.cohort.star^2)
R.cohort.star[1,1]<-1/100 
i.R.cohort.star<-forwardsolve(R.cohort.star,I.cohort)
i.Q.cohort.star<-i.R.cohort.star%*%t(i.R.cohort.star)
B.cohort.star<-J.cohort%*%i.Q.cohort.star%*%t(J.cohort)
ic.star<-(B.cohort.star[(4:C),(1:3)])%*%solve(B.cohort.star[(1:3),(1:3)])%*%(B.cohort.star[(1:3),(4:C)])
D.cohort.star<-B.cohort.star[(4:C),(4:C)]-ic.star
S.cohort.star<-sigma2.cohort*D.cohort.star
S.cohort.star<-0.5*(S.cohort.star+t(S.cohort.star))
 
prob.accept.rho.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dnorm(rho.cohort.star,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)
if (log(runif(1))<=prob.accept.rho.cohort){
(rho.cohort<-rho.cohort.star)
(R.cohort<-R.cohort.star)
(B.cohort<-B.cohort.star)
(D.cohort<-D.cohort.star)
(S.cohort<-S.cohort.star)
(accept.rho.cohort<-accept.rho.cohort+1)
}
}

chol.D.cohort<-chol(D.cohort)
i.chol.D.cohort<-backsolve(chol.D.cohort,diag(rep(1,C-3)))
i.D.cohort<-i.chol.D.cohort%*%t(i.chol.D.cohort)
#sigma2.cohort<-1/rgamma(1,a.cohort+(C-3)/2,b.cohort+0.5*t(cohort[-c(1,72,C)])%*%i.D.cohort%*%cohort[-c(1,72,C)])
sigma2.cohort.star<-(rnorm(1,sqrt(sigma2.cohort),sqrt(sigma2.prop.sigma2.cohort)))^2
if (sigma2.cohort.star<0.01){
S.cohort.star<-sigma2.cohort.star*D.cohort
prob.accept.sigma2.cohort<-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort.star,log=TRUE)+dunif(sqrt(sigma2.cohort.star),max=0.1,log=TRUE)-dmvnorm.manual(cohort[-c(1,72,C)],mean.vec=rep(0,C-3),sigma=S.cohort,log=TRUE)-dunif(sqrt(sigma2.cohort),max=0.1,log=TRUE)
if (log(runif(1))<=prob.accept.sigma2.cohort){
sigma2.cohort<-sigma2.cohort.star;S.cohort<-S.cohort.star;accept.sigma2.cohort<-accept.sigma2.cohort+1
}
}

S.cohort<-sigma2.cohort*D.cohort
S.cohort<-0.5*(S.cohort+t(S.cohort))

sigma2.k.star<-exp(rnorm(1,mean=log(sigma2.k),sd=sqrt(sigma2.k.prop)))
S.star<-2*sigma2.k.star*D
prob.accept.sigma2.k<-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S.star,log=TRUE)+dexp(sigma2.k.star,rate=lambda,log=TRUE)-dmvnorm(k[3:T],mean=rep(0,T-2),sigma=S,log=TRUE)-dexp(sigma2.k,rate=lambda,log=TRUE)+log(sigma2.k.star)-log(sigma2.k)
if (log (runif(1))<=prob.accept.sigma2.k){
sigma2.k<-sigma2.k.star
S<-S.star
accept.sigma2.k<-accept.sigma2.k+1 
}

#lambda<-rtrunc(1,spec="gamma",a=(0.1*2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1))),b=Inf,shape=(ak+1),rate=(bk/(2/((0.99*0.005+0.0154^2)*0.9767442*1.047056*(1)))+sigma2.k))
#lambda<-rtrunc(1,spec="gamma",a=0.0001,b=Inf,shape=(ak+1),rate=(bk/0.001+sigma2.k)) 
lambda<-rgamma(1,shape=(ak+1),rate=(bk/400+sigma2.k))

p.nbinom<-epsilon/(epsilon+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
epsilon.star<-exp(rnorm(1,log(epsilon),sqrt(sigma2.prop.epsilon)))
#if ((epsilon.star>1) & (epsilon.star<50000)){
p.nbinom.star<-epsilon.star/(epsilon.star+Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat))
prob.accept.epsilon<-sum(dnbinom(Dxt,size=epsilon.star,prob=p.nbinom.star,log=TRUE))+(a.epsilon-1)*log(epsilon.star)-b.epsilon*epsilon.star-sum(dnbinom(Dxt,size=epsilon,prob=p.nbinom,log=TRUE))-(a.epsilon-1)*log(epsilon)+b.epsilon*epsilon+log(epsilon.star)-log(epsilon)
if (log(runif(1))<=prob.accept.epsilon) {epsilon<-epsilon.star} & {accept.epsilon<-accept.epsilon+1}
#}

if ((m>burnin) & ((m-burnin) %in% g)){
iter<-iter+1
result[iter,]<-c(k,beta,alpha,cohort,rho,sigma2.k,lambda,rho.cohort,sigma2.cohort,epsilon)
}
}
list(k.new=result[,1:T],beta.new=result[,(T+1):(A+T)],alpha.new=result[,(A+T+1):(2*A+T)],cohort.new=result[,(2*A+T+1):(2*A+T+C)],rho.1=result[,(2*A+T+C+1)],sigma2.k=result[,(2*A+T+C+2)],lambda=result[,(2*A+T+C+3)],rho.cohort=result[,(2*A+T+C+4)],sigma2.cohort=result[,(2*A+T+C+5)],epsilon=result[,(2*A+T+C+6)],accept,accept.beta,accept.alpha,accept.cohort,accept.epsilon,accept.sigma2.k,accept.rho.cohort,accept.sigma2.cohort)
}

system.time(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-MCMC.rates.new.over.negbin.int.RW.notrunc.cohort.group.matchprior(n=201000,burnin=1000,thin=10,exposures=round(Ext),deaths=round(Dxt),t0=(-21),t.interval=42,k=k.new,alpha=alpha.new,beta=beta.new,cohort=cohort.new,sigma2.k=sigma2.k,sigma2.cohort=sigma2.cohort,rho=1,rho.cohort=rho.cohort.new,sigma2.rho.cohort=1,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,
lambda=1,epsilon=100,ak=ak,bk=bk,sigma2.rho=sigma2.rho,a.epsilon=25,b.epsilon=0.05,a.cohort=a.cohort,b.cohort=b.cohort,sigma.prop.cohort=((2.08^2)/138*marg.var.cohort),sigma.prop.k=((3.38^2)/40*marg.var.k),sigma2.x=c(0.000001,0.00001,0.00004,0.00002,rep(0.00004,10),rep(0.00002,16),rep(0.00003,7),rep(0.00001,8),rep(0.000007,27),rep(0.000007,24),rep(0.000005,4)),sigma2.x.alpha=c(0.0008,0.0008,0.003,rep(0.007,14),rep(0.002,21),rep(0.0005,62)),sigma2.prop.rho.cohort=0.1,sigma2.prop.epsilon=0.1,sigma2.k.prop=1,sigma2.prop.sigma2.cohort=0.00005))


theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-cbind(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$k.new,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$beta.new,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$alpha.new,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$cohort.new,log(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$sigma2.k),log(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$lambda),log(rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$sigma2.cohort),rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$rho.1,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$rho.cohort,rates.MCMC.over.negbin.int.RW.y0.new.notrunc.cohort.group.marg.matchprior.100.001$epsilon)
theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[seq(10,200000,by=10),] #further thinning

par(mfrow=c(4,4))
plot(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,384]),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,385]),xlab="iterations",ylab="",main="lambda",type="l")
plot(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,386]),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387],xlab="iterations",ylab="",main="rho.1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,388],xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389],xlab="iterations",ylab="",main="epsilon",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143],xlab="iterations",ylab="",main="alpha_1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,242],xlab="iterations",ylab="",main="alpha_100",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43],xlab="iterations",ylab="",main="beta_1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,142],xlab="iterations",ylab="",main="beta_100",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1],xlab="iterations",ylab="",main="kappa_1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,20],xlab="iterations",ylab="",main="kappa_20",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243],xlab="iterations",ylab="",main="cohort_1",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,277],xlab="iterations",ylab="",main="cohort_35",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,314],xlab="iterations",ylab="",main="cohort_72",type="l")
plot(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,342],xlab="iterations",ylab="",main="cohort_100",type="l")

par(mfrow=c(4,4))
plot(density(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,384]),n=50000),xlab="iterations",ylab="",main="sigma2_k",type="l")
plot(density(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,385]),n=50000),xlab="iterations",ylab="",main="lambda",type="l")
plot(density(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,386]),n=50000),xlab="iterations",ylab="",main="sigma2.cohort",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387],n=50000),xlab="iterations",ylab="",main="rho.1",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,388],n=50000),xlab="iterations",ylab="",main="rho.cohort",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389],n=50000),xlab="iterations",ylab="",main="epsilon",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143],n=50000),xlab="iterations",ylab="",main="alpha_1",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,242],n=50000),xlab="iterations",ylab="",main="alpha_100",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43],n=50000),xlab="iterations",ylab="",main="beta_1",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,142],n=50000),xlab="iterations",ylab="",main="beta_100",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1],n=50000),xlab="iterations",ylab="",main="kappa_1",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,20],n=50000),xlab="iterations",ylab="",main="kappa_20",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243],n=50000),xlab="iterations",ylab="",main="cohort_1",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,277],n=50000),xlab="iterations",ylab="",main="cohort_35",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,314],n=50000),xlab="iterations",ylab="",main="cohort_72",type="l")
plot(density(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,342],n=50000),xlab="iterations",ylab="",main="cohort_100",type="l")

acf(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,384]),main="sigma2_k")
acf(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,385]),main="lambda")
acf(exp(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,386]),main="sigma2.cohort")
#acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387],main="rho.1")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,388],main="rho.cohort")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389],main="epsilon")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143],main="alpha_1")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,242],main="alpha_100")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43],main="beta_1")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,142],main="beta_100")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1],main="kappa_1")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,20],main="kappa_20")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,244],main="cohort_1")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,278],main="cohort_35")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,315],main="cohort_72")
acf(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,343],main="cohort_100")


alpha.RW.over.negbin.int.loglinear.cohort.percentile<-apply(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,143:243],2,percentile.fn)
beta.RW.over.negbin.int.loglinear.cohort.percentile<-apply(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,43:143],2,percentile.fn)
kappa.RW.over.negbin.int.loglinear.cohort.percentile<-apply(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,1:42],2,percentile.fn)
cohort.RW.over.negbin.int.loglinear.cohort.percentile<-apply(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,243:383],2,percentile.fn)

plot(cohort.RW.over.negbin.int.loglinear.cohort.percentile[2,],type="l",ylim=c(-0.15,0.25))
lines(cohort.RW.over.negbin.int.loglinear.cohort.percentile[1,],lty=2)
lines(cohort.RW.over.negbin.int.loglinear.cohort.percentile[3,],lty=2)

##################
##Marginal likelihoods for APCI cohort models
###########################

##NBAPCI-AR1
 
like.prior.loglinear.negbin.match.prior.cohort<-function(param,Dxt,Ext,A,T,t,lx,lambda.alpha,lambda.beta,a.rho,b.rho,ak,bk,a.epsilon,b.epsilon,a.cohort,b.cohort,sigma2.rho.cohort,J,J.cohort,I.cohort){#supply param=c(k,beta,alpha,log.sigma2.k,log.lambda,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
cohort<-param[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-exp(param[3*A+2*T])
lambda<-exp(param[3*A+2*T+1])
sigma2.cohort<-exp(param[3*A+2*T+2])
rho<-param[3*A+2*T+3]
rho.cohort<-param[3*A+2*T+4]
epsilon<-param[3*A+2*T+5]

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic
S.cohort<-sigma2.cohort*D.cohort

I<-diag(1,nrow=T)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}
R[1,1]<-sqrt(1-rho^2)
i.R<-forwardsolve(R,I)
i.Q<-i.R%*%t(i.R)
C<-J%*%i.Q%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-2*sigma2.k*D 

p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat)+epsilon)	

result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+sum(log(ddoublex(beta,mu=0,lambda=lambda.beta)))+dmvnorm.tol(cohort[-c(1,72,A+T-1)],mean=rep(0,A+T-4),sigma=S.cohort,log=TRUE)+dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)+
#sum(log(ddoublex(alpha,mu=lx,lambda=lambda.alpha)))+log(0.5)+dbeta((rho+1)/2,a.rho,b.rho,log=TRUE)+log(lambda)-lambda*sigma2.k+log(sigma2.k)+ak*log(bk/400)-lgamma(ak)+ak*log(lambda)-bk/400*lambda+dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)+a.cohort*log(b.cohort)-lgamma(a.cohort)-a.cohort*log(sigma2.cohort)-b.cohort/sigma2.cohort+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon
sum(log(ddoublex(alpha,mu=lx,lambda=lambda.alpha)))+log(0.5)+dbeta((rho+1)/2,a.rho,b.rho,log=TRUE)+log(lambda)-lambda*sigma2.k+log(sigma2.k)+ak*log(bk/400)-lgamma(ak)+ak*log(lambda)-bk/400*lambda+dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)+log(5)+log(sigma2.cohort)/2+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon
if ((lambda<0.0001) | (epsilon<1) | (epsilon>50000) | (sigma2.cohort>0.01)){result<--Inf}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
ak<-1
bk<-0.0001
a.epsilon<-25
b.epsilon<-0.05
a.rho<-3
b.rho<-2
lambda.alpha<-rep(2.5,A)
lambda.beta<-rep(0.03,A)
a.cohort<-a.cohort
b.cohort<-b.cohort
sigma2.rho.cohort<-1

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1/sqrt(T),T)
J[2,]<-1/((T-1)/2)*((-(T-1)/2):((T-1)/2))
C<-A+T-1
J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1

I.cohort<-diag(rep(1,C))

#theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[seq(5,200000,by=5),]
#theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001<-theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[seq(5,200000,by=5),]

like.prior.loglinear.negbin.match.prior.cohort(param=theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.loglinear.group.match.prior.cohort<-apply(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001,1,like.prior.loglinear.negbin.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)

mean.loglinear.vec.match.prior.cohort<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,-c(1,2,243,314,383,387,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389])),2,mean)
covariance.loglinear.mat.match.prior.cohort<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,-c(1,2,243,314,383,387,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389])))
mean.rho.loglinear.match.prior.cohort<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387])
variance.rho.loglinear.match.prior.cohort<-var(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,387])

chol.cov.loglinear.group.match.prior.cohort<-chol(covariance.loglinear.mat.match.prior.cohort)
inverse.t.chol.cov.loglinear.group.match.prior.cohort<-solve(t(chol.cov.loglinear.group.match.prior.cohort))
 
find.k1<-function(x,T){
sum((1:(T-2))*x)
}
find.k2<-function(x,T){
-sum((2:(T-1))*x)
}
find.cohort<-function(x,A,T){
cohort1<-1/(71*(A+T-2))*sum(c((-70):(-1),1:68)*c((A+T-3):70,68:1)*x)
cohort72<-1/(69*71)*sum(-c((A+T-3):70,68:1)*c(1:70,72:(A+T-3))*x)
cohort141<-1/(69*(A+T-2))*sum(c(1:70,72:(A+T-3))*c(70:1,(-1):(-68))*x)
c(cohort1,x[1:70],cohort72,x[-(1:70)],cohort141)
}

M<-matrix(rep(mean.loglinear.vec.match.prior.cohort,20000),nrow=383,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(383*20000),nrow=383,ncol=20000)
sample.bridge.loglinear.group.match.prior.cohort<-M+t(chol.cov.loglinear.group.match.prior.cohort)%*%Z
sample.bridge.loglinear.group.match.prior.cohort<-t(sample.bridge.loglinear.group.match.prior.cohort)
gc()
sample.rho.bridge.loglinear.match.prior.cohort<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.loglinear.match.prior.cohort,sd=sqrt(variance.rho.loglinear.match.prior.cohort))
full.sample.bridge.loglinear.group.match.prior.cohort<-cbind(apply(sample.bridge.loglinear.group.match.prior.cohort[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.cohort[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.cohort[,1:240],t(apply(sample.bridge.loglinear.group.match.prior.cohort[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.loglinear.group.match.prior.cohort[,379:381],sample.rho.bridge.loglinear.match.prior.cohort,sample.bridge.loglinear.group.match.prior.cohort[,382],exp(sample.bridge.loglinear.group.match.prior.cohort[,383]))
rm(M);rm(Z);rm(sample.rho.bridge.loglinear.match.prior.cohort);rm(sample.bridge.loglinear.group.match.prior.cohort);gc()
like.prior.loglinear.negbin.match.prior.cohort(full.sample.bridge.loglinear.group.match.prior.cohort[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.loglinear.group.match.prior.cohort<-apply(full.sample.bridge.loglinear.group.match.prior.cohort,1,like.prior.loglinear.negbin.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)
    
log.det.Jacobian.loglinear.group.match.prior.cohort<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.cohort,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.cohort(x=c(full.sample.bridge.loglinear.group.match.prior.cohort[1000,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort[1000,389])),mean.vec=mean.loglinear.vec.match.prior.cohort,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort,mean.rho=mean.rho.loglinear.match.prior.cohort,variance.rho=variance.rho.loglinear.match.prior.cohort)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.cohort[1000,-c(1,2,243,314,383,387,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort[1000,389])),mean=mean.loglinear.vec.match.prior.cohort,sigma=covariance.loglinear.mat.match.prior.cohort,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior.cohort[1000,387],a=-1,b=1,mean=mean.rho.loglinear.match.prior.cohort,sd=sqrt(variance.rho.loglinear.match.prior.cohort)))
 
q2.loglinear.group.match.prior.cohort<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,-c(1,2,243,314,383,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort,mean.vec=mean.loglinear.vec.match.prior.cohort,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort,mean.rho=mean.rho.loglinear.match.prior.cohort,variance.rho=variance.rho.loglinear.match.prior.cohort)
q2.bridge.loglinear.group.match.prior.cohort<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.cohort[,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort,mean.vec=mean.loglinear.vec.match.prior.cohort,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort,mean.rho=mean.rho.loglinear.match.prior.cohort,variance.rho=variance.rho.loglinear.match.prior.cohort)   
log.l.loglinear.group.match.prior.cohort<-likelihood.loglinear.group.match.prior.cohort-q2.loglinear.group.match.prior.cohort
log.l.tilda.loglinear.group.match.prior.cohort<-likelihood.bridge.loglinear.group.match.prior.cohort-q2.bridge.loglinear.group.match.prior.cohort

log.l.tilda.loglinear.group.match.prior.cohort<-log.l.tilda.loglinear.group.match.prior.cohort+22900
log.l.loglinear.group.match.prior.cohort<-log.l.loglinear.group.match.prior.cohort+22900
l.loglinear.group.match.prior.cohort<-exp(log.l.loglinear.group.match.prior.cohort)
l.tilda.loglinear.group.match.prior.cohort<-exp(log.l.tilda.loglinear.group.match.prior.cohort)
 
nc.loglinear.group.match.prior.cohort<-bridge(initial=100,m=100,sample1=theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001,sample2=full.sample.bridge.loglinear.group.match.prior.cohort,n1=20000,n2=20000,l=l.loglinear.group.match.prior.cohort,l.tilda=l.tilda.loglinear.group.match.prior.cohort) 
log(nc.loglinear.group.match.prior.cohort)-22900 	#-22416.05 (n1=n2=20000,corrected and uniform prior for sigma.cohort)

##splitting
likelihood.loglinear.group.match.prior.cohort.split<-likelihood.loglinear.group.match.prior.cohort[10001:20000]

mean.loglinear.vec.match.prior.cohort.split<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,-c(1,2,243,314,383,387,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,389])),2,mean)
covariance.loglinear.mat.match.prior.cohort.split<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,-c(1,2,243,314,383,387,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,389])))
mean.rho.loglinear.match.prior.cohort.split<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,387])
variance.rho.loglinear.match.prior.cohort.split<-var(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,387])

chol.cov.loglinear.group.match.prior.cohort.split<-chol(covariance.loglinear.mat.match.prior.cohort.split)
inverse.t.chol.cov.loglinear.group.match.prior.cohort.split<-solve(t(chol.cov.loglinear.group.match.prior.cohort.split))

M<-matrix(rep(mean.loglinear.vec.match.prior.cohort.split,20000),nrow=383,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(383*20000),nrow=383,ncol=20000)
sample.bridge.loglinear.group.match.prior.cohort.split<-M+t(chol.cov.loglinear.group.match.prior.cohort.split)%*%Z
sample.bridge.loglinear.group.match.prior.cohort.split<-t(sample.bridge.loglinear.group.match.prior.cohort.split)
gc()
sample.rho.bridge.loglinear.match.prior.cohort.split<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.loglinear.match.prior.cohort.split,sd=sqrt(variance.rho.loglinear.match.prior.cohort.split))
full.sample.bridge.loglinear.group.match.prior.cohort.split<-cbind(apply(sample.bridge.loglinear.group.match.prior.cohort.split[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.cohort.split[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.cohort.split[,1:240],t(apply(sample.bridge.loglinear.group.match.prior.cohort.split[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.loglinear.group.match.prior.cohort.split[,379:381],sample.rho.bridge.loglinear.match.prior.cohort.split,sample.bridge.loglinear.group.match.prior.cohort.split[,382],exp(sample.bridge.loglinear.group.match.prior.cohort.split[,383]))
rm(M);rm(Z);rm(sample.rho.bridge.loglinear.match.prior.cohort.split);rm(sample.bridge.loglinear.group.match.prior.cohort.split);gc()
like.prior.loglinear.negbin.match.prior.cohort(full.sample.bridge.loglinear.group.match.prior.cohort.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.loglinear.group.match.prior.cohort.split<-apply(full.sample.bridge.loglinear.group.match.prior.cohort.split,1,like.prior.loglinear.negbin.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)

log.det.Jacobian.loglinear.group.match.prior.cohort.split<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.cohort.split,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.cohort(x=c(full.sample.bridge.loglinear.group.match.prior.cohort.split[1000,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.split[1000,389])),mean.vec=mean.loglinear.vec.match.prior.cohort.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.split,mean.rho=mean.rho.loglinear.match.prior.cohort.split,variance.rho=variance.rho.loglinear.match.prior.cohort.split)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.cohort.split[1000,-c(1,2,243,314,383,387,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.split[1000,389])),mean=mean.loglinear.vec.match.prior.cohort.split,sigma=covariance.loglinear.mat.match.prior.cohort.split,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior.cohort.split[1000,387],a=-1,b=1,mean=mean.rho.loglinear.match.prior.cohort.split,sd=sqrt(variance.rho.loglinear.match.prior.cohort.split)))
 
q2.loglinear.group.match.prior.cohort.split<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,-c(1,2,243,314,383,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort,mean.vec=mean.loglinear.vec.match.prior.cohort.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.split,mean.rho=mean.rho.loglinear.match.prior.cohort.split,variance.rho=variance.rho.loglinear.match.prior.cohort.split)
q2.bridge.loglinear.group.match.prior.cohort.split<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.cohort.split[,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.split[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort,mean.vec=mean.loglinear.vec.match.prior.cohort.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.split,mean.rho=mean.rho.loglinear.match.prior.cohort.split,variance.rho=variance.rho.loglinear.match.prior.cohort.split)   
log.l.loglinear.group.match.prior.cohort.split<-likelihood.loglinear.group.match.prior.cohort.split-q2.loglinear.group.match.prior.cohort.split
log.l.tilda.loglinear.group.match.prior.cohort.split<-likelihood.bridge.loglinear.group.match.prior.cohort.split-q2.bridge.loglinear.group.match.prior.cohort.split

log.l.tilda.loglinear.group.match.prior.cohort.split<-log.l.tilda.loglinear.group.match.prior.cohort.split+22900
log.l.loglinear.group.match.prior.cohort.split<-log.l.loglinear.group.match.prior.cohort.split+22900
l.loglinear.group.match.prior.cohort.split<-exp(log.l.loglinear.group.match.prior.cohort.split)
l.tilda.loglinear.group.match.prior.cohort.split<-exp(log.l.tilda.loglinear.group.match.prior.cohort.split)
 
nc.loglinear.group.match.prior.cohort.split<-bridge(initial=100,m=100,sample1=theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,],sample2=full.sample.bridge.loglinear.group.match.prior.cohort,n1=10000,n2=20000,l=l.loglinear.group.match.prior.cohort.split,l.tilda=l.tilda.loglinear.group.match.prior.cohort.split) 
log(nc.loglinear.group.match.prior.cohort.split)-22900  #-22414.11 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)


##cross-splitting
likelihood.loglinear.group.match.prior.cohort.split.2<-likelihood.loglinear.group.match.prior.cohort[1:10000]

mean.loglinear.vec.match.prior.cohort.split.2<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,-c(1,2,243,314,383,387,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,389])),2,mean)
covariance.loglinear.mat.match.prior.cohort.split.2<-cov(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,-c(1,2,243,314,383,387,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,389])))
mean.rho.loglinear.match.prior.cohort.split.2<-mean(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,387])
variance.rho.loglinear.match.prior.cohort.split.2<-var(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,387])

chol.cov.loglinear.group.match.prior.cohort.split.2<-chol(covariance.loglinear.mat.match.prior.cohort.split.2)
inverse.t.chol.cov.loglinear.group.match.prior.cohort.split.2<-solve(t(chol.cov.loglinear.group.match.prior.cohort.split.2))

M<-matrix(rep(mean.loglinear.vec.match.prior.cohort.split.2,20000),nrow=383,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(383*20000),nrow=383,ncol=20000)
sample.bridge.loglinear.group.match.prior.cohort.split.2<-M+t(chol.cov.loglinear.group.match.prior.cohort.split.2)%*%Z
sample.bridge.loglinear.group.match.prior.cohort.split.2<-t(sample.bridge.loglinear.group.match.prior.cohort.split.2)
gc()
sample.rho.bridge.loglinear.match.prior.cohort.split.2<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.loglinear.match.prior.cohort.split.2,sd=sqrt(variance.rho.loglinear.match.prior.cohort.split.2))
full.sample.bridge.loglinear.group.match.prior.cohort.split.2<-cbind(apply(sample.bridge.loglinear.group.match.prior.cohort.split.2[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.cohort.split.2[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.cohort.split.2[,1:240],t(apply(sample.bridge.loglinear.group.match.prior.cohort.split.2[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.loglinear.group.match.prior.cohort.split.2[,379:381],sample.rho.bridge.loglinear.match.prior.cohort.split.2,sample.bridge.loglinear.group.match.prior.cohort.split.2[,382],exp(sample.bridge.loglinear.group.match.prior.cohort.split.2[,383]))
rm(M);rm(Z);rm(sample.rho.bridge.loglinear.match.prior.cohort.split.2);rm(sample.bridge.loglinear.group.match.prior.cohort.split.2);gc()
like.prior.loglinear.negbin.match.prior.cohort(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.loglinear.group.match.prior.cohort.split.2<-apply(full.sample.bridge.loglinear.group.match.prior.cohort.split.2,1,like.prior.loglinear.negbin.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,a.rho=a.rho,b.rho=b.rho,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort,I.cohort=I.cohort)

log.det.Jacobian.loglinear.group.match.prior.cohort.split.2<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.cohort.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.cohort(x=c(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[1000,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[1000,389])),mean.vec=mean.loglinear.vec.match.prior.cohort.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.split.2,mean.rho=mean.rho.loglinear.match.prior.cohort.split.2,variance.rho=variance.rho.loglinear.match.prior.cohort.split.2)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[1000,-c(1,2,243,314,383,387,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[1000,389])),mean=mean.loglinear.vec.match.prior.cohort.split.2,sigma=covariance.loglinear.mat.match.prior.cohort.split.2,log=TRUE)+log(dtruncnorm(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[1000,387],a=-1,b=1,mean=mean.rho.loglinear.match.prior.cohort.split.2,sd=sqrt(variance.rho.loglinear.match.prior.cohort.split.2)))
 
q2.loglinear.group.match.prior.cohort.split.2<-apply(cbind(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,-c(1,2,243,314,383,389)],log(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort,mean.vec=mean.loglinear.vec.match.prior.cohort.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.split.2,mean.rho=mean.rho.loglinear.match.prior.cohort.split.2,variance.rho=variance.rho.loglinear.match.prior.cohort.split.2)
q2.bridge.loglinear.group.match.prior.cohort.split.2<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.split.2[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort,mean.vec=mean.loglinear.vec.match.prior.cohort.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.split.2,mean.rho=mean.rho.loglinear.match.prior.cohort.split.2,variance.rho=variance.rho.loglinear.match.prior.cohort.split.2)   
log.l.loglinear.group.match.prior.cohort.split.2<-likelihood.loglinear.group.match.prior.cohort.split.2-q2.loglinear.group.match.prior.cohort.split.2
log.l.tilda.loglinear.group.match.prior.cohort.split.2<-likelihood.bridge.loglinear.group.match.prior.cohort.split.2-q2.bridge.loglinear.group.match.prior.cohort.split.2

log.l.tilda.loglinear.group.match.prior.cohort.split.2<-log.l.tilda.loglinear.group.match.prior.cohort.split.2+22900
log.l.loglinear.group.match.prior.cohort.split.2<-log.l.loglinear.group.match.prior.cohort.split.2+22900
l.loglinear.group.match.prior.cohort.split.2<-exp(log.l.loglinear.group.match.prior.cohort.split.2)
l.tilda.loglinear.group.match.prior.cohort.split.2<-exp(log.l.tilda.loglinear.group.match.prior.cohort.split.2)
 
nc.loglinear.group.match.prior.cohort.split.2<-bridge(initial=100,m=100,sample1=theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,],sample2=full.sample.bridge.loglinear.group.match.prior.cohort.2,n1=10000,n2=20000,l=l.loglinear.group.match.prior.cohort.split.2,l.tilda=l.tilda.loglinear.group.match.prior.cohort.split.2) 
log(nc.loglinear.group.match.prior.cohort.split.2)-22900  #-22414.13 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)


##so cross-splitting estimates are #0.5*(-22414.11-22414.13)=-22414.12 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)

##Random walk RW

like.prior.loglinear.negbin.match.prior.cohort.RW<-function(param,Dxt,Ext,A,T,t,lx,lambda.alpha,lambda.beta,ak,bk,a.epsilon,b.epsilon,a.cohort,b.cohort,sigma2.rho.cohort,J,J.cohort){#supply param=c(k,beta,alpha,log.sigma2.k,log.lambda,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
cohort<-param[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-exp(param[3*A+2*T])
lambda<-exp(param[3*A+2*T+1])
sigma2.cohort<-exp(param[3*A+2*T+2])
rho<-param[3*A+2*T+3]
rho.cohort<-param[3*A+2*T+4]
epsilon<-param[3*A+2*T+5]

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

I.cohort<-diag(rep(1,C))
R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic
S.cohort<-sigma2.cohort*D.cohort

I<-diag(1,nrow=T)

R<-matrix(0,nrow=T,ncol=T)
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
if ((i-j)==0) R[i,j]<-1
}
}

i.R<-forwardsolve(R,I)
i.Q<-i.R%*%t(i.R)
C<-J%*%i.Q%*%t(J)
D<-C[(3:T),(3:T)]-(C[(3:T),(1:2)])%*%solve(C[(1:2),(1:2)])%*%(C[(1:2),(3:T)])
S<-2*sigma2.k*D 

p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(t)+matrix(rep(k,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat)+epsilon)	

result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+sum(log(ddoublex(beta,mu=0,lambda=lambda.beta)))+dmvnorm.tol(cohort[-c(1,72,A+T-1)],mean=rep(0,A+T-4),sigma=S.cohort,log=TRUE)+dmvnorm.tol(k[-(1:2)],mean=rep(0,T-2),sigma=S,log=TRUE)+
#sum(log(ddoublex(alpha,mu=lx,lambda=lambda.alpha)))+log(lambda)-lambda*sigma2.k+log(sigma2.k)+ak*log(bk/400)-lgamma(ak)+ak*log(lambda)-bk/400*lambda+dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)+a.cohort*log(b.cohort)-lgamma(a.cohort)-a.cohort*log(sigma2.cohort)-b.cohort/sigma2.cohort+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon
sum(log(ddoublex(alpha,mu=lx,lambda=lambda.alpha)))+log(lambda)-lambda*sigma2.k+log(sigma2.k)+ak*log(bk/400)-lgamma(ak)+ak*log(lambda)-bk/400*lambda+dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)+log(5)+log(sigma2.cohort)/2+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon
if ((lambda<0.0001) | (epsilon<1) | (epsilon>50000) | (sigma2.cohort>0.01)){result<--Inf}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
ak<-1
bk<-0.0001
a.epsilon<-25
b.epsilon<-0.05
lambda.alpha<-rep(2.5,A)
lambda.beta<-rep(0.03,A)
a.cohort<-a.cohort
b.cohort<-b.cohort
sigma2.rho.cohort<-1

I<-diag(1,nrow=T)
J<-I
J[1,]<-rep(1,T)
J[2,]<-1/((T-1)/2)*((-(T-1)/2):((T-1)/2))
C<-A+T-1
J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1

like.prior.loglinear.negbin.match.prior.cohort.RW(param=theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
likelihood.loglinear.group.match.prior.cohort.RW<-apply(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001,1,like.prior.loglinear.negbin.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)

mean.loglinear.vec.match.prior.cohort.RW<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,-c(1,2,243,314,383,387,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389])),2,mean)
covariance.loglinear.mat.match.prior.cohort.RW<-cov(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,-c(1,2,243,314,383,387,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389])))

chol.cov.loglinear.group.match.prior.cohort.RW<-chol(covariance.loglinear.mat.match.prior.cohort.RW)
inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW<-solve(t(chol.cov.loglinear.group.match.prior.cohort.RW))

M<-matrix(rep(mean.loglinear.vec.match.prior.cohort.RW,20000),nrow=383,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(383*20000),nrow=383,ncol=20000)
sample.bridge.loglinear.group.match.prior.cohort.RW<-M+t(chol.cov.loglinear.group.match.prior.cohort.RW)%*%Z
sample.bridge.loglinear.group.match.prior.cohort.RW<-t(sample.bridge.loglinear.group.match.prior.cohort.RW)
gc()
full.sample.bridge.loglinear.group.match.prior.cohort.RW<-cbind(apply(sample.bridge.loglinear.group.match.prior.cohort.RW[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.cohort.RW[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.cohort.RW[,1:240],t(apply(sample.bridge.loglinear.group.match.prior.cohort.RW[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.loglinear.group.match.prior.cohort.RW[,379:381],rep(1,20000),sample.bridge.loglinear.group.match.prior.cohort.RW[,382],exp(sample.bridge.loglinear.group.match.prior.cohort.RW[,383]))
rm(M);rm(Z);rm(sample.bridge.loglinear.group.match.prior.cohort.RW);gc()
like.prior.loglinear.negbin.match.prior.cohort.RW(full.sample.bridge.loglinear.group.match.prior.cohort.RW[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
likelihood.bridge.loglinear.group.match.prior.cohort.RW<-apply(full.sample.bridge.loglinear.group.match.prior.cohort.RW,1,like.prior.loglinear.negbin.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
    
log.det.Jacobian.loglinear.group.match.prior.cohort.RW<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.cohort.RW(x=c(full.sample.bridge.loglinear.group.match.prior.cohort.RW[1000,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW[1000,389])),mean.vec=mean.loglinear.vec.match.prior.cohort.RW,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.cohort.RW[1000,-c(1,2,243,314,383,387,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW[1000,389])),mean=mean.loglinear.vec.match.prior.cohort.RW,sigma=covariance.loglinear.mat.match.prior.cohort.RW,log=TRUE)
 
q2.loglinear.group.match.prior.cohort.RW<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,-c(1,2,243,314,383,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort.RW,mean.vec=mean.loglinear.vec.match.prior.cohort.RW,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW)
q2.bridge.loglinear.group.match.prior.cohort.RW<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.cohort.RW[,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort.RW,mean.vec=mean.loglinear.vec.match.prior.cohort.RW,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW)   
log.l.loglinear.group.match.prior.cohort.RW<-likelihood.loglinear.group.match.prior.cohort.RW-q2.loglinear.group.match.prior.cohort.RW
log.l.tilda.loglinear.group.match.prior.cohort.RW<-likelihood.bridge.loglinear.group.match.prior.cohort.RW-q2.bridge.loglinear.group.match.prior.cohort.RW

log.l.tilda.loglinear.group.match.prior.cohort.RW<-log.l.tilda.loglinear.group.match.prior.cohort.RW+22900
log.l.loglinear.group.match.prior.cohort.RW<-log.l.loglinear.group.match.prior.cohort.RW+22900
l.loglinear.group.match.prior.cohort.RW<-exp(log.l.loglinear.group.match.prior.cohort.RW)
l.tilda.loglinear.group.match.prior.cohort.RW<-exp(log.l.tilda.loglinear.group.match.prior.cohort.RW)
 
nc.loglinear.group.match.prior.cohort.RW<-bridge(initial=100,m=100,sample1=theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001,sample2=full.sample.bridge.loglinear.group.match.prior.cohort.RW,n1=20000,n2=20000,l=l.loglinear.group.match.prior.cohort.RW,l.tilda=l.tilda.loglinear.group.match.prior.cohort.RW) 
log(nc.loglinear.group.match.prior.cohort.RW)-22900  #-22418.73 (n2=n1=20000,corrected and uniform prior for sigma.cohort)

##splitting
likelihood.loglinear.group.match.prior.cohort.RW.split<-likelihood.loglinear.group.match.prior.cohort.RW[10001:20000]

mean.loglinear.vec.match.prior.cohort.RW.split<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,-c(1,2,243,314,383,387,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,389])),2,mean)
covariance.loglinear.mat.match.prior.cohort.RW.split<-cov(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,-c(1,2,243,314,383,387,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,389])))

chol.cov.loglinear.group.match.prior.cohort.RW.split<-chol(covariance.loglinear.mat.match.prior.cohort.RW.split)
inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split<-solve(t(chol.cov.loglinear.group.match.prior.cohort.RW.split))

M<-matrix(rep(mean.loglinear.vec.match.prior.cohort.RW.split,20000),nrow=383,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(383*20000),nrow=383,ncol=20000)
sample.bridge.loglinear.group.match.prior.cohort.RW.split<-M+t(chol.cov.loglinear.group.match.prior.cohort.RW.split)%*%Z
sample.bridge.loglinear.group.match.prior.cohort.RW.split<-t(sample.bridge.loglinear.group.match.prior.cohort.RW.split)
gc()
full.sample.bridge.loglinear.group.match.prior.cohort.RW.split<-cbind(apply(sample.bridge.loglinear.group.match.prior.cohort.RW.split[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.cohort.RW.split[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.cohort.RW.split[,1:240],t(apply(sample.bridge.loglinear.group.match.prior.cohort.RW.split[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.loglinear.group.match.prior.cohort.RW.split[,379:381],rep(1,20000),sample.bridge.loglinear.group.match.prior.cohort.RW.split[,382],exp(sample.bridge.loglinear.group.match.prior.cohort.RW.split[,383]))
rm(M);rm(Z);rm(sample.bridge.loglinear.group.match.prior.cohort.RW.split);gc()
like.prior.loglinear.negbin.match.prior.cohort.RW(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
likelihood.bridge.loglinear.group.match.prior.cohort.RW.split<-apply(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split,1,like.prior.loglinear.negbin.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
    
log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.cohort.RW(x=c(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[1000,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[1000,389])),mean.vec=mean.loglinear.vec.match.prior.cohort.RW.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[1000,-c(1,2,243,314,383,387,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[1000,389])),mean=mean.loglinear.vec.match.prior.cohort.RW.split,sigma=covariance.loglinear.mat.match.prior.cohort.RW.split,log=TRUE)
 
q2.loglinear.group.match.prior.cohort.RW.split<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,-c(1,2,243,314,383,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort.RW,mean.vec=mean.loglinear.vec.match.prior.cohort.RW.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split)
q2.bridge.loglinear.group.match.prior.cohort.RW.split<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort.RW,mean.vec=mean.loglinear.vec.match.prior.cohort.RW.split,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split)   
log.l.loglinear.group.match.prior.cohort.RW.split<-likelihood.loglinear.group.match.prior.cohort.RW.split-q2.loglinear.group.match.prior.cohort.RW.split
log.l.tilda.loglinear.group.match.prior.cohort.RW.split<-likelihood.bridge.loglinear.group.match.prior.cohort.RW.split-q2.bridge.loglinear.group.match.prior.cohort.RW.split

log.l.tilda.loglinear.group.match.prior.cohort.RW.split<-log.l.tilda.loglinear.group.match.prior.cohort.RW.split+22900
log.l.loglinear.group.match.prior.cohort.RW.split<-log.l.loglinear.group.match.prior.cohort.RW.split+22900
l.loglinear.group.match.prior.cohort.RW.split<-exp(log.l.loglinear.group.match.prior.cohort.RW.split)
l.tilda.loglinear.group.match.prior.cohort.RW.split<-exp(log.l.tilda.loglinear.group.match.prior.cohort.RW.split)
 
nc.loglinear.group.match.prior.cohort.RW.split<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,],sample2=full.sample.bridge.loglinear.group.match.prior.cohort.RW.split,n1=10000,n2=20000,l=l.loglinear.group.match.prior.cohort.RW.split,l.tilda=l.tilda.loglinear.group.match.prior.cohort.RW.split) 
log(nc.loglinear.group.match.prior.cohort.RW.split)-22900  #-22416.85 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)


##cross-splitting
likelihood.loglinear.group.match.prior.cohort.RW.split.2<-likelihood.loglinear.group.match.prior.cohort.RW[1:10000]

mean.loglinear.vec.match.prior.cohort.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,-c(1,2,243,314,383,387,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,389])),2,mean)
covariance.loglinear.mat.match.prior.cohort.RW.split.2<-cov(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,-c(1,2,243,314,383,387,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[10001:20000,389])))

chol.cov.loglinear.group.match.prior.cohort.RW.split.2<-chol(covariance.loglinear.mat.match.prior.cohort.RW.split.2)
inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split.2<-solve(t(chol.cov.loglinear.group.match.prior.cohort.RW.split.2))

M<-matrix(rep(mean.loglinear.vec.match.prior.cohort.RW.split.2,20000),nrow=383,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(383*20000),nrow=383,ncol=20000)
sample.bridge.loglinear.group.match.prior.cohort.RW.split.2<-M+t(chol.cov.loglinear.group.match.prior.cohort.RW.split.2)%*%Z
sample.bridge.loglinear.group.match.prior.cohort.RW.split.2<-t(sample.bridge.loglinear.group.match.prior.cohort.RW.split.2)
gc()
full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2<-cbind(apply(sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,1:40],1,find.k1,T=42),apply(sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,1:40],1,find.k2,T=42),sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,1:240],t(apply(sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,379:381],rep(1,20000),sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,382],exp(sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,383]))
rm(M);rm(Z);rm(sample.bridge.loglinear.group.match.prior.cohort.RW.split.2);gc()
like.prior.loglinear.negbin.match.prior.cohort.RW(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
likelihood.bridge.loglinear.group.match.prior.cohort.RW.split.2<-apply(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2,1,like.prior.loglinear.negbin.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,lambda.alpha=lambda.alpha,lambda.beta=lambda.beta,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,a.cohort=a.cohort,b.cohort=b.cohort,sigma2.rho.cohort=sigma2.rho.cohort,J=J,J.cohort=J.cohort)
    
log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split.2<-determinant(inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.loglinear.match.prior.cohort.RW(x=c(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[1000,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[1000,389])),mean.vec=mean.loglinear.vec.match.prior.cohort.RW.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split.2)
dmvnorm(c(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[1000,-c(1,2,243,314,383,387,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[1000,389])),mean=mean.loglinear.vec.match.prior.cohort.RW.split.2,sigma=covariance.loglinear.mat.match.prior.cohort.RW.split.2,log=TRUE)
 
q2.loglinear.group.match.prior.cohort.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,-c(1,2,243,314,383,389)],log(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort.RW,mean.vec=mean.loglinear.vec.match.prior.cohort.RW.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split.2)
q2.bridge.loglinear.group.match.prior.cohort.RW.split.2<-apply(cbind(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,-c(1,2,243,314,383,389)],log(full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2[,389])),1,transformation.dmvnorm.loglinear.match.prior.cohort.RW,mean.vec=mean.loglinear.vec.match.prior.cohort.RW.split.2,rij=inverse.t.chol.cov.loglinear.group.match.prior.cohort.RW.split.2,log.det.Jacobian=log.det.Jacobian.loglinear.group.match.prior.cohort.RW.split.2)   
log.l.loglinear.group.match.prior.cohort.RW.split.2<-likelihood.loglinear.group.match.prior.cohort.RW.split.2-q2.loglinear.group.match.prior.cohort.RW.split.2
log.l.tilda.loglinear.group.match.prior.cohort.RW.split.2<-likelihood.bridge.loglinear.group.match.prior.cohort.RW.split.2-q2.bridge.loglinear.group.match.prior.cohort.RW.split.2

log.l.tilda.loglinear.group.match.prior.cohort.RW.split.2<-log.l.tilda.loglinear.group.match.prior.cohort.RW.split.2+22900
log.l.loglinear.group.match.prior.cohort.RW.split.2<-log.l.loglinear.group.match.prior.cohort.RW.split.2+22900
l.loglinear.group.match.prior.cohort.RW.split.2<-exp(log.l.loglinear.group.match.prior.cohort.RW.split.2)
l.tilda.loglinear.group.match.prior.cohort.RW.split.2<-exp(log.l.tilda.loglinear.group.match.prior.cohort.RW.split.2)
 
nc.loglinear.group.match.prior.cohort.RW.split.2<-bridge(initial=100,m=1000,sample1=theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:10000,],sample2=full.sample.bridge.loglinear.group.match.prior.cohort.RW.split.2,n1=10000,n2=20000,l=l.loglinear.group.match.prior.cohort.RW.split.2,l.tilda=l.tilda.loglinear.group.match.prior.cohort.RW.split.2) 
log(nc.loglinear.group.match.prior.cohort.RW.split.2)-22900 #-22416.76 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)


##so cross-splitting estimate is 0.5*(-22416.85-22416.76)=-22416.81 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)

#######################################
##NBLCC-AR1 sum(beta_x)=1,sum(k_t)=0,sum(gamma_c)=sum(c*gamma_c)=sum(c^2*gamma_c)=0
#######################################

like.prior.negbin.lca.match.prior.cohort<-function(param,Dxt,Ext,A,T,t,lx,sigma2.l,a.rho,b.rho,gamma.0,sigma.mat.0,ak,bk,a.epsilon,b.epsilon,I=diag(rep(1,A-1)),K=matrix(1,nrow=A-1,ncol=A-1),sigma2.rho.cohort,J,J.cohort,I.cohort){#supply param=c(k,beta,alpha,log.sigma2.k,log.sigma2.beta,gamma1,gamma2,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
cohort<-param[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-exp(param[3*A+2*T])
sigma2.beta<-exp(param[3*A+2*T+1])
rho<-param[3*A+2*T+4]
gamma1<-param[3*A+2*T+2]
gamma2<-param[3*A+2*T+3]
gamma<-c(gamma1,gamma2)
ita.t<-gamma1+gamma2*t
rho.cohort<-param[3*A+2*T+5]
sigma2.cohort<-exp(param[3*A+2*T+6])
epsilon<-(param[3*A+2*T+7])

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic
S.cohort<-sigma2.cohort*D.cohort

R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
R[1,1]<-sqrt(1-rho^2)
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(k)+cohort.mat)+epsilon)	
X<-cbind(rep(1,T),t)


{result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+dmvnorm.tol(cohort[-c(1,72,A+T-1)],mean=rep(0,A+T-4),sigma=S.cohort,log=TRUE)+dmvnorm.tol(k[-1],mean=((X%*%gamma)[-1]-B[2:T,1]/B[1,1]*sum(X%*%gamma)),sigma=(sigma2.k*D),log=TRUE)+dmvnorm.tol(beta[-1],mean=rep(1/A,A-1),sigma=sigma2.beta*(I-1/A*K),log=TRUE)+
sum(dnorm(alpha,mean=lx,sd=sqrt(sigma2.l),log=TRUE))+log(0.5)+dbeta((rho+1)/2,a.rho,b.rho,log=TRUE)+dmvnorm(gamma,mean=gamma.0,sigma=sigma.mat.0,log=TRUE)+ak*log(bk)-lgamma(ak)-ak*log(sigma2.k)-bk/sigma2.k+dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)+log(5)+log(sigma2.cohort)/2+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon}
if (sigma2.cohort>0.01){result<--Inf}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001
a.rho<-3
b.rho<-2
gamma.0<-c(0,0)
sigma.mat.0<-matrix(c(2000,0,0,2),nrow=2)
a.epsilon<-25
b.epsilon<-0.05
J<-diag(rep(1,T))
J[1,]<-rep(1,T)
C<-A+T-1
J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1

I.cohort<-diag(rep(1,C))


like.prior.negbin.lca.match.prior.cohort(param=theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.negbin.match.prior.cohort<-apply(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif,1,like.prior.negbin.lca.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)

mean.negbin.vec.match.prior.cohort<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,-c(1,43,243,314,383,385,388,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391])),2,mean)
covariance.negbin.mat.match.prior.cohort<-cov(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,-c(1,43,243,314,383,385,388,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391])))
mean.rho.negbin.match.prior.cohort<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388])
variance.rho.negbin.match.prior.cohort<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,388])
	
chol.cov.negbin.match.prior.cohort<-chol(covariance.negbin.mat.match.prior.cohort)
inverse.t.chol.cov.negbin.match.prior.cohort<-solve(t(chol.cov.negbin.match.prior.cohort))

M<-matrix(rep(mean.negbin.vec.match.prior.cohort,20000),nrow=384,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(384*20000),nrow=384,ncol=20000)
sample.bridge.negbin.match.prior.cohort<-M+t(chol.cov.negbin.match.prior.cohort)%*%Z
sample.bridge.negbin.match.prior.cohort<-t(sample.bridge.negbin.match.prior.cohort)
gc()
sample.rho.bridge.negbin.match.prior.cohort<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.negbin.match.prior.cohort,sd=sqrt(variance.rho.negbin.match.prior.cohort))
full.sample.bridge.negbin.match.prior.cohort<-cbind(-apply(sample.bridge.negbin.match.prior.cohort[,1:41],1,sum),sample.bridge.negbin.match.prior.cohort[,1:41],1-apply(sample.bridge.negbin.match.prior.cohort[,42:140],1,sum),sample.bridge.negbin.match.prior.cohort[,42:240],t(apply(sample.bridge.negbin.match.prior.cohort[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.negbin.match.prior.cohort[,379],rep(log(0.005),20000),sample.bridge.negbin.match.prior.cohort[,380:381],sample.rho.bridge.negbin.match.prior.cohort,sample.bridge.negbin.match.prior.cohort[,382:383],exp(sample.bridge.negbin.match.prior.cohort[,384]))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior.cohort);rm(sample.bridge.negbin.match.prior.cohort);gc()
like.prior.negbin.lca.match.prior.cohort(full.sample.bridge.negbin.match.prior.cohort[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.match.prior.cohort<-apply(full.sample.bridge.negbin.match.prior.cohort,1,like.prior.negbin.lca.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)

log.det.Jacobian.negbin.match.prior.cohort<-determinant(inverse.t.chol.cov.negbin.match.prior.cohort,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.cohort.2(x=c(full.sample.bridge.negbin.match.prior.cohort[1000,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort[1000,391])),mean.vec=mean.negbin.vec.match.prior.cohort,rij=inverse.t.chol.cov.negbin.match.prior.cohort,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort,mean.rho=mean.rho.negbin.match.prior.cohort,variance.rho=variance.rho.negbin.match.prior.cohort)
dmvnorm(c(full.sample.bridge.negbin.match.prior.cohort[1000,-c(1,43,243,314,383,385,388,391)],log(full.sample.bridge.negbin.match.prior.cohort[1000,391])),mean=mean.negbin.vec.match.prior.cohort,sigma=covariance.negbin.mat.match.prior.cohort,log=TRUE)+log(dtruncnorm(full.sample.bridge.negbin.match.prior.cohort[1000,388],a=-1,b=1,mean=mean.rho.negbin.match.prior.cohort,sd=sqrt(variance.rho.negbin.match.prior.cohort)))

q2.negbin.match.prior.cohort<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,-c(1,43,243,314,383,385,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391])),1,transformation.dmvnorm.match.prior.cohort.2,mean.vec=mean.negbin.vec.match.prior.cohort,rij=inverse.t.chol.cov.negbin.match.prior.cohort,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort,mean.rho=mean.rho.negbin.match.prior.cohort,variance.rho=variance.rho.negbin.match.prior.cohort)
q2.bridge.match.prior.cohort<-apply(cbind(full.sample.bridge.negbin.match.prior.cohort[,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort[,391])),1,transformation.dmvnorm.match.prior.cohort.2,mean.vec=mean.negbin.vec.match.prior.cohort,rij=inverse.t.chol.cov.negbin.match.prior.cohort,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort,mean.rho=mean.rho.negbin.match.prior.cohort,variance.rho=variance.rho.negbin.match.prior.cohort)
 
log.l.match.prior.cohort<-likelihood.negbin.match.prior.cohort-q2.negbin.match.prior.cohort
log.l.tilda.match.prior.cohort<-likelihood.bridge.match.prior.cohort-q2.bridge.match.prior.cohort
 
log.l.tilda.match.prior.cohort<-log.l.tilda.match.prior.cohort+23000
log.l.match.prior.cohort<-log.l.match.prior.cohort+23000
l.match.prior.cohort<-exp(log.l.match.prior.cohort)
l.tilda.match.prior.cohort<-exp(log.l.tilda.match.prior.cohort)

nc.negbin.lca.match.prior.cohort<-bridge(initial=100,m=100,sample1=theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif,sample2=full.sample.bridge.negbin.lca.match.prior.cohort,n1=20000,n2=20000,l=l.match.prior.cohort,l.tilda=l.tilda.match.prior.cohort)  
log(nc.negbin.lca.match.prior.cohort)-23000  #-22633.55 (n2=n1=20000,corrected and uniform prior for sigma.cohort)

#############
##splitting
#############
 
likelihood.negbin.match.prior.cohort.split<-likelihood.negbin.match.prior.cohort[10001:20000]

mean.negbin.vec.match.prior.cohort.split<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,-c(1,43,243,314,383,385,388,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,391])),2,mean)
covariance.negbin.mat.match.prior.cohort.split<-cov(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,-c(1,43,243,314,383,385,388,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,391])))
mean.rho.negbin.match.prior.cohort.split<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,388])
variance.rho.negbin.match.prior.cohort.split<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,388])
	
chol.cov.negbin.match.prior.cohort.split<-chol(covariance.negbin.mat.match.prior.cohort.split)
inverse.t.chol.cov.negbin.match.prior.cohort.split<-solve(t(chol.cov.negbin.match.prior.cohort.split))

M<-matrix(rep(mean.negbin.vec.match.prior.cohort.split,20000),nrow=384,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(384*20000),nrow=384,ncol=20000)
sample.bridge.negbin.match.prior.cohort.split<-M+t(chol.cov.negbin.match.prior.cohort.split)%*%Z
sample.bridge.negbin.match.prior.cohort.split<-t(sample.bridge.negbin.match.prior.cohort.split)
gc()
sample.rho.bridge.negbin.match.prior.cohort.split<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.negbin.match.prior.cohort.split,sd=sqrt(variance.rho.negbin.match.prior.cohort.split))
full.sample.bridge.negbin.match.prior.cohort.split<-cbind(-apply(sample.bridge.negbin.match.prior.cohort.split[,1:41],1,sum),sample.bridge.negbin.match.prior.cohort.split[,1:41],1-apply(sample.bridge.negbin.match.prior.cohort.split[,42:140],1,sum),sample.bridge.negbin.match.prior.cohort.split[,42:240],t(apply(sample.bridge.negbin.match.prior.cohort.split[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.negbin.match.prior.cohort.split[,379],rep(log(0.005),20000),sample.bridge.negbin.match.prior.cohort.split[,380:381],sample.rho.bridge.negbin.match.prior.cohort.split,sample.bridge.negbin.match.prior.cohort.split[,382:383],exp(sample.bridge.negbin.match.prior.cohort.split[,384]))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior.cohort.split);rm(sample.bridge.negbin.match.prior.cohort.split);gc()
like.prior.negbin.lca.match.prior.cohort(full.sample.bridge.negbin.match.prior.cohort.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.match.prior.cohort.split<-apply(full.sample.bridge.negbin.match.prior.cohort.split,1,like.prior.negbin.lca.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
 
log.det.Jacobian.negbin.match.prior.cohort.split<-determinant(inverse.t.chol.cov.negbin.match.prior.cohort.split,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.cohort.2(x=c(full.sample.bridge.negbin.match.prior.cohort.split[1000,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.split[1000,391])),mean.vec=mean.negbin.vec.match.prior.cohort.split,rij=inverse.t.chol.cov.negbin.match.prior.cohort.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.split,mean.rho=mean.rho.negbin.match.prior.cohort.split,variance.rho=variance.rho.negbin.match.prior.cohort.split)
dmvnorm(c(full.sample.bridge.negbin.match.prior.cohort.split[1000,-c(1,43,243,314,383,385,388,391)],log(full.sample.bridge.negbin.match.prior.cohort.split[1000,391])),mean=mean.negbin.vec.match.prior.cohort.split,sigma=covariance.negbin.mat.match.prior.cohort.split,log=TRUE)+log(dtruncnorm(full.sample.bridge.negbin.match.prior.cohort.split[1000,388],a=-1,b=1,mean=mean.rho.negbin.match.prior.cohort.split,sd=sqrt(variance.rho.negbin.match.prior.cohort.split)))

q2.negbin.match.prior.cohort.split<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,-c(1,43,243,314,383,385,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,391])),1,transformation.dmvnorm.match.prior.cohort.2,mean.vec=mean.negbin.vec.match.prior.cohort.split,rij=inverse.t.chol.cov.negbin.match.prior.cohort.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.split,mean.rho=mean.rho.negbin.match.prior.cohort.split,variance.rho=variance.rho.negbin.match.prior.cohort.split)
q2.bridge.match.prior.cohort.split<-apply(cbind(full.sample.bridge.negbin.match.prior.cohort.split[,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.split[,391])),1,transformation.dmvnorm.match.prior.cohort.2,mean.vec=mean.negbin.vec.match.prior.cohort.split,rij=inverse.t.chol.cov.negbin.match.prior.cohort.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.split,mean.rho=mean.rho.negbin.match.prior.cohort.split,variance.rho=variance.rho.negbin.match.prior.cohort.split)
 
log.l.match.prior.cohort.split<-likelihood.negbin.match.prior.cohort.split-q2.negbin.match.prior.cohort.split
log.l.tilda.match.prior.cohort.split<-likelihood.bridge.match.prior.cohort.split-q2.bridge.match.prior.cohort.split
 
log.l.tilda.match.prior.cohort.split<-log.l.tilda.match.prior.cohort.split+23000
log.l.match.prior.cohort.split<-log.l.match.prior.cohort.split+23000
l.match.prior.cohort.split<-exp(log.l.match.prior.cohort.split)
l.tilda.match.prior.cohort.split<-exp(log.l.tilda.match.prior.cohort.split)

nc.negbin.lca.match.prior.cohort.split<-bridge(initial=100,m=100,sample1=theta.AR1.over.negbin.int.y0.normal.match.prior.cohort.unif[10001:20000,],sample2=full.sample.bridge.negbin.lca.match.prior.cohort.split,n1=10000,n2=20000,l=l.match.prior.cohort.split,l.tilda=l.tilda.match.prior.cohort.split)  
log(nc.negbin.lca.match.prior.cohort.split)-23000  #-22629.38 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)


#############
##cross-splitting
#############

likelihood.negbin.match.prior.cohort.split.2<-likelihood.negbin.match.prior.cohort[1:10000]

mean.negbin.vec.match.prior.cohort.split.2<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,-c(1,43,243,314,383,385,388,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,391])),2,mean)
covariance.negbin.mat.match.prior.cohort.split.2<-cov(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,-c(1,43,243,314,383,385,388,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,391])))
mean.rho.negbin.match.prior.cohort.split.2<-mean(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,388])
variance.rho.negbin.match.prior.cohort.split.2<-var(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,388])
	
chol.cov.negbin.match.prior.cohort.split.2<-chol(covariance.negbin.mat.match.prior.cohort.split.2)
inverse.t.chol.cov.negbin.match.prior.cohort.split.2<-solve(t(chol.cov.negbin.match.prior.cohort.split.2))

M<-matrix(rep(mean.negbin.vec.match.prior.cohort.split.2,20000),nrow=384,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(384*20000),nrow=384,ncol=20000)
sample.bridge.negbin.match.prior.cohort.split.2<-M+t(chol.cov.negbin.match.prior.cohort.split.2)%*%Z
sample.bridge.negbin.match.prior.cohort.split.2<-t(sample.bridge.negbin.match.prior.cohort.split.2)
gc()
sample.rho.bridge.negbin.match.prior.cohort.split.2<-rtruncnorm(20000,a=-1,b=1,mean=mean.rho.negbin.match.prior.cohort.split.2,sd=sqrt(variance.rho.negbin.match.prior.cohort.split.2))
full.sample.bridge.negbin.match.prior.cohort.split.2<-cbind(-apply(sample.bridge.negbin.match.prior.cohort.split.2[,1:41],1,sum),sample.bridge.negbin.match.prior.cohort.split.2[,1:41],1-apply(sample.bridge.negbin.match.prior.cohort.split.2[,42:140],1,sum),sample.bridge.negbin.match.prior.cohort.split.2[,42:240],t(apply(sample.bridge.negbin.match.prior.cohort.split.2[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.negbin.match.prior.cohort.split.2[,379],rep(log(0.005),20000),sample.bridge.negbin.match.prior.cohort.split.2[,380:381],sample.rho.bridge.negbin.match.prior.cohort.split.2,sample.bridge.negbin.match.prior.cohort.split.2[,382:383],exp(sample.bridge.negbin.match.prior.cohort.split.2[,384]))
rm(M);rm(Z);rm(sample.rho.bridge.negbin.match.prior.cohort.split.2);rm(sample.bridge.negbin.match.prior.cohort.split.2);gc()
like.prior.negbin.lca.match.prior.cohort(full.sample.bridge.negbin.match.prior.cohort.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.match.prior.cohort.split.2<-apply(full.sample.bridge.negbin.match.prior.cohort.split.2,1,like.prior.negbin.lca.match.prior.cohort,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,a.rho=a.rho,b.rho=b.rho,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
 
log.det.Jacobian.negbin.match.prior.cohort.split.2<-determinant(inverse.t.chol.cov.negbin.match.prior.cohort.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.cohort.2(x=c(full.sample.bridge.negbin.match.prior.cohort.split.2[1000,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.split.2[1000,391])),mean.vec=mean.negbin.vec.match.prior.cohort.split.2,rij=inverse.t.chol.cov.negbin.match.prior.cohort.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.split.2,mean.rho=mean.rho.negbin.match.prior.cohort.split.2,variance.rho=variance.rho.negbin.match.prior.cohort.split.2)
dmvnorm(c(full.sample.bridge.negbin.match.prior.cohort.split.2[1000,-c(1,43,243,314,383,385,388,391)],log(full.sample.bridge.negbin.match.prior.cohort.split.2[1000,391])),mean=mean.negbin.vec.match.prior.cohort.split.2,sigma=covariance.negbin.mat.match.prior.cohort.split.2,log=TRUE)+log(dtruncnorm(full.sample.bridge.negbin.match.prior.cohort.split.2[1000,388],a=-1,b=1,mean=mean.rho.negbin.match.prior.cohort.split.2,sd=sqrt(variance.rho.negbin.match.prior.cohort.split.2)))

q2.negbin.match.prior.cohort.split.2<-apply(cbind(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,-c(1,43,243,314,383,385,391)],log(theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,391])),1,transformation.dmvnorm.match.prior.cohort.2,mean.vec=mean.negbin.vec.match.prior.cohort.split.2,rij=inverse.t.chol.cov.negbin.match.prior.cohort.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.split.2,mean.rho=mean.rho.negbin.match.prior.cohort.split.2,variance.rho=variance.rho.negbin.match.prior.cohort.split.2)
q2.bridge.match.prior.cohort.split.2<-apply(cbind(full.sample.bridge.negbin.match.prior.cohort.split.2[,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.split.2[,391])),1,transformation.dmvnorm.match.prior.cohort.2,mean.vec=mean.negbin.vec.match.prior.cohort.split.2,rij=inverse.t.chol.cov.negbin.match.prior.cohort.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.split.2,mean.rho=mean.rho.negbin.match.prior.cohort.split.2,variance.rho=variance.rho.negbin.match.prior.cohort.split.2)
 
log.l.match.prior.cohort.split.2<-likelihood.negbin.match.prior.cohort.split.2-q2.negbin.match.prior.cohort.split.2
log.l.tilda.match.prior.cohort.split.2<-likelihood.bridge.match.prior.cohort.split.2-q2.bridge.match.prior.cohort.split.2
 
log.l.tilda.match.prior.cohort.split.2<-log.l.tilda.match.prior.cohort.split.2+23000
log.l.match.prior.cohort.split.2<-log.l.match.prior.cohort.split.2+23000
l.match.prior.cohort.split.2<-exp(log.l.match.prior.cohort.split.2)
l.tilda.match.prior.cohort.split.2<-exp(log.l.tilda.match.prior.cohort.split.2)

nc.negbin.lca.match.prior.cohort.split.2<-bridge(initial=100,m=1000,sample1=theta.AR1.over.negbin.int.y0.normal.match.prior.cohort.unif[1:10000,],sample2=full.sample.bridge.negbin.lca.match.prior.cohort.split.2,n1=10000,n2=20000,l=l.match.prior.cohort.split.2,l.tilda=l.tilda.match.prior.cohort.split.2)  
log(nc.negbin.lca.match.prior.cohort.split.2)-23000  #-22629.02 (n2=2*n1=20000,corrected and uniform prior for sigma.cohort)

#so cross splitting estimate is 0.5*(-22629.38-22629.02)=-22629.20

#######################################
##NBLCC-RW sum(beta_x)=1,sum(k_t)=0
#######################################

like.prior.negbin.lca.match.prior.cohort.RW<-function(param,Dxt,Ext,A,T,t,lx,sigma2.l,gamma.0,sigma.mat.0,ak,bk,a.epsilon,b.epsilon,I=diag(rep(1,A-1)),K=matrix(1,nrow=A-1,ncol=A-1),sigma2.rho.cohort,J,J.cohort,I.cohort){#supply param=c(k,beta,alpha,log.sigma2.k,log.sigma2.beta,gamma1,gamma2,rho,epsilon)
k<-param[1:T]
beta<-param[(T+1):(A+T)]
alpha<-param[(A+T+1):(2*A+T)]
cohort<-param[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-exp(param[3*A+2*T])
sigma2.beta<-exp(param[3*A+2*T+1])
rho<-param[3*A+2*T+4]
gamma1<-param[3*A+2*T+2]
gamma2<-param[3*A+2*T+3]
gamma<-c(gamma1,gamma2)
ita.t<-gamma1+gamma2*t
rho.cohort<-param[3*A+2*T+5]
sigma2.cohort<-exp(param[3*A+2*T+6])
epsilon<-(param[3*A+2*T+7])

cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort[j-i+A]
}
}

R.cohort<-diag(rep(1,C))
for (i in 1:C){
for (j in 1:C){
if ((i-j)==1) R.cohort[i,j]<--(1+rho.cohort)
if ((i-j)==2) R.cohort[i,j]<-rho.cohort
}
}
R.cohort[2,1]<--1*sqrt(1-rho.cohort^2)
R.cohort[2,2]<-sqrt(1-rho.cohort^2)
R.cohort[1,1]<-1/100 
i.R.cohort<-forwardsolve(R.cohort,I.cohort)
i.Q.cohort<-i.R.cohort%*%t(i.R.cohort)
B.cohort<-J.cohort%*%i.Q.cohort%*%t(J.cohort)
ic<-(B.cohort[(4:C),(1:3)])%*%solve(B.cohort[(1:3),(1:3)])%*%(B.cohort[(1:3),(4:C)])
D.cohort<-B.cohort[(4:C),(4:C)]-ic
S.cohort<-sigma2.cohort*D.cohort

R<-diag(rep(1,T))
for (i in 1:T){
for (j in 1:T){
if ((i-j)==1) R[i,j]<--rho
}
}
Q<-t(R)%*%R
B<-J%*%solve(Q)%*%t(J)
D<-B[2:T,2:T]-(B[2:T,1]/B[1,1])%*%t(B[1,2:T])
p<-epsilon/(Ext*exp(matrix(rep(alpha,T),nrow=A,ncol=T,byrow=FALSE)+beta%*%t(k)+cohort.mat)+epsilon)	
X<-cbind(rep(1,T),t)


{result<-sum(dnbinom(Dxt,prob=p,size=epsilon,log=TRUE))+dmvnorm.tol(cohort[-c(1,72,A+T-1)],mean=rep(0,A+T-4),sigma=S.cohort,log=TRUE)+dmvnorm.tol(k[-1],mean=((X%*%gamma)[-1]-B[2:T,1]/B[1,1]*sum(X%*%gamma)),sigma=(sigma2.k*D),log=TRUE)+dmvnorm.tol(beta[-1],mean=rep(1/A,A-1),sigma=sigma2.beta*(I-1/A*K),log=TRUE)+
sum(dnorm(alpha,mean=lx,sd=sqrt(sigma2.l),log=TRUE))+dmvnorm(gamma,mean=gamma.0,sigma=sigma.mat.0,log=TRUE)+ak*log(bk)-lgamma(ak)-ak*log(sigma2.k)-bk/sigma2.k+dnorm(rho.cohort,mean=0,sd=sqrt(sigma2.rho.cohort),log=TRUE)+log(5)+log(sigma2.cohort)/2+a.epsilon*log(b.epsilon)-lgamma(a.epsilon)+a.epsilon*log(epsilon)-b.epsilon*epsilon}
if (sigma2.cohort>0.01){result<--Inf}
return(result)
}

Dxt<-round(Dxt)
Ext<-round(Ext)
t0<--21
t.interval<-42
t<-t0:(t0+t.interval-1)
A<-100
T<-42
lx<-rep(-5,A)
sigma2.l<-4
ak<-1
bk<-0.0001
gamma.0<-c(0,0)
sigma.mat.0<-matrix(c(2000,0,0,2),nrow=2)
a.epsilon<-25
b.epsilon<-0.05
J<-diag(rep(1,T))
J[1,]<-rep(1,T)
C<-A+T-1
J.cohort<-matrix(0,nrow=C,ncol=C)
J.cohort[1,]<-rep(1/sqrt(C),C)
J.cohort[2,]<-1:141
J.cohort[3,]<-(1:141)^2
J.cohort[2,]<-(J.cohort[2,]-mean(J.cohort[2,]))/(sqrt(C-1)*sd(J.cohort[2,]))
J.cohort[3,]<-(J.cohort[3,]-mean(J.cohort[3,]))/(sqrt(C-1)*sd(J.cohort[3,]))
for (i in 4:73) J.cohort[i,(i-2)]<-1
for (i in 74:C) J.cohort[i,(i-1)]<-1

I.cohort<-diag(rep(1,C))


like.prior.negbin.lca.match.prior.cohort.RW(param=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.negbin.match.prior.cohort.RW<-apply(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif,1,like.prior.negbin.lca.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)

mean.negbin.vec.match.prior.cohort.RW<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,-c(1,43,243,314,383,385,388,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391])),2,mean)
covariance.negbin.mat.match.prior.cohort.RW<-cov(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,-c(1,43,243,314,383,385,388,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391])))
	
chol.cov.negbin.match.prior.cohort.RW<-chol(covariance.negbin.mat.match.prior.cohort.RW)
inverse.t.chol.cov.negbin.match.prior.cohort.RW<-solve(t(chol.cov.negbin.match.prior.cohort.RW))

M<-matrix(rep(mean.negbin.vec.match.prior.cohort.RW,20000),nrow=384,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(384*20000),nrow=384,ncol=20000)
sample.bridge.negbin.match.prior.cohort.RW<-M+t(chol.cov.negbin.match.prior.cohort.RW)%*%Z
sample.bridge.negbin.match.prior.cohort.RW<-t(sample.bridge.negbin.match.prior.cohort.RW)
gc()
full.sample.bridge.negbin.match.prior.cohort.RW<-cbind(-apply(sample.bridge.negbin.match.prior.cohort.RW[,1:41],1,sum),sample.bridge.negbin.match.prior.cohort.RW[,1:41],1-apply(sample.bridge.negbin.match.prior.cohort.RW[,42:140],1,sum),sample.bridge.negbin.match.prior.cohort.RW[,42:240],t(apply(sample.bridge.negbin.match.prior.cohort.RW[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.negbin.match.prior.cohort.RW[,379],rep(log(0.005),20000),sample.bridge.negbin.match.prior.cohort.RW[,380:381],rep(1,20000),sample.bridge.negbin.match.prior.cohort.RW[,382:383],exp(sample.bridge.negbin.match.prior.cohort.RW[,384]))
rm(M);rm(Z);rm(sample.bridge.negbin.match.prior.cohort.RW);gc()
like.prior.negbin.lca.match.prior.cohort.RW(full.sample.bridge.negbin.match.prior.cohort.RW[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.match.prior.cohort.RW<-apply(full.sample.bridge.negbin.match.prior.cohort.RW,1,like.prior.negbin.lca.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)

log.det.Jacobian.negbin.match.prior.cohort.RW<-determinant(inverse.t.chol.cov.negbin.match.prior.cohort.RW,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.cohort.RW(x=c(full.sample.bridge.negbin.match.prior.cohort.RW[1000,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW[1000,391])),mean.vec=mean.negbin.vec.match.prior.cohort.RW,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW,mean.rho=mean.rho.negbin.match.prior.cohort.RW,variance.rho=variance.rho.negbin.match.prior.cohort.RW)
dmvnorm(c(full.sample.bridge.negbin.match.prior.cohort.RW[1000,-c(1,43,243,314,383,385,388,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW[1000,391])),mean=mean.negbin.vec.match.prior.cohort.RW,sigma=covariance.negbin.mat.match.prior.cohort.RW,log=TRUE)

q2.negbin.match.prior.cohort.RW<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,-c(1,43,243,314,383,385,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[,391])),1,transformation.dmvnorm.match.prior.cohort.RW,mean.vec=mean.negbin.vec.match.prior.cohort.RW,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW,mean.rho=mean.rho.negbin.match.prior.cohort.RW,variance.rho=variance.rho.negbin.match.prior.cohort.RW)
q2.bridge.match.prior.cohort.RW<-apply(cbind(full.sample.bridge.negbin.match.prior.cohort.RW[,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW[,391])),1,transformation.dmvnorm.match.prior.cohort.RW,mean.vec=mean.negbin.vec.match.prior.cohort.RW,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW,mean.rho=mean.rho.negbin.match.prior.cohort.RW,variance.rho=variance.rho.negbin.match.prior.cohort.RW)
 
log.l.match.prior.cohort.RW<-likelihood.negbin.match.prior.cohort.RW-q2.negbin.match.prior.cohort.RW
log.l.tilda.match.prior.cohort.RW<-likelihood.bridge.match.prior.cohort.RW-q2.bridge.match.prior.cohort.RW
 
log.l.tilda.match.prior.cohort.RW<-log.l.tilda.match.prior.cohort.RW+23000
log.l.match.prior.cohort.RW<-log.l.match.prior.cohort.RW+23000
l.match.prior.cohort.RW<-exp(log.l.match.prior.cohort.RW)
l.tilda.match.prior.cohort.RW<-exp(log.l.tilda.match.prior.cohort.RW)

nc.negbin.lca.match.prior.cohort.RW<-bridge(initial=100,m=100,sample1=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif,sample2=full.sample.bridge.negbin.lca.match.prior.cohort.RW,n1=20000,n2=20000,l=l.match.prior.cohort.RW,l.tilda=l.tilda.match.prior.cohort.RW)  
log(nc.negbin.lca.match.prior.cohort.RW)-23000 #-22637.74 (n2=n1=20000,corrected and uniform prior for sigma.cohort)

#################
##splitting
#################

likelihood.negbin.match.prior.cohort.RW.split<-likelihood.negbin.match.prior.cohort.RW[10001:20000]

mean.negbin.vec.match.prior.cohort.RW.split<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,-c(1,43,243,314,383,385,388,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,391])),2,mean)
covariance.negbin.mat.match.prior.cohort.RW.split<-cov(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,-c(1,43,243,314,383,385,388,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,391])))
	
chol.cov.negbin.match.prior.cohort.RW.split<-chol(covariance.negbin.mat.match.prior.cohort.RW.split)
inverse.t.chol.cov.negbin.match.prior.cohort.RW.split<-solve(t(chol.cov.negbin.match.prior.cohort.RW.split))

M<-matrix(rep(mean.negbin.vec.match.prior.cohort.RW.split,20000),nrow=384,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(384*20000),nrow=384,ncol=20000)
sample.bridge.negbin.match.prior.cohort.RW.split<-M+t(chol.cov.negbin.match.prior.cohort.RW.split)%*%Z
sample.bridge.negbin.match.prior.cohort.RW.split<-t(sample.bridge.negbin.match.prior.cohort.RW.split)
gc()
full.sample.bridge.negbin.match.prior.cohort.RW.split<-cbind(-apply(sample.bridge.negbin.match.prior.cohort.RW.split[,1:41],1,sum),sample.bridge.negbin.match.prior.cohort.RW.split[,1:41],1-apply(sample.bridge.negbin.match.prior.cohort.RW.split[,42:140],1,sum),sample.bridge.negbin.match.prior.cohort.RW.split[,42:240],t(apply(sample.bridge.negbin.match.prior.cohort.RW.split[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.negbin.match.prior.cohort.RW.split[,379],rep(log(0.005),20000),sample.bridge.negbin.match.prior.cohort.RW.split[,380:381],rep(1,20000),sample.bridge.negbin.match.prior.cohort.RW.split[,382:383],exp(sample.bridge.negbin.match.prior.cohort.RW.split[,384]))
rm(M);rm(Z);rm(sample.bridge.negbin.match.prior.cohort.RW.split);gc()
like.prior.negbin.lca.match.prior.cohort.RW(full.sample.bridge.negbin.match.prior.cohort.RW.split[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.match.prior.cohort.RW.split<-apply(full.sample.bridge.negbin.match.prior.cohort.RW.split,1,like.prior.negbin.lca.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
 
log.det.Jacobian.negbin.match.prior.cohort.RW.split<-determinant(inverse.t.chol.cov.negbin.match.prior.cohort.RW.split,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.cohort.RW(x=c(full.sample.bridge.negbin.match.prior.cohort.RW.split[1000,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW.split[1000,391])),mean.vec=mean.negbin.vec.match.prior.cohort.RW.split,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW.split,mean.rho=mean.rho.negbin.match.prior.cohort.RW.split,variance.rho=variance.rho.negbin.match.prior.cohort.RW.split)
dmvnorm(c(full.sample.bridge.negbin.match.prior.cohort.RW.split[1000,-c(1,43,243,314,383,385,388,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW.split[1000,391])),mean=mean.negbin.vec.match.prior.cohort.RW.split,sigma=covariance.negbin.mat.match.prior.cohort.RW.split,log=TRUE)

q2.negbin.match.prior.cohort.RW.split<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,-c(1,43,243,314,383,385,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,391])),1,transformation.dmvnorm.match.prior.cohort.RW,mean.vec=mean.negbin.vec.match.prior.cohort.RW.split,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW.split,mean.rho=mean.rho.negbin.match.prior.cohort.RW.split,variance.rho=variance.rho.negbin.match.prior.cohort.RW.split)
q2.bridge.match.prior.cohort.RW.split<-apply(cbind(full.sample.bridge.negbin.match.prior.cohort.RW.split[,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW.split[,391])),1,transformation.dmvnorm.match.prior.cohort.RW,mean.vec=mean.negbin.vec.match.prior.cohort.RW.split,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW.split,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW.split,mean.rho=mean.rho.negbin.match.prior.cohort.RW.split,variance.rho=variance.rho.negbin.match.prior.cohort.RW.split)
 
log.l.match.prior.cohort.RW.split<-likelihood.negbin.match.prior.cohort.RW.split-q2.negbin.match.prior.cohort.RW.split
log.l.tilda.match.prior.cohort.RW.split<-likelihood.bridge.match.prior.cohort.RW.split-q2.bridge.match.prior.cohort.RW.split
 
log.l.tilda.match.prior.cohort.RW.split<-log.l.tilda.match.prior.cohort.RW.split+23000
log.l.match.prior.cohort.RW.split<-log.l.match.prior.cohort.RW.split+23000
l.match.prior.cohort.RW.split<-exp(log.l.match.prior.cohort.RW.split)
l.tilda.match.prior.cohort.RW.split<-exp(log.l.tilda.match.prior.cohort.RW.split)

nc.negbin.lca.match.prior.cohort.RW.split<-bridge(initial=100,m=100,sample1=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,],sample2=full.sample.bridge.negbin.lca.match.prior.cohort.RW.split,n1=10000,n2=20000,l=l.match.prior.cohort.RW.split,l.tilda=l.tilda.match.prior.cohort.RW.split)  
log(nc.negbin.lca.match.prior.cohort.RW.split)-23000 #-22634.78 (n2=n1=20000,corrected and uniform prior for sigma.cohort)##cross-splitting

##cross-splitting

likelihood.negbin.match.prior.cohort.RW.split.2<-likelihood.negbin.match.prior.cohort.RW[1:10000]

mean.negbin.vec.match.prior.cohort.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,-c(1,43,243,314,383,385,388,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,391])),2,mean)
covariance.negbin.mat.match.prior.cohort.RW.split.2<-cov(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,-c(1,43,243,314,383,385,388,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[10001:20000,391])))
	
chol.cov.negbin.match.prior.cohort.RW.split.2<-chol(covariance.negbin.mat.match.prior.cohort.RW.split.2)
inverse.t.chol.cov.negbin.match.prior.cohort.RW.split.2<-solve(t(chol.cov.negbin.match.prior.cohort.RW.split.2))

M<-matrix(rep(mean.negbin.vec.match.prior.cohort.RW.split.2,20000),nrow=384,ncol=20000,byrow=FALSE)
Z<-matrix(rnorm(384*20000),nrow=384,ncol=20000)
sample.bridge.negbin.match.prior.cohort.RW.split.2<-M+t(chol.cov.negbin.match.prior.cohort.RW.split.2)%*%Z
sample.bridge.negbin.match.prior.cohort.RW.split.2<-t(sample.bridge.negbin.match.prior.cohort.RW.split.2)
gc()
full.sample.bridge.negbin.match.prior.cohort.RW.split.2<-cbind(-apply(sample.bridge.negbin.match.prior.cohort.RW.split.2[,1:41],1,sum),sample.bridge.negbin.match.prior.cohort.RW.split.2[,1:41],1-apply(sample.bridge.negbin.match.prior.cohort.RW.split.2[,42:140],1,sum),sample.bridge.negbin.match.prior.cohort.RW.split.2[,42:240],t(apply(sample.bridge.negbin.match.prior.cohort.RW.split.2[,241:378],1,find.cohort,A=100,T=42)),sample.bridge.negbin.match.prior.cohort.RW.split.2[,379],rep(log(0.005),20000),sample.bridge.negbin.match.prior.cohort.RW.split.2[,380:381],rep(1,20000),sample.bridge.negbin.match.prior.cohort.RW.split.2[,382:383],exp(sample.bridge.negbin.match.prior.cohort.RW.split.2[,384]))
rm(M);rm(Z);rm(sample.bridge.negbin.match.prior.cohort.RW.split.2);gc()
like.prior.negbin.lca.match.prior.cohort.RW(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[100,],Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
likelihood.bridge.match.prior.cohort.RW.split.2<-apply(full.sample.bridge.negbin.match.prior.cohort.RW.split.2,1,like.prior.negbin.lca.match.prior.cohort.RW,Dxt=round(Dxt),Ext=round(Ext),A=A,T=T,t=t,lx=lx,sigma2.l=sigma2.l,gamma.0=gamma.0,sigma.mat.0=sigma.mat.0,ak=ak,bk=bk,a.epsilon=a.epsilon,b.epsilon=b.epsilon,J=J,sigma2.rho.cohort=1,J.cohort=J.cohort,I.cohort=I.cohort)
 
log.det.Jacobian.negbin.match.prior.cohort.RW.split.2<-determinant(inverse.t.chol.cov.negbin.match.prior.cohort.RW.split.2,logarithm=TRUE)$modulus
transformation.dmvnorm.match.prior.cohort.RW(x=c(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[1000,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[1000,391])),mean.vec=mean.negbin.vec.match.prior.cohort.RW.split.2,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW.split.2,mean.rho=mean.rho.negbin.match.prior.cohort.RW.split.2,variance.rho=variance.rho.negbin.match.prior.cohort.RW.split.2)
dmvnorm(c(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[1000,-c(1,43,243,314,383,385,388,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[1000,391])),mean=mean.negbin.vec.match.prior.cohort.RW.split.2,sigma=covariance.negbin.mat.match.prior.cohort.RW.split.2,log=TRUE)

q2.negbin.match.prior.cohort.RW.split.2<-apply(cbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,-c(1,43,243,314,383,385,391)],log(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,391])),1,transformation.dmvnorm.match.prior.cohort.RW,mean.vec=mean.negbin.vec.match.prior.cohort.RW.split.2,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW.split.2,mean.rho=mean.rho.negbin.match.prior.cohort.RW.split.2,variance.rho=variance.rho.negbin.match.prior.cohort.RW.split.2)
q2.bridge.match.prior.cohort.RW.split.2<-apply(cbind(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[,-c(1,43,243,314,383,385,391)],log(full.sample.bridge.negbin.match.prior.cohort.RW.split.2[,391])),1,transformation.dmvnorm.match.prior.cohort.RW,mean.vec=mean.negbin.vec.match.prior.cohort.RW.split.2,rij=inverse.t.chol.cov.negbin.match.prior.cohort.RW.split.2,log.det.Jacobian=log.det.Jacobian.negbin.match.prior.cohort.RW.split.2,mean.rho=mean.rho.negbin.match.prior.cohort.RW.split.2,variance.rho=variance.rho.negbin.match.prior.cohort.RW.split.2)
 
log.l.match.prior.cohort.RW.split.2<-likelihood.negbin.match.prior.cohort.RW.split.2-q2.negbin.match.prior.cohort.RW.split.2
log.l.tilda.match.prior.cohort.RW.split.2<-likelihood.bridge.match.prior.cohort.RW.split.2-q2.bridge.match.prior.cohort.RW.split.2
 
log.l.tilda.match.prior.cohort.RW.split.2<-log.l.tilda.match.prior.cohort.RW.split.2+23000
log.l.match.prior.cohort.RW.split.2<-log.l.match.prior.cohort.RW.split.2+23000
l.match.prior.cohort.RW.split.2<-exp(log.l.match.prior.cohort.RW.split.2)
l.tilda.match.prior.cohort.RW.split.2<-exp(log.l.tilda.match.prior.cohort.RW.split.2)

nc.negbin.lca.match.prior.cohort.RW.split.2<-bridge(initial=100,m=100,sample1=theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:10000,],sample2=full.sample.bridge.negbin.lca.match.prior.cohort.RW.split.2,n1=10000,n2=20000,l=l.match.prior.cohort.RW.split.2,l.tilda=l.tilda.match.prior.cohort.RW.split.2)  
log(nc.negbin.lca.match.prior.cohort.RW.split.2)-23000 #-22634.77 (n2=n1=20000,corrected and uniform prior for sigma.cohort)##cross-splitting

#so cross-splitting estimate is 0.5*(-22634.78-22634.77)=-22634.78

################################
##Model-averaged APCI & LCC cohort models
################################

post.prob.RW.loglinear.cohort<-1-exp(-22414.12+22610)/(exp(-22416.81+22610)+exp(-22414.12+22610)) #0.06356602 (corrected and and uniform prior for sigma.cohort)
average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort<-rbind(theta.RW.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:round(post.prob.RW.loglinear.cohort*20000),],theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:round((1-post.prob.RW.loglinear.cohort)*20000),])

post.prob.RW.LCC<-1-exp(-22629.2+22610)/(exp(-22629.2+22610)+exp(-22634.78+22610)) #0.003758387 (corrected and and uniform prior for sigma.cohort)
average.theta.AR1.over.negbin.int.LCC<-rbind(theta.RW.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:round(post.prob.RW.LCC*20000),],theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior.cohort.unif[1:round((1-post.prob.RW.LCC)*20000),])

alpha.loglinear.matchprior.cohort.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,143:242]
alpha.loglinear.matchprior.cohort.average.percentile<-apply(alpha.loglinear.matchprior.cohort.average,2,percentile.fn)
plot(alpha.loglinear.matchprior.cohort.average.percentile[2,],type="l",ylab="",xlab="Age",main=expression(alpha[x]),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(alpha.loglinear.matchprior.cohort.average.percentile[1,],lty=2)
lines(alpha.loglinear.matchprior.cohort.average.percentile[3,],lty=2)
lines(alpha.loglinear.matchprior.average.percentile[2,],col=2)
lines(alpha.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines(alpha.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
lines(alpha.loglinear,col="blue")
legend("bottomright",c("NBAPCI Median","NBAPI Median","Classical APCI","NBAPCI 95% Intervals","NBAPI 95% Intervals"),lty=c(1,1,1,2,2),col=c(1,2,"blue",1,2))

beta.loglinear.matchprior.cohort.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,43:142]
beta.loglinear.matchprior.cohort.average.percentile<-apply(beta.loglinear.matchprior.cohort.average,2,percentile.fn)
plot(beta.loglinear.matchprior.cohort.average.percentile[2,],ylim=c(-0.045,0),type="l",ylab="",xlab="Age",main=expression(beta[x]),cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(beta.loglinear.matchprior.cohort.average.percentile[1,],lty=2)
lines(beta.loglinear.matchprior.cohort.average.percentile[3,],lty=2)
lines(beta.loglinear.matchprior.average.percentile[2,],col=2)
lines(beta.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines(beta.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
lines(beta.loglinear,col="blue")
legend("bottomright",c("NBAPCI Median","NBAPI Median","Classical APCI","NBAPCI 95% Intervals","NBAPI 95% Intervals"),lty=c(1,1,1,2,2),col=c(1,2,"blue",1,2))

k.loglinear.matchprior.cohort.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,1:42]
k.loglinear.matchprior.cohort.average.percentile<-apply(k.loglinear.matchprior.cohort.average,2,percentile.fn)
k.loglinear.forecast.matchprior.cohort.average.percentile<-apply(k.forecast.ng.loglinear.cohort,1,percentile.fn)
plot((-41):0,k.loglinear.matchprior.cohort.average.percentile[2,],xaxt="n",type="l",xlim=c(-41,13),ylim=c(-0.15,0.1),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Year",ylab="",main=expression(kappa[t]))
axis(1,at=c(seq(-41,26,by=10)),label=c(seq(1961,2028,by=10)),cex.axis=1.15)
lines((-41):0,k.loglinear.matchprior.cohort.average.percentile[1,],lty=2)
lines((-41):0,k.loglinear.matchprior.cohort.average.percentile[3,],lty=2)
lines(1:14,k.loglinear.forecast.matchprior.cohort.average.percentile[2,1:14])
lines(1:14,k.loglinear.forecast.matchprior.cohort.average.percentile[1,1:14],lty=2)
lines(1:14,k.loglinear.forecast.matchprior.cohort.average.percentile[3,1:14],lty=2)

lines((-41):0,k.loglinear.matchprior.average.percentile[2,],col=2)
lines((-41):0,k.loglinear.matchprior.average.percentile[1,],lty=2,col=2)
lines((-41):0,k.loglinear.matchprior.average.percentile[3,],lty=2,col=2)
lines(1:14,k.loglinear.forecast.matchprior.average.percentile[2,1:14],col=2)
lines(1:14,k.loglinear.forecast.matchprior.average.percentile[1,1:14],lty=2,col=2)
lines(1:14,k.loglinear.forecast.matchprior.average.percentile[3,1:14],lty=2,col=2)

kappa.arima.100<-arima(kappa.loglinear,order=c(1,0,0),include.mean=F)
project.kappa.arima.100<-forecast(kappa.arima.100,h=26,level=95,bootstrap=FALSE,npaths=100)
project.kappa.median<-project.kappa.arima.100$mean
project.kappa.lower<-project.kappa.arima.100$lower
project.kappa.upper<-project.kappa.arima.100$upper
lines((-41):0,kappa.loglinear,col="blue")
lines(1:14,project.kappa.median[1:14],col="blue")
lines(1:14,project.kappa.lower[1:14],col="blue",lty=2)
lines(1:14,project.kappa.upper[1:14],col="blue",lty=2)

legend("bottomleft",c("NBAPCI Median","NBAPI Median","Classical APCI","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),lty=c(1,1,1,2,2,2),col=c(1,2,"blue",1,2,"blue"))

cohort.loglinear.matchprior.cohort.average<-average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,243:383]
cohort.loglinear.matchprior.cohort.average.percentile<-apply(cohort.loglinear.matchprior.cohort.average,2,percentile.fn)
cohort.loglinear.forecast.matchprior.cohort.average.percentile<-apply(cohort.forecast.ng.loglinear.cohort,1,percentile.fn)
plot((-140):0,cohort.loglinear.matchprior.cohort.average.percentile[2,],xaxt="n",type="l",xlim=c(-140,12),ylim=c(-0.115,0.245),cex.axis=1.15,cex.lab=1.2,cex.main=1.5,xlab="Cohort",ylab="",main=expression(gamma[c]))
axis(1,at=c(seq(-140,14,by=20),14),label=c(seq(1861,2016,by=20),2016),cex.axis=1.15)
lines((-140):0,cohort.loglinear.matchprior.cohort.average.percentile[1,],lty=2)
lines((-140):0,cohort.loglinear.matchprior.cohort.average.percentile[3,],lty=2)
lines(1:14,cohort.loglinear.forecast.matchprior.cohort.average.percentile[2,1:14])
lines(1:14,cohort.loglinear.forecast.matchprior.cohort.average.percentile[1,1:14],lty=2)
lines(1:14,cohort.loglinear.forecast.matchprior.cohort.average.percentile[3,1:14],lty=2)

cohort.arima.110<-arima(cohort.loglinear,order=c(1,1,0),include.mean=FALSE)
project.cohort.arima.110<-forecast(cohort.arima.110,h=26,level=95,bootstrap=FALSE,npaths=1)
project.cohort.median<-project.cohort.arima.110$mean
project.cohort.lower<-project.cohort.arima.110$lower
project.cohort.upper<-project.cohort.arima.110$upper
lines((-140):0,cohort.loglinear,col="blue")
lines(1:14,project.cohort.median[1:14],lty=1,col="blue")
lines(1:14,project.cohort.lower[1:14],lty=2,col="blue")
lines(1:14,project.cohort.upper[1:14],lty=2,col="blue")
project.cohort.loglinear.withP.percentile<-apply(project.miuxt.loglinear.withP[2627:2652,],1,percentile.fn)
lines(1:14,project.cohort.loglinear.withP.percentile[2,],col="purple")
lines(1:14,project.cohort.loglinear.withP.percentile[1,],col="purple",lty=2)
lines(1:14,project.cohort.loglinear.withP.percentile[3,],col="purple",lty=2)

legend("topleft",c("NBAPCI Median","Classical APCI","NBAPCI 95% Intervals","Classical APCI 95% Intervals"),lty=c(1,1,2,2),col=c(1,"blue",1,"blue"))

par(mfrow=c(3,2))
plot(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,384]),n=50000),xlab="",ylab="Density",ylim=c(0,8400),main=expression(sigma[k]^2),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243]),n=50000),col=2)
plot(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,385]),n=50000),xlab="",ylab="Density",main=expression(lambda),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244]),n=50000),col=2)
dens.rho.loglinear.AR1.cohort<-density(theta.AR1.over.negbin.int.y0.new.notrunc.cohort.group.marg.matchprior.100.001[1:18440,387],n=50000)
plot(dens.rho.loglinear.AR1.cohort$x,(1-0.07798824)*dens.rho.loglinear.AR1.cohort$y,xlim=c(0,1.1),ylim=c(0,2.5),xaxt="n",xlab="",ylab="Density",main=expression(rho),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
dens.rho.loglinear.AR1<-density(theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[1:4110,245],n=50000)
lines(dens.rho.loglinear.AR1$x,0.4109596*dens.rho.loglinear.AR1$y,col=2,main=expression(rho),ylab="Density",xlab="",xaxt="n",ylim=c(0,1.2),xlim=c(0,1.1),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
axis(1,at=c(0,0.25,0.5,0.75,1.055),label=c(0,0.25,0.5,0.75,1))
lines(c(1.055,1.055),c(0,0.5890404),col=2)
lines(c(1.055,1.055),c(0,0.06008665),col=1)
plot(density(1/average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,389],n=50000),xlim=c(0.00026,0.0016),xlab="",ylab="Density",main=expression(1/phi),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
lines(density(1/average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],n=50000),col=2)
plot(density(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,386]),n=50000),xlab="",ylab="Density",main=expression(sigma[gamma]^2),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)
plot(density(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,388],n=50000),xlab="",ylab="Density",main=expression(rho[gamma]),type="l",cex.axis=1.15,cex.lab=1.2,cex.main=1.5)

########################
##Projection/forecasting
#######################

##NBAPCI

NB.loglinear.cohort.projection<-function(posterior.param,h,A,T,C,t0){
t<-t0:(t0+T-1)
alpha<-posterior.param[(A+T+1):(2*A+T)]
beta<-posterior.param[(T+1):(A+T)]
kappa<-posterior.param[1:T]
cohort<-posterior.param[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-(exp(posterior.param[3*A+2*T]))
lambda<-(exp(posterior.param[3*A+2*T+1]))
sigma2.cohort<-exp(posterior.param[3*A+2*T+2])
rho<-posterior.param[3*A+2*T+3]
rho.cohort<-posterior.param[3*A+2*T+4]
epsilon<-posterior.param[3*A+2*T+5]
t.new<-(t0+T):(t0+T+h-1)
kappa.forecast<-rho*kappa[T]+rnorm(1,0,sqrt(2*sigma2.k))
for (i in 2:h){
kappa.forecast[i]<-rho*kappa.forecast[i-1]+rnorm(1,0,sqrt(2*sigma2.k))
}
cohort.forecast<-cohort[C]+rho.cohort*(cohort[C]-cohort[C-1])+rnorm(1,0,sqrt(sigma2.cohort))
cohort.forecast[2]<-cohort.forecast[1]+rho.cohort*(cohort.forecast[1]-cohort[C])+rnorm(1,0,sqrt(sigma2.cohort))
for (j in 3:h){
cohort.forecast[j]<-cohort.forecast[j-1]+rho.cohort*(cohort.forecast[j-1]-cohort.forecast[j-2])+rnorm(1,0,sqrt(sigma2.cohort))
}
cohort.forecast.mat<-matrix(0,nrow=A,ncol=h)
for (i in 1:A){
for (j in 1:h){
if ((j-i)<0) cohort.forecast.mat[i,j]<-cohort[(j-i)+A+T]
if ((j-i)>=0) cohort.forecast.mat[i,j]<-cohort.forecast[(j-i)+1]
}}
logmiuxt.forecast<-matrix(rep(alpha,h),nrow=A,ncol=h,byrow=FALSE)+beta%*%t(t.new)+matrix(rep(kappa.forecast,A),nrow=A,ncol=h,byrow=TRUE)+cohort.forecast.mat+matrix(log(rgamma(A*h,epsilon,epsilon)),nrow=A,ncol=h)
return(rbind(logmiuxt.forecast,kappa.forecast,cohort.forecast))
}

full.projected.ng.loglinear.cohort<-apply(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort,1,NB.loglinear.cohort.projection,h=26,A=100,T=42,C=141,t0=-21)
k.forecast.ng.loglinear.cohort<-full.projected.ng.loglinear.cohort[(seq(from=101,to=2652,by=102)),]
cohort.forecast.ng.loglinear.cohort<-full.projected.ng.loglinear.cohort[(seq(from=102,to=2652,by=102)),]
full.projected.ng.loglinear.cohort<-full.projected.ng.loglinear.cohort[-c(seq(from=101,to=2652,by=102),seq(from=102,to=2652,by=102)),];gc()

##Fitted and projected crude death rates

generate.Dxt.ng.loglinear.cohort.fn<-function(x,Ext.valid,A,h,t0){
t<-t0:(t0+h-1)
a<-x[(A+h+1):(2*A+h)]
b<-x[(h+1):(A+h)]
k<-x[1:h]
cohort<-x[(2*A+h+1):(3*A+2*h-1)]
cohort.mat<-matrix(0,nrow=A,ncol=h)
for (i in 1:A){
for (j in 1:h){
cohort.mat[i,j]<-cohort[j-i+A]
}}
e<-x[3*A+2*h+5]
Ext.valid.vec<-as.vector(Ext.valid)
logmiuxt.vec<-as.vector(matrix(rep(a,h),nrow=A,ncol=h,byrow=FALSE)+b%*%t(t)+matrix(rep(k,A),nrow=A,ncol=h,byrow=TRUE)+cohort.mat)
rnbinom(A*h,size=e,prob=(e/(e+Ext.valid.vec*exp(logmiuxt.vec))))
}

generate.Dxt.ng.loglinear.cohort.fn(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[1,],Ext.valid=Ext,A=100,h=42,t0=-21)
fitted.Dxt.ng.loglinear.cohort.average<-apply(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort,1,generate.Dxt.ng.loglinear.cohort.fn,Ext.valid=Ext,A=100,h=42,t0=-21)
EWexpo.female.mat.ex.mat<-matrix(rep(as.vector(Ext),20000),nrow=length(as.vector(Ext)),ncol=20000,byrow=FALSE)
fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover<-fitted.Dxt.ng.loglinear.cohort.average/EWexpo.female.mat.ex.mat


project.Dxt.ng.loglinear.cohort.fn<-function(x,Ext.valid,A,h){
e<-x[A*h+1]
miuxt.vec<-x[-(A*h+1)]
Ext.valid.vec<-as.vector(Ext.valid)
rnbinom(A*h,size=e,prob=(e/(e+Ext.valid.vec*miuxt.vec)))
}

projected.Dxt.11yrs.ng.loglinear.cohort<-apply(rbind(exp(full.projected.ng.loglinear.cohort[1:1400,]),average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior.cohort[,389]),2,project.Dxt.ng.loglinear.cohort.fn,Ext.valid=EWexpo.female.mat.ex.validation,A=100,h=14)
EWexpo.female.mat.ex.validation.mat<-matrix(rep(as.vector(EWexpo.female.mat.ex.validation),ncol(projected.Dxt.11yrs.ng.loglinear.cohort)),nrow=length(as.vector(EWexpo.female.mat.ex.validation)),ncol=ncol(projected.Dxt.11yrs.ng.loglinear.cohort),byrow=FALSE)
projected.miuxt.11yrs.ng.loglinear.cohort.withover<-projected.Dxt.11yrs.ng.loglinear.cohort/EWexpo.female.mat.ex.validation.mat 

#projection for classical APCI
cohort.mat<-matrix(0,nrow=A,ncol=T)
for (i in 1:A){
for (j in 1:T){
cohort.mat[i,j]<-cohort.loglinear[(j-i)+A]
}}
fitted.miuxt.loglinear<-exp(matrix(rep(alpha.loglinear,T),nrow=A,ncol=T,byrow=FALSE)+beta.loglinear%*%t(t)+matrix(rep(kappa.loglinear,A),nrow=A,ncol=T,byrow=TRUE)+cohort.mat)
rpois(n=4200,lambda=as.vector(Ext*fitted.miuxt.loglinear))
fitted.mean.loglinear.cohort<-matrix(rep(as.vector(Ext*fitted.miuxt.loglinear),10000),ncol=4200,byrow=TRUE)
fitted.Dxt.loglinear.cohort<-apply(fitted.mean.loglinear.cohort,1,rpois,n=4200)
rm(fitted.mean.loglinear.cohort);gc()
EWexpo.female.mat.ex.mat<-matrix(rep(as.vector(Ext),10000),nrow=length(as.vector(Ext)),ncol=10000,byrow=FALSE)
fitted.crude.miuxt.loglinear.cohort<-fitted.Dxt.loglinear.cohort/EWexpo.female.mat.ex.mat

poisson.loglinear.cohort.projection.miuxt<-function(theta,h,A,T,C,t0,exposure){
t<-t0:(t0+T-1)
alpha<-theta[(A+T+1):(2*A+T)]
beta<-theta[(T+1):(A+T)]
kappa<-theta[1:T]
cohort<-theta[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-((theta[3*A+2*T]))
sigma2.cohort<-(theta[3*A+2*T+1])
rho<-theta[3*A+2*T+2]
rho.cohort<-theta[3*A+2*T+3]
t.new<-(t0+T):(t0+T+h-1)
kappa.forecast<-rho*kappa[T]+rnorm(1,0,sqrt(sigma2.k))
for (i in 2:h){
kappa.forecast[i]<-rho*kappa.forecast[i-1]+rnorm(1,0,sqrt(sigma2.k))
}
cohort.forecast<-cohort[C]+rho.cohort*(cohort[C]-cohort[C-1])+rnorm(1,0,sqrt(sigma2.cohort))
cohort.forecast[2]<-cohort.forecast[1]+rho.cohort*(cohort.forecast[1]-cohort[C])+rnorm(1,0,sqrt(sigma2.cohort))
for (j in 3:h){
cohort.forecast[j]<-cohort.forecast[j-1]+rho.cohort*(cohort.forecast[j-1]-cohort.forecast[j-2])+rnorm(1,0,sqrt(sigma2.cohort))
}
cohort.forecast.mat<-matrix(0,nrow=A,ncol=h)
for (i in 1:A){
for (j in 1:h){
if ((j-i)<0) cohort.forecast.mat[i,j]<-cohort[(j-i)+A+T]
if ((j-i)>=0) cohort.forecast.mat[i,j]<-cohort.forecast[(j-i)+1]
}}
logmiuxt.forecast<-matrix(rep(alpha,h),nrow=A,ncol=h,byrow=FALSE)+beta%*%t(t.new)+matrix(rep(kappa.forecast,A),nrow=A,ncol=h,byrow=TRUE)+cohort.forecast.mat
miuxt.vec.forecast<-rpois(A*h,as.vector(exposure)*as.vector(exp(logmiuxt.forecast)))/as.vector(exposure)
return(c(miuxt.vec.forecast,kappa.forecast,cohort.forecast))
}

poisson.loglinear.cohort.projection.miuxt(theta=c(kappa.loglinear,beta.loglinear,alpha.loglinear,cohort.loglinear,kappa.arima.100$sigma2,cohort.arima.110$sigma2,kappa.arima.100$coef,cohort.arima.110$coef),h=14,A=100,T=42,C=141,t0=-21,exposure=EWexpo.female.mat.ex.validation)
m=20000
theta.rep<-matrix(rep(c(kappa.loglinear,beta.loglinear,alpha.loglinear,cohort.loglinear,kappa.arima.100$sigma2,cohort.arima.110$sigma2,kappa.arima.100$coef,cohort.arima.110$coef),m),nrow=m,byrow=TRUE)
project.miuxt.loglinear.withP<-apply(theta.rep,1,poisson.loglinear.cohort.projection.miuxt,h=14,A=100,T=42,C=141,t0=-21,exposure=EWexpo.female.mat.ex.validation)
project.miuxt.loglinear.withP.percentile<-apply(project.miuxt.loglinear.withP[1:1400,],1,percentile.fn)


##NBLCC

NB.LC.cohort.projection<-function(posterior.param,h,A,T,C,t0){
t<-t0:(t0+T-1)
alpha<-posterior.param[(A+T+1):(2*A+T)]
beta<-posterior.param[(T+1):(A+T)]
kappa<-posterior.param[1:T]
cohort<-posterior.param[(2*A+T+1):(3*A+2*T-1)]
sigma2.k<-(exp(posterior.param[3*A+2*T]))
gamma.1<-((posterior.param[3*A+2*T+2]))
gamma.2<-((posterior.param[3*A+2*T+3]))
rho<-posterior.param[3*A+2*T+4]
rho.cohort<-posterior.param[3*A+2*T+5]
sigma2.cohort<-exp(posterior.param[3*A+2*T+6])
epsilon<-posterior.param[3*A+2*T+7]
t.new<-(t0+T):(t0+T+h-1)
kappa.forecast<-gamma.1+gamma.2*t.new[1]+rho*(kappa[T]-gamma.1-gamma.2*t[T])+rnorm(1,mean=0,sd=sqrt(sigma2.k))
for (i in 2:h){
kappa.forecast[i]<-gamma.1+gamma.2*t.new[i]+rho*(kappa.forecast[i-1]-gamma.1-gamma.2*t.new[i-1])+rnorm(1,mean=0,sd=sqrt(sigma2.k))
}
cohort.forecast<-cohort[C]+rho.cohort*(cohort[C]-cohort[C-1])+rnorm(1,0,sqrt(sigma2.cohort))
cohort.forecast[2]<-cohort.forecast[1]+rho.cohort*(cohort.forecast[1]-cohort[C])+rnorm(1,0,sqrt(sigma2.cohort))
for (j in 3:h){
cohort.forecast[j]<-cohort.forecast[j-1]+rho.cohort*(cohort.forecast[j-1]-cohort.forecast[j-2])+rnorm(1,0,sqrt(sigma2.cohort))
}
cohort.forecast.mat<-matrix(0,nrow=A,ncol=h)
for (i in 1:A){
for (j in 1:h){
if ((j-i)<0) cohort.forecast.mat[i,j]<-cohort[(j-i)+A+T]
if ((j-i)>=0) cohort.forecast.mat[i,j]<-cohort.forecast[(j-i)+1]
}}
logmiuxt.forecast<-matrix(rep(alpha,h),nrow=A,ncol=h,byrow=FALSE)+beta%*%t(kappa.forecast)+cohort.forecast.mat+matrix(log(rgamma(A*h,epsilon,epsilon)),nrow=A,ncol=h)
return(rbind(logmiuxt.forecast,kappa.forecast,cohort.forecast))
}

full.projected.ng.LC.cohort<-apply(average.theta.AR1.over.negbin.int.LCC,1,NB.LC.cohort.projection,h=14,A=100,T=42,C=141,t0=-21)
k.forecast.ng.LC.cohort<-full.projected.ng.LC.cohort[(seq(from=101,to=1428,by=102)),]
cohort.forecast.ng.LC.cohort<-full.projected.ng.LC.cohort[(seq(from=102,to=1428,by=102)),]
full.projected.ng.LC.cohort<-full.projected.ng.LC.cohort[-c(seq(from=101,to=1428,by=102),seq(from=102,to=1428,by=102)),];gc()

##Fitted and projected crude death rates

generate.Dxt.ng.LC.cohort.fn<-function(x,Ext.valid,A,h,t0){
t<-t0:(t0+h-1)
a<-x[(A+h+1):(2*A+h)]
b<-x[(h+1):(A+h)]
k<-x[1:h]
cohort<-x[(2*A+h+1):(3*A+2*h-1)]
cohort.mat<-matrix(0,nrow=A,ncol=h)
for (i in 1:A){
for (j in 1:h){
cohort.mat[i,j]<-cohort[j-i+A]
}}
e<-x[3*A+2*h+7]
Ext.valid.vec<-as.vector(Ext.valid)
logmiuxt.vec<-as.vector(matrix(rep(a,h),nrow=A,ncol=h,byrow=FALSE)+b%*%t(k)+cohort.mat)
rnbinom(A*h,size=e,prob=(e/(e+Ext.valid.vec*exp(logmiuxt.vec))))
}

generate.Dxt.ng.LC.cohort.fn(average.theta.AR1.over.negbin.int.LCC[1,],Ext.valid=Ext,A=100,h=42,t0=-21)
fitted.Dxt.ng.LC.cohort.average<-apply(average.theta.AR1.over.negbin.int.LCC,1,generate.Dxt.ng.LC.cohort.fn,Ext.valid=Ext,A=100,h=42,t0=-21)
EWexpo.female.mat.ex.mat<-matrix(rep(as.vector(Ext),20000),nrow=length(as.vector(Ext)),ncol=20000,byrow=FALSE)
fitted.miuxt.11yrs.ng.LC.cohort.average.withover<-fitted.Dxt.ng.LC.cohort.average/EWexpo.female.mat.ex.mat


project.Dxt.ng.LC.cohort.fn<-function(x,Ext.valid,A,h){
e<-x[A*h+1]
miuxt.vec<-x[-(A*h+1)]
Ext.valid.vec<-as.vector(Ext.valid)
rnbinom(A*h,size=e,prob=(e/(e+Ext.valid.vec*miuxt.vec)))
} 

projected.Dxt.11yrs.ng.LC.cohort<-apply(rbind(exp(full.projected.ng.LC.cohort[1:1400,]),average.theta.AR1.over.negbin.int.LCC[,391]),2,project.Dxt.ng.LC.cohort.fn,Ext.valid=EWexpo.female.mat.ex.validation,A=100,h=14)
EWexpo.female.mat.ex.validation.mat<-matrix(rep(as.vector(EWexpo.female.mat.ex.validation),ncol(projected.Dxt.11yrs.ng.LC.cohort)),nrow=length(as.vector(EWexpo.female.mat.ex.validation)),ncol=ncol(projected.Dxt.11yrs.ng.LC.cohort),byrow=FALSE)
projected.miuxt.11yrs.ng.LC.cohort.withover<-projected.Dxt.11yrs.ng.LC.cohort/EWexpo.female.mat.ex.validation.mat 


#age 10
age<-11
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age0.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age0.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age0.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-10.03,-8),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)
#legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
legend("topright",c("Observed","Holdout","Median","95% Intervals"),cex=1,pch=c(4,20,NA,NA),lty=c(NA,NA,1,2),col=1)
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age0.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age0.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age0.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age0.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age0.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age0.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age0.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age0.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age0.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age0.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age0.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age0.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age0.loglinear.cohort<-apply(crude.logmiuxt.forecast.age0.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age0.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age0.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age0.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 30
age<-49
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age30.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age30.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age30.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-6.95,-5.4),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)
#legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
legend("topright",c("Observed","Holdout","Median","95% Intervals"),cex=1,pch=c(4,20,NA,NA),lty=c(NA,NA,1,2),col=1)
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age30.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age30.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age30.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age30.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age30.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age30.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age30.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age30.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age30.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age30.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age30.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age30.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age30.loglinear.cohort<-apply(crude.logmiuxt.forecast.age30.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age30.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age30.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age30.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 55
age<-56
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age55.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age55.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age55.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-5.8,-4.75),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age55.ng.loglinear.cohort.average[2,],type="l",col=3)
lines(43:56,PI.crude.logmiuxt.forecast.age55.ng.loglinear.cohort.average[1,],type="l",lty=2,col=3)
lines(43:56,PI.crude.logmiuxt.forecast.age55.ng.loglinear.cohort.average[3,],type="l",lty=2,col=3)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age55.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age55.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age55.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age55.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age55.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age55.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age55.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age55.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age55.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age55.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age55.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age55.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age55.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age55.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age55.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age55.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age55.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age55.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age55.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age55.loglinear.cohort<-apply(crude.logmiuxt.forecast.age55.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age55.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age55.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age55.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 60
age<-61
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age60.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age60.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age60.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-5.3,-4.4),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.cohort.average[2,],type="l",col=3)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.cohort.average[1,],type="l",lty=2,col=3)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.cohort.average[3,],type="l",lty=2,col=3)
#legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
legend("topright",c("Observed","Holdout","Median","95% Intervals"),cex=1,pch=c(4,20,NA,NA),lty=c(NA,NA,1,2),col=1)
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age60.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age60.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age60.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age60.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age60.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age60.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age60.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age60.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age60.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age60.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age60.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age60.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age60.loglinear.cohort<-apply(crude.logmiuxt.forecast.age60.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age60.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age60.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age60.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 65
age<-66
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age65.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age65.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age65.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-4.9,-3.7),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age65.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age65.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age65.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age65.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age65.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age65.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age65.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age65.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age65.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age65.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age65.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age65.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age65.loglinear.cohort<-apply(crude.logmiuxt.forecast.age65.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age65.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age65.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age65.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 75
age<-76
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age75.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age75.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age75.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-3.95,-2.67),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age75.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age75.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age75.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age75.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age75.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age75.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age75.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age75.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age75.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age75.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age75.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age75.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age75.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age75.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age75.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age75.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age75.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age75.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age75.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age75.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age75.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age75.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age75.loglinear.cohort<-apply(crude.logmiuxt.forecast.age75.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age75.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age75.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age75.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 80
age<-81
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age80.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age80.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age80.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-3.35,-2.3),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)
#legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
legend("topright",c("Observed","Holdout","Median","95% Intervals"),cex=1,pch=c(4,20,NA,NA),lty=c(NA,NA,1,2),col=1)
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age80.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age80.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age80.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age80.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age80.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age80.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age80.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age80.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age80.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age80.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age80.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age80.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age80.loglinear.cohort<-apply(crude.logmiuxt.forecast.age80.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age80.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age80.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age80.loglinear.cohort[3,],type="l",lty=2,col="blue")

#age 90
age<-91
ind.new<-seq(age,1400,by=100)
crude.logmiuxt.forecast.age90.ng.loglinear.cohort.average<-log(projected.miuxt.11yrs.ng.loglinear.cohort.withover[ind.new,])
PI.crude.logmiuxt.forecast.age90.ng.loglinear.cohort.average<-apply(crude.logmiuxt.forecast.age90.ng.loglinear.cohort.average,1,percentile.fn)
plot(1:42,log(round(Dxt)/round(Ext))[age,],pch=4,xlim=c(0,55),ylim=c(-2.05,-1.25),xaxt="n",xlab="Year",ylab="",main=paste0("Age ",age-1),cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25)
axis(1,at=c(1,seq(10,50,by=10)),label=c(1961,seq(1970,2010,by=10)),cex.axis=1.15)
lines(43:56,PI.crude.logmiuxt.forecast.age90.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age90.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(43:56,PI.crude.logmiuxt.forecast.age90.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)
legend("topright",c("Observed Log Crude Death Rates","Holdout Log Crude Death Rates","NBAPCI Median","NBAPI Median","Classical APCI Median","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),cex=1,pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"))
points(43:56,log(EWdeath.female.mat.ex.validation[age,]/EWexpo.female.mat.ex.validation[age,]),pch=20)

crude.logmiuxt.forecast.age90.ng.loglinear.average<-log(projected.miuxt.11yrs.ng.loglinear.average.withover[ind.new,])
PI.crude.logmiuxt.forecast.age90.ng.loglinear.average<-apply(crude.logmiuxt.forecast.age90.ng.loglinear.average,1,percentile.fn)
lines(43:56,PI.crude.logmiuxt.forecast.age90.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age90.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(43:56,PI.crude.logmiuxt.forecast.age90.ng.loglinear.average[3,],lty=2,type="l",col=2)

lines(43:56,log(project.miuxt.loglinear.withP.percentile[2,ind.new]),col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[1,ind.new]),lty=2,col="blue")
lines(43:56,log(project.miuxt.loglinear.withP.percentile[3,ind.new]),lty=2,col="blue")

ind.fitted<-seq(age,4200,by=100)
crude.logmiuxt.fitted.age90.ng.loglinear.cohort.average<-log(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age90.ng.loglinear.cohort.average<-apply(crude.logmiuxt.fitted.age90.ng.loglinear.cohort.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age90.ng.loglinear.cohort.average[2,],type="l",col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age90.ng.loglinear.cohort.average[1,],type="l",lty=2,col=1)
lines(1:42,CI.crude.logmiuxt.fitted.age90.ng.loglinear.cohort.average[3,],type="l",lty=2,col=1)

crude.logmiuxt.fitted.age90.ng.loglinear.average<-log(fitted.miuxt.11yrs.ng.loglinear.average.withover[ind.fitted,])
CI.crude.logmiuxt.fitted.age90.ng.loglinear.average<-apply(crude.logmiuxt.fitted.age90.ng.loglinear.average,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age90.ng.loglinear.average[2,],lty=1,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age90.ng.loglinear.average[1,],lty=2,type="l",col=2)
lines(1:42,CI.crude.logmiuxt.fitted.age90.ng.loglinear.average[3,],lty=2,type="l",col=2)

crude.logmiuxt.forecast.age90.loglinear.cohort<-log(fitted.crude.miuxt.loglinear.cohort[ind.fitted,])
CI.crude.logmiuxt.fitted.age90.loglinear.cohort<-apply(crude.logmiuxt.forecast.age90.loglinear.cohort,1,percentile.fn)
lines(1:42,CI.crude.logmiuxt.fitted.age90.loglinear.cohort[2,],type="l",col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age90.loglinear.cohort[1,],type="l",lty=2,col="blue")
lines(1:42,CI.crude.logmiuxt.fitted.age90.loglinear.cohort[3,],type="l",lty=2,col="blue")

#############################
##projected lifeexpectancy with Poisson variation 
#############################

##NBAPCI

project.expectancy.ng.loglinear.cohort.average.withP<-apply((projected.miuxt.11yrs.ng.loglinear.cohort.withover[1:1400,]),2,project.expectancy.fn,Ext=Ext,time=2003:2016)
fitted.expectancy.ng.loglinear.cohort.average.withP<-apply((fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover),2,project.expectancy.fn,Ext=Ext,time=1961:2002)

project.expectancy.ng.loglinear.cohort.average.withP.percentile<-apply(project.expectancy.ng.loglinear.cohort.average.withP,1,percentile.fn)
fitted.expectancy.ng.loglinear.cohort.average.withP.percentile<-apply(fitted.expectancy.ng.loglinear.cohort.average.withP,1,percentile.fn)
plot((-41):0,e0(demogdata(Dxt/Ext,pop=Ext,ages=0:99,years=1961:2002,label="EW",type="mortality",name="female"),type="period"),pch=4,cex=0.7,cex.axis=1.15,cex.lab=1.2,cex.main=1.25,ylim=c(73.8,83.6),xlim=c(-41,13),xlab="Years",ylab="Life Expectancy at Birth",main="",xaxt="n")
axis(1,at=c(-41,-32,-22,-12,-2,8,18,26),label=c(1961,1970,1980,1990,2000,2010,2020,2028),cex.axis=1.15)
lines(1:14,project.expectancy.ng.loglinear.cohort.average.withP.percentile[2,],lty=1,col=1)
lines(1:14,project.expectancy.ng.loglinear.cohort.average.withP.percentile[1,],lty=2,col=1)
lines(1:14,project.expectancy.ng.loglinear.cohort.average.withP.percentile[3,],lty=2,col=1)
lines(1:14,project.expectancy.ng.loglinear.average.withP.percentile[2,],lty=1,col=2)
lines(1:14,project.expectancy.ng.loglinear.average.withP.percentile[1,],lty=2,col=2)
lines(1:14,project.expectancy.ng.loglinear.average.withP.percentile[3,],lty=2,col=2)
points(1:14,e0(demogdata(round(EWdeath.female.mat.ex.validation)/round(EWexpo.female.mat.ex.validation),pop=round(EWexpo.female.mat.ex.validation),ages=0:99,years=2003:2016,label="EW",type="mortality",name="female"),type="period"),pch=20)
#legend("bottomright",c("Observed Life Expectancy","Holdout Life expectancy","NBAPCI Median","NBAPI Median","Classical APCI","NBAPCI 95% Intervals","NBAPI 95% Intervals","Classical APCI 95% Intervals"),pch=c(4,20,NA,NA,NA,NA,NA,NA),lty=c(NA,NA,1,1,1,2,2,2),col=c(1,1,1,2,"blue",1,2,"blue"),cex=1.25)
legend("topleft",c("Observed","Holdout","Median","95% Intervals"),pch=c(4,20,NA,NA),lty=c(NA,NA,1,2),col=1,cex=1.25)
lines((-41):0,fitted.expectancy.ng.loglinear.cohort.average.withP.percentile[2,],lty=1,col=1)
lines((-41):0,fitted.expectancy.ng.loglinear.cohort.average.withP.percentile[1,],lty=2,col=1)
lines((-41):0,fitted.expectancy.ng.loglinear.cohort.average.withP.percentile[3,],lty=2,col=1)
lines((-41):0,fitted.expectancy.ng.loglinear.average.withP.percentile[2,],lty=1,col=2)
lines((-41):0,fitted.expectancy.ng.loglinear.average.withP.percentile[1,],lty=2,col=2)
lines((-41):0,fitted.expectancy.ng.loglinear.average.withP.percentile[3,],lty=2,col=2)

##classical APCI
project.expectancy.loglinear.withP<-apply(project.miuxt.loglinear.withP[1:1400,],2,project.expectancy.fn,Ext=EWexpo.female.mat.ex.validation,time=2003:2016)
project.expectancy.loglinear.withP.percentile<-apply(project.expectancy.loglinear.withP,1,percentile.fn)
lines(1:14,project.expectancy.loglinear.withP.percentile[2,],col="blue")
lines(1:14,project.expectancy.loglinear.withP.percentile[1,],lty=2,col="blue")
lines(1:14,project.expectancy.loglinear.withP.percentile[3,],lty=2,col="blue")

fitted.expectancy.loglinear.cohort.withP<-apply((fitted.crude.miuxt.loglinear.cohort),2,project.expectancy.fn,Ext=Ext,time=1961:2002)
fitted.expectancy.loglinear.cohort.withP.percentile<-apply(fitted.expectancy.loglinear.cohort.withP,1,percentile.fn)
lines((-41):0,fitted.expectancy.loglinear.cohort.withP.percentile[2,],lty=1,col="blue")
lines((-41):0,fitted.expectancy.loglinear.cohort.withP.percentile[1,],lty=2,col="blue")
lines((-41):0,fitted.expectancy.loglinear.cohort.withP.percentile[3,],lty=2,col="blue")

##NBAPCI

project.expectancy.ng.LC.cohort.average.withP<-apply(projected.miuxt.11yrs.ng.LC.cohort.withover,2,project.expectancy.fn,Ext=Ext,time=2003:2016)
fitted.expectancy.ng.LC.cohort.average.withP<-apply(fitted.miuxt.11yrs.ng.LC.cohort.average.withover,2,project.expectancy.fn,Ext=Ext,time=1961:2002)


##trace and ACF plots

#NBLC

par(mfrow=c(5,2))
plot(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,143],xlab="Iteration",ylab="",main=expression(alpha[1]),type="l")
acf(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,143],main="")
plot(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,43],xlab="Iteration",ylab="",main=expression(beta[1]),type="l")
acf(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,43],main="")
plot(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,1],xlab="Iteration",ylab="",main=expression(kappa[1]),type="l")
acf(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,1],main="")
#plot(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,42],xlab="Iteration",ylab="",main=expression(kappa[42]),type="l")
#acf(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,42],main="")
plot(exp(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243]),xlab="Iteration",ylab="",main=expression(sigma[kappa]^2),type="l")
acf(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,243],main="")
plot(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248],xlab="Iteration",ylab="",main=expression(phi),type="l")
acf(average.theta.AR1.over.negbin.int.group.marg.y0.normal.match.prior[,248],main="")

#NBAPI

par(mfrow=c(5,2))
plot(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143],xlab="Iteration",ylab="",main=expression(alpha[1]),type="l")
acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,143],main="")
plot(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43],xlab="Iteration",ylab="",main=expression(beta[1]),type="l")
acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,43],main="")
plot(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1],xlab="Iteration",ylab="",main=expression(kappa[1]),type="l")
acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,1],main="")
#plot(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,42],xlab="Iteration",ylab="",main=expression(kappa[42]),type="l")
#acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,42],main="")
#plot(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243]),xlab="Iteration",ylab="",main=expression(sigma[kappa]^2),type="l")
#acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,243],main="")
plot(exp(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244]),xlab="Iteration",ylab="",main=expression(lambda),type="l")
acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,244],main="")
plot(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],xlab="Iteration",ylab="",main=expression(phi),type="l")
acf(average.theta.AR1.over.negbin.int.y0.new.notrunc.fast.group.cond.hess.matchprior[,246],main="")



##################################
##quantitative measures
##################################

##Scoring For projection

projected.Dxt.mean.APCI<-apply(projected.Dxt.11yrs.ng.loglinear.cohort,1,mean)
projected.Dxt.mean.API<-apply(projected.Dxt.11yrs.ng.loglinear.average,1,mean)
projected.Dxt.mean.LCC<-apply(projected.Dxt.11yrs.ng.LC.cohort,1,mean)
projected.Dxt.mean.LC<-apply(projected.Dxt.11yrs.ng.matchprior.average,1,mean)

project.miuxt.mean.cAPCI<-apply(project.miuxt.loglinear.withP[1:1400,],1,mean)
projected.Dxt.mean.cAPCI<-project.miuxt.mean.cAPCI*as.vector(EWexpo.female.mat.ex.validation)

MAE.APCI<-mean(abs(as.vector(EWdeath.female.mat.ex.validation)-projected.Dxt.mean.APCI))
MAE.API<-mean(abs(as.vector(EWdeath.female.mat.ex.validation)-projected.Dxt.mean.API))
MAE.LCC<-mean(abs(as.vector(EWdeath.female.mat.ex.validation)-projected.Dxt.mean.LCC))
MAE.LC<-mean(abs(as.vector(EWdeath.female.mat.ex.validation)-projected.Dxt.mean.LC))
MAE.cAPCI<-mean(abs(as.vector(EWdeath.female.mat.ex.validation)-projected.Dxt.mean.cAPCI))

MAE<-c(MAE.APCI,MAE.API,MAE.cAPCI,MAE.LCC,MAE.LC)
names(MAE)<-c("APCI","API","cAPCI","LCC","LC");MAE



y <- 1:2
sample <- matrix(rnorm(20), nrow = 2)
sample<-rbind(rnorm(10000),rnorm(10000,mean=5,sd=10))
crps_sample(y = y, dat = sample)
logs_sample(y = y, dat = sample);-c(dnorm(y[1],log=TRUE),dnorm(y[2],mean=5,sd=10,log=TRUE))

sample<-rnorm(10000,mean=5,sd=10)
crps_sample(y = 1, dat = sample)
2/10000^2*sum((sort(sample)-1)*(10000*(1<sort(sample))-(1:10000)+0.5))

EWrates.female.vec.ex.validation<-as.vector(EWdeath.female.mat.ex.validation/EWexpo.female.mat.ex.validation)

logscore_APCI<-logs_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.loglinear.cohort.withover)
slogscore_APCI<-mean(logscore_APCI)
logscore_API<-logs_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.loglinear.average.withover)
slogscore_API<-mean(logscore_API)
logscore_cAPCI<-logs_sample(y=EWrates.female.vec.ex.validation,dat=project.miuxt.loglinear.withP[1:1400,])
slogscore_cAPCI<-mean(logscore_cAPCI)
logscore_LCC<-logs_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.LC.cohort.withover)
slogscore_LCC<-mean(logscore_LCC)
logscore_LC<-logs_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.matchprior.average.withover)
slogscore_LC<-mean(logscore_LC)

LOGS<-c(slogscore_APCI,slogscore_API,slogscore_cAPCI,slogscore_LCC,slogscore_LC)
names(LOGS)<-c("APCI","API","cAPCI","LCC","LC");LOGS


crps_APCI<-crps_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.loglinear.cohort.withover)
scrps_APCI<-mean(crps_APCI)
crps_API<-crps_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.loglinear.average.withover)
scrps_API<-mean(crps_API)
crps_cAPCI<-crps_sample(y=EWrates.female.vec.ex.validation,dat=project.miuxt.loglinear.withP[1:1400,])
scrps_cAPCI<-mean(crps_cAPCI)
crps_LCC<-crps_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.LC.cohort.withover)
scrps_LCC<-mean(crps_LCC)
crps_LC<-crps_sample(y=EWrates.female.vec.ex.validation,dat=projected.miuxt.11yrs.ng.matchprior.average.withover)
scrps_LC<-mean(crps_LC)

CRPS<-c(scrps_APCI,scrps_API,scrps_cAPCI,scrps_LCC,scrps_LC)
names(CRPS)<-c("APCI","API","cAPCI","LCC","LC");CRPS

lll<-1200
sum(crps_sample(y=EWrates.female.vec.ex.validation[lll],dat=projected.miuxt.11yrs.ng.loglinear.cohort.withover[lll,]))
2/20000^2*sum((sort(projected.miuxt.11yrs.ng.loglinear.cohort.withover[lll,])-EWrates.female.vec.ex.validation[lll])*(20000*(EWrates.female.vec.ex.validation[lll]<sort(projected.miuxt.11yrs.ng.loglinear.cohort.withover[lll,]))-(1:20000)+0.5))
sum(crps_APCI[lll])
sum(crps_sample(y=EWrates.female.vec.ex.validation[lll],dat=projected.miuxt.11yrs.ng.loglinear.average.withover[lll,]))
2/10000^2*sum((sort(projected.miuxt.11yrs.ng.loglinear.average.withover[lll,])-EWrates.female.vec.ex.validation[lll])*(10000*(EWrates.female.vec.ex.validation[lll]<sort(projected.miuxt.11yrs.ng.loglinear.average.withover[lll,]))-(1:10000)+0.5))
sum(crps_API[lll])
#nothing seemed wrong here

#by age
x<-matrix(nrow=100,ncol=2)
for (i in 1:100){
lll<-seq(i,1400,by=100)
x[i,1]<-sum(crps_sample(y=EWrates.female.vec.ex.validation[lll],dat=projected.miuxt.11yrs.ng.loglinear.cohort.withover[lll,]))
sum(crps_APCI[lll])
x[i,2]<-sum(crps_sample(y=EWrates.female.vec.ex.validation[lll],dat=projected.miuxt.11yrs.ng.loglinear.average.withover[lll,]))
sum(crps_API[lll])
}
x<-cbind(x,(x[,1]>x[,2]))

scores<-rbind(format(round(MAE, 4), nsmall = 4),format(round(LOGS, 4), nsmall = 4),format(round(CRPS, 6), nsmall = 6))
rownames(scores)<-c("MAE","LOGS","CRPS");scores #projected rates
#I think it is likely that the CRPS penalises less for (posterior) forecast distributions that have wide intervals, 
#and rewards less on forecasts that predict well. Meaning distributions will be scored well by CRPS if they have  
#wider intervals, as in the API and LC without cohort models.



##Scoring For fitted rates

Ext.vec<-as.vector(round(Ext));Dxt.vec<-as.vector(round(Dxt))
fitted.Dxt.mean.APCI<-apply(fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover,1,mean)*Ext.vec
fitted.Dxt.mean.API<-apply(fitted.miuxt.11yrs.ng.loglinear.average.withover,1,mean)*Ext.vec
fitted.Dxt.mean.LCC<-apply(fitted.miuxt.11yrs.ng.LC.cohort.average.withover,1,mean)*Ext.vec
fitted.Dxt.mean.LC<-apply(fitted.miuxt.11yrs.ng.matchprior.average.withover,1,mean)*Ext.vec

fitted.miuxt.mean.cAPCI<-apply(fitted.crude.miuxt.loglinear.cohort,1,mean)
fitted.Dxt.mean.cAPCI<-fitted.miuxt.mean.cAPCI*Ext.vec

MAE.fitted.APCI<-mean(abs(Dxt.vec-fitted.Dxt.mean.APCI))
MAE.fitted.API<-mean(abs(Dxt.vec-fitted.Dxt.mean.API))
MAE.fitted.LCC<-mean(abs(Dxt.vec-fitted.Dxt.mean.LCC))
MAE.fitted.LC<-mean(abs(Dxt.vec-fitted.Dxt.mean.LC))
MAE.fitted.cAPCI<-mean(abs(Dxt.vec-fitted.Dxt.mean.cAPCI))

MAE.fitted<-c(MAE.fitted.APCI,MAE.fitted.API,MAE.fitted.cAPCI,MAE.fitted.LCC,MAE.fitted.LC)
names(MAE.fitted)<-c("APCI","API","cAPCI","LCC","LC");MAE.fitted


EWrates.female.vec<-Dxt.vec/Ext.vec

logscore.fitted_APCI<-logs_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover)
slogscore.fitted_APCI<-mean(logscore.fitted_APCI)
logscore.fitted_API<-logs_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.loglinear.average.withover)
slogscore.fitted_API<-mean(logscore.fitted_API)
logscore.fitted_cAPCI<-logs_sample(y=EWrates.female.vec,dat=fitted.crude.miuxt.loglinear.cohort)
slogscore.fitted_cAPCI<-mean(logscore.fitted_cAPCI)
logscore.fitted_LCC<-logs_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.LC.cohort.average.withover)
slogscore.fitted_LCC<-mean(logscore.fitted_LCC)
logscore.fitted_LC<-logs_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.matchprior.average.withover)
slogscore.fitted_LC<-mean(logscore.fitted_LC)

LOGS.fitted<-c(slogscore.fitted_APCI,slogscore.fitted_API,slogscore.fitted_cAPCI,slogscore.fitted_LCC,slogscore.fitted_LC)
names(LOGS.fitted)<-c("APCI","API","cAPCI","LCC","LC");LOGS.fitted

crps.fitted_APCI<-crps_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.loglinear.cohort.average.withover)
scrps.fitted_APCI<-mean(crps.fitted_APCI)
crps.fitted_API<-crps_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.loglinear.average.withover)
scrps.fitted_API<-mean(crps.fitted_API)
crps.fitted_cAPCI<-crps_sample(y=EWrates.female.vec,dat=fitted.crude.miuxt.loglinear.cohort)
scrps.fitted_cAPCI<-mean(crps.fitted_cAPCI)
crps.fitted_LCC<-crps_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.LC.cohort.average.withover)
scrps.fitted_LCC<-mean(crps.fitted_LCC)
crps.fitted_LC<-crps_sample(y=EWrates.female.vec,dat=fitted.miuxt.11yrs.ng.matchprior.average.withover)
scrps.fitted_LC<-mean(crps.fitted_LC)

CRPS.fitted<-c(scrps.fitted_APCI,scrps.fitted_API,scrps.fitted_cAPCI,scrps.fitted_LCC,scrps.fitted_LC)
names(CRPS.fitted)<-c("APCI","API","cAPCI","LCC","LC");CRPS.fitted

scores.fitted<-rbind(format(round(MAE.fitted, 4), nsmall = 4),format(round(LOGS.fitted, 4), nsmall = 4),format(round(CRPS.fitted, 6), nsmall = 6))
rownames(scores.fitted)<-c("MAE","LOGS","CRPS");scores.fitted #fitted rates
#I think it is likely that the CRPS penalises less for (posterior) forecast distributions that have wide intervals, 
#and rewards less on forecasts that predict well. Meaning distributions will be scored well by CRPS if they have  
#wider intervals, as in the API and LC without cohort models.


##scoring for projected life expectancy

projected.LE.mean.APCI<-apply(project.expectancy.ng.loglinear.cohort.average.withP,1,mean)
projected.LE.mean.API<-apply(project.expectancy.ng.loglinear.average.withP,1,mean)
projected.LE.mean.cAPCI<-apply(project.expectancy.loglinear.withP,1,mean)
projected.LE.mean.LCC<-apply(project.expectancy.ng.LC.cohort.average.withP,1,mean)
projected.LE.mean.LC<-apply(project.expectancy.ng.matchprior.average.withP,1,mean)

EW.female.LE.validation<-as.vector(e0(demogdata(round(EWdeath.female.mat.ex.validation)/round(EWexpo.female.mat.ex.validation),pop=round(EWexpo.female.mat.ex.validation),ages=0:99,years=2003:2016,label="EW",type="mortality",name="female"),type="period"))

MAE.LE.APCI<-mean(abs(EW.female.LE.validation-projected.LE.mean.APCI))
MAE.LE.API<-mean(abs(EW.female.LE.validation-projected.LE.mean.API))
MAE.LE.cAPCI<-mean(abs(EW.female.LE.validation-projected.LE.mean.cAPCI))
MAE.LE.LCC<-mean(abs(EW.female.LE.validation-projected.LE.mean.LCC))
MAE.LE.LC<-mean(abs(EW.female.LE.validation-projected.LE.mean.LC))

MAE.LE<-c(MAE.LE.APCI,MAE.LE.API,MAE.LE.cAPCI,MAE.LE.LCC,MAE.LE.LC)
names(MAE.LE)<-c("APCI","API","cAPCI","LCC","LC");MAE.LE


logscore.LE_APCI<-logs_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.loglinear.cohort.average.withP)
slogscore.LE_APCI<-mean(logscore.LE_APCI)
logscore.LE_API<-logs_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.loglinear.average.withP)
slogscore.LE_API<-mean(logscore.LE_API)
logscore.LE_cAPCI<-logs_sample(y=EW.female.LE.validation,dat=project.expectancy.loglinear.withP)
slogscore.LE_cAPCI<-mean(logscore.LE_cAPCI)
logscore.LE_LCC<-logs_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.LC.cohort.average.withP)
slogscore.LE_LCC<-mean(logscore.LE_LCC)
logscore.LE_LC<-logs_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.matchprior.average.withP)
slogscore.LE_LC<-mean(logscore.LE_LC)

LOGS.LE<-c(slogscore.LE_APCI,slogscore.LE_API,slogscore.LE_cAPCI,slogscore.LE_LCC,slogscore.LE_LC)
names(LOGS.LE)<-c("APCI","API","cAPCI","LCC","LC");LOGS.LE

crps.LE_APCI<-crps_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.loglinear.cohort.average.withP)
scrps.LE_APCI<-mean(crps.LE_APCI)
crps.LE_API<-crps_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.loglinear.average.withP)
scrps.LE_API<-mean(crps.LE_API)
crps.LE_cAPCI<-crps_sample(y=EW.female.LE.validation,dat=project.expectancy.loglinear.withP)
scrps.LE_cAPCI<-mean(crps.LE_cAPCI)
crps.LE_LCC<-crps_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.LC.cohort.average.withP)
scrps.LE_LCC<-mean(crps.LE_LCC)
crps.LE_LC<-crps_sample(y=EW.female.LE.validation,dat=project.expectancy.ng.matchprior.average.withP)
scrps.LE_LC<-mean(crps.LE_LC)

CRPS.LE<-c(scrps.LE_APCI,scrps.LE_API,scrps.LE_cAPCI,scrps.LE_LCC,scrps.LE_LC)
names(CRPS.LE)<-c("APCI","API","cAPCI","LCC","LC");CRPS.LE

scores.LE<-rbind(format(round(MAE.LE, 4), nsmall = 4),format(round(LOGS.LE, 4), nsmall = 4),format(round(CRPS.LE, 6), nsmall = 6))
rownames(scores.LE)<-c("MAE","LOGS","CRPS");scores.LE #projected e0

##scoring for fitted life expectancy

fitted.LE.mean.APCI<-apply(fitted.expectancy.ng.loglinear.cohort.average.withP,1,mean)
fitted.LE.mean.API<-apply(fitted.expectancy.ng.loglinear.average,1,mean)
fitted.LE.mean.cAPCI<-apply(fitted.expectancy.loglinear.cohort.withP,1,mean)
fitted.LE.mean.LCC<-apply(fitted.expectancy.ng.LC.cohort.average.withP,1,mean)
fitted.LE.mean.LC<-apply(fitted.expectancy.ng.matchprior.average,1,mean)

EW.female.LE<-as.vector(e0(demogdata(round(Dxt)/round(Ext),pop=round(Ext),ages=0:99,years=1961:2002,label="EW",type="mortality",name="female"),type="period"))

MAE.fitted.LE.APCI<-mean(abs(EW.female.LE-fitted.LE.mean.APCI))
MAE.fitted.LE.API<-mean(abs(EW.female.LE-fitted.LE.mean.API))
MAE.fitted.LE.cAPCI<-mean(abs(EW.female.LE-fitted.LE.mean.cAPCI))
MAE.fitted.LE.LCC<-mean(abs(EW.female.LE-fitted.LE.mean.LCC))
MAE.fitted.LE.LC<-mean(abs(EW.female.LE-fitted.LE.mean.LC))

MAE.fitted.LE<-c(MAE.fitted.LE.APCI,MAE.fitted.LE.API,MAE.fitted.LE.cAPCI,MAE.fitted.LE.LCC,MAE.fitted.LE.LC)
names(MAE.fitted.LE)<-c("APCI","API","cAPCI","LCC","LC");MAE.fitted.LE

logscore.fitted.LE_APCI<-logs_sample(y=EW.female.LE,dat=fitted.expectancy.ng.loglinear.cohort.average.withP)
slogscore.fitted.LE_APCI<-mean(logscore.fitted.LE_APCI)
logscore.fitted.LE_API<-logs_sample(y=EW.female.LE,dat=fitted.expectancy.ng.loglinear.average)
slogscore.fitted.LE_API<-mean(logscore.fitted.LE_API)
logscore.fitted.LE_cAPCI<-logs_sample(y=EW.female.LE,dat=fitted.expectancy.loglinear.cohort.withP)
slogscore.fitted.LE_cAPCI<-mean(logscore.fitted.LE_cAPCI)
logscore.fitted.LE_LCC<-logs_sample(y=EW.female.LE,dat=fitted.expectancy.ng.LC.cohort.average.withP)
slogscore.fitted.LE_LCC<-mean(logscore.fitted.LE_LCC)
logscore.fitted.LE_LC<-logs_sample(y=EW.female.LE,dat=fitted.expectancy.ng.matchprior.average)
slogscore.fitted.LE_LC<-mean(logscore.fitted.LE_LC)

LOGS.fitted.LE<-c(slogscore.fitted.LE_APCI,slogscore.fitted.LE_API,slogscore.fitted.LE_cAPCI,slogscore.fitted.LE_LCC,slogscore.fitted.LE_LC)
names(LOGS.fitted.LE)<-c("APCI","API","cAPCI","LCC","LC");LOGS.fitted.LE

crps.fitted.LE_APCI<-crps_sample(y=EW.female.LE,dat=fitted.expectancy.ng.loglinear.cohort.average.withP)
scrps.fitted.LE_APCI<-mean(crps.fitted.LE_APCI)
crps.fitted.LE_API<-crps_sample(y=EW.female.LE,dat=fitted.expectancy.ng.loglinear.average)
scrps.fitted.LE_API<-mean(crps.fitted.LE_API)
crps.fitted.LE_cAPCI<-crps_sample(y=EW.female.LE,dat=fitted.expectancy.loglinear.cohort.withP)
scrps.fitted.LE_cAPCI<-mean(crps.fitted.LE_cAPCI)
crps.fitted.LE_LCC<-crps_sample(y=EW.female.LE,dat=fitted.expectancy.ng.LC.cohort.average.withP)
scrps.fitted.LE_LCC<-mean(crps.fitted.LE_LCC)
crps.fitted.LE_LC<-crps_sample(y=EW.female.LE,dat=fitted.expectancy.ng.matchprior.average)
scrps.fitted.LE_LC<-mean(crps.fitted.LE_LC)

CRPS.fitted.LE<-c(scrps.fitted.LE_APCI,scrps.fitted.LE_API,scrps.fitted.LE_cAPCI,scrps.fitted.LE_LCC,scrps.fitted.LE_LC)
names(CRPS.fitted.LE)<-c("APCI","API","cAPCI","LCC","LC");CRPS.fitted.LE

scores.fitted.LE<-rbind(format(round(MAE.fitted.LE, 4), nsmall = 4),format(round(LOGS.fitted.LE, 4), nsmall = 4),format(round(CRPS.fitted.LE, 6), nsmall = 6))
rownames(scores.fitted.LE)<-c("MAE","LOGS","CRPS");scores.fitted.LE #fitted e0


