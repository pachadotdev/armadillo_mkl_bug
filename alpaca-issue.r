# 1: packges ----

if (!requireNamespace("alpaca", quietly = TRUE)) {
  install.packages("alpaca")
}

if (!requireNamespace("dplyr", quietly = TRUE)) {
  install.packages("dplyr")
}

if (!requireNamespace("janitor", quietly = TRUE)) {
  install.packages("janitor")
}

if (!requireNamespace("readr", quietly = TRUE)) {
  install.packages("readr")
}

if (!requireNamespace("tidyr", quietly = TRUE)) {
  install.packages("tidyr")
}

if (!requireNamespace("tradepolicy", quietly = TRUE)) {
  install.packages("tradepolicy")
}

library(alpaca)
library(dplyr)
library(janitor)
library(readr)
library(tidyr)
library(tradepolicy)

# 2: data ----

ch1_application3 <- tradepolicy::agtpa_applications %>%
  clean_names() %>%
  filter(year %in% seq(1986, 2006, 4)) %>%
  mutate(
    exp_year = paste0(exporter, year),
    imp_year = paste0(importer, year),
    year = paste0("intl_border_", year),
    log_trade = log(trade),
    log_dist = log(dist),
    intl_brdr = ifelse(exporter == importer, pair_id, "inter"),
    intl_brdr_2 = ifelse(exporter == importer, 0, 1),
    pair_id_2 = ifelse(exporter == importer, "0-intra", pair_id)
  ) %>%
  pivot_wider(
    names_from = year,
    values_from = intl_brdr_2,
    values_fill = 0
  ) %>%
  group_by(pair_id) %>%
  mutate(sum_trade = sum(trade)) %>%
  ungroup()

# 3: trade diversion model ----

form <- trade ~ log_dist + cntg + lang + clny + rta | exp_year + imp_year + intl_brdr

feglm(form, data = ch1_application3, family = poisson())

# log_dist     cntg     lang     clny      rta
# -0.13350  0.25738  0.06945 -0.11775  0.06084

feglm(form, data = ch1_application3, family = poisson())

#  log_dist      cntg      lang      clny       rta
# -0.213246  0.175521  0.008711  0.116188  0.246975

feglm(form, data = ch1_application3, family = poisson())

# log_dist     cntg     lang     clny      rta
# -0.07164  0.10955  0.19845 -0.09351  0.06167

# 4: export the design matrix to a plain file

# do the same as the GLM function

load_all()

formula <- Formula(form)

data <- ch1_application3

family <- poisson()

formula <- Formula(formula)

setDT(data)
data <- data[, c(all.vars(formula), weights), with = FALSE]

lhs <- names(data)[[1L]]

nobs.full <- nrow(data)

data <- na.omit(data)

nobs.na <- nobs.full - nrow(data)

nobs.full <- nrow(data)

k.vars <- attr(terms(formula, rhs = 2L), "term.labels")
k <- length(k.vars)

setkeyv(data, k.vars)

tmp.var <- tempVar(data)

repeat {
  # Drop observations that do not contribute to the log-likelihood
  ncheck <- nrow(data)
  for (j in k.vars) {
    data[, (tmp.var) := mean(get(lhs)), by = eval(j)]
    if (family[["family"]] == "binomial") {
      data <- data[get(tmp.var) > 0.0 & get(tmp.var) < 1.0]
    } else {
      data <- data[get(tmp.var) > 0.0]
    }
    data[, (tmp.var) := NULL]
  }

  # Check termination
  if (ncheck == nrow(data)) break
}

data[, (k.vars) := lapply(.SD, checkFactor), .SDcols = k.vars]
if (length(formula)[[2L]] > 2L) {
  add.vars <- attr(terms(formula, rhs = 3L), "term.labels")
  data[, (add.vars) := lapply(.SD, checkFactor), .SDcols = add.vars]
}

nt <- nrow(data)
nobs <- c(
  nobs.full = nobs.full,
  nobs.na   = nobs.na,
  nobs.pc   = nobs.full - nt,
  nobs      = nt
)

# Extract model response and regressor matrix
y <- data[[1L]]
X <- model.matrix(formula, data, rhs = 1L)[, -1L, drop = FALSE]
nms.sp <- attr(X, "dimnames")[[2L]]
attr(X, "dimnames") <- NULL
p <- ncol(X)

wt <- data[[weights]]

beta <- numeric(p)
eta <- rep(family[["linkfun"]](sum(wt * (y + 0.1)) / sum(wt)), nt)

nms.fe <- lapply(data[, k.vars, with = FALSE], levels)
lvls.k <- sapply(nms.fe, length)

# Generate auxiliary list of indexes for different sub panels
k.list <- getIndexList(k.vars, data)

control <- do.call(feglmControl, list())

fit1 <- feglmFit(beta, eta, y, X, wt, k.list, family, control)

fit1$coefficients
# [1] -0.1833676  0.3283301 -0.1496216 -0.1094769  0.1609965

fit2 <- feglmFit(beta, eta, y, X, wt, k.list, family, control)

fit2$coefficients
# [1] -0.18381312  0.08949918  0.08496080 -0.04889974  0.16255769

my_feglmFit <- function(beta, eta, y, X, wt, k.list, family, control) {
  # Extract control arguments
  center.tol <- control[["center.tol"]]
  dev.tol <- control[["dev.tol"]]
  epsilon <- max(min(1.0e-07, dev.tol / 1000.0), .Machine[["double.eps"]])
  iter.max <- control[["iter.max"]]
  trace <- control[["trace"]]
  keep.mx <- control[["keep.mx"]]

  # Compute initial quantities for the maximization routine
  nt <- length(y)
  mu <- family[["linkinv"]](eta)
  dev <- sum(family[["dev.resids"]](y, mu, wt))
  null.dev <- sum(family[["dev.resids"]](y, mean(y), wt))

  # Generate temporary variables
  Mnu <- as.matrix(numeric(nt))
  MX <- X

  # Start maximization of the log-likelihood
  conv <- FALSE
  for (iter in seq.int(iter.max)) {
    # Store \eta, \beta, and deviance of the previous iteration
    eta.old <- eta
    beta.old <- beta
    dev.old <- dev

    # Compute weights and dependent variable
    mu.eta <- family[["mu.eta"]](eta)
    w <- (wt * mu.eta^2) / family[["variance"]](mu)
    w.tilde <- sqrt(w)
    nu <- (y - mu) / mu.eta

    # Centering variables - store multiple copies for comparison
    Mnu <- centerVariables((Mnu + nu), w, k.list, center.tol)
    Mnu1 <- centerVariables((Mnu + nu - nu), w, k.list, center.tol) # Same input but recomputed
    Mnu2 <- centerVariables((Mnu + nu - nu), w, k.list, center.tol) # Same input but recomputed again

    # Check if results are identical and print message if not
    mnu_equal1 <- all.equal(Mnu, Mnu1)
    mnu_equal2 <- all.equal(Mnu1, Mnu2)
    if (!isTRUE(mnu_equal1)) {
      cat("Iteration", iter, "- Mnu differs from Mnu1:", mnu_equal1, "\n")
    }
    if (!isTRUE(mnu_equal2)) {
      cat("Iteration", iter, "- Mnu1 differs from Mnu2:", mnu_equal2, "\n")
    }

    MX <- centerVariables(MX, w, k.list, center.tol)
    MX1 <- centerVariables(MX, w, k.list, center.tol) # Same input but recomputed
    MX2 <- centerVariables(MX, w, k.list, center.tol) # Same input but recomputed again

    # Check if results are identical and print message if not
    mx_equal1 <- all.equal(MX, MX1)
    mx_equal2 <- all.equal(MX1, MX2)
    if (!isTRUE(mx_equal1)) {
      cat("Iteration", iter, "- MX differs from MX1:", mx_equal1, "\n")
    }
    if (!isTRUE(mx_equal2)) {
      cat("Iteration", iter, "- MX1 differs from MX2:", mx_equal2, "\n")
    }

    # Compute update step and update \eta
    beta.upd <- as.vector(qr.solve(MX * w.tilde, Mnu * w.tilde, epsilon))
    eta.upd <- nu - as.vector(Mnu - MX %*% beta.upd)

    # Step-halving with three checks
    # 1. finite deviance
    # 2. valid \eta and \mu
    # 3. improvement as in glm2
    rho <- 1.0
    for (inner.iter in seq.int(50L)) {
      eta <- eta.old + rho * eta.upd
      beta <- beta.old + rho * beta.upd
      mu <- family[["linkinv"]](eta)
      dev <- sum(family[["dev.resids"]](y, mu, wt))
      dev.crit <- is.finite(dev)
      val.crit <- family[["valideta"]](eta) && family[["validmu"]](mu)
      imp.crit <- (dev - dev.old) / (0.1 + abs(dev)) <= -dev.tol
      if (dev.crit && val.crit && imp.crit) break
      rho <- rho / 2.0
    }

    # Check if step-halving failed (deviance and invalid \eta or \mu)
    if (!dev.crit || !val.crit) {
      stop("Inner loop failed; cannot correct step size.", call. = FALSE)
    }

    # Stop if we do not improve
    if (!imp.crit) {
      eta <- eta.old
      beta <- beta.old
      dev <- dev.old
      mu <- family[["linkinv"]](eta)
    }

    # Progress information
    if (trace) {
      cat("Deviance=", format(dev, digits = 5L, nsmall = 2L), "Iterations -", iter, "\n")
      cat("Estimates=", format(beta, digits = 3L, nsmall = 2L), "\n")
    }

    # Check convergence
    dev.crit <- abs(dev - dev.old) / (0.1 + abs(dev))
    if (trace) cat("Stopping criterion=", dev.crit, "\n")
    if (dev.crit < dev.tol) {
      if (trace) cat("Convergence\n")
      conv <- TRUE
      break
    }

    # Update starting guesses for acceleration
    Mnu <- Mnu - nu
  }

  # Information if convergence failed
  if (!conv && trace) cat("Algorithm did not converge.\n")

  # Update weights and dependent variable
  mu.eta <- family[["mu.eta"]](eta)
  w <- (wt * mu.eta^2) / family[["variance"]](mu)

  # Center variables with additional copies and checks
  MX <- centerVariables(X, w, k.list, center.tol)
  MX1 <- centerVariables(X, w, k.list, center.tol) # Same input but recomputed
  MX2 <- centerVariables(X, w, k.list, center.tol) # Same input but recomputed again

  # Check if results are identical and print message if not
  mx_equal1 <- all.equal(MX, MX1)
  mx_equal2 <- all.equal(MX1, MX2)
  if (!isTRUE(mx_equal1)) {
    cat("Final centering - MX differs from MX1:", mx_equal1, "\n")
  }
  if (!isTRUE(mx_equal2)) {
    cat("Final centering - MX1 differs from MX2:", mx_equal2, "\n")
  }

  # Recompute Hessian
  H <- crossprod(MX * sqrt(w))

  # Generate result list
  reslist <- list(
    coefficients  = beta,
    eta           = eta,
    weights       = wt,
    Hessian       = H,
    deviance      = dev,
    null.deviance = null.dev,
    conv          = conv,
    iter          = iter
  )

  # Update result list
  if (keep.mx) reslist[["MX"]] <- MX

  # Return result list
  reslist
}

fail <- my_feglmFit(beta, eta, y, X, wt, k.list, family, control)

# Iteration 1 - Mnu differs from Mnu1: Mean relative difference: 4.073442e-08 
# Iteration 1 - MX differs from MX1: Mean relative difference: 7.951906e-08 
# Iteration 2 - Mnu differs from Mnu1: Mean relative difference: 1.087724e-07 
# Iteration 2 - MX differs from MX1: Mean relative difference: 1.389104e-07 
# Iteration 3 - Mnu differs from Mnu1: Mean relative difference: 1.126623e-07 
# Iteration 3 - MX differs from MX1: Mean relative difference: 6.596992e-08 
# Iteration 4 - Mnu differs from Mnu1: Mean relative difference: 7.738145e-08 
# Iteration 4 - MX differs from MX1: Mean relative difference: 6.307038e-08 
# Iteration 5 - Mnu differs from Mnu1: Mean relative difference: 6.626428e-08 
# Iteration 5 - MX differs from MX1: Mean relative difference: 6.690698e-08 
# Iteration 6 - Mnu differs from Mnu1: Mean relative difference: 4.832838e-08 
# Iteration 6 - MX differs from MX1: Mean relative difference: 6.61089e-08 
# Iteration 7 - Mnu differs from Mnu1: Mean relative difference: 7.130049e-08 
# Iteration 7 - MX differs from MX1: Mean relative difference: 7.819167e-08 
# Iteration 8 - Mnu differs from Mnu1: Mean relative difference: 5.404867e-08 
# Iteration 8 - MX differs from MX1: Mean relative difference: 8.233684e-08 
# Iteration 9 - Mnu differs from Mnu1: Mean relative difference: 1.59087e-07 
# Iteration 9 - MX differs from MX1: Mean relative difference: 1.117398e-07 
# Iteration 10 - Mnu differs from Mnu1: Mean relative difference: 6.526269e-07 
# Iteration 10 - MX differs from MX1: Mean relative difference: 3.295745e-07 

# 4: save Y and X to a file ----

# Armadillo docs:

# csv_ascii: Numerical data stored in comma separated value (CSV) text format, without a header.
# To save/load with a header, use the csv_name(filename, header) specification instead.

write_csv(
  as_tibble(X),
  "X.csv",
  col_names = FALSE
)

write_csv(
  as_tibble(y),
  "y.csv",
  col_names = FALSE
)
