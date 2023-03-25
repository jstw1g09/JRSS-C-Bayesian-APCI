# Bayesian model comparison for mortality forecasting
## *Journal of the Royal Statistical Society Series C*

## Data

The data chosen for illustrative purposes in this paper are the female death data and the corresponding exposures for England and Wales, extracted from the Human Mortality Database (HMD). They are classified by single year of age from 0 to 99, and years ranging from 1961 to 2002. They are respectively contained in the files "1x1EWdeath.txt" and "1x1EWexposure.txt".

Also provided are the *holdout data* corresponding to female death and exposure data spanning years 2003-2016, stored respectively in the files "1x1EWdeath_validation_correct.txt" and "1x1EWexposure_validation_correct.txt".

These data were extracted from the following resources available in the public domain: https://www.mortality.org/

## Code

The code for the MCMC algorithms, simulations studies, and various Bayesian computations, presented in the paper has been written in `R`. This is stored in the file "Bayesian_model_compare_MF_Rcode_final.R".

For more info, please refer to the paper [https://doi.org/10.1093/jrsssc/qlad021].

## References

HMD. Human Mortality Database. Max Planck Institute for Demographic Research (Germany), University of California, Berkeley (USA), and French Institute for Demographic Studies (France). 

Jackie S T Wong, Jonathan J Forster, Peter W F Smith, Bayesian model comparison for mortality forecasting, *Journal of the Royal Statistical Society Series C: Applied Statistics*, 2023;, qlad021, https://doi.org/10.1093/jrsssc/qlad021
