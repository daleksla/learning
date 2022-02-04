# Linear Regression is a fancy word for finding the best possible straight line through a scatterplot relating two quantitative variables
  # In others words, its a way of calculating the line of best fit between two axis with numbers
# Multiple regression is finding a line of best fit for multiple variables
# To calculate values needed to perform regression, see ./calculatingRegression.R
# 'geom_abline(slope, intercept)' is a useful function which draws a line of best fit on top of a given plot when given values
# 'lm()' is an R function that can do all both LR and MR for us, from calculating a + b to plotting a line of best fit
  # In reality you should use that (especially when there are 3+ predicting factors)
  # We can use this in conjunction with 'geom_smooth()', where we add it to a plot and pass it the 'lm' function as a parameter
    # This goes on to use the 'lm()' calculator automatically with a given x and y axis on a plot
# 'autoplot()' can be used automatically creates plots
  # 'Residuals vs Fitted / Linearality ' ~ shows linear relationship (the line of best fit of this plot should be 0)
  # 'Normal Q-Q / Normality of residuals' ~ check whether residuals are distributed normally (ie all are on a straight line)
  # 'Scale-location / Homogenity of residual variances' ~ checks whether residuals are spread equally along predictors (should be horizontal line)
  # 'Residuals vs Leverage / Independence of residuals' ~ shows outliers which may influence predictors (which have values > 3 || < -3)
# These four plots can allow us to assess how well a linear model explains/fits a dataset

library(tidyverse)
library(datarium) # get another dataset
library(ggfortify) # contains the function 'autoplot' 
marketing = as_tibble(marketing)

# Note, we can 'lm()' is used to fit linear models - it can be used to carry out regression
model = lm(marketing$sales~marketing$youtube) # automatically calculates y-intercept (a) & slope (b) based the result (sales) and the causing factor (youtube)
a = model$coefficients[1] # index the value returned, first one is a 
b = model$coefficients[2] # second index is b

# Now display the data - 'geom_abline(slope, intercept)' draws an appropriate line of best fit on top of plot
ggplot(data = NULL, mapping = aes(x=marketing$youtube, y=marketing$sales)) + geom_point(size = 4) + geom_abline(slope=b, intercept=a) #reconstruct plot

# We can also use the 'lm()' function directly to calculate and plot our line of best fit - instead of 'geom_abline()', use 'geom_smooth()'
# 'geom_smooth()' is a function which adds different types of lines to a graph - we can specify that we want it to use 'lm()' to calculate how it should draw a line
ggplot(data = NULL, mapping = aes(x=marketing$youtube, y=marketing$sales)) + geom_point(size = 4) + geom_smooth(method=lm, se=FALSE)

## MULTIPLE REGRESSION USING 'lm()' - basically we can use the same concept from LR
# We can also use two predictor variables (youtube and facebook) to predict / make a line of best fit for sales
ggplot(data = marketing, mapping = aes(x=youtube+facebook,y=sales)) + geom_point() + geom_smooth(method=lm, se=FALSE)

autoplot(model) # plots 4 plots allowing us to assess regression / prediction model