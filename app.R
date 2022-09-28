# Load packages

library(abind)
library(colorRamps)
library(crosstalk)
library(DT)
library(ellipse)
library(jsonlite)
library(lme4)
library(mada)
library(magic)
library(Matrix)
library(msm)
library(mvtnorm)
library(plotrix)
library(png)
library(rlang)
library(shiny)
library(shinyjs)
library(shinyWidgets)
library(stats)
library(yaml)
library(foreach)
library(Hmisc)
library(meta)
library(metafor)
library(rjags)
library(ggplot2)
library(dplyr)
library(data.table)
library(tidyverse)
library(bayesplot)
library(car)
library(BayesianTools)




#################################
### Functions Used in the App ###
#################################

options(warn=-1)
### Frequentist Method
### Function for Frequentist-based Reference Range based on REML
### Takes in study means, study standard deviations, study sample sizes (n)
FreqFit <- function(means, sds, n, quant,method="REML",hakn=FALSE){
    N <- length(means)
    means.use <- means
    sds.use <- sds
    
    #################################################################
    
    trans=FALSE
    if(trans){
      mu_hat <-sum(n*means)/sum(n)
      sigma_hat <- sqrt(sum((n-1)*sds^2)/sum(n-1))
      var.e.w<- sum((n-1)*(means - mu_hat)^2)/sum(n-1)
      totalvar <- var.e.w + sigma_hat^2
      
      center_para=mu_hat
      
      scale_para=sqrt(totalvar)
      
      means.use=(means.use-center_para)/scale_para
      sds.use=sds.use/scale_para
    }
    
    #fit random effects model using REML
    m.reml <- metagen(means.use,
                      sds.use/sqrt(n),
                      fixed = FALSE,
                      random = TRUE,
                      method.tau = method,
                      hakn = hakn,
                      prediction=TRUE,
                      #level.comb=quant,
                      #level.predict=quant
                      )
    
    #print(m.reml$I2)
    
    #pooled variance - assumes study populations drawn independently 
    sigma_hat <- sqrt(sum((n-1)*sds.use^2)/sum(n-1))
    
    s2=(sum(n/(sds.use)^2)*N)/((sum(n/(sds.use)^2))^2-sum((n/(sds.use)^2)^2))
    #s2=sigma_hat/N
    
    
    
    #Estimates from RE model
    tau_hat <- m.reml$tau
    mu_hat <- m.reml$TE.random
    
  
    
    
    #Estimate of total variance (within and between studies)
    total.var <- sigma_hat^2 + tau_hat^2
    
    
    
    #Estimates for limits of reference range
    lower_limit <- qnorm((1-quant)/2, mean = mu_hat, sd = sqrt(total.var))
    upper_limit <- qnorm((1+quant)/2, mean = mu_hat, sd = sqrt(total.var))
    

    if(trans){
      lower_limit=lower_limit*scale_para+center_para
      upper_limit=upper_limit*scale_para+center_para
    }
    #Isq=(tau_hat^2)/(s2+tau_hat^2)
 
    return(list(m.reml, lower_limit, upper_limit,Isq=m.reml$I2,sigma=sigma_hat))
}


### Bayesian Method (For Case Study)
### Function for Bayesian Reference Range
### Takes in study means, study standard deviations, study sample sizes (n)
### Fits Bayesian model using packages rjags and coda
BayesFitCaseStudy <- function(means, sds, n,quant,plot=TRUE,iter=50000,burnin=5000){
    N <- length(means)
    y <- means
    sd <- sds
    sigma_hat <- sqrt(sum((n-1)*sds^2)/sum(n-1))
    mu_hat <-sum(n*means)/sum(n)
    var.e.w<- sum((n-1)*(means - mu_hat)^2)/sum(n-1)
    total.var <- var.e.w + sigma_hat^2
    
    #print(tau_hat)
    #print(sigma_hat)
    center_para=mu_hat
    #scale_para=1
    scale_para=sqrt(total.var)
    #print(scale_para)
    #center_para=0
   
    #scale_para=0.01
    #scale and center the parameter autometically
    y=(y-center_para)/scale_para
    sd=sd/scale_para
    #print(sd)
    x <- (n-1)*(sd^2)
    data <- list(y = y, x = x, n=n)
    Inits1=list(.RNG.name = "base::Mersenne-Twister", .RNG.seed = 123)
    Inits2=list(.RNG.name = "base::Mersenne-Twister", .RNG.seed = 124)
    Inits <- list(Inits1, Inits2)
    #upb1=as.character((quant+1)*50)
    #upb=paste0(upb1,"%")
    #lob1=as.character((1-quant)*50)
    #lob=paste0(lob1,"%")
   
    jags.model=jags.model(file="./Bayesian.txt",data=data,inits=Inits,n.chain=2, quiet = T)
    
    burn.in <- burnin
    update(jags.model, n.iter = burn.in)
    params <- c("tau", "mu", "sigma", "new")
    samps=coda.samples(jags.model, params, n.iter = iter, .RNG.name = "base::Mersenne-Twister", .RNG.seed = 123)
    #print(summary(samps))
    findout=c(samps[[1]][,2],samps[[2]][,2])
    meantau=mean(c(samps[[1]][,4],samps[[2]][,4]))*(scale_para)
    meansigma=mean(c(samps[[1]][,3],samps[[2]][,3]))*(scale_para)
    #trac=plot(samps[[1]][,2],trace=TRUE,density=TRUE)
    color_scheme_set("mix-blue-red")
    if(plot){
      trac=tracePlot(samps)
    }else{
      trac=0
    }
    
    #trac=mcmc_trace(samps,pars = "new")
    #print(quantile(findout,0.025))
    results=list(samps,quantile(findout,(1-quant)/2)*scale_para+center_para , quantile(findout,(1+quant)/2)*scale_para+center_para,
                 trac,
                 tau=meantau,
                 Isq=(meantau^2)/(meantau^2+(meansigma^2)/N),
                 sigma=meansigma)
    return(results)
}




### Empirical Approach
### Takes in study means, sds, and sample sizes (n)
EmpFit <- function(means, sds, n,quant){
    N <- length(means)
    
    sigma_hat <- sqrt(sum((n-1)*sds^2)/sum(n-1))
    mu_hat <-sum(n*means)/sum(n)
    var.e.w<- sum((n-1)*(means - mu_hat)^2)/sum(n-1)
    total.var <- var.e.w + sigma_hat^2
    
    lower_limit <- qnorm((1-quant)/2, mean = mu_hat, sd = sqrt(total.var))
    upper_limit <- qnorm((1+quant)/2, mean = mu_hat, sd = sqrt(total.var))
    
    
    return(list(lower_limit, upper_limit))
}

## Mixture distribution method
## Takes in study means, sds, and sample sizes (n)
## Two weight options: sample size (ss) or inverse variance (iv)
MixFit <- function(means, sds, n, weight = "ss",quant){
    if(weight=="ss"){
        w <- n/sum(n)
    }
    else{
        w <- (n/sds^2)/sum(n/sds^2)
    }
    f = function(x,w,p){
        y=w%*%pnorm(x,means,sds)-p
        #y=w%*%plnorm(x,meanlog=log(means/sqrt(1 + (sds^2)/(means^2))), sdlog =sqrt(log(1+(sds^2/means^2))))-p
        #y=w%*%pgamma(x,shape = means^2/sds^2,scale = sds^2/means)-p
    }
    lo=(1-quant)/2
    up=(1+quant)/2
    lower=uniroot(f,lower=-5000,upper=5000, p=lo,w=w)
    upper=uniroot(f,lower=-5000,upper=5000, p=up,w=w)
    return(c(lower$root,upper$root))
}


study_level_outcomes <- function(data = NULL, subset=NULL, formula = NULL,
                                 mean="mean", author="author", n="n", sd="sd", quant=0.95)
  {
  qu=0.95
    if(!is.null(data) & is.character(c(mean,author,n,sd))){
      X <- as.data.frame(data)
      origdata <- data
      author <- getElement(X,author)
      mean <- getElement(X,mean)
      sd <- getElement(X,sd)
      n <- getElement(X,n)
    }
    if(is.null(data) & !is.character(c(mean,author,n,sd))){
      origdata <- data.frame(author = author, mean = mean, sd = sd, n = n)
    }
    
    freqdata <- cbind(mean,author,n,sd)
    # Need checkdata function from basics.R (or end of this R file) for this to work
    checkdata(freqdata)
  # Sensitivity and specificity calculations for each study
    #print(quant)
    Lower.mean = mean-qnorm((1+qu)/2)*sd/sqrt(n)
    Upper.mean = mean+qnorm((1+qu)/2)*sd/sqrt(n)
    Lower.pred = mean - qt((1+quant)/2, n-1)*sqrt(1+1/n)*sd
    Upper.pred = mean + qt((1+quant)/2, n-1)*sqrt(1+1/n)*sd
   
  
  study_level <- data.frame(author=origdata$author, mean=origdata$mean, sd=origdata$sd, n=origdata$n, 
                            Lower.mean=Lower.mean,Upper.mean=Upper.mean,
                            Lower.pred=Lower.pred,Upper.pred=Upper.pred)
  #print(study_level)
  return(study_level)
}


# Function needed to checkdata in correct format before calculating 95% CI for Mean and predictive CI for each study

checkdata <- function(X, nrowwarn = 2){
    X <- as.data.frame(X)
    if(!all(c("author","mean","sd","n") %in% names(X))){
        stop("Data frame or matrix must have columns labelled author, mean, sd, n.")}
    if(nrow(X) < nrowwarn){warning("There are only one study!")}
    return(invisible(NULL))
}





# Define UI for application that draws a histogram
ui <- navbarPage(title = "RIMeta: Meta-Analysis for Reference Interval",
                 
                 #Set up google analytics 
                 header = singleton(tags$head(includeScript("google_analytics.js"))),
                 
                 #########################
                 ### Tab 1 - Home page ###
                 #########################
                 
                 
                 
                 # Start with a home tab
                 tabPanel("Home", 
                          h1("RIMeta: Estimating the Reference Interval from a Meta-Analysis v3.0 (Sep 2022)"),
                          br(),
                          h4("A reference interval, or reference range, is defined as the interval in which some proportion (usually 95%) of measurements from a healthy population is expected to fall ",tags$strong("(see Siegel et.al.2022)"),"It is useful in practice   for clinicians or caregivers to decide whether a patient \'s measurement reflects that of a healthy \'normal\' individual. One can estimate it from a single study or preferably from a meta-analysis of multiple studies to increase generalizability. This range differs from the confidence interval for the pooled mean or the prediction interval for a new study mean in a meta-analysis, which do not capture natural variation across healthy individuals. With the aggregate data (study mean, standard deviation, and sample size) from each study, RIMeta allows users to estimate the reference interval using multiple methods.",tags$strong("(see Siegel et.al.2021 & Cao et.al.2021)")),
                          br(),
                          h4("RIMeta implements two meta-analysis models that can be used to estimate the pooled mean and reference interval: the random effects model and the fixed effects model. The random effects model assumes all study means follow a common distribution. Thus, the reference interval in the random effects model reflects both the between study variation and the within study variation. The fixed effects model, which is usually preferred when the number of studies is small, assumes the study means are independent of each other. "),
                          br(),
                          h4("For the random effects model, RIMeta implements three methods proposed by Siegel et. al. to estimate the reference interval: the frequentist method, the Bayesian method and the empirical method.  The frequentist method assumes the data in each study follows a normal distribution with equal variance. It first uses restricted maximum likelihood (REML) to estimate the overall mean and the between study variance. The within study variance is then estimated using the pooled sample variance from each study. Finally, the 95% reference interval is calculated using the estimated mean and variance of the overall (marginal) normal distribution. The Bayesian method has the same assumptions as the frequentist method and uses the sampling distribution of the sample variance to estimate the within study variance. The bounds of the 95% reference interval are then given by the 2.5% and 97.5% quantiles of the posterior predictive distribution for a new individual. The empirical method does not require each study to have a normal distribution or equal variance, only that the overall (marginal) distribution across all studies is normal. The total variance is estimated as the sum of a weighted average of the sample variances and the sample variance of the study means. After getting the estimated total variance, the reference interval is calculated the same as in the frequentist method. "),
                          br(),
                          h4("For the fixed effects model, RIMeta implements the mixture distribution method proposed by Cao et. al. This method assumes the pooled population of the included studies is representative of the overall population. Each study included in the mixture distribution method can have any distribution that is completely determined by the mean and variance. Although the mixture distribution method does not restrict whether each study follows a normal distribution, the method implemented in RIMeta does treat each study as normally distributed for simplicity. The mixture distribution method calculates the pooled distribution as a mixture of the study distributions, weighted by their sample sizes The reference interval is then estimated by solving for the 2.5% and 97.5% quantiles of the pooled distribution."),
                          br(),
                          h4(tags$strong("References:")),
                          p("[1]:",tags$a(href="https://doi.org/10.1002/jrsm.1442", "Siegel L, Murad MH, Chu H. Estimating the reference range from a meta‐analysis. Research synthesis methods. 2021 Mar;12(2):148-60.")),
                          p("[2]:",tags$a(href="https://doi.org/10.1002/jrsm.1488", "Cao W, Siegel L, Zhou J, Zhu M, Tong T, Chen Y, Chu H. Estimating the reference interval from a fixed effects meta‐analysis. Research Synthesis Methods. 2021 Apr 17;12:630-640
                                 ")),
                          p("[3]:",tags$a(href="https://doi.org/10.1093/aje/kwac013", "Lianne Siegel, M Hassan Murad, Richard D Riley, Fateh Bazerbachi,Zhen Wang, Haitao Chu, A Guide to Estimating the Reference Range From a Meta-Analysis Using Aggregate or Individual Participant Data, American Journal of Epidemiology, Volume 191, Issue 5, May 2022, Pages 948 -956
                                          ")),
                          p("If you use RIMeta please cite these papers."),
                          br(),
                          
                          p("Ziren Jiang, Wenhao Cao, Haitao Chu, Lianne Siegel"),
                          p("For feedback/questions about this app please contact Ziren Jiang at jian0746@umn.edu"),
                          br(),
                          br(),
                          p("Codes for this app are available on GitHub: "),
                          # tags$a(href = ""),
                          br(),
                          br(),
                          p("RIMeta is constructed using the following packages from R:"),
                          p("abind, bayesplot, BayesianTools, colorRamps, crosstalk, car, DT, data.table, dplyr, ellipse, foreach, ggplot2, Hmisc, jsonlite, lme4, mada, magic, Matrix, msm, mvtnorm, meta, metafor, plotrix, png, rlang, rjags, shiny, shinyjs, shinyWidgets, stats, tidyverse, yaml."),
                          
                         # downloadButton("downloadUG", "Download User Guide"),
                          br(),
                          br(),
                          
                          p("THE SOFTWARE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING 
                            BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND 
                            NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, 
                            DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
                            OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE."),
                         br(),
                         h4(tags$strong("Below is the additional instructions for RIMeta: ")),
                         br(),
                         
                         imageOutput("g01"),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         imageOutput("g02"),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         br(),
                         imageOutput("g03")
                 ),
                 
                 #########################
                 ### Tab 2 - Load data ###
                 #########################
                 
                 # Within the load data tab let users select a file to upload, the upload happens in a sidebarPanel on
                 # the left and the mainPanel will show the data once file uploaded. Code to show data is in the server 
                 # section below
                 tabPanel("Load Data",
                          sidebarLayout(
                              sidebarPanel(
                                  fileInput(inputId="data", label="Please select CSV file", buttonLabel="Select", placeholder="No file selected"),
                                  helpText("Default maximum file size is 5MB"),
                                  # Horizontal line ----
                                  tags$hr(),
                                  
                                  # Input: Checkbox if file has header ----
                                  checkboxInput("header", "Header", TRUE),
                                  
                                  # Input: Select separator ----
                                  radioButtons("sep", "Separator",
                                               choices = c(Comma = ",",
                                                           Semicolon = ";",
                                                           Tab = "\t"),
                                               selected = ","),
                                  
                                  # Input: Select quotes ----
                                  radioButtons("quote", "Quote",
                                               choices = c(None = "",
                                                           "Double Quote" = '"',
                                                           "Single Quote" = "'"),
                                               selected = '"'),
                                  br(),
                                  h4(helpText(tags$strong("Download example datasets"))),
                                  downloadButton("downloadData1", "Standard Example"),
                                  br(),
                                  br(),
                                  br(),
                                  p(tags$a(href="https://shiny.rstudio.com/gallery/file-upload.html", "The upload data part is built according to this code")),
                              ),
                              mainPanel(
                                  tabsetPanel(
                                      tabPanel("File Upload", 
                                               h3("Please select a CSV file to upload or double click the table below to change value"),
                                               br(),
                                               p("The file should contain four columns. Labelling of columns is case sensitive."),
                                               p("The", tags$strong("first"), "column should be labelled", tags$strong("author"), "and contain the name of 
                                           the study author and the year of 
                                           publication."),
                                               p("The", tags$strong("second"), "column should be labelled", tags$strong("mean"), "and contain the observed mean of each study."),
                                               p("The", tags$strong("third"), "column should be labelled", tags$strong("sd"), "and contain the observed standard deviation of each study population (this is not the standard error of the mean)."),
                                               p("The", tags$strong("fourth"), "column should be labelled", tags$strong("n"), "and contain the number of 
                                           participants in each study."),
                                               #p("The row with all value equal to \"0\" will be omitted for data analysis"),
                                     #          sidebarLayout(
                                     #            sidebarPanel(
                                     #               numericInput("studynum","Number of studies:",value = 15,min = 0,max = 100)
                                     #            ),
                                    #             mainPanel(
                                     #               actionButton("goo",label = "Apply Number")
                                      #           )
                                       #        ),
                                              fluidRow(
                                                column(2.5,
                                                  numericInput("studynum","Number of studies:",value = 15,min = 0,max = 100)
                                                ),
                                                column(9.5,
                                                  actionButton("goo",label = "Apply Number")
                                                )
                                              ),
                                               br(),
                                               DTOutput("my_datatable")
                                      ),
                                  )
                              )
                          )),
                 #############################
                 ### Tab 3 - Meta-analysis ###
                 #############################
                 
                 # Set up a third tab for showing the results of the meta-analysis
                 tabPanel("Meta-Analysis", h1("Meta-Analysis for Estimating Reference Interval"),
                          sidebarLayout(
                              sidebarPanel(
                                  uiOutput("MA_input"),
                                  actionButton(inputId = "MA_reset", label = "Reset all inputs")
                              ),
                              mainPanel(
                                  tabsetPanel(
                                    tabPanel("Study-level Outcomes",
                                               br(),
                                               p("Note 1: Use standard normal distribution to estimate the confidence interval for the mean."),
                                               br(), 
                                               p("Note 2: Use t-distribution to estimate the prediction interval for a new individual from each study."),
                                               br(),
                                               p("Note 3: Calculate the inverse variance weights and sample size weights."),
                                               br(),
                                               p("Note 4: The Upper and Lower limits of prediction interval refer to the percentile entered in the panel on the left, the limits of Confidence Interval is 95% and not affected by the change of level "),
                                               br(),
                                               DT::dataTableOutput("table"),
                                               downloadButton("downloadTable", "Download Table"),
                                               br()
                                      ),
                                      tabPanel("Reference Interval Plot",
                                               h5("Note: At least one box under 'Options for Reference Interval plot tab' must be selected to avoid an error 
                                            message"),
                                               br(),
                                               h4("Please wait for the MCMC sampling"),
                                               fluidRow(
                                                 column(6,
                                                        textInput("title", label = h4("Plot title"), value = "Reference Interval Plot", width='500px'),
                                                 )
                                               ),
                                              
                                               plotOutput("RRP", width="800px", height="800px"),
                                               br(),
                                               radioButtons("filetype", label="Select plot format", choices=list("png")),
                                               downloadButton("downloadRRP", "Download Plot")
                                      ),
                                      
                                      tabPanel("Table of Results", 
                                               h3("Results for estimated Intervals"),
                                               br(),
                                               tableOutput("statTable"),
                                               downloadButton("downloadStatTable", "Download Table"),
                                               br(),
                                               uiOutput("hetero"),
                                               tableOutput("heterotable"),
                                               conditionalPanel( condition = "output.remodel",
                                                                 downloadButton("downloadStatTable2", "Download Table")),
                                               br()
                                      ),
                                      tabPanel("Diagostic Plots", br(),
                                               #h4(id="text1","Please wait for the MCMC sampling"),
                                               #h3(id="text2","The plot may take some time to load"),
                                               br(),
                                               uiOutput("diag_plot"),
                                               #plotOutput("QQP", width="400px", height="400px"),
                                               br(),
                                               #h3("The Trace Plot for checking the MCMC convergence in Bayesian method"),
                                               br(),
                                               #plotOutput("TRAP", height="1200px")
                                      ),
                                      tabPanel("Appendix", br(),
                                               h3("The aggregate data after automatically scaling and centering"),
                                               br(),
                                               tableOutput("ScaledData")
                                      )
                                    
                                  ) 
                              )
                          )
                 ),
                 
    
)



# Define server logic required to draw a histogram
server <- function(input, output) {
    Standard <- read.csv("./Standard.csv")
    
    #bbb=study_level_outcomes(Standard,quant=0.95)
    #bb.bayes = BayesFitCaseStudy(means = bbb$mean, sds =bbb$sd, n = bbb$n, quant = quantile)
    
    
    data <- reactive({ 
        file1 <- input$data
        if(is.null(file1)){
              return(Standard)
        }
        else{
          tryCatch({
            a <- read.csv(file = file1$datapath, stringsAsFactors = FALSE,fill = TRUE,header = input$header,
                          sep = input$sep,
                          quote = input$quote)
            
          },
            error=function(e){
              stop(safeError(e))
            }
          )
        }
        shiny::validate(
          need(NCOL(a)==4,"Please Check the format of the uploaded file or choose appropriate separator.")
        )
        shiny::validate(
          need(all(c("author","mean","sd","n") %in% names(a)),"Please lable the column as required.")
        )
        return(a)
        
            
    })
    v=reactiveValues(data = { 
      Standard
    })
    
    observeEvent(input$data,{
      v$data=data()
      
    })
    
    bb.bayes=reactive({
      if(!is.null(input$percentile)){
        quantile = (input$percentile)/100
      }
      bbb=study_level_outcomes(v$data,quant=quantile)
      BayesFitCaseStudy(means = bbb$mean, sds =bbb$sd, n = bbb$n, quant = quantile,iter = input$mcmc[2],burnin = input$mcmc[1])
    })
    #####################
    ### Load data tab ###
    #####################
    
    # Create a table which displays the raw data just uploaded by the user
    observeEvent(input$data,{
       updateNumericInput(inputId = "studynum",value = nrow(data()))
    })
    observeEvent(input$goo,{
      while(nrow(v$data)>1){
        lastrow=nrow(v$data)
        v$data=v$data[-lastrow,]
        #print(2)
      }
      v$data[,1]=0
      v$data[,2]=0
      v$data[,3]=0
      v$data[,4]=0
      #print(input$studynum)
      while(nrow(v$data)<input$studynum){
        v$data=rbind(v$data,c(0,0,0,0))
        #print(3)
      }
      output$my_datatable <- renderDT({
        DT::datatable(v$data, editable = TRUE)
      })
    })
    plot_title="Reference Interval Plot"
    
    plot_title=eventReactive(input$titlegoo,{
      input$title
    })
    
    output$my_datatable <- renderDT({
      DT::datatable(data(), editable = TRUE)
    })
    
    
    
    
    
    
    observeEvent(input$my_datatable_cell_edit, {
      #get values
      info = input$my_datatable_cell_edit
      i = as.numeric(info$row)
      j = as.numeric(info$col)
      k=info$value
      if(j!=1){
         k = as.numeric(info$value)
      }
     
      
      #write values to reactive
      v$data[i,j]=k
      #print(v$data[i,j])
    })
    
   # output$rawtable <- renderTable({
   #     if(is.null(data())){return()}
   #     data()
   # })
    
    # In the "Load data" tab (created in the UI section) we divide the main panel into mutlipe tabs and add the content
    # we've just created
    # When there is no data loaded display the instructions for how the data should be formatted
    # Once data is loaded display the raw data
    
    output$g01=renderImage({
      list(
        src=file.path("guide011.jpg"),
        contentType="image/jpeg",
        width=1000,
        height=600
      )
    })
    output$g02=renderImage({
      list(
        src=file.path("guide02.png"),
        contentType="png",
        width=900,
        height=600
      )
    })
    output$g03=renderImage({
      list(
        src=file.path("guide03.png"),
        contentType="png",
        width=940,
        height=650
      )
    })
    
    output$diag_plot=renderUI({
      if(input$model=="Random-effects"){
        RangeCheck=(input$RangeCheckr)
      }
      if(input$model=="Fixed-effects"){
        RangeCheck=(input$RangeCheckf)
      }
      text1=ifelse((input$model=="Random-effects")&('8' %in% RangeCheck),"Please wait for MCMC sampling","")
      text2=ifelse(input$model=="Random-effects","The QQ Plot for checking the normality of each study mean","")
      text3=ifelse(('8' %in% RangeCheck),"Trace Plot for checking the MCMC convergence in Bayesian method","")
      
      if(input$model=="Random-effects"){
        tagList(
          h3(id="text2","The plot may take some time to load"),
          h3(text2),
          
          plotOutput(outputId="QQP", width="400px", height="400px"),
          
          h3(text3),
          
          plotOutput("TRAP", height="1200px")
        )
      }else{
        tagList(
          
          h3(text3),
          
          plotOutput("TRAP", height="1200px"),
          
          h3(text2),
          
         
          
          plotOutput(outputId="QQP", width="400px", height="400px"),
        )
      }
      
    })
    
    output$hetero=renderUI({
      if(input$model=="Random-effects"){
        RangeCheck=(input$RangeCheckr)
      }
      if(input$model=="Fixed-effects"){
        RangeCheck=(input$RangeCheckf)
      }
      text4=ifelse((input$model=="Random-effects")&(!((!'8' %in% RangeCheck)&(!'6' %in% RangeCheck))),
                   "The estimated between-study heterogeneity under the random effects model","")
      h3(text4)
    })
    
    
    
    output$contents <- renderTable({
        
        # input$file1 will be NULL initially. After the user selects
        # and uploads a file, head of that data file by default,
        # or all rows if selected, will be shown.
        
        req(data)
        
        df <- read.csv(data$datapath,
                       header = input$header,
                       sep = input$sep,
                       quote = input$quote)
        
        if(input$disp == "head") {
            return(head(df))
        }
        else {
            return(df)
        }
        
    })
    
    # Allow users the option to download the standard example dataset
    output$downloadData1 <- downloadHandler(
        # Speicfy the file name 
        filename = function(){
            paste("Standard.csv")
        },
        content = function(file){
            # open the device
            # create the plot
            # close the device
            Standard
            write.table(Standard, file, sep=",", row.names=FALSE)
        }
    )
   
     # Display all input options for Meta_Analysis tab 
    output$MA_input <- renderUI({
        times <- input$MA_reset
        tabchk=tabsetPanel(
          id="tabc",
          type="hidden",
          tabPanel("Random-effects",
                   checkboxGroupInput(inputId = "RangeCheckr", label = h4("Options for Reference Interval Plot (Random effects model)"),
                                      choices = list("Confidence Interval for Study Mean"=1, "Study-Specific Predictive Interval"=2,
                                                     "Overall Confidence Interval for Mean (Random)"=3, "New Study (Random)" = 4,
                                                       "Frequentist"=6,
                                                     "Empirical" =7, "Bayesian" =8),
                                      selected=list(1,2,3,4,6,7,8))
          ),
          tabPanel("Fixed-effects",
                   checkboxGroupInput(inputId = "RangeCheckf", label = h4("Options for Reference Interval Plot(Fixed effects model)"),
                                      choices = list("Confidence Interval for study Mean"=1, "Study-Specific Predictive Interval"=2,
                                                     "Overall Confidence Interval for Mean (Fixed)"=5, "Mixture Distirbution" = 9),
                                      selected=list(1,2,5,9))
          )
          
        )
        
        
        tagList(
            
            numericInput(inputId = "percentile","(1-\U03B1) \U00D7 100% (level of reference interval)",value = 95,min = 1,max = 100),
            br(),
            selectInput("model","Meta-analysis Model",
                        choices = c("Random-effects","Fixed-effects")      
            ),
            tabchk,
            selectInput("cimethod","Method for estimating the confidance interval of the overall mean effect",
                                          choices = c("Wald-type Interval", "Hartung-Knapp/Sidik-Jonkman Interval")),
            sliderInput(inputId = "mcmc","Specify the MCMC iteration number and the burn.in number for Bayesian method",value = c(5000,50000),min = 0,max = 200000,step = 1000),
            conditionalPanel( condition = "output.fmethod",
                              selectInput("frmethod","Estimation methods for the between-study variance (Frequentist method)",
                                          choices = c("REML","Paule-Mandel","DerSimonian-Laird")))
            
        )
    })
    
    output$fmethod=reactive({
      
      return((input$model=="Random-effects")&('6' %in% input$RangeCheckr))
      
    })
   
    outputOptions(output, "fmethod", suspendWhenHidden = FALSE)  
    
    output$remodel=reactive({
      return((input$model=="Random-effects"))
    })
    
    outputOptions(output, "remodel", suspendWhenHidden = FALSE)  
    
    observeEvent(input$model, {
      updateTabsetPanel(inputId = "tabc",selected = input$model)
      if(input$model=="Random-effects"){
        RangeCheck=reactive(input$RangeCheckr)
      }
      if(input$model=="Fixed-effects"){
        RangeCheck=reactive(input$RangeCheckf)
       
      }
    })
    
    # Create a table which displays 95% CI for Mean and predictive interval for each study
    output$table <- DT::renderDataTable({
      if(is.null(v$data)){return()}
      else
        newData <- v$data
      numr=nrow(newData)
      for(i in numr:1){
        if(as.numeric(newData$sd[i])==0){
          newData=newData[-i,]
        }
      }
      #quantile = 0.95
      req(input$percentile)
      if(!is.null(input$percentile)){
        quantile = (input$percentile)/100
      }
      
      b <- study_level_outcomes(newData,quant=quantile) # get sens, spec for each trial
      #b.bayes <<- BayesFitCaseStudy(means = b$mean, sds =b$sd, n = b$n, quant = quantile)
      bb <- data.frame(author=newData$author, mean=newData$mean, sd=newData$sd, n=newData$n,
                       Lower.mean=b$Lower.mean,Upper.mean=b$Upper.mean,
                       Lower.pred=b$Lower.pred,Upper.pred=b$Upper.pred)
      bb$Lower.mean <- sprintf('%4.2f', bb$Lower.mean) # restrict number of figures after decimal place for sens
      bb$Upper.mean <- sprintf('%4.2f', bb$Upper.mean)
      bb$Lower.pred <- sprintf('%4.2f', bb$Lower.pred)
      bb$Upper.pred <- sprintf('%4.2f', bb$Upper.pred)
      # add information about inverse variance weights and sample size weight 
      k <- length(newData$n)
      wsize <- newData$n/sum(newData$n)*100
      winv <- (newData$n/newData$sd^2)/sum(newData$n/newData$sd^2)*100
      bb$Weight_Inv <- sprintf('%4.2f', winv)
      bb$Weight_Size <- sprintf('%4.2f', wsize)
      options(DT.options = list(pageLength = 30))
      datatable(bb)
      
    })
    
    
    
    # Allow users the option to download the table of 95% CI for Mean and predictive interval for each study
    output$downloadTable <- downloadHandler(
      # Speicfy the file name 
      filename = function(){
        paste("table.csv")
      },
      content = function(file){
        # open the device
        # create the plot
        # close the device
        if(is.null(v$data)){return()}
        else
          newData <- v$data
        
        numr=nrow(newData)
        for(i in numr:1){
          if(as.numeric(newData$sd[i])==0){
            newData=newData[-i,]
          }
        }
        if(!is.null(input$percentile)){
          quantile = (input$percentile)/100
        }
       
        b <- study_level_outcomes(newData,quant=quantile) # get sens, spec for each trial
        bb <- data.frame(author=newData$author, mean=newData$mean, sd=newData$sd, n=newData$n,
                         Lower.mean=b$Lower.mean,Upper.mean=b$Upper.mean,
                         Lower.pred=b$Lower.pred,Upper.pred=b$Upper.pred)
        bb$Lower.mean <- sprintf('%4.2f', bb$Lower.mean) # restrict number of figures after decimal place for sens
        bb$Upper.mean <- sprintf('%4.2f', bb$Upper.mean)
        bb$Lower.pred <- sprintf('%4.2f', bb$Lower.pred)
        bb$Upper.pred <- sprintf('%4.2f', bb$Upper.pred)
        # add information about inverse variance weights (used for random-effects model) and sample size weight (used for fixed-effects model) 
        k <- length(newData$n)
        wsize <- newData$n/sum(newData$n)*100
        winv <- (newData$n/newData$sd^2)/sum(newData$n/newData$sd^2)*100
        bb$Weight_Inv <- sprintf('%4.2f', winv)
        bb$Weight_Size <- sprintf('%4.2f', wsize)
        options(DT.options = list(pageLength = 30))
        datatable(bb)
        write.table(bb, file, sep=",", row.names=FALSE)
      })
    
    RangeCheck=list(1,2,3,4,6,7,8)
    
    output$QQP=renderPlot({
      if(input$model=="Random-effects"){
        if(is.null(v$data)){return()}
        else{X <- v$data}
        if(!is.null(input$percentile)){
          quantile = (input$percentile)/100
        }
        b <- study_level_outcomes(X,quant=quantile)
        #qqnorm(b$mean)
        #qqline(b$mean)
        qqPlot(b$mean)
      }
    })
    
    output$TRAP=renderPlot({
      if(input$model=="Random-effects"){
        RangeCheck=(input$RangeCheckr)
      }
      if(input$model=="Fixed-effects"){
        RangeCheck=(input$RangeCheckf)
      }
      if(('8' %in% RangeCheck)&input$model=="Random-effects"){
        if(is.null(v$data)){return()}
        else{X <- v$data}
        if(!is.null(input$percentile)){
          quantile = (input$percentile)/100
        }
        b <- study_level_outcomes(X,quant=quantile)
        #b.bayes=bb.bayes()
        b.bayes <- BayesFitCaseStudy(means = b$mean, sds =b$sd, n = b$n, quant = quantile,iter = input$mcmc[2],burnin = input$mcmc[1])
        (b.bayes[[4]])
      }
      
      
    })
    
    output$RRP <- renderPlot({
      if(TRUE){
        if(input$model=="Random-effects"){
          RangeCheck=(input$RangeCheckr)
        }
        if(input$model=="Fixed-effects"){
          RangeCheck=(input$RangeCheckf)
        }
      }
      
      if(is.null(v$data)){return()}
      else
        X <- v$data
      numr=nrow(X)
      for(i in numr:1){
        if(as.numeric(X$sd[i])==0){
          X=X[-i,]
        }
      }
      # Count the number of studies
      N <- length(X$author)
      # Calculate the 95% CI for Mean, and 95% Predictive Interval
      
      if(!is.null(input$percentile)){
        quantile = (input$percentile)/100
      }
      
      b <- study_level_outcomes(X,quant=quantile)
      
      #########################################################
      ## Three methods based on random-effects meta-analysis ##
      #########################################################
      ## Frequentist method
      
      hakn=ifelse(input$cimethod=="Wald-type Interval",FALSE,TRUE)
      
      fmethod="REML"
      if(input$frmethod=="Paule-Mandel"){
        fmethod="PM"
       
      }
      if(input$frmethod=="DerSimonian-Laird"){
        fmethod="DL"
        
      }
      if(input$frmethod=="REML"){
        fmethod="REML"
        
      }
      
      b.freq=FreqFit(b$mean, b$sd, b$n, quant = quantile,method = fmethod,hakn = hakn)
      
      
      
      ## Overall mean from random-effects model (REML)
      pooled.mean.random <- b.freq[[1]]$TE.random
      
      ### Bayesian method
      set.seed(123)
      #b.bayes <<- BayesFitCaseStudy(means = b$mean, sds =b$sd, n = b$n, quant = quantile)
      if('8' %in% RangeCheck){
        b.bayes=bb.bayes()
      }
      
      ### Empirical method
      b.emp <- EmpFit(b$mean, b$sd, b$n, quant = quantile)
      
      #########################################################
      ## One method based on fixed-effects meta-analysis ##
      #########################################################
      ### Mixture distribution method (sample size weight)
      b.mix <- MixFit(means = b$mean, sds = b$sd, n = b$n, quant = quantile)
      pooled.mean.fixed <- weighted.mean(b$mean, b$n)
      weight_ss = b$n/sum(b$n)
      se.fixed = sqrt(sum(weight_ss^2*b$sd^2/b$n)/(sum(weight_ss))^2)
      
      l1=paste0(95, "% CI for Mean")
      l2=paste0(quantile*100, "% Prediction Interval")
      l3=paste0(95, "% CI for Mean (Random)")
      l4=paste0(95, "% CI for Mean (Fixed)")
      l5=paste0(quantile*100, "% Reference Interval")
      # Create long data for ggplot
      b_long <- melt(setDT(b), id = c("author", "mean"), measure = patterns("^Lower", "^Upper"),
                       value.name = c("Lower", "Upper"), variable.name = "IntervalType", value.factor=T)
      # change the level name to correspond result
      levels(b_long$IntervalType) <- c(l1, l2)
      
      
      
      result.matrix <- matrix(c(b.freq[[1]]$lower.random, b.freq[[1]]$upper.random, 
                                b.freq[[1]]$lower.predict, b.freq[[1]]$upper.predict,
                                pooled.mean.fixed-1.96*se.fixed,pooled.mean.fixed+1.96*se.fixed,
                                b.freq[[2]], b.freq[[3]],
                                b.emp[[1]], b.emp[[2]], 
                                b.bayes[[2]], b.bayes[[3]],
                                b.mix[1],b.mix[2]), nrow = 7,byrow = T)
      result.toadd <- cbind(c(rep("Overall", 3),rep(l5, 4)),  
                            c(rep(pooled.mean.random,2), pooled.mean.fixed, rep(pooled.mean.random,3), pooled.mean.fixed), 
                            c(l3, "95% Prediction Interval of New Study mean", l4, "Frequentist", "Empirical", "Bayesian", "Mixture"), result.matrix)
      # Combine all the results
      b_long2 <- rbind(b_long, result.toadd, use.names = F)
      b_long2$MeanEstimate <- as.numeric(b_long2$mean)
      b_long2$Lower <- as.numeric(b_long2$Lower)
      b_long2$Upper <- as.numeric(b_long2$Upper)
      b_long2$IntervalType2 <- factor(b_long2$IntervalType,levels(b_long2$IntervalType)[c(9,8,7,6,4,5,3,2,1)])
      b_long2$author <- factor(b_long2$author)
      author1 <- c(which(levels(b_long2$author)=="Overall"),which(levels(b_long2$author)==l5))
      b_long2$author2 <- factor(b_long2$author,levels(b_long2$author)[c(c(1:length(levels(b_long2$author)))[-author1],author1)])
      
      color_select=rep(TRUE,9)
      
      #observeEvent(input$titlegoo,{
      #  plot_title=input$title
      #})
      
      # Create new data based on the tab selection
       plot_long <- b_long2[FALSE,]
      if ('1' %in% RangeCheck){
        plot_long <-rbind(plot_long, b_long2[b_long2$IntervalType2 == l1,])}else{color_select[1]=FALSE}
      if ('2' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == l2,])}else{color_select[2]=FALSE}
      if ('3' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == l3 ,])}else{color_select[3]=FALSE}
      if ('4' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "95% Prediction Interval of New Study mean",])}else{color_select[4]=FALSE}
      if ('5' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == l4,])}else{color_select[5]=FALSE}
      if ('6' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Frequentist",])}else{color_select[6]=FALSE}
      if ('7' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Empirical",])}else{color_select[7]=FALSE}
      if ('8' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Bayesian" ,])}else{color_select[8]=FALSE}
      if ('9' %in% RangeCheck){
        plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Mixture",])}else{color_select[9]=FALSE}
      # Draw the plot
       meanline = c()
       
       if(input$model=="Random-effects"){
         meanline<-c(meanline, pooled.mean.random)
       }
       if(input$model=="Fixed-effects"){
         meanline<-c(meanline, pooled.mean.fixed)
       }
       plottitleapplied="Reference Interval Plot"
       
       #plottitleapplied=ifelse(is.na(plot_title()),"Reference Interval Plot",plot_title())
      # print(c("#619CFF","#C77CFF", "#7CAE00", "goldenrod2", "darkorange4","#F4460D","#00BFC4","gray","#F8766D")[color_select])
      ggplot(plot_long,aes(x = IntervalType2,y = MeanEstimate, ymin = Lower, ymax = Upper))+
         geom_pointrange(aes(col=IntervalType2))+
         geom_hline(aes(fill=IntervalType2),yintercept = meanline, linetype=2)+
         xlab('Study')+ ylab("Reference Interval")+
         geom_errorbar(aes(ymin=Lower, ymax=Upper,col=IntervalType2),width=0.5,cex=1)+ 
         facet_wrap(~author2,strip.position="left",nrow=nrow(X)*2,scales = "free_y") +
        ggtitle(input$title)+
         theme(plot.title=element_text(size=16,face="bold"),
               axis.text.y=element_blank(),
               axis.ticks.y=element_blank(),
               axis.text.x=element_text(face="bold"),
               axis.title=element_text(size=12,face="bold"),
               legend.title = element_blank(),
               strip.text.y.left = element_text(hjust=0.5,vjust = 1,angle=0,face="bold"))+
               coord_flip() + 
               guides(fill = guide_legend(reverse = TRUE))+ 
               guides(color = guide_legend(reverse = TRUE)) + 
               scale_color_manual(values = rev(c("#619CFF","#C77CFF", "#7CAE00", "goldenrod2", "darkorange4","#F4460D","#00BFC4","gray","#F8766D")[color_select]))
       
      
    })
    
    
    
    output$downloadRRP <- downloadHandler(
      # Speicfy the file name 
      filename = function(){
        paste("ReferenceRange", input$filetype, sep=".")
      },
      content = function(file){
        # open the device
        # create the plot
        # close the device
        if(input$filetype == "png")
          #png(file, width = 600, height = 500)
        
        if(TRUE){
          if(input$model=="Random-effects"){
            RangeCheck=(input$RangeCheckr)
          }
          if(input$model=="Fixed-effects"){
            RangeCheck=(input$RangeCheckf)
          }
        }
          X <- v$data
          
          numr=nrow(X)
          for(i in numr:1){
            if(as.numeric(X$sd[i])==0){
              X=X[-i,]
            }
          }
        # Count the number of studies
          N <- length(X$author)
          # Calculate the 95% CI for Mean, and 95% Predictive Interval
          
          if(!is.null(input$percentile)){
            quantile = (input$percentile)/100
          }
          
          b <- study_level_outcomes(X,quant=quantile)
          
          #########################################################
          ## Three methods based on random-effects meta-analysis ##
          #########################################################
          ## Frequentist method
          hakn=ifelse(input$cimethod=="Wald-type Interval",FALSE,TRUE)
          
          
          fmethod="REML"
          if(input$frmethod=="Paule-Mandel"){
            fmethod="PM"
          }
          if(input$frmethod=="DerSimonian-Laird"){
            fmethod="DL"
          }
          if(input$frmethod=="REML"){
            fmethod="REML"
          }
          
          
          b.freq <- FreqFit(b$mean, b$sd, b$n, quant = quantile,method =fmethod,hakn = hakn)
          
          ## Overall mean from random-effects model (REML)
          pooled.mean.random <- b.freq[[1]]$TE.random
          
          ### Bayesian method
          set.seed(123)
          #b.bayes <<- BayesFitCaseStudy(means = b$mean, sds =b$sd, n = b$n, quant = quantile)
          b.bayes=bb.bayes()
          ### Empirical method
          b.emp <- EmpFit(b$mean, b$sd, b$n, quant = quantile)
          
          #########################################################
          ## One method based on fixed-effects meta-analysis ##
          #########################################################
          ### Mixture distribution method (sample size weight)
          b.mix <- MixFit(means = b$mean, sds = b$sd, n = b$n, quant = quantile)
          pooled.mean.fixed <- weighted.mean(b$mean, b$n)
          weight_ss = b$n/sum(b$n)
          se.fixed = sqrt(sum(weight_ss^2*b$sd^2/b$n)/(sum(weight_ss))^2)
          
          l1=paste0(95, "% CI for Mean")
          l2=paste0(quantile*100, "% Prediction Interval")
          l3=paste0(95, "% CI for Mean (Random)")
          l4=paste0(95, "% CI for Mean (Fixed)")
          l5=paste0(quantile*100, "% Reference Interval")
          # Create long data for ggplot
          b_long <- melt(setDT(b), id = c("author", "mean"), measure = patterns("^Lower", "^Upper"),
                         value.name = c("Lower", "Upper"), variable.name = "IntervalType", value.factor=T)
          # change the level name to correspond result
          levels(b_long$IntervalType) <- c(l1, l2)
          
          
          
          result.matrix <- matrix(c(b.freq[[1]]$lower.random, b.freq[[1]]$upper.random, 
                                    b.freq[[1]]$lower.predict, b.freq[[1]]$upper.predict,
                                    pooled.mean.fixed-1.96*se.fixed,pooled.mean.fixed+1.96*se.fixed,
                                    b.freq[[2]], b.freq[[3]],
                                    b.emp[[1]], b.emp[[2]], 
                                    b.bayes[[2]], b.bayes[[3]],
                                    b.mix[1],b.mix[2]), nrow = 7,byrow = T)
          result.toadd <- cbind(c(rep("Overall", 3),rep(l5, 4)),  
                                c(rep(pooled.mean.random,2), pooled.mean.fixed, rep(pooled.mean.random,3), pooled.mean.fixed), 
                                c(l3, "95% Prediction Interval of New Study mean", l4, "Frequentist", "Empirical", "Bayesian", "Mixture"), result.matrix)
          # Combine all the results
          b_long2 <- rbind(b_long, result.toadd, use.names = F)
          b_long2$MeanEstimate <- as.numeric(b_long2$mean)
          b_long2$Lower <- as.numeric(b_long2$Lower)
          b_long2$Upper <- as.numeric(b_long2$Upper)
          b_long2$IntervalType2 <- factor(b_long2$IntervalType,levels(b_long2$IntervalType)[c(9,8,7,6,4,5,3,2,1)])
          b_long2$author <- factor(b_long2$author)
          author1 <- c(which(levels(b_long2$author)=="Overall"),which(levels(b_long2$author)==l5))
          b_long2$author2 <- factor(b_long2$author,levels(b_long2$author)[c(c(1:length(levels(b_long2$author)))[-author1],author1)])
          
          color_select=rep(TRUE,9)
          # Create new data based on the tab selection
          plot_long <- b_long2[FALSE,]
          if ('1' %in% RangeCheck){
            plot_long <-rbind(plot_long, b_long2[b_long2$IntervalType2 == l1,])}else{color_select[1]=FALSE}
          if ('2' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == l2,])}else{color_select[2]=FALSE}
          if ('3' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == l3 ,])}else{color_select[3]=FALSE}
          if ('4' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "95% Prediction Interval of New Study mean",])}else{color_select[4]=FALSE}
          if ('5' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == l4,])}else{color_select[5]=FALSE}
          if ('6' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Frequentist",])}else{color_select[6]=FALSE}
          if ('7' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Empirical",])}else{color_select[7]=FALSE}
          if ('8' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Bayesian" ,])}else{color_select[8]=FALSE}
          if ('9' %in% RangeCheck){
            plot_long <-rbind(plot_long,  b_long2[b_long2$IntervalType2 == "Mixture",])}else{color_select[9]=FALSE}
          # Draw the plot
          meanline = c()
          
          if(input$model=="Random-effects"){
            meanline<-c(meanline, pooled.mean.random)
          }
          if(input$model=="Fixed-effects"){
            meanline<-c(meanline, pooled.mean.fixed)
          }
        p= ggplot(plot_long,aes(x = IntervalType2,y = MeanEstimate, ymin = Lower, ymax = Upper))+
          geom_pointrange(aes(col=IntervalType2))+
          geom_hline(aes(fill=IntervalType2),yintercept = meanline, linetype=2)+
          xlab('Study')+ ylab("Reference Interval")+
          geom_errorbar(aes(ymin=Lower, ymax=Upper,col=IntervalType2),width=0.5,cex=1)+ 
          ggtitle(input$title)+
          facet_wrap(~author2,strip.position="left",nrow=nrow(X)*2,scales = "free_y") +
          theme(plot.title=element_text(size=16,face="bold",hjust=0.65),
                axis.text.y=element_blank(),
                axis.ticks.y=element_blank(),
                axis.text.x=element_text(face="bold"),
                axis.title=element_text(size=12,face="bold"),
                legend.title = element_blank(),
                strip.text.y.left = element_text(hjust=0.5,vjust = 1,angle=0,face="bold"))+
          coord_flip() + 
          guides(fill = guide_legend(reverse = TRUE))+ 
          guides(color = guide_legend(reverse = TRUE)) + 
          scale_color_manual(values = rev(c("#619CFF","#C77CFF", "#7CAE00", "goldenrod2", "darkorange4","#F4460D","#00BFC4","gray","#F8766D")[color_select]))
        
        #print(p)
        ggsave(file,plot=p,bg="white",width =26,units = "cm",height =30)
        #dev.off()
      }
    )
   
    output$heterotable <- renderTable({
      bb=data.frame()
      if(input$model=="Random-effects"){
        if(is.null(v$data)){return()}
        else
          X <- v$data
        numr=nrow(X)
        for(i in numr:1){
          if(as.numeric(X$sd[i])==0){
            X=X[-i,]
          }
        }
        # Count the number of studies
        N <- length(X$author)
        # Calculate the 95% CI for Mean, and 95% Predictive Interval
        if(!is.null(input$percentile)){
          quantile = (input$percentile)/100
        }
        b <- study_level_outcomes(X,quant=quantile)
        
        hakn=ifelse(input$cimethod=="Wald-type Interval",FALSE,TRUE)
        fmethod="REML"
        if(input$frmethod=="Paule-Mandel"){
          fmethod="PM"
        }
        if(input$frmethod=="DerSimonian-Laird"){
          fmethod="DL"
        }
        if(input$frmethod=="REML"){
          fmethod="REML"
        }
        ## Frequentist method
        b.freq <- FreqFit(b$mean, b$sd, b$n, quant = quantile,method = fmethod,hakn = hakn)
        
        RangeCheck=(input$RangeCheckr)
        
        if ('8' %in% RangeCheck){
          b.bayes=bb.bayes()
          bb=rbind(bb,c("Bayesian",
                        sprintf('%4.2f', as.numeric(b.bayes$tau)^2),
                        sprintf('%4.2f', as.numeric(b.bayes$sigma)^2),
                        ""))
          #bb=rbind(bb,c("Bayesian",b.bayes$tau^2))
        }
        
        if ('6' %in% RangeCheck){
          bb=rbind(bb,c("Frequentist",
                        sprintf('%4.2f', as.numeric((b.freq[[1]]$tau)^2)),
                        sprintf('%4.2f', as.numeric(b.freq$sigma)^2),
                        sprintf('%4.2f', as.numeric(b.freq$Isq))))
        }
        
        
        if(!((!'8' %in% RangeCheck)&(!'6' %in% RangeCheck))){
          colnames(bb) <- c("Method", "Between-Study Variance","Within-Study Variance","I^2")
        }
        
        
      }
      return(bb)
    })
    
    
    output$downloadStatTable2 <- downloadHandler( 
      filename = function(){
        paste("table.csv")
      },
      content = function(file){
        bb=data.frame()
        if(input$model=="Random-effects"){
          if(is.null(v$data)){return()}
          else
            X <- v$data
          numr=nrow(X)
          for(i in numr:1){
            if(as.numeric(X$sd[i])==0){
              X=X[-i,]
            }
          }
          # Count the number of studies
          N <- length(X$author)
          # Calculate the 95% CI for Mean, and 95% Predictive Interval
          if(!is.null(input$percentile)){
            quantile = (input$percentile)/100
          }
          b <- study_level_outcomes(X,quant=quantile)
          
          hakn=ifelse(input$cimethod=="Wald-type Interval",FALSE,TRUE)
          fmethod="REML"
          if(input$frmethod=="Paule-Mandel"){
            fmethod="PM"
          }
          if(input$frmethod=="DerSimonian-Laird"){
            fmethod="DL"
          }
          if(input$frmethod=="REML"){
            fmethod="REML"
          }
          ## Frequentist method
          b.freq <- FreqFit(b$mean, b$sd, b$n, quant = quantile,method = fmethod,hakn = hakn)
          
          RangeCheck=(input$RangeCheckr)
          
          if ('8' %in% RangeCheck){
            b.bayes=bb.bayes()
            bb=rbind(bb,c("Bayesian",
                          sprintf('%4.2f', as.numeric(b.bayes$tau)^2),
                          sprintf('%4.2f', as.numeric(b.bayes$sigma)^2),
                          sprintf('%4.2f', as.numeric(b.bayes$Isq))))
            #bb=rbind(bb,c("Bayesian",b.bayes$tau^2))
          }
          
          if ('6' %in% RangeCheck){
            bb=rbind(bb,c("Frequentist",
                          sprintf('%4.2f', as.numeric((b.freq[[1]]$tau)^2)),
                          sprintf('%4.2f', as.numeric(b.freq$sigma)^2),
                          sprintf('%4.2f', as.numeric(b.freq$Isq))))
          }
          
          
          if(!((!'8' %in% RangeCheck)&(!'6' %in% RangeCheck))){
            colnames(bb) <- c("Method", "Between-Study Variance","Within-Study Variance","I^2")
          }
          
          
        }
        datatable(bb)
        write.table(bb, file, sep=",", row.names=FALSE)
      })
    
    
    # Table of MA statistics - overall sens, spec etc
    output$statTable <- renderTable({
      
      if(input$model=="Random-effects"){
        RangeCheck=(input$RangeCheckr)
      }
      if(input$model=="Fixed-effects"){
        RangeCheck=(input$RangeCheckf)
      }
      content_select=rep(TRUE,7)
      if ('3' %in% RangeCheck){}else{content_select[1]=FALSE}
      if ('4' %in% RangeCheck){}else{content_select[2]=FALSE}
      if ('5' %in% RangeCheck){}else{content_select[3]=FALSE}
      if ('6' %in% RangeCheck){}else{content_select[4]=FALSE}
      if ('7' %in% RangeCheck){}else{content_select[5]=FALSE}
      if ('8' %in% RangeCheck){}else{content_select[6]=FALSE}
      if ('9' %in% RangeCheck){}else{content_select[7]=FALSE}
      
      
      if(is.null(v$data)){return()}
      else
        X <- v$data
      numr=nrow(X)
      for(i in numr:1){
        if(as.numeric(X$sd[i])==0){
          X=X[-i,]
        }
      }
      # Count the number of studies
      N <- length(X$author)
      # Calculate the 95% CI for Mean, and 95% Predictive Interval
      if(!is.null(input$percentile)){
        quantile = (input$percentile)/100
      }
      b <- study_level_outcomes(X,quant=quantile)
      #########################################################
      ## Three methods based on random-effects meta-analysis ##
      #########################################################
      
      ## Frequentist method
      hakn=ifelse(input$cimethod=="Wald-type Interval",FALSE,TRUE)
      fmethod="REML"
      if(input$frmethod=="Paule-Mandel"){
        fmethod="PM"
      }
      if(input$frmethod=="DerSimonian-Laird"){
        fmethod="DL"
      }
      if(input$frmethod=="REML"){
        fmethod="REML"
      }
      b.freq <- FreqFit(b$mean, b$sd, b$n, quant = quantile,method =fmethod,hakn = hakn)
      
      ## Overall mean from random-effects model (REML)
      pooled.mean.random <- b.freq[[1]]$TE.random
      
      ### Bayesian method
      set.seed(123)
      #b.bayes <- BayesFitCaseStudy(means = b$mean, sds =b$sd, n = b$n, quant = quantile,plot=FALSE)
      b.bayes=bb.bayes()
      
      ### Empirical method
      b.emp <- EmpFit(b$mean, b$sd, b$n, quant = quantile)
      
      #########################################################
      ## One method based on fixed-effects meta-analysis ##
      #########################################################
      ### Mixture distribution method (sample size weight)
      b.mix <- MixFit(means = b$mean, sds = b$sd, n = b$n, quant = quantile)
      pooled.mean.fixed <- weighted.mean(b$mean, b$n)
      weight_ss = b$n/sum(b$n)
      se.fixed = sqrt(sum(weight_ss^2*b$sd^2/b$n)/(sum(weight_ss))^2)
      
      l1=paste0(quantile*100, "% CI for Mean")
      l2=paste0(quantile*100, "% Predictive Interval")
      l3=paste0("95 % CI for Mean (Random)")
      l4=paste0("95 % CI for Mean (Fixed)")
      l5=paste0(quantile*100, "% Reference Interval")
      result.matrix <- matrix(c(b.freq[[1]]$lower.random, b.freq[[1]]$upper.random, 
                                b.freq[[1]]$lower.predict, b.freq[[1]]$upper.predict,
                               # pooled.mean.fixed-qnorm((1+quantile)/2)*se.fixed,pooled.mean.fixed+qnorm((1+quantile)/2)*se.fixed,
                                pooled.mean.fixed-1.96*se.fixed,pooled.mean.fixed+1.96*se.fixed, 
                                b.freq[[2]], b.freq[[3]],
                                b.emp[[1]], b.emp[[2]], 
                                b.bayes[[2]], b.bayes[[3]],
                                b.mix[1],b.mix[2]), nrow = 7,byrow = T)
      result.toadd <- cbind(c(rep("Overall", 3),rep(l5, 4)),  
                            c(rep(pooled.mean.random,2), pooled.mean.fixed, rep(pooled.mean.random,3), pooled.mean.fixed), 
                            c(l3, "New Study (Random)", l4, "Frequentist", "Empirical", "Bayesian", "Mixture"), result.matrix)
      result.toadd=result.toadd[content_select,]
      bb <- data.frame(result.toadd)
      colnames(bb) <- c("Interval Type", "Mean", "Method", "Lower", "Upper")
      bb$Mean <- sprintf('%4.2f', as.numeric(bb$Mean))
      bb$Lower <- sprintf('%4.2f', as.numeric(bb$Lower))
      bb$Upper <- sprintf('%4.2f', as.numeric(bb$Upper))
      bb
      })
    
    output$ScaledData=renderTable({
      if(is.null(v$data)){return()}
      else
        X <- v$data
      numr=nrow(X)
      for(i in numr:1){
        if(as.numeric(X$sd[i])==0){
          X=X[-i,]
        }
      }
      # Count the number of studies
      N <- length(X$author)
      # Calculate the 95% CI for Mean, and 95% Predictive Interval
      if(!is.null(input$percentile)){
        quantile = (input$percentile)/100
      }
      b <- study_level_outcomes(X,quant=quantile)
      sds=b$sd
      means=b$mean
      n=b$n
      sigma_hat <- sqrt(sum((n-1)*sds^2)/sum(n-1))
      mu_hat <-sum(n*means)/sum(n)
      var.e.w<- sum((n-1)*(means - mu_hat)^2)/sum(n-1)
      total.var <- var.e.w + sigma_hat^2
      
      #print(tau_hat)
      #print(sigma_hat)
      center_para=mu_hat
      #scale_para=1
      scale_para=sqrt(total.var)

      bb=X
      bb$author=X$author
      bb$mean=(b$mean-center_para)/scale_para
      bb$sd=b$sd/scale_para
      bb$n=b$n
      bb
    })
    
    # Allow users the option to download the table of statistics
    
    
    
    output$downloadStatTable <- downloadHandler(
      # Speicfy the file name 
      filename = function(){
        paste("table.csv")
      },
      content = function(file){
        # open the device
        # create the plot
        # close the device
        if(input$model=="Random-effects"){
          RangeCheck=(input$RangeCheckr)
        }
        if(input$model=="Fixed-effects"){
          RangeCheck=(input$RangeCheckf)
        }
        content_select=rep(TRUE,7)
        if ('3' %in% RangeCheck){}else{content_select[1]=FALSE}
        if ('4' %in% RangeCheck){}else{content_select[2]=FALSE}
        if ('5' %in% RangeCheck){}else{content_select[3]=FALSE}
        if ('6' %in% RangeCheck){}else{content_select[4]=FALSE}
        if ('7' %in% RangeCheck){}else{content_select[5]=FALSE}
        if ('8' %in% RangeCheck){}else{content_select[6]=FALSE}
        if ('9' %in% RangeCheck){}else{content_select[7]=FALSE}
        
        
        if(is.null(v$data)){return()}
        else
          X <- v$data
        numr=nrow(X)
        for(i in numr:1){
          if(as.numeric(X$sd[i])==0){
            X=X[-i,]
          }
        }
        # Count the number of studies
        N <- length(X$author)
        # Calculate the 95% CI for Mean, and 95% Predictive Interval
        if(!is.null(input$percentile)){
          quantile = (input$percentile)/100
        }
        b <- study_level_outcomes(X,quant=quantile)
        #########################################################
        ## Three methods based on random-effects meta-analysis ##
        #########################################################
        
        ## Frequentist method
        hakn=ifelse(input$cimethod=="Wald-type Interval",FALSE,TRUE)
        fmethod="REML"
        if(input$frmethod=="Paule-Mandel"){
          fmethod="PM"
        }
        if(input$frmethod=="DerSimonian-Laird"){
          fmethod="DL"
        }
        if(input$frmethod=="REML"){
          fmethod="REML"
        }
        b.freq <- FreqFit(b$mean, b$sd, b$n, quant = quantile,method = fmethod,hakn = hakn)
        
        ## Overall mean from random-effects model (REML)
        pooled.mean.random <- b.freq[[1]]$TE.random
        
        ### Bayesian method
        set.seed(123)
        #b.bayes <- BayesFitCaseStudy(means = b$mean, sds =b$sd, n = b$n, quant = quantile,plot=FALSE)
        b.bayes=bb.bayes()
        
        ### Empirical method
        b.emp <- EmpFit(b$mean, b$sd, b$n, quant = quantile)
        
        #########################################################
        ## One method based on fixed-effects meta-analysis ##
        #########################################################
        ### Mixture distribution method (sample size weight)
        b.mix <- MixFit(means = b$mean, sds = b$sd, n = b$n, quant = quantile)
        pooled.mean.fixed <- weighted.mean(b$mean, b$n)
        weight_ss = b$n/sum(b$n)
        se.fixed = sqrt(sum(weight_ss^2*b$sd^2/b$n)/(sum(weight_ss))^2)
        
        l1=paste0(quantile*100, "% CI for Mean")
        l2=paste0(quantile*100, "% Predictive Interval")
        l3=paste0("95 % CI for Mean (Random)")
        l4=paste0("95 % CI for Mean (Fixed)")
        l5=paste0(quantile*100, "% Reference Interval")
        result.matrix <- matrix(c(b.freq[[1]]$lower.random, b.freq[[1]]$upper.random, 
                                  b.freq[[1]]$lower.predict, b.freq[[1]]$upper.predict,
                                  # pooled.mean.fixed-qnorm((1+quantile)/2)*se.fixed,pooled.mean.fixed+qnorm((1+quantile)/2)*se.fixed,
                                  pooled.mean.fixed-1.96*se.fixed,pooled.mean.fixed+1.96*se.fixed, 
                                  b.freq[[2]], b.freq[[3]],
                                  b.emp[[1]], b.emp[[2]], 
                                  b.bayes[[2]], b.bayes[[3]],
                                  b.mix[1],b.mix[2]), nrow = 7,byrow = T)
        result.toadd <- cbind(c(rep("Overall", 3),rep(l5, 4)),  
                              c(rep(pooled.mean.random,2), pooled.mean.fixed, rep(pooled.mean.random,3), pooled.mean.fixed), 
                              c(l3, "New Study (Random)", l4, "Frequentist", "Empirical", "Bayesian", "Mixture"), result.matrix)
        result.toadd=result.toadd[content_select,]
        bb <- data.frame(result.toadd)
        colnames(bb) <- c("Interval Type", "Mean", "Method", "Lower", "Upper")
        bb$Mean <- sprintf('%4.2f', as.numeric(bb$Mean))
        bb$Lower <- sprintf('%4.2f', as.numeric(bb$Lower))
        bb$Upper <- sprintf('%4.2f', as.numeric(bb$Upper))
        #bb
      datatable(bb)
      write.table(bb, file, sep=",", row.names=FALSE)
    })
    
   
    
    
}

# Run the application 
shinyApp(ui = ui, server = server)
