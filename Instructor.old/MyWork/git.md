
### Check your git Remotes

From within VSCode and our repo, open a terminal (Terminal > New)
or (View > Terminal). Be advised you can configure VSCode to use
any of a variety of platform-native terminal programs. I use the
standard Terminal app on my Mac, and the bare bones *git bash* on
Windows, installable as part of "Git for Windows."

The main precondition for this part of the homework is that you
have git installed on your machine and that when you run git at
the command line of the open terminal, it actually run. Get your
system in shape so that that's the case.

Now use the following command to see what remote repositories
your cloned repository (on your laptop) has defined. Run the
command, git remote --v. The git command should run and list
the repo's remote repositories. For me the output is this

- origin  https://github.com/kevinsullivan/dmtl4 (fetch)
- origin  https://github.com/kevinsullivan/dmtl4 (push)

In other words, git in my laptop repo is configured to know
that I can push and pull from my laptop to my GitHub repo with
the commands *git C origin main" where C is fetch, push, etc.
You want will to see origin referring to *your* GitHub repo.
If you're lucky you'll also have a remote called *upstream*
that points to my repo.

If that's the case for you, you are done with this step and
can skip to the next one. Otherwise you need to add upstream
as a remote by issuing this command in your terminal:

```sh
git remote add upstream https://github.com/kevinsullivan/dmtl4
```

From this point on, you should be able can download into the
repo on your laptop the latest changes that I've pushed to my
repo on GitHub. You will do that with this command:

```sh
git pull upstream main
```

### Download The Latest Changes to Our Class Repo

At this point you're set up to pull the homework assignment and
any other latest updates from the class repo. Go ahead and do that.
Be sure you don't have problems with that. If you do, debug, as you
will need to do this kind of stuff throughout your career. If you
get really studk, we'll have a TA who can help. Once you've pulled
the latest changes,

### Open the Homework File



