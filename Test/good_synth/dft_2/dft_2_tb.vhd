library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity dft_2_tb is
  generic (N : integer := 8);
end entity;

architecture behavioural of dft_2_tb is
  component dft_2 is
      port (
            bs : in std_logic_vector (2*N-1 downto 0);
            res : out std_logic_vector (2*(N+1)-1 downto 0)
            );
  end component;

  signal a,b : signed (N-1 downto 0);
  signal inp : std_logic_vector(2*N-1 downto 0);
  signal res : std_logic_vector(2*(N+1)-1 downto 0);
  signal x,y : signed (N downto 0);

begin

  uut : dft_2 port map(
    bs => inp,
    res => res);

  inp <= std_logic_vector(a & b);
  x <= signed(res(2*(N+1)-1 downto N+1));
  y <= signed(res(N downto 0));

  process is
  begin
    for i in (-32) to 32 loop
      for j in (-32) to 32 loop
        a <= to_signed(i,a'length);
        b <= to_signed(j,b'length);
        wait for 2 ns;
        assert (std_logic_vector(x) = std_logic_vector(to_signed(i+j,x'length)))
          report "error" severity failure;
        assert (std_logic_vector(y) = std_logic_vector(to_signed(i-j,y'length)))
          report "error" severity failure;
      end loop;
    end loop;
    wait;
  end process;

end behavioural;
