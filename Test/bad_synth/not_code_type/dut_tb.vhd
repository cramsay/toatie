library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity dut_tb is
  generic (N : integer := 1);
end entity;

architecture behavioural of dut_tb is
  component dut is
    port(
      ext_0 : in std_logic_vector (N-1 downto 0);
      res : out std_logic_vector (N-1 downto 0)
      );
  end component;

  signal a,b : std_logic_vector (N-1 downto 0);

begin

  uut : dut port map(
    ext_0 => a,
    res => b);

end behavioural;
